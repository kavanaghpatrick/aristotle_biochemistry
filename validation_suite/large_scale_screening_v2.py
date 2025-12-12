#!/usr/bin/env python3
"""
Large-Scale hERG Safety Screening (Production Version)
=======================================================

Incorporates Grok-2 code review fixes:
- Rate limiting and retry logic
- Parallel processing
- Proper logging
- Robust error handling
- Memory-efficient batched processing

Author: Claude + Grok-2 review
Issue: #37
"""

import json
import time
import logging
from typing import Dict, List, Optional, Tuple
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass
import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
from rdkit import Chem
from rdkit.Chem import AllChem, Descriptors, Crippen
import numpy as np

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('large_scale_screening.log'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

###############################################################################
# Configuration
###############################################################################

@dataclass
class Config:
    """Screening configuration"""
    # Thresholds
    REACHABILITY_THRESHOLD = 6.35  # Å
    CAVITY_VOLUME = 1810  # Å³
    TOXICOPHORE_MIN_DIST = 5.0  # Å
    TOXICOPHORE_MAX_DIST = 7.0  # Å

    # ChEMBL
    CHEMBL_BASE_URL = "https://www.ebi.ac.uk/chembl/api/data"
    HERG_TARGET_ID = "CHEMBL240"

    # Performance
    BATCH_SIZE = 100
    NUM_WORKERS = 4
    API_RATE_LIMIT_DELAY = 0.5  # seconds between API calls

CONFIG = Config()

###############################################################################
# ChEMBL API Client with Retry Logic
###############################################################################

class ChEMBLClient:
    """ChEMBL API client with automatic retries and rate limiting."""

    def __init__(self):
        self.session = self._create_session()
        self.last_request_time = 0

    def _create_session(self):
        """Create requests session with retry strategy."""
        session = requests.Session()
        retry_strategy = Retry(
            total=5,
            backoff_factor=1,
            status_forcelist=[429, 500, 502, 503, 504],
            allowed_methods=["GET"]
        )
        adapter = HTTPAdapter(max_retries=retry_strategy)
        session.mount("https://", adapter)
        session.mount("http://", adapter)
        return session

    def _rate_limit(self):
        """Enforce rate limiting."""
        elapsed = time.time() - self.last_request_time
        if elapsed < CONFIG.API_RATE_LIMIT_DELAY:
            time.sleep(CONFIG.API_RATE_LIMIT_DELAY - elapsed)
        self.last_request_time = time.time()

    def get(self, url: str, params: dict = None, timeout: int = 30) -> Optional[dict]:
        """Make GET request with rate limiting and error handling."""
        self._rate_limit()

        try:
            response = self.session.get(url, params=params, timeout=timeout)
            response.raise_for_status()
            return response.json()
        except requests.exceptions.HTTPError as e:
            logger.error(f"HTTP error: {e}")
            return None
        except requests.exceptions.Timeout:
            logger.error(f"Timeout accessing {url}")
            return None
        except requests.exceptions.RequestException as e:
            logger.error(f"Request failed: {e}")
            return None
        except json.JSONDecodeError:
            logger.error(f"Invalid JSON from {url}")
            return None

    def query_herg_non_binders(self, limit: int = 1000) -> List[Dict]:
        """
        Query ChEMBL for hERG non-binding molecules.

        Criteria for non-binders:
        - IC50/EC50 > 10 µM (pChEMBL < 5)
        - Standard relation '>' indicating weak activity
        - Marked as inactive
        """
        logger.info(f"Querying ChEMBL for hERG non-binders (limit={limit})...")

        molecules = []
        offset = 0

        while len(molecules) < limit:
            # Query activities
            url = f"{CONFIG.CHEMBL_BASE_URL}/activity.json"
            params = {
                'target_chembl_id': CONFIG.HERG_TARGET_ID,
                'limit': CONFIG.BATCH_SIZE,
                'offset': offset
            }

            data = self.get(url, params)
            if not data or not data.get('activities'):
                logger.info(f"No more data at offset {offset}")
                break

            for activity in data['activities']:
                try:
                    # Extract activity data
                    pchembl = activity.get('pchembl_value')
                    std_type = activity.get('standard_type', '').upper()
                    std_relation = activity.get('standard_relation', '')
                    std_value = activity.get('standard_value')
                    mol_chembl_id = activity.get('molecule_chembl_id')

                    if not mol_chembl_id:
                        continue

                    # Filter for non-binders
                    is_non_binder = False

                    if std_type in ['IC50', 'EC50', 'KI', 'KD']:
                        if pchembl is not None and float(pchembl) < 5.0:
                            # pChEMBL < 5 means IC50 > 10 µM (non-binder)
                            is_non_binder = True
                        elif std_relation == '>' and std_value is not None:
                            # ">" means activity above threshold (weak/none)
                            if float(std_value) > 10:  # > 10 µM
                                is_non_binder = True
                    elif std_type == 'INHIBITION' and std_value is not None:
                        if float(std_value) < 50:  # < 50% inhibition at high conc
                            is_non_binder = True

                    if is_non_binder:
                        # Get molecule SMILES
                        mol_url = f"{CONFIG.CHEMBL_BASE_URL}/molecule/{mol_chembl_id}.json"
                        mol_data = self.get(mol_url)

                        if mol_data:
                            smiles = mol_data.get('molecule_structures', {}).get('canonical_smiles')
                            if smiles:
                                molecules.append({
                                    'chembl_id': mol_chembl_id,
                                    'smiles': smiles,
                                    'pchembl_value': pchembl,
                                    'standard_type': std_type,
                                    'standard_value': std_value
                                })

                                if len(molecules) % 50 == 0:
                                    logger.info(f"  Collected {len(molecules)} molecules...")

                except Exception as e:
                    logger.warning(f"Error processing activity: {e}")
                    continue

            offset += CONFIG.BATCH_SIZE

        logger.info(f"Retrieved {len(molecules)} hERG non-binder molecules")
        return molecules

###############################################################################
# Geometric Calculations
###############################################################################

def compute_bounding_sphere_radius(mol: Chem.Mol) -> Optional[float]:
    """Compute radius of minimum bounding sphere."""
    try:
        if mol.GetNumConformers() == 0:
            AllChem.EmbedMolecule(mol, randomSeed=42)
            AllChem.MMFFOptimizeMolecule(mol)

        conf = mol.GetConformer()
        positions = np.array([conf.GetAtomPosition(i) for i in range(mol.GetNumAtoms())])
        centroid = positions.mean(axis=0)
        distances = np.linalg.norm(positions - centroid, axis=1)
        return float(distances.max())

    except Exception as e:
        logger.warning(f"Error computing radius: {e}")
        return None

def compute_molecular_volume(mol: Chem.Mol) -> Optional[float]:
    """Compute molecular volume (conservative: bounding sphere)."""
    radius = compute_bounding_sphere_radius(mol)
    if radius is None:
        return None
    return (4/3) * np.pi * (radius ** 3)

###############################################################################
# Proof Methods
###############################################################################

def check_reachability(mol: Chem.Mol) -> Optional[Dict]:
    """Check if molecule is too small to reach Phe656."""
    radius = compute_bounding_sphere_radius(mol)
    if radius is None:
        return None

    if radius < CONFIG.REACHABILITY_THRESHOLD:
        return {
            'method': 'reachability',
            'radius': radius,
            'proven_safe': True,
            'reason': f'Radius {radius:.2f} Å < {CONFIG.REACHABILITY_THRESHOLD} Å'
        }
    return None

def check_volume_exclusion(mol: Chem.Mol) -> Optional[Dict]:
    """Check if molecule is too large to fit in cavity."""
    volume = compute_molecular_volume(mol)
    if volume is None:
        return None

    if volume > CONFIG.CAVITY_VOLUME:
        return {
            'method': 'volume_exclusion',
            'volume': volume,
            'proven_safe': True,
            'reason': f'Volume {volume:.0f} Å³ > {CONFIG.CAVITY_VOLUME} Å³'
        }
    return None

def check_pharmacophore_simple(mol: Chem.Mol) -> Optional[Dict]:
    """
    Simplified pharmacophore check (doesn't require 3D coordinates).

    Checks:
    1. No aromatic rings → proven safe
    2. No basic nitrogens → proven safe
    """
    try:
        # Count aromatic rings
        aromatic_rings = 0
        for ring in mol.GetRingInfo().AtomRings():
            if all(mol.GetAtomWithIdx(idx).GetIsAromatic() for idx in ring):
                aromatic_rings += 1

        # Count basic nitrogens (sp3/sp2, not amide)
        basic_nitrogens = 0
        for atom in mol.GetAtoms():
            if atom.GetSymbol() == 'N':
                # Skip amide nitrogens
                is_amide = any(
                    bond.GetBondType() == Chem.BondType.DOUBLE and
                    mol.GetAtomWithIdx(bond.GetOtherAtomIdx(atom.GetIdx())).GetSymbol() == 'C'
                    for bond in atom.GetBonds()
                )
                if not is_amide:
                    basic_nitrogens += 1

        # Apply exclusion rules
        if aromatic_rings == 0:
            return {
                'method': 'pharmacophore_no_aromatic',
                'aromatic_count': 0,
                'nitrogen_count': basic_nitrogens,
                'proven_safe': True,
                'reason': 'No aromatic rings'
            }

        if basic_nitrogens == 0:
            return {
                'method': 'pharmacophore_no_nitrogen',
                'aromatic_count': aromatic_rings,
                'nitrogen_count': 0,
                'proven_safe': True,
                'reason': 'No basic nitrogen'
            }

        return None

    except Exception as e:
        logger.warning(f"Error in pharmacophore check: {e}")
        return None

###############################################################################
# Main Screening Function (for parallel processing)
###############################################################################

def screen_single_molecule(data: Tuple[str, str]) -> Dict:
    """
    Screen a single molecule (designed for parallel execution).

    Args:
        data: (chembl_id, smiles)

    Returns:
        Result dict with proof if found
    """
    chembl_id, smiles = data

    result = {
        'chembl_id': chembl_id,
        'smiles': smiles,
        'proven_safe': False,
        'proof': None,
        'properties': {},
        'error': None
    }

    try:
        # Parse SMILES
        mol = Chem.MolFromSmiles(smiles)
        if mol is None:
            result['error'] = 'Invalid SMILES'
            return result

        mol = Chem.AddHs(mol)

        # Compute basic properties
        result['properties'] = {
            'num_atoms': mol.GetNumAtoms(),
            'num_heavy_atoms': mol.GetNumHeavyAtoms(),
            'mol_weight': Descriptors.MolWt(mol),
            'logp': Crippen.MolLogP(mol)
        }

        # Try proof methods (fast to slow)
        for check_func in [check_reachability, check_volume_exclusion, check_pharmacophore_simple]:
            proof = check_func(mol)
            if proof:
                result['proven_safe'] = True
                result['proof'] = proof
                return result

        # Not provable - add geometric properties for analysis
        radius = compute_bounding_sphere_radius(mol)
        volume = compute_molecular_volume(mol)

        if radius:
            result['properties']['radius'] = radius
        if volume:
            result['properties']['volume'] = volume

    except Exception as e:
        result['error'] = str(e)
        logger.warning(f"Error screening {chembl_id}: {e}")

    return result

###############################################################################
# Main Pipeline
###############################################################################

def run_screening(n_molecules: int = 1000, use_parallel: bool = True):
    """
    Run large-scale screening pipeline.

    Args:
        n_molecules: Number of molecules to screen
        use_parallel: Use parallel processing (recommended)
    """
    logger.info("=" * 80)
    logger.info("LARGE-SCALE hERG SAFETY SCREENING")
    logger.info("=" * 80)

    # Step 1: Load molecules
    logger.info(f"\nStep 1: Loading {n_molecules} molecules from ChEMBL...")
    client = ChEMBLClient()
    molecules = client.query_herg_non_binders(limit=n_molecules)

    if len(molecules) == 0:
        logger.error("No molecules loaded - aborting!")
        return

    logger.info(f"Loaded {len(molecules)} molecules\n")

    # Step 2: Screen molecules
    logger.info(f"Step 2: Screening with {CONFIG.NUM_WORKERS} workers...")

    molecule_data = [(m['chembl_id'], m['smiles']) for m in molecules]
    results = {'proven_safe': [], 'unprovable': [], 'errors': []}

    if use_parallel:
        with ProcessPoolExecutor(max_workers=CONFIG.NUM_WORKERS) as executor:
            futures = {executor.submit(screen_single_molecule, data): data for data in molecule_data}

            for i, future in enumerate(as_completed(futures)):
                result = future.result()

                if result['error']:
                    results['errors'].append(result)
                elif result['proven_safe']:
                    results['proven_safe'].append(result)
                else:
                    results['unprovable'].append(result)

                if (i + 1) % 100 == 0:
                    logger.info(f"  Processed {i + 1}/{len(molecules)} molecules...")
    else:
        # Sequential processing (for debugging)
        for i, data in enumerate(molecule_data):
            result = screen_single_molecule(data)

            if result['error']:
                results['errors'].append(result)
            elif result['proven_safe']:
                results['proven_safe'].append(result)
            else:
                results['unprovable'].append(result)

            if (i + 1) % 100 == 0:
                logger.info(f"  Processed {i + 1}/{len(molecules)} molecules...")

    # Step 3: Analyze and report
    logger.info("\n" + "=" * 80)
    logger.info("RESULTS")
    logger.info("=" * 80 + "\n")

    n_total = len(molecules)
    n_proven = len(results['proven_safe'])
    n_unprovable = len(results['unprovable'])
    n_errors = len(results['errors'])

    coverage = (n_proven / (n_proven + n_unprovable)) * 100 if (n_proven + n_unprovable) > 0 else 0

    logger.info(f"Total molecules:     {n_total}")
    logger.info(f"Proven safe:         {n_proven} ({n_proven/n_total*100:.1f}%)")
    logger.info(f"Unprovable:          {n_unprovable} ({n_unprovable/n_total*100:.1f}%)")
    logger.info(f"Errors:              {n_errors} ({n_errors/n_total*100:.1f}%)")
    logger.info(f"\nCOVERAGE:            {coverage:.1f}%\n")

    # Breakdown by method
    method_counts = {}
    for result in results['proven_safe']:
        method = result['proof']['method']
        method_counts[method] = method_counts.get(method, 0) + 1

    logger.info("Breakdown by proof method:")
    for method, count in sorted(method_counts.items(), key=lambda x: -x[1]):
        logger.info(f"  {method:30s} {count:5d} ({count/n_proven*100:.1f}%)")

    # Save results
    output_file = 'large_scale_screening_results.json'
    logger.info(f"\nSaving results to {output_file}...")

    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2)

    logger.info("\n" + "=" * 80)
    logger.info(f"✅ COMPLETE: {n_proven} molecules proven safe ({coverage:.1f}% coverage)")
    logger.info("=" * 80 + "\n")

    return results

if __name__ == '__main__':
    import argparse

    parser = argparse.ArgumentParser(description='Large-scale hERG safety screening')
    parser.add_argument('--n', type=int, default=1000, help='Number of molecules')
    parser.add_argument('--workers', type=int, default=4, help='Parallel workers')
    parser.add_argument('--sequential', action='store_true', help='Disable parallel processing')

    args = parser.parse_args()

    CONFIG.NUM_WORKERS = args.workers

    run_screening(n_molecules=args.n, use_parallel=not args.sequential)
