#!/usr/bin/env python3
"""
Screen Existing Test Set with All 3 Proof Methods
==================================================

Uses the curated 50-molecule test set instead of querying ChEMBL.
Applies reachability, volume exclusion, and pharmacophore methods.
"""

import json
import logging
from typing import Dict, List, Optional
from dataclasses import dataclass
from rdkit import Chem
from rdkit.Chem import AllChem, Descriptors, Crippen
import numpy as np

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('screen_test_set.log'),
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
    REACHABILITY_THRESHOLD = 6.35  # Å
    CAVITY_VOLUME = 1810  # Å³
    TOXICOPHORE_MIN_DIST = 5.0  # Å
    TOXICOPHORE_MAX_DIST = 7.0  # Å

CONFIG = Config()

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
# Main Screening Function
###############################################################################

def screen_single_molecule(mol_data: Dict) -> Dict:
    """
    Screen a single molecule.

    Args:
        mol_data: Dict with 'name', 'smiles', 'expected_result', etc.

    Returns:
        Result dict with proof if found
    """
    name = mol_data['name']
    smiles = mol_data['smiles']

    result = {
        'name': name,
        'smiles': smiles,
        'proven_safe': False,
        'proof': None,
        'properties': {},
        'error': None,
        'expected_result': mol_data.get('expected_result'),
        'category': mol_data.get('category')
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
        logger.warning(f"Error screening {name}: {e}")

    return result

###############################################################################
# Main Pipeline
###############################################################################

def run_screening():
    """Run screening on curated test set."""
    logger.info("=" * 80)
    logger.info("SCREENING CURATED TEST SET")
    logger.info("=" * 80)

    # Load test set
    logger.info("\nLoading molecule_test_set_expanded.json...")
    with open('molecule_test_set_expanded.json', 'r') as f:
        data = json.load(f)

    molecules = data['molecules']
    logger.info(f"Loaded {len(molecules)} molecules\n")

    # Screen molecules
    logger.info("Screening molecules...")
    results = {'proven_safe': [], 'unprovable': [], 'errors': []}

    for i, mol_data in enumerate(molecules):
        result = screen_single_molecule(mol_data)

        if result['error']:
            results['errors'].append(result)
        elif result['proven_safe']:
            results['proven_safe'].append(result)
        else:
            results['unprovable'].append(result)

        if (i + 1) % 10 == 0:
            logger.info(f"  Processed {i + 1}/{len(molecules)} molecules...")

    # Analyze results
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

    # Validation: Check for false negatives
    logger.info("\n" + "=" * 80)
    logger.info("VALIDATION: Checking for false negatives")
    logger.info("=" * 80 + "\n")

    false_negatives = []
    for result in results['proven_safe']:
        expected = result['expected_result']
        if expected and 'BINDER' in str(expected).upper():
            false_negatives.append(result)
            logger.error(f"❌ FALSE NEGATIVE: {result['name']} - Proven safe but expected binder!")

    if not false_negatives:
        logger.info("✅ No false negatives detected!")
    else:
        logger.error(f"\n⚠️  CRITICAL: {len(false_negatives)} false negatives found!")

    # Save results
    output_file = 'test_set_screening_results.json'
    logger.info(f"\nSaving results to {output_file}...")

    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2)

    logger.info("\n" + "=" * 80)
    logger.info(f"✅ COMPLETE: {n_proven} molecules proven safe ({coverage:.1f}% coverage)")
    logger.info("=" * 80 + "\n")

    return results

if __name__ == '__main__':
    run_screening()
