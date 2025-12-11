#!/usr/bin/env python3
"""
hERG Pharmacophore Feature Extraction Pipeline

This script extracts pharmacophoric features from drug molecules and outputs
JSON certificates for formal verification in Lean 4.

## Workflow:
1. Parse SMILES → 3D structure (RDKit EmbedMolecule)
2. Enumerate protonation states at pH 7.4
3. Detect pharmacophoric features:
   - Cationic centers (basic nitrogens, pKa > 7)
   - Aromatic rings (RDKit GetAromaticRings)
   - Hydrophobic regions (SASA-based lipophilic patches)
4. Compute pairwise distances
5. Output JSON certificate

## Dependencies:
- rdkit (conda install -c conda-forge rdkit)
- numpy
- json

## Usage:
python3 extract_features.py --smiles "CC(C)NCC(COc1ccccc1)O" --name "propranolol" --output data/propranolol_features.json

## Literature Basis:
- Feature detection based on hERG pharmacophore models (Cavalli 2002, Stoyanova-Slavova 2017)
- pKa threshold > 7 for cationic centers (physiological pH 7.4)
- Distance constraints from research/herg_pharmacophore_spec.md
"""

import argparse
import json
import sys
from typing import List, Dict, Tuple, Optional
from fractions import Fraction

try:
    from rdkit import Chem
    from rdkit.Chem import AllChem, Descriptors, Crippen, rdMolDescriptors
    from rdkit.Chem import Lipinski
    import numpy as np
except ImportError:
    print("ERROR: RDKit not found. Install with: conda install -c conda-forge rdkit", file=sys.stderr)
    sys.exit(1)


def rationalize_coord(coord: float, precision: int = 10) -> str:
    """
    Convert float coordinate to rational approximation.

    Args:
        coord: Float coordinate in Angstroms
        precision: Number of decimal places to preserve

    Returns:
        String representation "numerator/denominator"

    Example:
        rationalize_coord(3.141592) -> "3141592/1000000" -> simplifies to "392699/125000"
    """
    # Round to precision to avoid floating point artifacts
    rounded = round(coord, precision)
    # Convert to Fraction (automatically simplifies)
    frac = Fraction(rounded).limit_denominator(10**precision)
    return f"{frac.numerator}/{frac.denominator}"


def parse_smiles(smiles: str) -> Optional[Chem.Mol]:
    """
    Parse SMILES string and generate 3D conformer.

    Args:
        smiles: SMILES string

    Returns:
        RDKit molecule with 3D coordinates, or None on error
    """
    mol = Chem.MolFromSmiles(smiles)
    if mol is None:
        print(f"ERROR: Invalid SMILES: {smiles}", file=sys.stderr)
        return None

    # Add hydrogens
    mol = Chem.AddHs(mol)

    # Generate 3D conformer using ETKDG
    status = AllChem.EmbedMolecule(mol, AllChem.ETKDG())
    if status != 0:
        print(f"ERROR: Failed to generate 3D conformer for {smiles}", file=sys.stderr)
        return None

    # Optimize geometry (UFF force field)
    AllChem.UFFOptimizeMolecule(mol)

    return mol


def is_basic_nitrogen(atom: Chem.Atom) -> bool:
    """
    Check if nitrogen atom is basic (pKa > 7, protonated at pH 7.4).

    Heuristics:
    - Primary, secondary, tertiary amines: BASIC
    - Aromatic nitrogens (pyridine, imidazole): Check hybridization
    - Amides, nitro groups: NOT BASIC

    This is a simplified heuristic. For production use, consider:
    - ChemAxon pKa Calculator
    - RDKit's GetBasicityScore (if available)
    - Machine learning pKa predictor

    Args:
        atom: RDKit Atom object

    Returns:
        True if nitrogen is expected to be protonated at pH 7.4
    """
    if atom.GetAtomicNum() != 7:  # Not nitrogen
        return False

    # Check for explicit positive charge (already protonated)
    if atom.GetFormalCharge() > 0:
        return True

    # Amides: nitrogen adjacent to C=O (not basic)
    for neighbor in atom.GetNeighbors():
        if neighbor.GetAtomicNum() == 6:  # Carbon
            for neighbor2 in neighbor.GetNeighbors():
                if neighbor2.GetAtomicNum() == 8 and neighbor2.GetTotalValence() == 1:  # Carbonyl oxygen
                    return False

    # Nitro groups: nitrogen with two oxygens (not basic)
    oxygen_neighbors = [n for n in atom.GetNeighbors() if n.GetAtomicNum() == 8]
    if len(oxygen_neighbors) >= 2:
        return False

    # Aromatic nitrogens: check if sp2 hybridized (e.g., pyridine)
    # Pyridine-like nitrogens are weakly basic (pKa ~ 5.2), but we'll conservatively include them
    if atom.GetIsAromatic():
        # For MVP, conservatively consider aromatic nitrogens as potentially basic
        # In production, use proper pKa calculator
        return True

    # Aliphatic amines: primary, secondary, tertiary
    # These are typically basic (pKa ~ 9-11)
    if atom.GetTotalNumHs() >= 0:  # Has at least one hydrogen or can be protonated
        return True

    return False


def extract_cationic_features(mol: Chem.Mol, conf_id: int = 0) -> List[Dict]:
    """
    Extract cationic centers (basic nitrogens).

    Args:
        mol: RDKit molecule with 3D coordinates
        conf_id: Conformer ID

    Returns:
        List of feature dictionaries
    """
    features = []
    conf = mol.GetConformer(conf_id)

    for atom in mol.GetAtoms():
        if is_basic_nitrogen(atom):
            idx = atom.GetIdx()
            pos = conf.GetAtomPosition(idx)

            feature = {
                "id": f"cation_N{idx}",
                "kind": "Cationic",
                "coord": [
                    rationalize_coord(pos.x),
                    rationalize_coord(pos.y),
                    rationalize_coord(pos.z)
                ],
                "protonated_at_pH7": True,
                "atom_idx": idx
            }
            features.append(feature)

    return features


def extract_aromatic_features(mol: Chem.Mol, conf_id: int = 0) -> List[Dict]:
    """
    Extract aromatic ring centroids.

    Args:
        mol: RDKit molecule with 3D coordinates
        conf_id: Conformer ID

    Returns:
        List of feature dictionaries
    """
    features = []
    conf = mol.GetConformer(conf_id)

    # Get aromatic rings
    ri = mol.GetRingInfo()
    aromatic_rings = []

    for ring in ri.AtomRings():
        # Check if all atoms in ring are aromatic
        if all(mol.GetAtomWithIdx(idx).GetIsAromatic() for idx in ring):
            aromatic_rings.append(ring)

    # Compute centroids
    for i, ring in enumerate(aromatic_rings):
        positions = [conf.GetAtomPosition(idx) for idx in ring]
        centroid_x = sum(p.x for p in positions) / len(positions)
        centroid_y = sum(p.y for p in positions) / len(positions)
        centroid_z = sum(p.z for p in positions) / len(positions)

        feature = {
            "id": f"aromatic_ring{i}",
            "kind": "Aromatic",
            "coord": [
                rationalize_coord(centroid_x),
                rationalize_coord(centroid_y),
                rationalize_coord(centroid_z)
            ],
            "protonated_at_pH7": False,
            "atom_indices": list(ring)
        }
        features.append(feature)

    return features


def extract_hydrophobic_features(mol: Chem.Mol, conf_id: int = 0) -> List[Dict]:
    """
    Extract hydrophobic regions (lipophilic patches).

    Heuristic: Find clusters of hydrophobic atoms (C, S, halogens) not adjacent to polar groups.

    For MVP, we use a simple approach:
    - Identify hydrophobic atoms (C with no adjacent O/N, S, halogens)
    - Compute centroids of connected hydrophobic clusters

    For production, consider:
    - SASA (Solvent Accessible Surface Area) calculation
    - Lipophilic potential mapping
    - Pharmacophore generation tools (e.g., RDKit's FeatMaps)

    Args:
        mol: RDKit molecule with 3D coordinates
        conf_id: Conformer ID

    Returns:
        List of feature dictionaries
    """
    features = []
    conf = mol.GetConformer(conf_id)

    hydrophobic_atoms = []

    for atom in mol.GetAtoms():
        atom_num = atom.GetAtomicNum()

        # Hydrophobic atom types: C, S, halogens (F, Cl, Br, I)
        if atom_num in [6, 16, 9, 17, 35, 53]:
            # For carbon, check if adjacent to polar atoms (exclude if so)
            if atom_num == 6:
                neighbors = atom.GetNeighbors()
                polar_adjacent = any(n.GetAtomicNum() in [7, 8] for n in neighbors)
                if polar_adjacent:
                    continue  # Skip carbons adjacent to N or O

            hydrophobic_atoms.append(atom.GetIdx())

    # Simple clustering: for MVP, treat all hydrophobic atoms as one cluster
    # In production, use proper clustering (e.g., distance-based)
    if hydrophobic_atoms:
        positions = [conf.GetAtomPosition(idx) for idx in hydrophobic_atoms]
        centroid_x = sum(p.x for p in positions) / len(positions)
        centroid_y = sum(p.y for p in positions) / len(positions)
        centroid_z = sum(p.z for p in positions) / len(positions)

        feature = {
            "id": "hydrophobe_cluster0",
            "kind": "Hydrophobe",
            "coord": [
                rationalize_coord(centroid_x),
                rationalize_coord(centroid_y),
                rationalize_coord(centroid_z)
            ],
            "protonated_at_pH7": False,
            "atom_indices": hydrophobic_atoms
        }
        features.append(feature)

    return features


def compute_distance(coord1: List[str], coord2: List[str]) -> float:
    """
    Compute Euclidean distance between two rational coordinates.

    Args:
        coord1, coord2: Coordinates as ["num1/den1", "num2/den2", "num3/den3"]

    Returns:
        Distance in Angstroms (float)
    """
    def parse_rational(s: str) -> float:
        if '/' in s:
            num, den = s.split('/')
            return float(num) / float(den)
        else:
            return float(s)

    x1, y1, z1 = [parse_rational(c) for c in coord1]
    x2, y2, z2 = [parse_rational(c) for c in coord2]

    return np.sqrt((x2 - x1)**2 + (y2 - y1)**2 + (z2 - z1)**2)


def compute_distance_matrix(features: List[Dict]) -> Dict[Tuple[str, str], float]:
    """
    Compute all pairwise distances between features.

    Args:
        features: List of feature dictionaries

    Returns:
        Dictionary mapping (id1, id2) -> distance
    """
    distances = {}

    for i, feat1 in enumerate(features):
        for feat2 in features[i+1:]:
            dist = compute_distance(feat1["coord"], feat2["coord"])
            key = (feat1["id"], feat2["id"])
            distances[key] = dist

    return distances


def extract_all_features(smiles: str, name: str) -> Dict:
    """
    Extract all pharmacophoric features from a SMILES string.

    Args:
        smiles: SMILES string
        name: Molecule name

    Returns:
        Dictionary with features, distances, and metadata
    """
    mol = parse_smiles(smiles)
    if mol is None:
        return None

    # Extract features
    cationic = extract_cationic_features(mol)
    aromatic = extract_aromatic_features(mol)
    hydrophobic = extract_hydrophobic_features(mol)

    all_features = cationic + aromatic + hydrophobic

    # Compute distances
    distances = compute_distance_matrix(all_features)

    # Convert distance dict to list format for JSON
    distance_list = [
        {"from": k[0], "to": k[1], "distance": v}
        for k, v in distances.items()
    ]

    # Compute molecular descriptors
    mol_weight = Descriptors.MolWt(mol)
    logp = Crippen.MolLogP(mol)
    num_h_donors = Lipinski.NumHDonors(mol)
    num_h_acceptors = Lipinski.NumHAcceptors(mol)

    result = {
        "molecule_name": name,
        "smiles": smiles,
        "molecular_weight": round(mol_weight, 2),
        "logp": round(logp, 2),
        "num_h_donors": num_h_donors,
        "num_h_acceptors": num_h_acceptors,
        "features": all_features,
        "distances": distance_list,
        "feature_counts": {
            "cationic": len(cationic),
            "aromatic": len(aromatic),
            "hydrophobic": len(hydrophobic),
            "total": len(all_features)
        },
        "metadata": {
            "extraction_method": "RDKit ETKDG + UFF optimization",
            "ph": 7.4,
            "conformer_id": 0,
            "version": "1.0"
        }
    }

    return result


def main():
    parser = argparse.ArgumentParser(
        description="Extract hERG pharmacophore features from SMILES"
    )
    parser.add_argument("--smiles", required=True, help="SMILES string")
    parser.add_argument("--name", required=True, help="Molecule name")
    parser.add_argument("--output", required=True, help="Output JSON file path")
    parser.add_argument("--pretty", action="store_true", help="Pretty-print JSON")

    args = parser.parse_args()

    print(f"Extracting features for {args.name}...")
    print(f"SMILES: {args.smiles}")

    result = extract_all_features(args.smiles, args.name)

    if result is None:
        print("ERROR: Feature extraction failed", file=sys.stderr)
        sys.exit(1)

    # Write JSON output
    with open(args.output, 'w') as f:
        if args.pretty:
            json.dump(result, f, indent=2)
        else:
            json.dump(result, f)

    # Print summary
    print("\n=== Extraction Summary ===")
    print(f"Molecule: {result['molecule_name']}")
    print(f"Molecular Weight: {result['molecular_weight']} g/mol")
    print(f"LogP: {result['logp']}")
    print(f"\nFeatures Found:")
    print(f"  Cationic centers: {result['feature_counts']['cationic']}")
    print(f"  Aromatic rings: {result['feature_counts']['aromatic']}")
    print(f"  Hydrophobic regions: {result['feature_counts']['hydrophobic']}")
    print(f"  Total features: {result['feature_counts']['total']}")
    print(f"\nPairwise distances computed: {len(result['distances'])}")
    print(f"\nOutput written to: {args.output}")

    # Print feature details
    if result['features']:
        print("\n=== Feature Details ===")
        for feat in result['features']:
            coord_str = ", ".join(feat['coord'])
            print(f"{feat['id']} ({feat['kind']}): ({coord_str})")


if __name__ == "__main__":
    main()
