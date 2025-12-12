#!/usr/bin/env python3
"""
Quick validation: Do unprovable molecules have steric clashes?

This is a FAST test to validate the approach works BEFORE
investing in full Lean formalization.

Goal: Find 2-3 molecules with clashes → validates approach
"""

import json
import numpy as np
from rdkit import Chem
from rdkit.Chem import AllChem

# Van der Waals radii (Bondi, 1964) - Physical constants
VDW_RADII = {
    'C': 1.70, 'N': 1.55, 'O': 1.52, 'S': 1.80,
    'H': 1.20, 'F': 1.47, 'Cl': 1.75, 'Br': 1.85, 'P': 1.80
}

def quick_clash_check(smiles, mol_name, num_conformers=10, cavity_sample=20):
    """
    Quick and dirty clash check.

    Args:
        smiles: SMILES string
        mol_name: Molecule name for logging
        num_conformers: Number of conformers to test (default 10, not 100)
        cavity_sample: Number of cavity atoms to check (default 20, not all 244)

    Returns:
        dict with clash info or None
    """
    # Load cavity atoms
    with open('data/herg_cavity_atoms.json', 'r') as f:
        cavity_data = json.load(f)
    cavity_atoms = cavity_data['cavity_atoms'][:cavity_sample]  # Just first 20

    # Generate conformers
    mol = Chem.MolFromSmiles(smiles)
    if mol is None:
        print(f"  {mol_name}: ERROR - Invalid SMILES")
        return None

    mol = Chem.AddHs(mol)

    # Generate fewer conformers for speed
    try:
        conf_ids = AllChem.EmbedMultipleConfs(
            mol,
            numConfs=num_conformers,
            params=AllChem.ETKDGv3()
        )
    except Exception as e:
        print(f"  {mol_name}: ERROR - Conformer generation failed: {e}")
        return None

    if len(conf_ids) == 0:
        print(f"  {mol_name}: ERROR - No conformers generated")
        return None

    print(f"  {mol_name}: Testing {len(conf_ids)} conformers vs {len(cavity_atoms)} cavity atoms...")

    # Check for clashes
    for conf_id in conf_ids:
        conformer = mol.GetConformer(conf_id)

        for mol_atom_idx in range(mol.GetNumAtoms()):
            mol_atom = mol.GetAtomWithIdx(mol_atom_idx)
            mol_elem = mol_atom.GetSymbol()
            mol_vdw = VDW_RADII.get(mol_elem, 1.70)
            mol_pos = np.array(conformer.GetAtomPosition(mol_atom_idx))

            for cavity_idx, cavity_atom in enumerate(cavity_atoms):
                cavity_elem = cavity_atom['element']
                cavity_vdw = VDW_RADII.get(cavity_elem, 1.70)
                cavity_pos = np.array(cavity_atom['position'])

                distance = np.linalg.norm(mol_pos - cavity_pos)
                threshold = mol_vdw + cavity_vdw

                if distance < threshold:
                    overlap = threshold - distance
                    print(f"    ✅ CLASH FOUND!")
                    print(f"       Conformer {conf_id}, mol atom {mol_atom_idx} ({mol_elem})")
                    print(f"       vs cavity atom {cavity_idx} ({cavity_elem})")
                    print(f"       Distance: {distance:.3f} Å < Threshold: {threshold:.3f} Å")
                    print(f"       Overlap: {overlap:.3f} Å")
                    return {
                        'has_clash': True,
                        'conformer_id': int(conf_id),
                        'mol_atom_idx': mol_atom_idx,
                        'mol_element': mol_elem,
                        'mol_pos': mol_pos.tolist(),
                        'cavity_atom_idx': cavity_idx,
                        'cavity_element': cavity_elem,
                        'cavity_pos': cavity_pos.tolist(),
                        'distance': float(distance),
                        'threshold': float(threshold),
                        'overlap': float(overlap)
                    }

    print(f"    ❌ No clashes found")
    return {'has_clash': False}

def main():
    print("=" * 60)
    print("QUICK CLASH TEST - Validating Steric Clash Approach")
    print("=" * 60)

    # Test molecules from unprovable list
    # These are currently unprovable - if they have clashes, we can prove them!
    test_molecules = [
        ("Warfarin", "CC(=O)CC(C1=CC=CC=C1)C2=C(C3=CC=CC=C3OC2=O)O"),
        ("Atorvastatin", "CC(C)C1=C(C(=C(N1CC[C@H](C[C@H](CC(=O)O)O)O)C2=CC=C(C=C2)F)C3=CC=CC=C3)C(=O)NC4=CC=CC=C4"),
        ("Colchicine", "CC(=O)N[C@H]1CC2=CC(=C(C(=C2C=C1OC)OC)OC)OC"),
        ("Tamoxifen", "CCC(=C(C1=CC=CC=C1)C2=CC=C(C=C2)OCCN(C)C)C3=CC=CC=C3"),
        ("Metoprolol", "CCOC(=O)C1=CC=CC=C1OC2CCNC2C"),
    ]

    results = []
    clashes_found = 0

    for mol_name, smiles in test_molecules:
        print(f"\n{mol_name}:")
        result = quick_clash_check(smiles, mol_name)

        if result and result.get('has_clash'):
            clashes_found += 1
            results.append({
                'molecule': mol_name,
                'smiles': smiles,
                **result
            })

    print("\n" + "=" * 60)
    print(f"RESULTS: Found clashes in {clashes_found}/{len(test_molecules)} molecules")
    print("=" * 60)

    if clashes_found >= 2:
        print("\n✅ SUCCESS: Approach validated!")
        print(f"   Found {clashes_found} molecules with steric clashes")
        print("   Next step: Full Lean formalization + Python implementation")

        # Save results
        with open('validation_suite/quick_clash_results.json', 'w') as f:
            json.dump(results, f, indent=2)
        print(f"\n   Saved results to validation_suite/quick_clash_results.json")
    else:
        print("\n❌ FAILURE: Approach may not work")
        print(f"   Only found {clashes_found} molecules with clashes")
        print("   Consider: Graph substructure approach instead (Issue #32)")

    return 0 if clashes_found >= 2 else 1

if __name__ == '__main__':
    import sys
    sys.exit(main())
