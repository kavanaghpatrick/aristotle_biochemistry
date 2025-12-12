#!/usr/bin/env python3
"""
Extract hERG cavity atoms from PDB 7CN0.

This script extracts atoms within the hERG binding cavity for use in
steric clash detection. Cavity is defined as all atoms within 12 Å of
the Phe656 binding site center.

Output: data/herg_cavity_atoms.json
"""

from Bio.PDB import PDBParser
import numpy as np
import json
import sys

def get_residue_center(structure, chain_id='A', resid=656):
    """
    Calculate geometric center of a residue.

    Args:
        structure: BioPython structure object
        chain_id: Chain identifier (default 'A')
        resid: Residue number (default 656 for Phe656)

    Returns:
        np.array: [x, y, z] coordinates of residue center
    """
    for chain in structure.get_chains():
        if chain.id == chain_id:
            for residue in chain.get_residues():
                # BioPython uses (hetflag, resid, icode) tuple for residue id
                if residue.id[1] == resid:
                    coords = np.array([atom.coord for atom in residue.get_atoms()])
                    return np.mean(coords, axis=0)

    raise ValueError(f"Residue {chain_id}:{resid} not found in structure")

def extract_herg_cavity_atoms(pdb_file='data/7cn0.pdb', cavity_radius=12.0):
    """
    Extract cavity atoms from PDB 7CN0.

    Cavity definition:
    - All atoms within cavity_radius of Phe656 geometric center
    - Exclude Phe656 itself (it's the target we're checking reachability to)
    - Include all protein atoms in cavity region

    Args:
        pdb_file: Path to PDB file
        cavity_radius: Radius in Angstroms for cavity definition (default 12.0)

    Returns:
        list: Cavity atoms with element, position, residue info
    """
    print(f"Parsing PDB file: {pdb_file}")
    parser = PDBParser(QUIET=True)
    structure = parser.get_structure('hERG', pdb_file)

    # Find Phe656 center (known binding site)
    print("Finding Phe656 binding site center...")
    try:
        phe656_center = get_residue_center(structure, chain_id='A', resid=656)
        print(f"  Phe656 center: ({phe656_center[0]:.2f}, {phe656_center[1]:.2f}, {phe656_center[2]:.2f})")
    except ValueError as e:
        print(f"ERROR: {e}")
        print("Trying alternative chain/residue numbering...")

        # Try to find Phe656 in any chain
        for chain in structure.get_chains():
            for residue in chain.get_residues():
                if residue.get_resname() == 'PHE':
                    resid = residue.id[1]
                    if 650 <= resid <= 660:  # Likely candidate
                        phe656_center = get_residue_center(structure, chain_id=chain.id, resid=resid)
                        print(f"  Found PHE at chain {chain.id}, residue {resid}")
                        print(f"  Center: ({phe656_center[0]:.2f}, {phe656_center[1]:.2f}, {phe656_center[2]:.2f})")
                        break

    # Extract cavity atoms
    print(f"Extracting atoms within {cavity_radius} Å of Phe656...")
    cavity_atoms = []
    atom_count = 0

    for chain in structure.get_chains():
        for residue in chain.get_residues():
            # Skip Phe656 itself (it's the binding target, not part of cavity walls)
            if residue.id[1] == 656:
                continue

            for atom in residue.get_atoms():
                atom_count += 1
                dist = np.linalg.norm(atom.coord - phe656_center)

                if dist <= cavity_radius:
                    cavity_atoms.append({
                        'element': atom.element.strip(),  # Remove whitespace
                        'position': [float(x) for x in atom.coord],  # Convert numpy to Python float
                        'residue_name': residue.get_resname(),
                        'residue_id': int(residue.id[1]),  # Convert to Python int
                        'chain_id': chain.id,
                        'atom_name': atom.name,
                        'distance_from_phe656': float(round(dist, 2))  # Convert to Python float
                    })

    print(f"  Total atoms in structure: {atom_count}")
    print(f"  Cavity atoms found: {len(cavity_atoms)}")

    # Statistics
    if cavity_atoms:
        elements = {}
        for atom in cavity_atoms:
            elem = atom['element']
            elements[elem] = elements.get(elem, 0) + 1

        print(f"\nElement distribution in cavity:")
        for elem, count in sorted(elements.items(), key=lambda x: -x[1]):
            print(f"  {elem}: {count}")

        # Distance distribution
        distances = [a['distance_from_phe656'] for a in cavity_atoms]
        print(f"\nDistance distribution:")
        print(f"  Min: {min(distances):.2f} Å")
        print(f"  Max: {max(distances):.2f} Å")
        print(f"  Mean: {np.mean(distances):.2f} Å")

    return cavity_atoms, [float(x) for x in phe656_center]  # Convert to Python floats

def main():
    # Extract cavity atoms
    cavity_atoms, phe656_center = extract_herg_cavity_atoms()

    # Save to JSON
    output_file = 'data/herg_cavity_atoms.json'
    output_data = {
        'pdb_file': '7cn0.pdb',
        'pdb_source': 'RCSB PDB (Wang & MacKinnon, 2017)',
        'cavity_definition': 'Atoms within 12 Å of Phe656 geometric center',
        'phe656_center': phe656_center,
        'cavity_radius_angstroms': 12.0,
        'total_cavity_atoms': len(cavity_atoms),
        'cavity_atoms': cavity_atoms
    }

    with open(output_file, 'w') as f:
        json.dump(output_data, f, indent=2)

    print(f"\n✅ Saved {len(cavity_atoms)} cavity atoms to {output_file}")
    print(f"   File size: {len(json.dumps(output_data)) / 1024:.1f} KB")

    return 0

if __name__ == '__main__':
    sys.exit(main())
