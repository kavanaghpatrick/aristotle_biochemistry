#!/usr/bin/env python3
"""
Calculate hERG binding cavity volume from PDB structure.

Uses simple sphere approximation based on key residues (Phe656, Tyr652).
Conservative estimate for formal proofs.
"""

import numpy as np
from Bio.PDB import PDBParser
from scipy.spatial import ConvexHull

def extract_binding_site_residues(pdb_file: str, residue_ids: list = [656, 652]) -> list:
    """
    Extract key binding site residues from PDB.

    Args:
        pdb_file: Path to PDB file
        residue_ids: List of residue numbers to extract (default: Phe656, Tyr652)

    Returns:
        List of atom coordinates from specified residues
    """
    parser = PDBParser(QUIET=True)
    structure = parser.get_structure('hERG', pdb_file)

    binding_site_atoms = []

    for model in structure:
        for chain in model:
            for residue in chain:
                res_id = residue.get_id()[1]

                if res_id in residue_ids:
                    for atom in residue:
                        coord = atom.get_coord()
                        binding_site_atoms.append({
                            'chain': chain.get_id(),
                            'residue': residue.get_resname(),
                            'res_id': res_id,
                            'atom': atom.get_name(),
                            'coord': coord
                        })

    print(f"Extracted {len(binding_site_atoms)} atoms from {len(set(a['res_id'] for a in binding_site_atoms))} residues")

    return binding_site_atoms

def calculate_cavity_sphere(atoms: list) -> tuple:
    """
    Calculate cavity as sphere enclosing key residues.

    Conservative estimate: uses centroid + max distance.

    Returns:
        (center, radius) tuple
    """
    coords = np.array([a['coord'] for a in atoms])

    center = coords.mean(axis=0)
    distances = np.linalg.norm(coords - center, axis=1)
    radius = distances.max()

    return center, radius

def calculate_cavity_convex_hull(atoms: list) -> float:
    """
    Calculate cavity volume using convex hull of key residues.

    More accurate than sphere, still conservative.
    """
    coords = np.array([a['coord'] for a in atoms])

    try:
        hull = ConvexHull(coords)
        return hull.volume
    except Exception as e:
        print(f"Warning: ConvexHull failed ({e}), falling back to sphere")
        center, radius = calculate_cavity_sphere(atoms)
        return (4/3) * np.pi * radius**3

def analyze_herg_cavity(pdb_file: str = "data/pdb/7cn0.pdb"):
    """
    Comprehensive analysis of hERG binding cavity.
    """
    print(f"\n{'='*80}")
    print(f"hERG Binding Cavity Analysis")
    print(f"{'='*80}")
    print(f"PDB: {pdb_file}")

    # Extract key residues (Phe656 and Tyr652 from all chains)
    print(f"\n📍 Extracting key binding site residues...")
    atoms = extract_binding_site_residues(pdb_file, residue_ids=[656, 652, 623, 624, 625])

    # Calculate sphere approximation
    print(f"\n⚪ Sphere Approximation:")
    center, radius = calculate_cavity_sphere(atoms)
    sphere_volume = (4/3) * np.pi * radius**3

    print(f"  Center: ({center[0]:.2f}, {center[1]:.2f}, {center[2]:.2f})")
    print(f"  Radius: {radius:.2f} Å")
    print(f"  Volume: {sphere_volume:.0f} Å³")

    # Calculate convex hull
    print(f"\n🔷 Convex Hull:")
    hull_volume = calculate_cavity_convex_hull(atoms)
    print(f"  Volume: {hull_volume:.0f} Å³")

    # Analyze per-chain Phe656 positions
    print(f"\n📊 Phe656 Positions (4 chains):")
    phe656_atoms = [a for a in atoms if a['res_id'] == 656 and a['atom'] == 'CA']

    for atom in phe656_atoms:
        print(f"  Chain {atom['chain']}: ({atom['coord'][0]:.2f}, {atom['coord'][1]:.2f}, {atom['coord'][2]:.2f})")

    # Calculate Phe656 spacing (distance between chains)
    if len(phe656_atoms) >= 2:
        coords = np.array([a['coord'] for a in phe656_atoms])
        distances = []
        for i in range(len(coords)):
            for j in range(i+1, len(coords)):
                dist = np.linalg.norm(coords[i] - coords[j])
                distances.append(dist)

        print(f"\n📏 Phe656 Inter-chain Distances:")
        print(f"  Min: {min(distances):.2f} Å")
        print(f"  Max: {max(distances):.2f} Å")
        print(f"  Mean: {np.mean(distances):.2f} Å")

    # Summary
    print(f"\n{'='*80}")
    print(f"CAVITY VOLUME ESTIMATES:")
    print(f"{'='*80}")
    print(f"Sphere approximation: {sphere_volume:.0f} Å³")
    print(f"Convex hull:          {hull_volume:.0f} Å³")
    print(f"\nFor formal proofs, use: {max(sphere_volume, hull_volume):.0f} Å³ (conservative)")

    return {
        'sphere': {'center': center.tolist(), 'radius': float(radius), 'volume': float(sphere_volume)},
        'hull_volume': float(hull_volume),
        'conservative_volume': float(max(sphere_volume, hull_volume))
    }

if __name__ == "__main__":
    import sys
    import json

    pdb_file = sys.argv[1] if len(sys.argv) > 1 else "data/pdb/7cn0.pdb"

    result = analyze_herg_cavity(pdb_file)

    # Save results
    with open("pilot_study/results/cavity_analysis.json", 'w') as f:
        json.dump(result, f, indent=2)

    print(f"\n💾 Saved to: pilot_study/results/cavity_analysis.json")
