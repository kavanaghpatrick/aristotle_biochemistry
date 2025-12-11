#!/usr/bin/env python3
"""
Multi-Conformer Ensemble Generation Pipeline

Generates diverse conformer ensembles for geometric impossibility proofs.
Goal: 100+ conformers per molecule, diverse sampling of conformational space.
"""

import json
import numpy as np
from rdkit import Chem
from rdkit.Chem import AllChem, Descriptors
from typing import List, Tuple, Dict
import time

def generate_conformer_ensemble(
    smiles: str,
    name: str,
    n_conformers: int = 100,
    energy_window: float = 10.0,  # kcal/mol
    rms_threshold: float = 0.5,    # Å (for pruning similar conformers)
    optimize: bool = True
) -> Dict:
    """
    Generate diverse conformer ensemble for molecule.

    Args:
        smiles: SMILES string
        name: Molecule name
        n_conformers: Target number of conformers
        energy_window: Keep conformers within X kcal/mol of minimum
        rms_threshold: Prune conformers closer than X Å RMSD
        optimize: Run MMFF optimization after generation

    Returns:
        Dict with conformer data, bounding sphere, volume
    """

    print(f"\n{'='*80}")
    print(f"Generating conformer ensemble: {name}")
    print(f"{'='*80}")
    print(f"SMILES: {smiles}")

    # Create molecule
    mol = Chem.MolFromSmiles(smiles)
    if mol is None:
        raise ValueError(f"Invalid SMILES: {smiles}")

    mol = Chem.AddHs(mol)

    # Molecular properties
    mw = Descriptors.MolWt(mol)
    n_atoms = mol.GetNumAtoms()
    n_rotatable = Descriptors.NumRotatableBonds(mol)

    print(f"  MW: {mw:.1f} Da")
    print(f"  Atoms: {n_atoms}")
    print(f"  Rotatable bonds: {n_rotatable}")

    # ETKDG parameters
    params = AllChem.ETKDGv3()
    params.randomSeed = -1  # Different seed each time
    params.pruneRmsThresh = rms_threshold
    params.numThreads = 0  # Use all available cores

    # Generate conformers
    print(f"\n🔄 Generating {n_conformers} conformers...")
    start = time.time()

    conf_ids = AllChem.EmbedMultipleConfs(
        mol,
        numConfs=n_conformers,
        params=params
    )

    if len(conf_ids) == 0:
        raise ValueError(f"Failed to generate conformers for {name}")

    print(f"  Generated: {len(conf_ids)} conformers in {time.time()-start:.1f}s")

    # Optimize with MMFF
    if optimize:
        print(f"🔧 Optimizing with MMFF...")
        start = time.time()

        results = AllChem.MMFFOptimizeMoleculeConfs(mol, numThreads=0)

        # Extract energies
        energies = [result[1] for result in results]
        min_energy = min(energies)

        print(f"  Optimized in {time.time()-start:.1f}s")
        print(f"  Energy range: {min_energy:.2f} to {max(energies):.2f} kcal/mol")

        # Filter by energy window
        valid_confs = [
            (conf_id, energy)
            for conf_id, energy in zip(conf_ids, energies)
            if energy - min_energy <= energy_window
        ]

        print(f"  Kept {len(valid_confs)}/{len(conf_ids)} within {energy_window} kcal/mol")

        conf_ids = [c[0] for c in valid_confs]
        energies = [c[1] for c in valid_confs]
    else:
        energies = [0.0] * len(conf_ids)

    # Extract conformer coordinates
    print(f"\n📊 Extracting conformer geometries...")
    conformers = []
    all_coords = []

    for conf_id in conf_ids:
        conf = mol.GetConformer(conf_id)
        coords = []

        for atom_idx in range(mol.GetNumAtoms()):
            pos = conf.GetAtomPosition(atom_idx)
            coords.append([pos.x, pos.y, pos.z])

        conformers.append({
            'id': int(conf_id),
            'coords': coords,
            'energy': energies[conf_ids.index(conf_id)] if optimize else None
        })

        all_coords.extend(coords)

    all_coords = np.array(all_coords)

    # Calculate minimal bounding sphere
    print(f"\n⚪ Calculating minimal bounding sphere...")
    bounding_center, bounding_radius = calculate_bounding_sphere(all_coords)
    bounding_volume = (4/3) * np.pi * bounding_radius**3

    print(f"  Center: ({bounding_center[0]:.2f}, {bounding_center[1]:.2f}, {bounding_center[2]:.2f})")
    print(f"  Radius: {bounding_radius:.2f} Å")
    print(f"  Volume: {bounding_volume:.0f} Å³")

    # Calculate ensemble statistics
    print(f"\n📈 Ensemble Statistics:")
    print(f"  Conformers: {len(conformers)}")
    if optimize:
        print(f"  Energy span: {max(energies) - min(energies):.2f} kcal/mol")

    # Calculate diversity (avg pairwise RMSD)
    if len(conformers) > 1:
        rmsd_values = []
        for i in range(min(10, len(conformers))):  # Sample 10 pairs
            for j in range(i+1, min(10, len(conformers))):
                rmsd = calculate_rmsd(
                    np.array(conformers[i]['coords']),
                    np.array(conformers[j]['coords'])
                )
                rmsd_values.append(rmsd)

        avg_rmsd = np.mean(rmsd_values)
        print(f"  Avg pairwise RMSD: {avg_rmsd:.2f} Å (sample)")

    # Package results
    result = {
        'molecule_name': name,
        'smiles': smiles,
        'properties': {
            'mw': mw,
            'n_atoms': n_atoms,
            'n_rotatable_bonds': n_rotatable
        },
        'conformers': conformers,
        'bounding_sphere': {
            'center': bounding_center.tolist(),
            'radius': float(bounding_radius)
        },
        'bounding_volume': float(bounding_volume),
        'n_conformers': len(conformers)
    }

    print(f"\n✅ Ensemble generation complete!")

    return result

def calculate_bounding_sphere(points: np.ndarray) -> Tuple[np.ndarray, float]:
    """
    Calculate minimal bounding sphere for point cloud.

    Uses simple centroid + max distance method (fast, slightly conservative).
    For formal proofs, conservative is good!

    Args:
        points: Nx3 array of coordinates

    Returns:
        (center, radius) tuple
    """
    center = points.mean(axis=0)
    distances = np.linalg.norm(points - center, axis=1)
    radius = distances.max()

    return center, radius

def calculate_rmsd(coords1: np.ndarray, coords2: np.ndarray) -> float:
    """Calculate RMSD between two coordinate sets."""
    return np.sqrt(((coords1 - coords2)**2).sum(axis=1).mean())

def save_ensemble(ensemble: Dict, output_path: str):
    """Save ensemble to JSON file."""
    with open(output_path, 'w') as f:
        json.dump(ensemble, f, indent=2)
    print(f"💾 Saved to: {output_path}")

if __name__ == "__main__":
    import sys

    # Test with metformin (pilot molecule 1)
    if len(sys.argv) > 1:
        smiles = sys.argv[1]
        name = sys.argv[2] if len(sys.argv) > 2 else "test"
        n_conf = int(sys.argv[3]) if len(sys.argv) > 3 else 100
    else:
        # Default: Metformin
        smiles = "CN(C)C(=N)NC(=N)N"
        name = "metformin"
        n_conf = 100

    ensemble = generate_conformer_ensemble(smiles, name, n_conformers=n_conf)

    output_file = f"pilot_study/conformers/{name}_ensemble.json"
    save_ensemble(ensemble, output_file)

    print(f"\n{'='*80}")
    print(f"SUMMARY: {name}")
    print(f"{'='*80}")
    print(f"Conformers: {ensemble['n_conformers']}")
    print(f"Bounding radius: {ensemble['bounding_sphere']['radius']:.2f} Å")
    print(f"Bounding volume: {ensemble['bounding_volume']:.0f} Å³")
