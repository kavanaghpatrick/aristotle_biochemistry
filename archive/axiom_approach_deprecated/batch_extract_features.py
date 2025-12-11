#!/usr/bin/env python3
"""
Batch feature extraction for hERG validation dataset.

Processes multiple molecules from JSON and generates comprehensive analysis.
"""

import json
import sys
from pathlib import Path
from extract_features import extract_all_features

def load_dataset(dataset_path: str):
    """Load validation dataset from JSON."""
    with open(dataset_path) as f:
        return json.load(f)

def process_dataset(dataset_path: str, output_dir: str):
    """
    Process all molecules in dataset and save individual feature files.

    Args:
        dataset_path: Path to validation dataset JSON
        output_dir: Directory to save feature files
    """
    dataset = load_dataset(dataset_path)
    output_path = Path(output_dir)
    output_path.mkdir(exist_ok=True)

    results = []

    print(f"Processing {len(dataset['molecules'])} molecules...")
    print("=" * 60)

    for mol_data in dataset['molecules']:
        name = mol_data['name']
        smiles = mol_data['smiles']
        category = mol_data['category']

        print(f"\n[{category.upper()}] {name}")
        print(f"SMILES: {smiles}")

        # Extract features
        try:
            features = extract_all_features(smiles, name)

            if features is None:
                print(f"  ❌ FAILED to extract features")
                results.append({
                    "name": name,
                    "category": category,
                    "status": "FAILED",
                    "error": "Feature extraction failed"
                })
                continue

            # Save individual feature file
            output_file = output_path / f"{name}_features.json"
            with open(output_file, 'w') as f:
                json.dump(features, f, indent=2)

            # Extract key distances for analysis
            distances = {}
            for dist_entry in features['distances']:
                from_feat = dist_entry['from']
                to_feat = dist_entry['to']
                dist_value = dist_entry['distance']

                # Look for cation-aromatic distances
                if 'cation' in from_feat and 'aromatic' in to_feat:
                    key = f"{from_feat}→{to_feat}"
                    distances[key] = dist_value
                elif 'aromatic' in from_feat and 'cation' in to_feat:
                    key = f"{to_feat}→{from_feat}"
                    distances[key] = dist_value

            # Find min/max cation-aromatic distances
            cation_aromatic_dists = [d for k, d in distances.items() if 'cation' in k and 'aromatic' in k]

            result = {
                "name": name,
                "category": category,
                "status": "SUCCESS",
                "feature_counts": features['feature_counts'],
                "cation_aromatic_distances": cation_aromatic_dists,
                "min_cation_aromatic": min(cation_aromatic_dists) if cation_aromatic_dists else None,
                "max_cation_aromatic": max(cation_aromatic_dists) if cation_aromatic_dists else None,
                "ic50": mol_data.get('ic50_nm', mol_data.get('ic50_um', 'N/A'))
            }

            results.append(result)

            print(f"  ✅ Features: {features['feature_counts']['total']} total")
            print(f"     - Cationic: {features['feature_counts']['cationic']}")
            print(f"     - Aromatic: {features['feature_counts']['aromatic']}")
            print(f"     - Hydrophobic: {features['feature_counts']['hydrophobic']}")

            if cation_aromatic_dists:
                print(f"  📏 Cation-Aromatic Distances:")
                for dist in cation_aromatic_dists:
                    print(f"     - {dist:.3f} Å")
                print(f"  📊 Range: [{min(cation_aromatic_dists):.3f}, {max(cation_aromatic_dists):.3f}] Å")
            else:
                print(f"  ⚠️  NO cation-aromatic pairs found")

        except Exception as e:
            print(f"  ❌ ERROR: {e}")
            results.append({
                "name": name,
                "category": category,
                "status": "ERROR",
                "error": str(e)
            })

    # Save summary
    summary = {
        "dataset": dataset['description'],
        "total_molecules": len(dataset['molecules']),
        "successful_extractions": sum(1 for r in results if r['status'] == 'SUCCESS'),
        "results": results
    }

    summary_file = output_path / "extraction_summary.json"
    with open(summary_file, 'w') as f:
        json.dump(summary, f, indent=2)

    print("\n" + "=" * 60)
    print(f"✅ Processing complete!")
    print(f"   Successful: {summary['successful_extractions']}/{summary['total_molecules']}")
    print(f"   Summary saved to: {summary_file}")

    return summary

def analyze_distances(summary_file: str):
    """Analyze distance distributions by category."""
    with open(summary_file) as f:
        summary = json.load(f)

    print("\n" + "=" * 60)
    print("DISTANCE ANALYSIS BY CATEGORY")
    print("=" * 60)

    categories = {}
    for result in summary['results']:
        if result['status'] != 'SUCCESS':
            continue

        category = result['category']
        if category not in categories:
            categories[category] = []

        if result['min_cation_aromatic'] is not None:
            categories[category].append({
                "name": result['name'],
                "min": result['min_cation_aromatic'],
                "max": result['max_cation_aromatic'],
                "distances": result['cation_aromatic_distances']
            })

    for category, mols in categories.items():
        print(f"\n{category.upper().replace('_', ' ')}:")
        print(f"  Count: {len(mols)}")

        if not mols:
            print("  No data")
            continue

        all_dists = []
        for mol in mols:
            all_dists.extend(mol['distances'])

        if all_dists:
            print(f"  Distance Range: [{min(all_dists):.3f}, {max(all_dists):.3f}] Å")
            print(f"  Average: {sum(all_dists)/len(all_dists):.3f} Å")
            print(f"  Molecules:")
            for mol in mols:
                print(f"    - {mol['name']}: [{mol['min']:.3f}, {mol['max']:.3f}] Å")

    # Determine optimal constraint
    print("\n" + "=" * 60)
    print("CONSTRAINT RECOMMENDATION")
    print("=" * 60)

    binder_dists = []
    for result in summary['results']:
        if result['status'] == 'SUCCESS' and result['category'] == 'known_binder':
            if result['cation_aromatic_distances']:
                binder_dists.extend(result['cation_aromatic_distances'])

    if binder_dists:
        print(f"\nKnown binders cation-aromatic distances:")
        print(f"  Min: {min(binder_dists):.3f} Å")
        print(f"  Max: {max(binder_dists):.3f} Å")
        print(f"  Mean: {sum(binder_dists)/len(binder_dists):.3f} Å")

        suggested_lower = max(4.0, min(binder_dists) - 0.5)
        suggested_upper = max(binder_dists) + 0.5

        print(f"\n💡 SUGGESTED CONSTRAINT: [{suggested_lower:.1f}, {suggested_upper:.1f}] Å")
        print(f"   (adds 0.5 Å margin for conformational flexibility)")

        current_fails = sum(1 for d in binder_dists if d < 4.0 or d > 5.0)
        print(f"\n⚠️  Current [4.0, 5.0] Å constraint:")
        print(f"   False negatives: {current_fails}/{len(binder_dists)} known binders")

if __name__ == "__main__":
    dataset_path = "data/herg_validation_dataset.json"
    output_dir = "data/validation_features"

    # Process dataset
    summary = process_dataset(dataset_path, output_dir)

    # Analyze distances
    analyze_distances(f"{output_dir}/extraction_summary.json")
