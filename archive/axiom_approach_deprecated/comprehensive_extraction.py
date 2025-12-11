#!/usr/bin/env python3
"""
Comprehensive drug dataset extraction and classification.

Processes 50+ drugs and classifies which are certifiable (missing features).
"""

import json
import sys
from pathlib import Path
from extract_features import extract_all_features

def load_dataset(dataset_path: str):
    """Load comprehensive dataset."""
    with open(dataset_path) as f:
        return json.load(f)

def classify_certifiable(features):
    """
    Determine if molecule is certifiable (missing required features).

    Returns: (certifiable: bool, reason: str, missing_features: list)
    """
    counts = features['feature_counts']

    missing = []
    if counts['cationic'] == 0:
        missing.append('cationic')
    if counts['aromatic'] == 0:
        missing.append('aromatic')
    if counts['hydrophobic'] == 0:
        missing.append('hydrophobic')

    if missing:
        return (True, f"Missing: {', '.join(missing)}", missing)
    else:
        return (False, "Has all pharmacophore features", [])

def process_comprehensive_dataset():
    """Process all 50 drugs and generate classification report."""

    dataset = load_dataset("data/comprehensive_drug_dataset.json")
    output_dir = Path("data/comprehensive_features")
    output_dir.mkdir(exist_ok=True)

    results = []
    certifiable_count = 0
    total_count = 0

    print(f"Processing {len(dataset['molecules'])} drugs...")
    print("=" * 80)

    for mol_data in dataset['molecules']:
        name = mol_data['name']
        smiles = mol_data['smiles']
        category = mol_data['category']
        expected_cert = mol_data.get('expected_certifiable', False)
        herg_known = mol_data.get('herg_known', 'unknown')

        total_count += 1

        # Skip peptides
        if smiles == "PEPTIDE":
            print(f"\n[{total_count}/{len(dataset['molecules'])}] {name} ({category})")
            print(f"  ⏭️  SKIPPED: Peptide/protein")
            results.append({
                "name": name,
                "category": category,
                "status": "SKIPPED",
                "reason": "Peptide"
            })
            continue

        print(f"\n[{total_count}/{len(dataset['molecules'])}] {name} ({category})")
        print(f"  SMILES: {smiles[:60]}{'...' if len(smiles) > 60 else ''}")
        print(f"  Known hERG: {herg_known}")

        try:
            # Extract features
            features = extract_all_features(smiles, name)

            if features is None:
                print(f"  ❌ FAILED extraction")
                results.append({
                    "name": name,
                    "category": category,
                    "status": "FAILED"
                })
                continue

            # Save features
            output_file = output_dir / f"{name}_features.json"
            with open(output_file, 'w') as f:
                json.dump(features, f, indent=2)

            # Classify
            is_certifiable, reason, missing = classify_certifiable(features)

            result = {
                "name": name,
                "category": category,
                "class": mol_data.get('class', 'unknown'),
                "herg_known": herg_known,
                "fda_status": mol_data.get('fda_status', 'unknown'),
                "status": "SUCCESS",
                "feature_counts": features['feature_counts'],
                "certifiable": is_certifiable,
                "missing_features": missing,
                "reason": reason,
                "expected_certifiable": expected_cert,
                "prediction_correct": is_certifiable == expected_cert
            }

            results.append(result)

            # Print results
            if is_certifiable:
                certifiable_count += 1
                print(f"  ✅ CERTIFIABLE: {reason}")
                print(f"     Features: C={features['feature_counts']['cationic']}, "
                      f"A={features['feature_counts']['aromatic']}, "
                      f"H={features['feature_counts']['hydrophobic']}")
                if not expected_cert:
                    print(f"  ⚠️  UNEXPECTED: Was expected to be non-certifiable")
            else:
                print(f"  ❌ NOT CERTIFIABLE: {reason}")
                print(f"     Features: C={features['feature_counts']['cationic']}, "
                      f"A={features['feature_counts']['aromatic']}, "
                      f"H={features['feature_counts']['hydrophobic']}")
                if expected_cert:
                    print(f"  ⚠️  UNEXPECTED: Was expected to be certifiable")

        except Exception as e:
            print(f"  ❌ ERROR: {e}")
            results.append({
                "name": name,
                "category": category,
                "status": "ERROR",
                "error": str(e)
            })

    # Generate summary
    print("\n" + "=" * 80)
    print("COMPREHENSIVE ANALYSIS SUMMARY")
    print("=" * 80)

    successful = [r for r in results if r['status'] == 'SUCCESS']
    certifiable = [r for r in successful if r['certifiable']]
    non_certifiable = [r for r in successful if not r['certifiable']]

    print(f"\nTotal molecules: {total_count}")
    print(f"Successfully processed: {len(successful)}")
    print(f"Certifiable (missing ≥1 feature): {len(certifiable)} ({len(certifiable)/len(successful)*100:.1f}%)")
    print(f"Non-certifiable (has all features): {len(non_certifiable)} ({len(non_certifiable)/len(successful)*100:.1f}%)")

    # Category breakdown
    print("\n" + "-" * 80)
    print("CERTIFIABLE BY CATEGORY")
    print("-" * 80)

    categories = {}
    for r in certifiable:
        cat = r['category']
        if cat not in categories:
            categories[cat] = []
        categories[cat].append(r['name'])

    for cat, names in sorted(categories.items()):
        print(f"\n{cat.upper()}: {len(names)} certifiable")
        for name in names:
            result = next(r for r in results if r['name'] == name)
            print(f"  - {name}: Missing {', '.join(result['missing_features'])}")

    # hERG known binders analysis
    print("\n" + "-" * 80)
    print("VALIDATION: Known hERG Binders/Non-Binders")
    print("-" * 80)

    known_binders = [r for r in successful if r.get('herg_known') == 'strong_binder']
    known_non_binders = [r for r in successful if r.get('herg_known') == 'non_binder']

    print(f"\nKnown STRONG binders: {len(known_binders)}")
    for r in known_binders:
        cert_str = "✅ CERTIFIABLE" if r['certifiable'] else "❌ NOT CERTIFIABLE"
        print(f"  - {r['name']}: {cert_str}")
        if r['certifiable']:
            print(f"    ⚠️  FALSE NEGATIVE! (known binder but we say safe)")

    print(f"\nKnown NON-binders: {len(known_non_binders)}")
    for r in known_non_binders:
        cert_str = "✅ CERTIFIABLE" if r['certifiable'] else "❌ NOT CERTIFIABLE"
        print(f"  - {r['name']}: {cert_str}")
        if not r['certifiable']:
            print(f"    ⚠️  CANNOT CERTIFY (has all features, need other methods)")

    # Save comprehensive results
    summary = {
        "dataset": dataset['description'],
        "total_molecules": total_count,
        "successful": len(successful),
        "certifiable_count": len(certifiable),
        "certifiable_percentage": len(certifiable)/len(successful)*100 if successful else 0,
        "results": results
    }

    summary_file = output_dir / "comprehensive_analysis.json"
    with open(summary_file, 'w') as f:
        json.dump(summary, f, indent=2)

    print(f"\n✅ Analysis complete!")
    print(f"   Results saved to: {summary_file}")

    return summary

if __name__ == "__main__":
    summary = process_comprehensive_dataset()
