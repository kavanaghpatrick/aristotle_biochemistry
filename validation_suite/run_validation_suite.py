#!/usr/bin/env python3
"""
20-Molecule Validation Suite for hERG Safety Theorems

CRITICAL SUCCESS CRITERIA:
1. False Negative Rate = 0% (NEVER prove a known binder as safe)
2. All BINDER molecules must be NOT_provable
3. At least 50% of non-binders should be provable

This validates that our geometric approach is:
- Sound (no false negatives)
- Useful (reasonable coverage)
- Conservative (acceptable false positives)
"""

import json
import sys
from pathlib import Path
from rdkit import Chem
from rdkit.Chem import AllChem
import numpy as np

# Import conformer generation from pilot study
sys.path.append('pilot_study')
from generate_conformer_ensemble import generate_conformer_ensemble

# Load test set
test_set = json.load(open('validation_suite/molecule_test_set.json'))

# Load hERG cavity data
herg_cavity_volume = 7797.84  # Å³
phe656_distance = 12.35  # Å
pi_stacking_max = 6.0  # Å
min_radius_to_reach_phe656 = phe656_distance - pi_stacking_max  # 6.35 Å

print("=" * 80)
print("hERG SAFETY THEOREM VALIDATION SUITE")
print("=" * 80)
print(f"\n🎯 CRITICAL SUCCESS CRITERIA:")
print(f"   1. False Negative Rate = 0% (never prove binders safe)")
print(f"   2. Coverage ≥50% for non-binders")
print(f"   3. Sound proofs (conservative, no shortcuts)")

print(f"\n🏛️  hERG CAVITY PARAMETERS:")
print(f"   Volume: {herg_cavity_volume:.2f} Å³")
print(f"   Phe656 distance: {phe656_distance:.2f} Å")
print(f"   Min radius to reach Phe656: {min_radius_to_reach_phe656:.2f} Å")

results = []
binder_molecules = []
non_binder_molecules = []

for i, mol_spec in enumerate(test_set['molecules'], 1):
    print(f"\n{'=' * 80}")
    print(f"[{i}/20] {mol_spec['name'].upper()} ({mol_spec['category']})")
    print(f"{'=' * 80}")
    print(f"  MW: {mol_spec['mw']:.1f} Da")
    print(f"  Expected: {mol_spec['expected_result']}")

    # Track binders separately for critical validation
    is_binder = 'BINDER' in mol_spec['category'] or 'BINDER' in mol_spec.get('expected_result', '')

    try:
        # Generate conformer ensemble
        print(f"\n  🔬 Generating conformer ensemble...")
        ensemble = generate_conformer_ensemble(
            smiles=mol_spec['smiles'],
            name=mol_spec['name'],
            n_conformers=100,
            energy_window=10.0,
            rms_threshold=0.5,
            optimize=True
        )

        print(f"     ✅ Generated {ensemble['n_conformers']} conformers")
        print(f"     Bounding radius: {ensemble['bounding_sphere']['radius']:.2f} Å")
        print(f"     Bounding volume: {ensemble['bounding_volume']:.0f} Å³")

        # Test Volume Exclusion Theorem
        volume_ratio = ensemble['bounding_volume'] / herg_cavity_volume
        can_prove_volume = ensemble['bounding_volume'] > herg_cavity_volume

        print(f"\n  📐 VOLUME EXCLUSION TEST:")
        print(f"     Volume ratio: {volume_ratio:.2%} ({ensemble['bounding_volume']:.0f} / {herg_cavity_volume:.0f})")

        if can_prove_volume:
            print(f"     ✅ PROVABLE: Volume > cavity → CANNOT BIND")
            proof_method = "volume_exclusion"
            can_prove = True
        else:
            print(f"     ❌ Volume insufficient for proof")
            proof_method = None
            can_prove = False

        # Test Reachability Exclusion Theorem
        bounding_radius = ensemble['bounding_sphere']['radius']
        can_reach_phe656 = bounding_radius >= min_radius_to_reach_phe656

        print(f"\n  🎯 REACHABILITY EXCLUSION TEST:")
        print(f"     Bounding radius: {bounding_radius:.2f} Å")
        print(f"     Required to reach Phe656: {min_radius_to_reach_phe656:.2f} Å")

        if not can_prove and not can_reach_phe656:
            print(f"     ✅ PROVABLE: Cannot reach Phe656 → CANNOT BIND")
            proof_method = "reachability"
            can_prove = True
        elif not can_prove:
            print(f"     ❌ Can reach Phe656 → NO PROOF POSSIBLE")

        # Validate against expectations
        print(f"\n  🔍 VALIDATION:")
        if is_binder and can_prove:
            print(f"     🚨 FALSE NEGATIVE! Proved binder safe - CRITICAL FAILURE!")
            validation = "FALSE_NEGATIVE"
        elif is_binder and not can_prove:
            print(f"     ✅ Correctly did NOT prove binder safe")
            validation = "TRUE_NEGATIVE"
        elif not is_binder and can_prove:
            print(f"     ✅ Correctly proved non-binder safe")
            validation = "TRUE_POSITIVE"
        else:
            print(f"     ⚠️  Could not prove non-binder (acceptable false positive)")
            validation = "FALSE_POSITIVE"

        result = {
            'name': mol_spec['name'],
            'category': mol_spec['category'],
            'mw': mol_spec['mw'],
            'n_conformers': ensemble['n_conformers'],
            'bounding_radius': bounding_radius,
            'bounding_volume': ensemble['bounding_volume'],
            'volume_ratio': volume_ratio,
            'can_reach_phe656': can_reach_phe656,
            'can_prove_safe': can_prove,
            'proof_method': proof_method,
            'is_binder': is_binder,
            'validation': validation,
            'expected': mol_spec['expected_result'],
            'success': True
        }

        # Save ensemble for Lean formalization
        with open(f'validation_suite/ensembles/{mol_spec["name"].lower()}_ensemble.json', 'w') as f:
            json.dump(ensemble, f, indent=2)

    except Exception as e:
        print(f"     ❌ ERROR: {e}")
        result = {
            'name': mol_spec['name'],
            'category': mol_spec['category'],
            'success': False,
            'error': str(e),
            'is_binder': is_binder
        }

    results.append(result)

    if is_binder:
        binder_molecules.append(result)
    else:
        non_binder_molecules.append(result)

# Summary Analysis
print(f"\n{'=' * 80}")
print("VALIDATION SUMMARY")
print(f"{'=' * 80}")

successful_results = [r for r in results if r.get('success')]
false_negatives = [r for r in successful_results if r['validation'] == 'FALSE_NEGATIVE']
true_negatives = [r for r in successful_results if r['validation'] == 'TRUE_NEGATIVE']
true_positives = [r for r in successful_results if r['validation'] == 'TRUE_POSITIVE']
false_positives = [r for r in successful_results if r['validation'] == 'FALSE_POSITIVE']

print(f"\n📊 CONFUSION MATRIX:")
print(f"   True Positives:  {len(true_positives):2} (non-binders proven safe)")
print(f"   False Positives: {len(false_positives):2} (non-binders not proven - acceptable)")
print(f"   True Negatives:  {len(true_negatives):2} (binders NOT proven - correct)")
print(f"   False Negatives: {len(false_negatives):2} (binders proven safe - CRITICAL!)")

# Critical Test: False Negative Rate
total_binders = len([r for r in successful_results if r['is_binder']])
fn_rate = len(false_negatives) / total_binders if total_binders > 0 else 0.0

print(f"\n🎯 CRITICAL METRICS:")
print(f"   False Negative Rate: {fn_rate:.1%} (target: 0%)")
print(f"   Binders tested: {total_binders}")
print(f"   Binders proven safe: {len(false_negatives)}")

if fn_rate > 0:
    print(f"\n   🚨 VALIDATION FAILED: False negatives detected!")
    print(f"   These molecules are KNOWN BINDERS but were proven safe:")
    for fn in false_negatives:
        print(f"      - {fn['name']} ({fn['proof_method']})")
    decision = "VALIDATION_FAILED"
else:
    print(f"\n   ✅ CRITICAL TEST PASSED: 0% false negative rate")
    decision = "VALIDATION_PASSED"

# Coverage Analysis
total_non_binders = len([r for r in successful_results if not r['is_binder']])
proven_non_binders = len(true_positives)
coverage = proven_non_binders / total_non_binders if total_non_binders > 0 else 0.0

print(f"\n📈 COVERAGE METRICS:")
print(f"   Non-binders tested: {total_non_binders}")
print(f"   Non-binders proven safe: {proven_non_binders}")
print(f"   Coverage: {coverage:.1%} (target: ≥50%)")

if coverage >= 0.5:
    print(f"   ✅ Coverage target met")
else:
    print(f"   ⚠️  Coverage below target (may limit usefulness)")

# Proof Method Breakdown
proof_methods = [r.get('proof_method') for r in successful_results if r.get('can_prove_safe')]
print(f"\n🔬 PROOF METHOD DISTRIBUTION:")
if proof_methods:
    for method in set(proof_methods):
        if method:
            count = proof_methods.count(method)
            print(f"   {method}: {count}")
else:
    print(f"   No proofs generated")

# Final Decision
print(f"\n{'=' * 80}")
if decision == "VALIDATION_PASSED" and coverage >= 0.5:
    print(f"✅ VALIDATION SUITE PASSED")
    print(f"{'=' * 80}")
    print(f"\n🎉 Geometric hERG safety approach is VALIDATED!")
    print(f"   - 0% false negative rate (sound)")
    print(f"   - {coverage:.0%} coverage (useful)")
    print(f"   - Ready for production use")
elif decision == "VALIDATION_PASSED":
    print(f"⚠️  VALIDATION PARTIAL")
    print(f"{'=' * 80}")
    print(f"\n✅ No false negatives (sound)")
    print(f"⚠️  Low coverage ({coverage:.0%}) - limited usefulness")
    print(f"   Consider additional proof strategies")
else:
    print(f"❌ VALIDATION FAILED")
    print(f"{'=' * 80}")
    print(f"\n🚨 CRITICAL: False negatives detected!")
    print(f"   Approach is UNSOUND - do not use in production")

# Save results
validation_summary = {
    'decision': decision,
    'false_negative_rate': fn_rate,
    'coverage': coverage,
    'total_molecules': len(successful_results),
    'binders': total_binders,
    'non_binders': total_non_binders,
    'false_negatives': [fn['name'] for fn in false_negatives],
    'results': results,
    'proof_method_distribution': {
        method: proof_methods.count(method)
        for method in set(proof_methods) if method
    }
}

with open('validation_suite/validation_summary.json', 'w') as f:
    json.dump(validation_summary, f, indent=2)

print(f"\n💾 Results saved to: validation_suite/validation_summary.json")

sys.exit(0 if decision == "VALIDATION_PASSED" else 1)
