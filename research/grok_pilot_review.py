#!/usr/bin/env python3
"""
Consult Grok on pilot study results and next steps.
"""

import json
import subprocess
import sys

# Load pilot results
metformin = json.load(open('pilot_study/conformers/metformin_ensemble.json'))
terfenadine = json.load(open('pilot_study/conformers/terfenadine_ensemble.json'))
cavity = json.load(open('pilot_study/results/cavity_analysis.json'))

# Grok consultation prompt
prompt = f"""You are an expert computational chemist. I need your critical review of pilot study results for multi-conformer geometric proofs.

# PILOT STUDY RESULTS

## hERG Cavity (from PDB 7CN0)
- **Sphere volume**: {cavity['sphere']['volume']:.0f} Å³
- **Convex hull volume**: {cavity['hull_volume']:.0f} Å³
- **Conservative estimate**: {cavity['conservative_volume']:.0f} Å³

This is MUCH larger than expected (400-600 Å³). Is this correct? Or did I measure wrong?

## Molecule 1: Metformin (small, rigid - should prove safe)
- **MW**: {metformin['properties']['mw']:.1f} Da
- **Conformers**: {metformin['n_conformers']}
- **Bounding radius**: {metformin['bounding_sphere']['radius']:.2f} Å
- **Bounding volume**: {metformin['bounding_volume']:.0f} Å³
- **Volume ratio**: {metformin['bounding_volume']}/{cavity['conservative_volume']:.0f} = {metformin['bounding_volume']/cavity['conservative_volume']:.2%}

**Analysis**: Volume << Cavity, but can't use volume exclusion alone. Need reachability test.

## Molecule 2: Terfenadine (known hERG binder IC50=56nM - MUST NOT prove safe!)
- **MW**: {terfenadine['properties']['mw']:.1f} Da
- **Conformers**: {terfenadine['n_conformers']}
- **Bounding radius**: {terfenadine['bounding_sphere']['radius']:.2f} Å
- **Bounding volume**: {terfenadine['bounding_volume']:.0f} Å³
- **Volume ratio**: {terfenadine['bounding_volume']}/{cavity['conservative_volume']:.0f} = {terfenadine['bounding_volume']/cavity['conservative_volume']:.2%}

**Analysis**: Volume < Cavity → Cannot prove via volume exclusion ✅ CORRECT (it binds!)

## Molecule 3: Vancomycin (large MW 1449 Da - should prove safe)
**PROBLEM**: Invalid SMILES - RDKit parse error

I need correct SMILES for vancomycin.

---

# QUESTIONS FOR GROK

## 1. Cavity Volume Validation
Is 7798 Å³ correct for hERG binding cavity? This is 13x larger than expected (400-600 Å³).

**Possible issues**:
- Extracted wrong residues (too many?)
- Should measure central cavity, not outer vestibule?
- Literature estimates may be for tighter binding region?

**Your task**: Tell me if this is reasonable or if I need to recalculate.

## 2. Vancomycin SMILES
The SMILES I used failed to parse:
```
CC1C(C(CC(O1)OC2C(C(CC(O2)OC3C(C(CC(O3)(C(=O)C(C(C(=O)O)C)O)O)C)OC(=O)C)C)N(C)C)C)C)O)(C)O
```

**Your task**: Provide correct SMILES for vancomycin (MW ~1449 Da, glycopeptide antibiotic).

## 3. Pilot Study Interpretation

Based on results so far:
- **Metformin**: 291 Å³ (way smaller than cavity, but can it REACH Phe656 at ~12 Å from center?)
- **Terfenadine**: 5873 Å³ < 7798 Å³ → Cannot prove via volume ✅
- **Vancomycin**: TBD (waiting for correct SMILES)

**Critical question**: If cavity is 7798 Å³, volume exclusion theorem will only catch MASSIVE molecules (>7800 Å³). Is this approach still viable?

**Alternative**: Focus on REACHABILITY instead of volume (Phe656 at ~12 Å from center, molecules must reach it for π-stacking).

## 4. Next Steps Algorithm

Assuming vancomycin works, what's the best algorithm to prove:
1. **Volume exclusion**: Bounding volume > cavity volume
2. **Reachability**: No conformer can reach Phe656 (within 6 Å for π-stacking)
3. **Backbone clash**: All conformers clash with rigid protein backbone

Which is most discriminative? Which should I implement first?

## 5. Code Review

Review my bounding sphere calculation:
```python
center = all_points.mean(axis=0)
distances = np.linalg.norm(all_points - center, axis=1)
radius = distances.max()
```

Is this too conservative? Should I use Welzl's algorithm for exact minimal sphere?

---

# YOUR TASK
1. Validate or correct cavity volume (7798 Å³)
2. Provide correct vancomycin SMILES
3. Assess pilot viability: Can this approach work with such large cavity?
4. Recommend: Volume vs Reachability vs Clash - which to focus on?
5. Code review: Keep simple method or implement Welzl?

Be CRITICAL. If pilot is failing, tell me now before I waste more time!
"""

# Create request
request_data = {
    "messages": [{"role": "user", "content": prompt}],
    "model": "grok-2-latest",
    "temperature": 0.2
}

with open('/tmp/grok_pilot.json', 'w') as f:
    json.dump(request_data, f)

print("🤖 Consulting Grok on pilot study results...")
print("=" * 80)

# Call Grok
result = subprocess.run(
    [
        'curl', '-X', 'POST',
        'https://api.x.ai/v1/chat/completions',
        '-H', 'Authorization: Bearer ' + subprocess.check_output(['bash', '-c', 'echo $GROK_API_KEY']).decode().strip(),
        '-H', 'Content-Type: application/json',
        '-d', '@/tmp/grok_pilot.json',
        '--max-time', '300'
    ],
    capture_output=True,
    text=True
)

if result.returncode != 0:
    print(f"❌ Error: {result.stderr}", file=sys.stderr)
    sys.exit(1)

try:
    response = json.loads(result.stdout)
    grok_feedback = response['choices'][0]['message']['content']

    with open('research/grok_pilot_review.md', 'w') as f:
        f.write("# Grok Review: Pilot Study Results\n\n")
        f.write("**Date**: 2025-12-11\n")
        f.write("**Model**: grok-2-latest\n\n")
        f.write("---\n\n")
        f.write(grok_feedback)

    print("✅ Grok review complete!")
    print(f"📄 Saved to: research/grok_pilot_review.md")
    print()
    print("=" * 80)
    print("GROK'S FEEDBACK:")
    print("=" * 80)
    print(grok_feedback)

except Exception as e:
    print(f"❌ Error: {e}", file=sys.stderr)
    print(f"Raw: {result.stdout}", file=sys.stderr)
    sys.exit(1)
