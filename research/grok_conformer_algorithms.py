#!/usr/bin/env python3
"""
Consult Grok on optimal algorithms for multi-conformer geometric proofs.
Focus: Conformer generation, minimal bounding sphere, convex hull.
"""

import json
import subprocess
import sys

# Grok consultation prompt
prompt = """You are an expert in computational geometry and cheminformatics. I need optimal algorithms for a multi-conformer molecular geometry project.

# PROJECT CONTEXT
Building formal proofs that molecules CANNOT bind to hERG protein based on geometric impossibility. Using 100+ conformer ensembles per molecule.

# ALGORITHMIC CHALLENGES

## 1. CONFORMER GENERATION (Most Critical)

**Goal**: Generate 100 diverse, low-energy conformers for drug-like molecules (MW 100-1500 Da, 10-100 atoms)

**Current Plan**: RDKit ETKDG with different random seeds

**Questions**:
1. Is ETKDG + MMFF the right approach? Or should I use something else?
2. How to ensure conformer DIVERSITY (not 100 similar structures)?
3. How to balance speed vs quality (100 conformers/molecule × 20 molecules = 2000 total)
4. Should I cluster conformers and take representatives?
5. Energy window: Keep all within X kcal/mol of minimum?

**Give me**: Pseudocode for optimal conformer generation pipeline

## 2. MINIMAL BOUNDING SPHERE

**Goal**: Calculate smallest sphere enclosing ALL atoms from ALL conformers

**Current Plan**:
```python
all_points = np.vstack([conf.coords for conf in conformers])
center = all_points.mean()
radius = max(distance(point, center) for point in all_points)
```

**Questions**:
1. Is this optimal? Or is there a better algorithm (Welzl's algorithm?)
2. Should I use bounding sphere or convex hull?
3. How to make this FAST (100 conformers × 50 atoms = 5000 points)?

**Give me**: Best algorithm with Python implementation

## 3. CONSERVATIVE VOLUME ESTIMATION

**Goal**: Estimate volume occupied by conformer ensemble (for cavity comparison)

**Options**:
- Bounding sphere volume: (4/3)πr³
- Convex hull volume: More accurate but slower
- Voxel grid: Discretize space, count occupied voxels

**Questions**:
1. Which method is most CONSERVATIVE (least likely to under-estimate)?
2. Trade-off: Speed vs accuracy?
3. For Lean formal proofs, which is easiest to formalize?

## 4. CAVITY VOLUME FROM PDB

**Goal**: Calculate hERG binding pocket volume from PDB 7CN0

**Options**:
- Sphere approximation (fast, crude)
- CASTp web server (accurate, slow)
- PyMOL "cavities" (visual, not quantitative)
- POVME (Python, accurate)

**Give me**: Best tool + code snippet

## 5. BACKBONE vs SIDECHAIN SEPARATION

**Goal**: Identify which atoms are rigid (backbone) vs flexible (sidechain) in protein

**Questions**:
1. Can I just use "CA" atoms for backbone?
2. How to estimate max sidechain extent (rotation)?
3. BioPython sufficient or need specialized tool?

## YOUR TASK:
For each of the 5 challenges above:
1. Recommend BEST algorithm/tool
2. Provide pseudocode or Python snippet
3. Explain trade-offs (speed vs accuracy)
4. Identify potential pitfalls

**Focus on**: SPEED and ROBUSTNESS (must handle 100+ molecules × 100 conformers)

**Code style**: Practical Python that I can run today, not theoretical algorithms
"""

# Create request payload
request_data = {
    "messages": [{"role": "user", "content": prompt}],
    "model": "grok-2-latest",
    "temperature": 0.2  # Low temp for precise algorithmic answers
}

# Write to temp file
with open('/tmp/grok_algorithms.json', 'w') as f:
    json.dump(request_data, f)

print("🤖 Consulting Grok on conformer generation algorithms...")
print("=" * 80)

# Call Grok API
result = subprocess.run(
    [
        'curl', '-X', 'POST',
        'https://api.x.ai/v1/chat/completions',
        '-H', 'Authorization: Bearer ' + subprocess.check_output(['bash', '-c', 'echo $GROK_API_KEY']).decode().strip(),
        '-H', 'Content-Type: application/json',
        '-d', '@/tmp/grok_algorithms.json',
        '--max-time', '300'
    ],
    capture_output=True,
    text=True
)

if result.returncode != 0:
    print(f"❌ Error calling Grok: {result.stderr}", file=sys.stderr)
    sys.exit(1)

# Parse response
try:
    response = json.loads(result.stdout)
    grok_advice = response['choices'][0]['message']['content']

    # Save to file
    with open('research/grok_conformer_algorithms.md', 'w') as f:
        f.write("# Grok: Conformer Generation & Bounding Volume Algorithms\n\n")
        f.write("**Date**: 2025-12-11\n")
        f.write("**Model**: grok-2-latest\n")
        f.write("**Focus**: Optimal algorithms for multi-conformer geometric proofs\n\n")
        f.write("---\n\n")
        f.write(grok_advice)

    print("✅ Grok consultation complete!")
    print(f"📄 Saved to: research/grok_conformer_algorithms.md")
    print()
    print("=" * 80)
    print("GROK'S ALGORITHMIC ADVICE:")
    print("=" * 80)
    print(grok_advice)

except Exception as e:
    print(f"❌ Error parsing response: {e}", file=sys.stderr)
    print(f"Raw output: {result.stdout}", file=sys.stderr)
    sys.exit(1)
