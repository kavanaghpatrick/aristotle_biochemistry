#!/usr/bin/env python3
"""
Query Grok for validation of geometric reachability plan.
Focus: Implementation feasibility, technical concerns, PDB accuracy.
"""

import json
import subprocess
import sys

# Read the plan
with open('docs/geometric_breakthrough_plan.md') as f:
    plan = f.read()

# Grok validation prompt
prompt = f"""You are reviewing a formal verification plan for drug safety. Please provide critical technical feedback.

# PLAN TO REVIEW:
{plan}

# SPECIFIC QUESTIONS:

1. **PDB Resolution**: The hERG structure (7CN0) is 3.8 Å resolution. Is this sufficient for accurate geometric proofs? Or do we need higher resolution data?

2. **VDW Radii**: Should we use standard van der Waals radii (C=1.7Å, N=1.55Å, etc.) or adjust them? What margin of error should we add?

3. **Conformational Flexibility**: The plan ignores molecular flexibility (uses single conformer). Is this a fatal flaw or acceptable for MVP?

4. **hERG Pocket Volume**: Plan estimates 400-600 Å³ cavity volume. Is this reasonable? How to calculate accurately from PDB?

5. **Induced Fit**: hERG pocket may deform when ligands bind. Does this invalidate rigid geometric proofs?

6. **Macrolide Test**: Will azithromycin/erythromycin (MW 749/734 Da) fail the volume exclusion test? Or are they still small enough to fit?

7. **Implementation Risks**: What are the top 3 technical risks that could derail this approach?

8. **Simplifications**: The plan uses sphere approximations for atoms. Is this too crude? Should we use more sophisticated molecular surfaces?

# YOUR TASK:
- Point out any technical flaws or unrealistic assumptions
- Identify potential blockers
- Suggest improvements or alternatives
- Rate feasibility (1-10) and explain

Be CRITICAL. We want to know if this will fail before we invest 2-3 weeks.
"""

# Create request payload
request_data = {
    "messages": [{"role": "user", "content": prompt}],
    "model": "grok-2-latest",
    "temperature": 0.3  # More focused, less creative
}

# Write to temp file for curl
with open('/tmp/grok_geometric_validation.json', 'w') as f:
    json.dump(request_data, f)

print("🔍 Querying Grok for geometric plan validation...")
print("=" * 80)

# Call Grok API
result = subprocess.run(
    [
        'curl', '-X', 'POST',
        'https://api.x.ai/v1/chat/completions',
        '-H', 'Authorization: Bearer ' + subprocess.check_output(['bash', '-c', 'echo $GROK_API_KEY']).decode().strip(),
        '-H', 'Content-Type: application/json',
        '-d', '@/tmp/grok_geometric_validation.json',
        '--max-time', '300'  # 5 min timeout
    ],
    capture_output=True,
    text=True
)

if result.returncode != 0:
    print(f"❌ Error calling Grok API: {result.stderr}", file=sys.stderr)
    sys.exit(1)

# Parse response
try:
    response = json.loads(result.stdout)
    grok_feedback = response['choices'][0]['message']['content']

    # Save to file
    with open('research/grok_geometric_validation.md', 'w') as f:
        f.write("# Grok Validation: Geometric Reachability Plan\n\n")
        f.write("**Date**: 2025-12-11\n")
        f.write("**Model**: grok-2-latest\n\n")
        f.write("---\n\n")
        f.write(grok_feedback)

    print("✅ Grok validation complete!")
    print(f"📄 Saved to: research/grok_geometric_validation.md")
    print()
    print("=" * 80)
    print("GROK FEEDBACK:")
    print("=" * 80)
    print(grok_feedback)

except Exception as e:
    print(f"❌ Error parsing response: {e}", file=sys.stderr)
    print(f"Raw output: {result.stdout}", file=sys.stderr)
    sys.exit(1)
