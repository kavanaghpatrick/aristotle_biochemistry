#!/usr/bin/env python3
import json
import os
import requests

prompt = """Identify 10 extremely difficult biochemistry problems that cause drug failures and could potentially be solved with formal verification (mathematical theorem proving in Lean 4).

Focus on CRITICAL problems that:
1. Cost pharma companies $100M+ when they fail
2. Are discovered late (Phase II/III trials)
3. Could be prevented by mathematical proofs
4. Involve molecular properties, kinetics, or binding

For EACH problem provide:
- **Problem Name**: Clear, specific title
- **Why Hard**: Why experimental/computational methods fail
- **Cost**: Estimated cost when this causes failure
- **Example**: Real drug that failed due to this issue
- **What to Prove**: Specific mathematical property to verify
- **Feasibility**: Can this realistically be formalized in Lean?

Be brutally honest about feasibility. Focus on:
- hERG cardiac toxicity (QT prolongation)
- CYP450 metabolism and drug-drug interactions
- Blood-brain barrier permeability
- Protein aggregation and immunogenicity
- Off-target kinase binding
- Reactive metabolite formation
- PK/PD modeling failures

Output in clear markdown format with specific examples."""

api_key = os.environ.get('GROK_API_KEY')
if not api_key:
    print("ERROR: GROK_API_KEY not set")
    exit(1)

try:
    response = requests.post(
        'https://api.x.ai/v1/chat/completions',
        headers={
            'Authorization': f'Bearer {api_key}',
            'Content-Type': 'application/json'
        },
        json={
            'model': 'grok-3',
            'messages': [{'role': 'user', 'content': prompt}],
            'temperature': 0.3,
            'max_tokens': 4000
        },
        timeout=300
    )

    if response.status_code == 200:
        result = response.json()
        content = result['choices'][0]['message']['content']

        # Save full response
        with open('research/grok_response_full.json', 'w') as f:
            json.dump(result, f, indent=2)

        # Save just the content
        with open('research/grok_problems.md', 'w') as f:
            f.write(content)

        print(f"✓ Grok research complete ({len(content)} chars)")
        print(f"Saved to research/grok_problems.md")
    else:
        print(f"ERROR: Grok API returned {response.status_code}")
        print(response.text)
        exit(1)

except Exception as e:
    print(f"ERROR calling Grok: {e}")
    exit(1)
