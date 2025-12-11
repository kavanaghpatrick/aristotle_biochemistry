#!/usr/bin/env python3
"""
Grok audit script - Critical analysis of biochemistry problem approaches
"""

import sys
import json
import os
import requests

def audit_issue(issue_num):
    """Audit a GitHub issue using Grok for critical analysis"""

    # Get issue content
    import subprocess
    issue_body = subprocess.check_output([
        'gh', 'issue', 'view', str(issue_num), '--json', 'body,title',
        '--jq', '.title + "\n\n" + .body'
    ]).decode('utf-8')

    prompt = f"""You are a critical reviewer for biochemistry formal verification research.

Review this proposed approach and provide CRITICAL analysis:

{issue_body}

Provide:
1. **Feasibility Assessment** (High/Medium/Low)
2. **Key Risks** - What could go wrong?
3. **Missing Considerations** - What's been overlooked?
4. **Recommendation** (Proceed/Modify/Defer)
5. **Specific Improvements** - How to make this more rigorous?

Be BRUTALLY HONEST. If the approach is flawed, say so clearly.
Focus on: Can this be formalized in Lean? Will Aristotle be able to prove it?"""

    # Call Grok API
    api_key = os.environ.get('GROK_API_KEY')
    if not api_key:
        print("ERROR: GROK_API_KEY not set", file=sys.stderr)
        sys.exit(1)

    response = requests.post(
        'https://api.x.ai/v1/chat/completions',
        headers={
            'Authorization': f'Bearer {api_key}',
            'Content-Type': 'application/json'
        },
        json={
            'model': 'grok-beta',
            'messages': [{'role': 'user', 'content': prompt}],
            'temperature': 0.3,
            'max_tokens': 2000
        },
        timeout=300
    )

    if response.status_code != 200:
        print(f"ERROR: Grok API returned {response.status_code}", file=sys.stderr)
        print(response.text, file=sys.stderr)
        sys.exit(1)

    result = response.json()
    audit = result['choices'][0]['message']['content']

    # Output markdown
    print(f"# Grok Critical Analysis (Issue #{issue_num})\n")
    print(audit)

if __name__ == '__main__':
    if len(sys.argv) != 2:
        print("Usage: grok_audit.py <issue_number>")
        sys.exit(1)

    issue_num = sys.argv[1]
    audit_issue(issue_num)
