#!/usr/bin/env python3
import json, os, requests

with open('research/herg_deep_dive_prompt.md') as f:
    prompt = f.read()

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
            'temperature': 0.2,
            'max_tokens': 6000
        },
        timeout=300
    )

    if response.status_code == 200:
        result = response.json()
        content = result['choices'][0]['message']['content']

        with open('research/herg_grok_deep.md', 'w') as f:
            f.write("# Grok Deep Dive: hERG Formal Verification\n\n")
            f.write(content)

        print(f"✓ Grok deep dive complete ({len(content)} chars)")
    else:
        print(f"ERROR: {response.status_code} - {response.text}")
        exit(1)
except Exception as e:
    print(f"ERROR: {e}")
    exit(1)
