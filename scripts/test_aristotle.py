#!/usr/bin/env python3
"""
Test Aristotle API on hERG helper lemmas.

Usage:
    export ARISTOTLE_API_KEY="your-key-here"
    python3 scripts/test_aristotle.py BiochemFormal/DrugSafety/hERG/HelperTest.lean
"""

import os
import sys
import json
import requests
from pathlib import Path

API_URL = "https://aristotle.harmonic.fun/v1/prove"
API_KEY = os.environ.get("ARISTOTLE_API_KEY")

if not API_KEY:
    print("ERROR: ARISTOTLE_API_KEY environment variable not set", file=sys.stderr)
    sys.exit(1)

def call_aristotle(lean_file_path: str, theorem_name: str = None):
    """
    Call Aristotle API to prove theorems in a Lean file.

    Args:
        lean_file_path: Path to Lean source file
        theorem_name: Optional specific theorem to prove
    """
    file_path = Path(lean_file_path)
    if not file_path.exists():
        print(f"ERROR: File not found: {lean_file_path}", file=sys.stderr)
        sys.exit(1)

    with open(file_path) as f:
        lean_code = f.read()

    print(f"=== Testing Aristotle on {file_path.name} ===\n")
    print(f"File contents:\n{lean_code}\n")
    print("=" * 60)

    # Prepare API request
    headers = {
        "Authorization": f"Bearer {API_KEY}",
        "Content-Type": "application/json"
    }

    payload = {
        "lean_code": lean_code,
        "theorem": theorem_name,
        "timeout": 60000  # 60 seconds
    }

    print(f"\nCalling Aristotle API...")
    print(f"URL: {API_URL}")
    print(f"Theorem: {theorem_name or 'ALL'}")

    try:
        response = requests.post(API_URL, headers=headers, json=payload, timeout=120)

        print(f"\nStatus Code: {response.status_code}")

        if response.status_code == 200:
            result = response.json()
            print("\n=== SUCCESS ===")
            print(json.dumps(result, indent=2))
            return result
        else:
            print(f"\n=== ERROR ===")
            print(f"Response: {response.text}")
            return None

    except requests.exceptions.Timeout:
        print("\n=== TIMEOUT ===")
        print("Aristotle API request timed out after 120 seconds")
        return None
    except Exception as e:
        print(f"\n=== EXCEPTION ===")
        print(f"Error: {e}")
        return None

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python3 test_aristotle.py <lean_file> [theorem_name]")
        sys.exit(1)

    lean_file = sys.argv[1]
    theorem = sys.argv[2] if len(sys.argv) > 2 else None

    result = call_aristotle(lean_file, theorem)

    if result:
        print("\n✅ Aristotle successfully responded")
        sys.exit(0)
    else:
        print("\n❌ Aristotle failed or returned error")
        sys.exit(1)
