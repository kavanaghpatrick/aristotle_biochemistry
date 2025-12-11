#!/usr/bin/env python3
"""
Synthesize 3 AI audits (Grok, Gemini, Codex) into consensus recommendation
"""

import sys
import re

def extract_sections(text, ai_name):
    """Extract key sections from AI audit"""
    sections = {
        'ai': ai_name,
        'feasibility': 'Unknown',
        'risks': [],
        'recommendation': 'Unknown',
        'improvements': []
    }

    # Simple keyword extraction (could be more sophisticated)
    lines = text.split('\n')
    for i, line in enumerate(lines):
        lower = line.lower()

        if 'feasibility' in lower and i+1 < len(lines):
            sections['feasibility'] = lines[i+1].strip()

        if 'risk' in lower or 'concern' in lower:
            # Collect next few lines as risks
            for j in range(i+1, min(i+5, len(lines))):
                if lines[j].strip() and not lines[j].startswith('#'):
                    sections['risks'].append(lines[j].strip())

        if 'recommend' in lower and i+1 < len(lines):
            sections['recommendation'] = lines[i+1].strip()

    return sections

def synthesize(grok_text, gemini_text, codex_text):
    """Synthesize three audits into consensus"""

    grok = extract_sections(grok_text, 'Grok')
    gemini = extract_sections(gemini_text, 'Gemini')
    codex = extract_sections(codex_text, 'Codex')

    # Build synthesis markdown
    output = []
    output.append("# Multi-AI Audit Synthesis\n")

    output.append("## Individual Assessments\n")
    output.append("### 🔴 Grok (Critical Analysis)")
    output.append(f"- **Feasibility**: {grok['feasibility']}")
    output.append(f"- **Recommendation**: {grok['recommendation']}")
    if grok['risks']:
        output.append(f"- **Key Risks**: {', '.join(grok['risks'][:3])}")
    output.append("")

    output.append("### 🔵 Gemini (Scientific Validation)")
    output.append(f"- **Feasibility**: {gemini['feasibility']}")
    output.append(f"- **Recommendation**: {gemini['recommendation']}")
    output.append("")

    output.append("### 🟢 Codex (Implementation)")
    output.append(f"- **Feasibility**: {codex['feasibility']}")
    output.append(f"- **Recommendation**: {codex['recommendation']}")
    output.append("")

    # Consensus logic
    output.append("## Consensus\n")

    # Simple voting on recommendations
    recs = [grok['recommendation'].lower(), gemini['recommendation'].lower(), codex['recommendation'].lower()]
    if recs.count('proceed') >= 2:
        output.append("✅ **PROCEED** - Majority recommendation")
    elif recs.count('modify') >= 2 or recs.count('defer') >= 2:
        output.append("⚠️  **MODIFY** - Needs revision based on feedback")
    else:
        output.append("🔴 **MIXED** - AIs disagree, human review needed")

    output.append("\n## Combined Insights\n")
    output.append("### Critical Risks (from all AIs)")
    all_risks = grok['risks'] + gemini['risks'] + codex['risks']
    for i, risk in enumerate(all_risks[:5], 1):
        output.append(f"{i}. {risk}")

    output.append("\n### Next Steps")
    output.append("1. Address critical risks identified above")
    output.append("2. Incorporate improvements from all three audits")
    output.append("3. Revise approach and re-validate if needed")

    return '\n'.join(output)

def main():
    # Read from stdin (expects concatenated audits)
    all_input = sys.stdin.read()

    # Split by AI markers (assuming they're clearly marked)
    parts = re.split(r'# (Grok|Gemini|Codex)', all_input)

    grok_text = ""
    gemini_text = ""
    codex_text = ""

    for i in range(1, len(parts), 2):
        if i+1 < len(parts):
            ai_name = parts[i]
            content = parts[i+1]

            if 'Grok' in ai_name:
                grok_text = content
            elif 'Gemini' in ai_name:
                gemini_text = content
            elif 'Codex' in ai_name:
                codex_text = content

    # Synthesize
    result = synthesize(grok_text, gemini_text, codex_text)
    print(result)

if __name__ == '__main__':
    main()
