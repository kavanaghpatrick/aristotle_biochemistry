# CLAUDE.md - Biochemistry Formal Verification

## Project Essence

**Core idea**: Prove drug safety mathematically, like chip correctness, before $100M+ trials.

**Status**: Exploration phase - validating feasibility with Aristotle + Lean 4.

---

## GitHub Workflow (CRITICAL)

<workflow_rules priority="critical">
**GitHub issues are the single source of truth for ALL work.**

### Mandatory Rules
1. **NEVER start work without a GitHub issue**
2. **ALWAYS commit with issue reference**: `git commit -m "feat: description (#123)"`
3. **ALWAYS update issue status** when starting/completing work
4. **ALWAYS link PRs to issues**: Use "Fixes #123" or "Closes #123"
5. **ALWAYS create branch from issue**: `git checkout -b issue-123-description`

### Workflow Pattern
```bash
# 1. Create/assign issue on GitHub (or via gh CLI)
gh issue create --title "Prove Michaelis-Menten rate bounds" --body "..."

# 2. Create branch from main
git checkout main && git pull
git checkout -b issue-42-mm-rate-bounds

# 3. Do work, commit with issue reference
git add BiochemFormal/Kinetics/MichaelisMenten.lean
git commit -m "feat: prove rate_bounded_by_vmax theorem (#42)"

# 4. Push and create PR
git push -u origin issue-42-mm-rate-bounds
gh pr create --title "Prove MM rate bounds" --body "Fixes #42"

# 5. Merge PR (closes issue automatically)
gh pr merge --squash
```

### Issue Labels
- `theorem`: New theorem to prove
- `validation`: Experimental validation needed
- `bug`: Incorrect proof or model
- `enhancement`: Improve existing formalization
- `documentation`: Update docs
- `case-study`: Real drug analysis
- `infrastructure`: Tooling/CI/build

### Issue Templates
**Theorem**:
```
Title: Prove [theorem name]
Labels: theorem

## Description
[What property needs to be proved]

## Why It Matters
[Business/scientific value]

## Acceptance Criteria
- [ ] Theorem formalized in Lean
- [ ] Proof completed (Aristotle or manual)
- [ ] Tests pass
- [ ] Documented in module
```

**Case Study**:
```
Title: Formalize [drug name]
Labels: case-study

## Drug
[Name, structure, known properties]

## Goals
- [ ] Molecular structure formalized
- [ ] Known property X proved
- [ ] Validated against experimental data

## Success Metric
[What prediction/insight would be valuable]
```

### Branch Naming
- `issue-N-short-description` (always reference issue number)
- Examples: `issue-42-mm-rate-bounds`, `issue-15-aspirin-cox-selectivity`

### Commit Messages (Conventional Commits)
- `feat: add theorem X (#N)`
- `fix: correct proof of Y (#N)`
- `docs: update README with results (#N)`
- `test: add validation for Z (#N)`
- `refactor: simplify kinetics module (#N)`

### When to Create Issues
- **Always** before starting new work
- When bug is discovered
- When new idea emerges during work (capture immediately)
- For discussion/decisions (use issue for context)

### Issue Milestones
- `v0.1-exploration`: Initial validation (current)
- `v0.2-case-study`: First real drug
- `v0.3-prediction`: Novel property proved
- `v1.0-platform`: Production-ready tool

</workflow_rules>

---

## Research & Problem Identification Workflow

<research_workflow priority="critical">
**For identifying and validating hard biochemistry problems suitable for formal verification.**

### Phase 1: Parallel AI Research (30min)

Launch 3 AI agents simultaneously to gather difficult biochemistry problems:

```bash
# 1. Grok (xAI) - Focused on critical issues
python3 << 'EOF'
import json
prompt = """Identify 10 extremely difficult biochemistry problems that cause drug failures and could potentially be solved with formal verification (theorem proving).

Focus on:
- Problems that cost pharma $100M+ when they fail
- Properties that are hard to predict experimentally
- Safety issues discovered late in trials (Phase II/III)
- Off-target effects, metabolic issues, toxicity

For each problem, provide:
1. Problem name
2. Why it's hard/expensive
3. What needs to be proved
4. Example drug that failed due to this

Be specific and technical."""

req = {"messages": [{"role": "user", "content": prompt}], "model": "grok-4", "temperature": 0.3}
json.dump(req, open('/tmp/grok_biochem_req.json', 'w'))
EOF

curl -X POST https://api.x.ai/v1/chat/completions \
  -H "Authorization: Bearer $GROK_API_KEY" \
  -H "Content-Type: application/json" \
  -d @/tmp/grok_biochem_req.json \
  > research/grok_problems.json

# 2. Gemini - Broad scientific analysis
gemini -p "$(cat research/prompt_problems.txt)" > research/gemini_problems.md

# 3. Codex CLI - Autonomous deep dive
codex exec --full-auto "Research biochemistry problems suitable for formal verification. Focus on: (1) hERG cardiac toxicity, (2) CYP450 metabolism, (3) blood-brain barrier prediction, (4) protein aggregation. Output detailed analysis to research/codex_problems.md"
```

### Phase 2: Synthesis (15min)

Combine all AI outputs:
1. Read all 3 research files
2. Identify common themes
3. Rank by: (a) Business impact, (b) Technical feasibility, (c) Novelty
4. Select top 10-15 problems

### Phase 3: Issue Creation with Audit Loop (per problem)

For EACH problem identified:

```bash
# 1. Create initial GitHub issue
gh issue create --title "Prove [property]" --label "research" --body "$(cat << 'EOF'
## Problem
[Description from research]

## Why It Matters
[Business/scientific impact]

## Approach (DRAFT - needs audit)
[Initial formalization approach]

## Acceptance Criteria
- [ ] Formalized in Lean
- [ ] Approach audited by 3 AIs
- [ ] Proof strategy documented
- [ ] Related theorems identified

## Status
🔴 Needs audit from Grok, Gemini, Codex
EOF
)"

# 2. Get issue number
ISSUE_NUM=$(gh issue list --limit 1 --json number --jq '.[0].number')

# 3. PARALLEL AUDIT by 3 AIs
# Launch all 3 simultaneously, collect results

# Grok: Critical analysis
python3 research/grok_audit.py $ISSUE_NUM > /tmp/grok_audit_${ISSUE_NUM}.md &
GROK_PID=$!

# Gemini: Scientific validation
gemini -p "Review this approach: $(gh issue view $ISSUE_NUM)" > /tmp/gemini_audit_${ISSUE_NUM}.md &
GEMINI_PID=$!

# Codex: Implementation feasibility
codex exec "Analyze feasibility: $(gh issue view $ISSUE_NUM --json body --jq .body)" > /tmp/codex_audit_${ISSUE_NUM}.md &
CODEX_PID=$!

# Wait for all audits
wait $GROK_PID $GEMINI_PID $CODEX_PID

# 4. Synthesize audits
cat /tmp/*_audit_${ISSUE_NUM}.md | python3 research/synthesize_audits.py > research/issue_${ISSUE_NUM}_revised.md

# 5. Update issue with revised approach
gh issue edit $ISSUE_NUM --body "$(cat research/issue_${ISSUE_NUM}_revised.md)"

# 6. Add audit summary as comment
gh issue comment $ISSUE_NUM --body "## Audit Complete ✅

**Grok**: [Key points]
**Gemini**: [Key points]
**Codex**: [Key points]

**Consensus**: [Approach validated/needs revision]"
```

### Phase 4: Prioritization (10min)

After all issues created and audited:

```bash
# Create project board
gh project create --title "Biochemistry Formal Verification" --body "Prioritized problems"

# Assign priorities based on audit consensus
# Add to milestone based on difficulty/value
```

### Issue Body Template (Post-Audit)

```markdown
## Problem
[Clear description of biochemistry issue]

## Business Impact
- **Cost of failure**: $XXX million
- **Affected drugs**: [Examples]
- **Current solutions**: [Why they fail]

## Formal Verification Approach

### What to Prove
```lean
theorem property_name (params) : conclusion := by
  sorry
```

### Key Challenges
1. [Challenge 1 and mitigation]
2. [Challenge 2 and mitigation]

### Required Background
- Theorems: [Dependencies]
- Data: [Experimental inputs needed]
- Tools: [Aristotle, external integration]

## Multi-AI Audit Results

### 🔴 Grok (Critical Analysis)
- **Feasibility**: [High/Medium/Low]
- **Key Risk**: [Main concern]
- **Recommendation**: [Proceed/Modify/Defer]

### 🔵 Gemini (Scientific Validation)
- **Scientific Accuracy**: [Assessment]
- **Missing Considerations**: [Gaps]
- **Related Work**: [Prior art]

### 🟢 Codex (Implementation)
- **Technical Feasibility**: [Assessment]
- **Estimated Effort**: [Person-hours]
- **Suggested Approach**: [Implementation strategy]

## Consensus & Revised Approach
[Synthesized final approach incorporating all feedback]

## Acceptance Criteria
- [ ] Lean formalization complete
- [ ] Proof strategy validated
- [ ] Test cases identified
- [ ] Success metrics defined

## Next Steps
1. [Concrete action 1]
2. [Concrete action 2]
```

### Workflow Automation Scripts

Create these in `research/` directory:
- `grok_audit.py` - Queries Grok API for critical analysis
- `gemini_audit.sh` - Calls Gemini CLI with standard prompt
- `codex_audit.sh` - Launches Codex with implementation focus
- `synthesize_audits.py` - Combines 3 AI outputs into consensus

### Quality Gates

Before marking issue as "ready":
- ✅ All 3 AIs reviewed
- ✅ Consensus reached or disagreements documented
- ✅ Approach is specific (not hand-wavy)
- ✅ Success criteria are measurable
- ✅ Business value quantified

### Research Workflow Summary

```
Input: "Find hard biochemistry problems"
  ↓
[Parallel] Grok + Gemini + Codex research (30min)
  ↓
Synthesize → Top 10-15 problems (15min)
  ↓
For each problem:
  - Create GitHub issue (5min)
  - [Parallel] 3 AI audits (10min)
  - Synthesize → Update issue (5min)
  ↓
Prioritize → Milestone assignment (10min)
  ↓
Output: 10-15 validated, ready-to-work issues
```

**Total time**: ~2-3 hours for complete research → validated issues pipeline

</research_workflow>

---

## The Opportunity

### Current Drug Discovery: Chaos
- Design → test → $100M Phase II → **FAIL** (off-target toxicity)
- 90% of drugs fail in clinical trials
- $2.6B average cost per approved drug
- Takes 10-15 years

### What Formal Verification Unlocks
**Prove impossibilities before testing**:
- "This molecule CANNOT cross blood-brain barrier" (size/MW proof)
- "This drug CANNOT bind to cardiac channels" (geometry/charge proof)
- "Reaction yield is guaranteed ≥80%" (kinetics proof)
- "No metabolite can be toxic" (pathway analysis proof)

**Result**: 5-10× cost/time reduction, like formal methods did for hardware.

---

## Mental Model: Biochemistry as Type System

### Bad mental model
Biochemistry = wet lab experiments + statistical analysis

### Correct mental model
Biochemistry = **constraint satisfaction with physical laws as invariants**

Like proving your code can't overflow by showing all inputs map to valid ranges, we prove drugs can't cause side effects by showing molecular constraints forbid binding.

---

## Architecture: Three Layers

```
1. PHYSICAL LAWS (always true)
   ├─ Conservation: mass, charge, energy
   ├─ Thermodynamics: ΔG < 0 for spontaneous reactions
   └─ Quantum mechanics: bonding rules

2. BIOLOGICAL MODELS (domain-specific)
   ├─ Enzyme kinetics: Michaelis-Menten, competitive inhibition
   ├─ Pharmacokinetics: ADME models
   └─ Protein structure: binding site geometry

3. DRUG PROPERTIES (what we prove)
   ├─ "Cannot bind to off-target X" (safety)
   ├─ "Km < 1μM for target Y" (efficacy)
   └─ "Bioavailability > 20%" (delivery)
```

**Strategy**: Prove Layer 3 properties by showing they follow from Layers 1-2.

---

## Problem-Solving Framework

### 1. Identify Provable Negatives
**Most valuable proofs are IMPOSSIBILITIES**:
- ✅ "Too large to cross BBB" (simple size check)
- ✅ "Wrong charge to bind site X" (electrostatics)
- ✅ "Geometry incompatible with pocket Y" (shape mismatch)
- ❌ "Will definitely bind with Kd=1nM" (too strong, needs QM)

**Heuristic**: If a pharma scientist would say "obviously impossible", we should prove it.

### 2. Start Continuous, Refine to Discrete
**Phase 1**: Real-valued concentrations, continuous kinetics
- Easier to prove (use Mathlib real analysis)
- Matches how biochemists think

**Phase 2**: Add discrete structure when needed
- Individual atoms/bonds for structural proofs
- Graph theory for metabolic pathways

**Phase 3**: Quantum effects if required
- Bridge to DFT calculations for binding energies
- SMT solvers for detailed geometry

### 3. Hierarchical Abstraction
**Don't model atoms when molecules suffice**:
- Blood-brain barrier: Just need MW + LogP (Lipinski rules)
- Enzyme specificity: Active site geometry, not full protein
- Toxicity: Key off-target families, not all 20,000 proteins

**Principle**: Use coarsest model that captures the property to prove.

### 4. Leverage Symmetry and Conservation
**Free theorems from physics**:
- Mass balance: ∑reactants = ∑products
- Charge conservation: Total charge unchanged
- Chiral symmetry: Enantiomers behave differently

**Pattern**: Biochemistry theorems often reduce to linear algebra + positivity constraints.

---

## What Aristotle Should Prove Automatically

### Tier 1: Should be easy
- Conservation laws (linear algebra)
- Monotonicity (d/dx > 0)
- Bounds from denominators (a/(a+b) ≤ 1)

### Tier 2: Moderate difficulty
- Michaelis-Menten properties
- Competitive inhibition math
- Thermodynamic constraints

### Tier 3: May need guidance
- Geometric packing arguments
- Multi-step pathway analysis
- Optimization (max yield)

**Strategy**: Start Tier 1, identify automation boundaries, guide Tier 3 manually.

---

## Success Milestones

### Technical validation
1. ✅ Aristotle proves ≥1 conservation law automatically
2. ⏳ Prove ≥3 Michaelis-Menten theorems
3. ⏳ Prove one structural impossibility (size/charge)

### Scientific credibility
4. ⏳ Formalize one real drug (aspirin/ibuprofen)
5. ⏳ Prove known selectivity property
6. ⏳ Predict unknown property, validate experimentally

### Business traction
7. ⏳ Create pharma demo (10-min presentation)
8. ⏳ Identify 3 potential customers
9. ⏳ Pilot project with one biotech

**Critical path**: #6 (novel prediction) is the "Nature paper" that unlocks #7-9.

---

## Working with This Codebase

### Reading order
1. `QUICKSTART.md` - Practical next steps
2. `BiochemFormal/DrugSafety/OffTargetProofs.lean` - The key innovation
3. `BiochemFormal/Kinetics/MichaelisMenten.lean` - Enzyme math
4. `EXPLORATION_LOG.md` - Detailed progress

### When adding theorems
**Template**:
```lean
/-
  THEOREM: [One-line description]

  Why it matters: [Drug discovery application]

  Real example: [Specific drug or scenario]
-/
theorem name (params) (hypotheses) : conclusion := by
  sorry
```

**Key**: Every theorem needs business justification in comment.

### Testing strategy
1. Write theorem with `sorry` placeholder
2. Run `aristotle prove-from-file` to see if AI can complete
3. If fails, try simplifying or adding lemmas
4. If succeeds, check proof is meaningful (not vacuous)

### Common patterns
```lean
-- Bound from fraction
theorem fraction_bound (x y : ℝ) (hy : y > 0) : x / (x + y) ≤ 1

-- Monotonicity
theorem mono (f : ℝ → ℝ) (hf : ∀ x y, x ≤ y → f x ≤ f y) : ...

-- Conservation
theorem conserve (a b a' b' : ℝ) (h : a + b = a' + b') : ...

-- Non-negativity
theorem nonneg (x y : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) : x * y ≥ 0
```

---

## Integration Points

### Databases to connect
- **PDB**: Protein structures → extract binding site geometry
- **ChEMBL**: Drug activity data → validate Km predictions
- **KEGG**: Metabolic pathways → prove mass balance
- **UniProt**: Protein families → define off-target sets

### Tools to bridge
- **RDKit**: Parse SMILES → Lean molecule structure
- **Gaussian/ORCA**: QM calculations → binding energy inputs
- **AlphaFold**: Protein structure → binding site extraction

**Automation goal**: `drug.sdf` → Lean theorems → Aristotle proofs → safety report

---

## Failure Modes & Recovery

| Problem | Fix |
|---------|-----|
| Theorem too hard for Aristotle | Break into lemmas, prove manually once |
| Model too simple | Add detail incrementally (test at each step) |
| Model too complex | Abstract away (do we need atoms or just MW?) |
| Proof found but meaningless | Add stronger hypotheses (non-vacuous conditions) |
| Real data contradicts proof | Bug in model or data; investigate (learning opportunity!) |

**Meta-principle**: Aristotle failing is information. Refine based on failure patterns.

---

## Long-term Vision

### Year 1: Tool
Pharma companies send us drug candidates, we return safety proofs.

### Year 3: Platform
In-house teams use our system for real-time feedback during design.

### Year 5: Discovery
We design drugs ourselves with provable properties, license to pharma.

### Year 10: Standard
FDA accepts formal proofs as evidence, like aviation uses DO-178C.

---

## Thinking Tools

### When stuck on formalization
**Ask**: "What would make this obviously impossible to a chemist?"
- Usually: size, charge, geometry
- Formalize that constraint

### When theorem won't prove
**Ask**: "Is this actually always true, or just usually?"
- Add edge case conditions
- Or prove weaker version

### When model feels wrong
**Ask**: "Does this capture the KEY constraint or just details?"
- Refine abstraction level
- Test against known examples

### When prioritizing theorems
**Ask**: "Would proving this save a pharma company $10M+?"
- Yes → high priority (off-target safety)
- No → interesting but not urgent (optimization)

---

## Key Insights (Learned So Far)

1. **Conservation laws are free**: Physics gives us theorems for free
2. **Negatives are easier than positives**: Proving "cannot bind" >> "will bind with Kd=X"
3. **Geometry is powerful**: Size/shape exclusion is surprisingly discriminative
4. **Michaelis-Menten is fundamental**: Most drug targets are enzymes
5. **Hierarchy matters**: Right abstraction level makes proofs tractable

---

## Commands (Quick Reference)

```bash
# Prove with Aristotle
aristotle prove-from-file BiochemFormal/Kinetics/MichaelisMenten.lean

# Build manually
~/.elan/bin/lake build

# Check file syntax
~/.elan/bin/lean BiochemFormal/Basic/ConservationLaws.lean
```

---

## Questions to Answer Next

1. **Automation boundary**: What % of theorems can Aristotle prove unguided?
2. **Model fidelity**: How detailed must molecular structure be?
3. **Validation**: Can we predict ONE property that surprises a chemist?
4. **Scaling**: Does this approach work for antibodies (large) or just small molecules?
5. **Regulation**: Will FDA accept formal proofs? (Precedent: DO-178C in aviation)

---

**Mental model check**: If you can't explain why a theorem would save $10M in drug development, don't prove it yet.

**Exploration goal**: Find the ONE theorem that makes a pharma executive say "shut up and take my money."
