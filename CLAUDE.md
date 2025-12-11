# CLAUDE.md - Biochemistry Formal Verification

## Project Essence

**Core idea**: Prove drug safety mathematically, like chip correctness, before $100M+ trials.

**Status**: ✅ Concept validated → 🚀 Implementing hERG cardiac toxicity proof (Week 1/4)

**Repo**: https://github.com/kavanaghpatrick/aristotle_biochemistry

---

## Current State (2025-12-11)

### What We've Proven
✅ Lean 4 + Aristotle can formalize biochemistry (20+ theorems)
✅ Aristotle proved 6/6 test theorems automatically (conservation laws, kinetics)
✅ Multi-AI research workflow validated (Grok, Gemini, Codex)
✅ Production PRD ready: hERG toxicity (pharmacophore approach)

### Active Work
🎯 **Issue #5**: hERG Week 1 - Literature review + feature extraction
📋 **PRD**: `PRD_hERG_COMPLETE.md` - 4-week implementation plan
🔬 **Approach**: Discrete pharmacophore impossibility proof (simplest validated)

### Key Achievements
- **Technical**: Automated proofs working (Aristotle: ring, linarith, mul_nonneg)
- **Research**: 10-15 hard problems identified via multi-AI consensus
- **Business**: hERG proof prevents $500M+ Phase III failures
- **Novel**: First formal verification for drug discovery globally

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

---

## Validated Design Patterns

### 1. Simplicity Principle (PROVEN EFFECTIVE)

**Core Rule**: If you can't explain the proof approach in 2 minutes to a chemist, simplify.

**Validated Choices**:
- ✅ **Discrete > Continuous**: Pharmacophore features (10-20) >> 3D volume integrals
- ✅ **Algebraic > Thermodynamic**: Distance inequalities (`linarith`) >> ΔG calculations
- ✅ **Impossibility > Prediction**: "Cannot bind" >> "Kd = 10nM ± 20%"
- ✅ **Necessary conditions > Sufficient**: "Must have motif to bind" >> "Will bind if..."
- ✅ **Finite cases > Infinite search**: Case split over features >> continuous optimization

**Example (hERG)**:
- ❌ Complex: 3D geometric volume overlap with protein dynamics
- ✅ Simple: Check if drug has {cation, aromatic, tail} with distance bounds
- **Why**: Aristotle can automate finite case splits + `linarith`, not continuous geometry

### 2. Multi-AI Research Workflow (VALIDATED)

**Pattern**: Parallel research → Synthesis → Audit → Implement

```bash
# Phase 1: Parallel Research (30min)
grok_research.py &      # Critical analysis, feasibility
gemini -p "prompt" &    # Scientific depth, formal methods
task_agent research &   # Web search, examples
wait

# Phase 2: Synthesis (15min)
python synthesize.py grok.md gemini.md task.md > synthesis.md

# Phase 3: Multi-AI Audit (per approach)
for approach in synthesis.md; do
  grok_audit.py "$approach" &
  gemini_audit.py "$approach" &
  codex exec "audit $approach" &
  wait
  synthesize_audits.py > revised_approach.md
done

# Phase 4: Create GitHub Issue
gh issue create --body "$(cat revised_approach.md)"
```

**Validated Results**:
- Grok: Conservative feasibility (good reality check)
- Gemini: Advanced formal methods (Petri nets, barrier certificates)
- Codex: Implementation focus (what Aristotle can actually do)
- **Consensus**: Pharmacophore approach (Codex) simplest + most feasible

### 3. Formalization Strategy (VALIDATED)

**Layered Architecture**:
```
Layer 1: Data Preparation (Outside Lean)
  - Chemistry: RDKit, ChemAxon
  - Output: Rational coordinates, validated features
  - Why: Keep complexity out of Lean

Layer 2: Lean Formalization
  - Types: Feature, Molecule, BindingCertificate
  - Axioms: Literature-backed (necessary_motif)
  - Theorems: Specific drug proofs
  - Why: Pure logic, no external dependencies

Layer 3: Aristotle Automation
  - Input: JSON features
  - Generate: Case splits + linarith proofs
  - Output: Complete Lean proof
  - Why: Automate the tedious parts
```

**Proven Pattern**:
1. Prove general theorem ONCE (e.g., `necessary_motif`)
2. New molecules → just data instantiation
3. Aristotle generates routine proofs
4. Human reviews axioms/assumptions

### 4. What Aristotle Can/Cannot Do (VALIDATED)

**✅ Aristotle Excels At**:
- Ring simplification: `a + b - a = b`
- Linear arithmetic: `linarith` for inequalities
- Mathlib lemmas: `mul_nonneg`, `div_le_one`
- Finite case splits: Enumerate 10-20 feature combos
- Pattern matching: Apply existing tactics

**❌ Aristotle Struggles With**:
- Novel proof strategies
- Complex geometric reasoning
- Continuous optimization
- Integration/differentiation (without heavy hints)
- Domain-specific axioms (need human to state)

**Design Implication**: Structure proofs so Aristotle does repetitive work, humans do creative work.

---

## Problem Selection Criteria (VALIDATED)

### High-Value Targets (Implement These)
Ranked by: Feasibility × Business Impact × Novelty

**Tier 1: Quick Wins** (2-4 weeks)
1. ✅ **PK/PD modeling** - Already mathematical, proves bounds
2. ⏳ **hERG toxicity** - Pharmacophore approach, $500M+ impact
3. ⏳ **Solubility** - Thermodynamic models, bioavailability

**Tier 2: Core Program** (1-3 months)
4. Blood-brain barrier - Lipinski rules + transporter kinetics
5. Kinase selectivity - Finite kinome, binding pockets
6. Off-target panel - Limited target set

**Tier 3: Advanced** (3-6 months)
7. CYP450 interactions - Complex but high-impact
8. Lysosomal trapping - Novel pH gradient approach
9. Stereochemical stability - Graph transformation

**Tier 4: Research** (6-12 months)
10. Reactive metabolites - Metabolic network Petri nets
11. Protein aggregation - Barrier certificates
12. Cytokine storm - Control theory stability

### Selection Heuristics
- **Start**: Discrete, algebraic, well-defined constraints
- **Avoid**: Continuous, quantum mechanical, incomplete data
- **Validate**: Must catch ≥1 real drug failure to prove value

---

## Lean + Aristotle Best Practices (VALIDATED)

### Theorem Structure
```lean
-- ALWAYS include business justification in comments
/-
  THEOREM: [One-line description]
  
  Why it matters: [Drug discovery value]
  Real example: [Specific drug that failed]
  Business impact: $XXX million
-/
theorem name (params) (hypotheses) : conclusion := by
  sorry  -- Let Aristotle fill in
```

### Testing Pattern
```bash
# 1. Write theorem with sorry
# 2. Test with Aristotle
aristotle prove-from-file Module.lean

# 3. Check output
- If succeeds: Validate proof is non-vacuous
- If fails: Simplify or add lemmas
- If partial: Human-guide remaining steps

# 4. Iterate
```

### Automation Boundary
- **Aristotle generates**: 80% of routine proofs (case splits, arithmetic)
- **Human provides**: 20% of creative work (axioms, strategies)
- **Validate**: Every Aristotle proof for correctness

---

## Common Pitfalls (LEARNED)

### ❌ Anti-Patterns
1. **Over-engineering**: "Let's model protein dynamics" → TOO COMPLEX
   - Fix: Start with simplest constraint that rules out binding
   
2. **Premature optimization**: "Let's prove for all conformers" → NOT MVP
   - Fix: Prove for one rigid structure first
   
3. **Missing business value**: "Let's prove this elegant theorem" → SO WHAT?
   - Fix: Every theorem must prevent a real drug failure
   
4. **Ignoring data availability**: "We'll need quantum calculations" → NO DATA
   - Fix: Use existing databases (PDB, ChEMBL, FDA)
   
5. **Continuous when discrete works**: "3D volume integrals" → OVERKILL
   - Fix: Discretize to finite features

### ✅ Correct Patterns
1. **Start simple**: One molecule, one property, one proof
2. **Validate early**: Does this catch a real failure?
3. **Iterate**: Simple proof → More drugs → More properties
4. **Business-driven**: Only prove theorems worth $10M+
5. **Data-first**: Use available structures/databases

---

## Success Metrics (UPDATED)

### Technical (Achieved ✅)
- [x] Lean + Aristotle environment working
- [x] Automated proofs successful (6/6)
- [x] Framework scales (20+ theorems)
- [x] Multi-AI workflow validated

### Scientific (In Progress ⏳)
- [ ] hERG proof complete (Week 4 target)
- [ ] Validates against known binder (terfenadine)
- [ ] Extensible to new molecules (<1 hour)

### Business (Next Phase 🎯)
- [ ] Pharma feedback: "This could work"
- [ ] Catches ≥1 real drug failure retroactively
- [ ] Publication (Nature/Science)
- [ ] Industry partnership initiated

---

## Quick Reference

### Daily Workflow
1. Check GitHub issues (source of truth)
2. Work on active issue (currently #5: hERG Week 1)
3. Commit with issue reference (`#5`)
4. Update issue when done

### File Organization
```
BiochemFormal/         # Lean formalization
  Basic/              # Conservation, fundamentals
  Kinetics/           # Enzyme kinetics
  DrugSafety/         # hERG, off-targets
research/             # AI research outputs
  *_deep.md          # Deep dives
  synthesis.md       # Problem rankings
scripts/              # Python tools (RDKit, etc.)
data/                 # Feature JSONs, molecules
PRD_*.md             # Requirements docs
```

### Commands
```bash
# Aristotle
aristotle prove-from-file file.lean

# Research
python3 research/query_grok.py
gemini -p "prompt"
codex exec "task"

# GitHub
gh issue create --title "..." --label "theorem,high-priority"
gh issue list
```

---

## Next Session Checklist

**Before starting**:
- [ ] Read active issue (#5)
- [ ] Check PRD (`PRD_hERG_COMPLETE.md`)
- [ ] Review last commit
- [ ] Understand current week's goals

**After completing work**:
- [ ] Commit with issue reference
- [ ] Update issue status
- [ ] Document any learnings in this file
- [ ] Create next issue if needed

**Key Question**: Does this bring us closer to a working hERG proof that prevents a $500M+ failure?

---

**Last Updated**: 2025-12-11
**Active Issue**: #5 (hERG Week 1)
**Next Milestone**: Working hERG proof (4 weeks)
