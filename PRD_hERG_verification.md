# PRD: hERG Cardiac Toxicity Formal Verification

**Status**: v1.0 - Ready for Multi-AI Audit
**Priority**: P0 (Highest business impact)
**Target**: 2-4 week MVP
**Last Updated**: 2025-12-11

---

## Executive Summary

Build the world's first formal verification system for drug-induced cardiac toxicity by **proving mathematically** that drug molecules CANNOT bind to the hERG potassium channel, preventing $500M+ Phase III failures.

**Goal**: Prove that Molecule X lacks the necessary pharmacophore geometry required for hERG binding.

**Approach**: Discrete pharmacophore-based impossibility proof (NOT continuous docking or thermodynamics).

**Business Value**: Deterministic safety guarantee that current QSAR/docking (~70% accuracy) cannot provide.

---

## Problem Statement

### Business Problem
- **Cost**: $500M+ per drug withdrawn for cardiac toxicity
- **Frequency**: Leading cause of drug withdrawals since 1990s
  - Terfenadine (Seldane) - 1997 withdrawal
  - Cisapride - 2000 withdrawal
  - Grepafloxacin - 1999 withdrawal
- **Current Solution**: Patch-clamp assays + QSAR models
  - ~70% precision (too low for Phase III confidence)
  - High false positives (kill good drugs)
  - High false negatives (miss toxic drugs)
- **Gap**: No mathematical guarantees - discover toxicity too late

### Technical Problem
hERG (KCNH2) channel binding is hard to predict because:
- **Promiscuous pocket**: 13Å wide aromatic cage accepts many structures
- **Dynamic gating**: Pocket shape changes with voltage/state
- **Subtle structure-activity**: Minor chemical changes → huge affinity shifts
- **Protonation dependence**: pH-dependent binding at physiological conditions
- **QSAR limitations**: Black-box models miss conformational "black swans"

**Root Cause**: No way to PROVE impossibility - only estimate probability.

**Solution**: Formal verification can prove structural incompatibility.

---

## Solution Approach: Pharmacophore-Based Impossibility Proof

### What We Will Prove
```lean
-- DRAFT - will be refined
theorem herg_geometric_exclusion (drug : Molecule) (herg_pore : BindingSite) :
    geometric_incompatible drug herg_pore →
    ¬can_bind drug herg_pore := by
  sorry
```

### Why This is Feasible
[TO BE FILLED]

### Why This is Valuable
[TO BE FILLED]

---

## Technical Architecture

### Layer 1: Data Representation
[TO BE FILLED]
- Molecular structure representation
- hERG binding site model
- Geometric constraints

### Layer 2: Formalization (Lean 4)
[TO BE FILLED]
- Core types and definitions
- Key theorems
- Proof strategy

### Layer 3: Automation (Aristotle)
[TO BE FILLED]
- What Aristotle can prove automatically
- What needs human guidance
- Proof workflow

---

## MVP Definition

### Success Criteria
1. **Provable**: Formally verify 1 property for 1 drug molecule
2. **Valuable**: Property that would have prevented a real failure
3. **Demonstrable**: Working Lean proof + Aristotle automation
4. **Explainable**: Clear narrative for pharma executives

### Minimum Scope
[TO BE FILLED - simplest possible proof]

### Out of Scope (for MVP)
[TO BE FILLED - what we're NOT doing]

---

## Implementation Plan

### Phase 1: Research & Validation (Week 1)
[TO BE FILLED]

### Phase 2: Formalization (Week 2)
[TO BE FILLED]

### Phase 3: Proof & Testing (Week 3)
[TO BE FILLED]

### Phase 4: Documentation & Demo (Week 4)
[TO BE FILLED]

---

## Success Metrics

### Technical Metrics
- [ ] Lean proof compiles without errors
- [ ] Aristotle can prove theorem (fully or partially)
- [ ] Proof is non-vacuous (actually excludes binding)

### Business Metrics
- [ ] Would have caught ≥1 real drug failure
- [ ] Explainable to pharma scientists (no hand-waving)
- [ ] Extensible to other molecules/properties

---

## Risks & Mitigations

[TO BE FILLED from AI analysis]

---

## Open Questions

[TO BE FILLED from AI research]

---

## References

- hERG cryo-EM structures: PDB
- Failed drugs database: FDA withdrawals
- Binding data: ChEMBL, BindingDB

---

**Next**: Synthesize Grok + Gemini + Codex research → Fill in blanks → Multi-AI audit
