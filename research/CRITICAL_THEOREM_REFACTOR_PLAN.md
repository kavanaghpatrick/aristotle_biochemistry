# 🔴 CRITICAL: Theorem Design Refactor Required

**Date**: 2025-12-11
**Severity**: HIGH - Affects validity of entire approach
**Source**: Grok-4 analysis of Aristotle-proven theorems

---

## Problem Statement

Our theorems are **vacuous tautologies** - they prove `True` instead of meaningful safety properties.

### Current (BROKEN):
```lean
theorem ensemble_volume_exclusion
    (molecule : ConformerEnsemble)
    (h_volume : sphere_volume molecule.bounding_radius > herg_cavity_volume) :
    True := by
  trivial  -- ← Always succeeds, proves nothing substantive
```

**Issue**: "If volume > cavity, then True" is a tautology. Aristotle "proved" it trivially because `True` is always provable.

### What We Need:
```lean
theorem ensemble_volume_exclusion
    (molecule : ConformerEnsemble)
    (h_volume : sphere_volume molecule.bounding_radius > herg_cavity_volume) :
    CannotBind molecule := by
  -- ← Proves actual safety property
```

---

## Why This Matters

1. **For Pharma Validation**: FDA/regulators need proofs of safety properties, not tautologies
2. **For Publication**: Nature Methods won't accept vacuous proofs
3. **For Trust**: Current "proofs" are just hypothesis checking (like unit tests), not formal verification

### What Still Works:
- Numeric verification (via `norm_num`) ✅
- Pilot validation (metformin, vancomycin proven; terfenadine not) ✅
- 0% false negative rate ✅

### What's Missing:
- Formal encoding of "cannot bind" ❌
- Substantive proofs linking geometry → safety ❌
- Auditable safety certificates ❌

---

## Grok's Recommended Solution (Option A)

### Step 1: Define Core Predicates

```lean
-- What it means to fit in cavity
def FitsInCavity (radius : ℝ) : Prop :=
  sphere_volume radius ≤ herg_cavity_volume

-- What it means to reach critical residue
def ReachesPhe656 (radius : ℝ) : Prop :=
  radius ≥ min_radius_to_reach_phe656

-- What it means to be unable to bind
def CannotBind (molecule : ConformerEnsemble) : Prop :=
  ¬ (FitsInCavity molecule.bounding_radius ∧ ReachesPhe656 molecule.bounding_radius)
```

**Rationale**:
- `CannotBind` encodes the core safety property
- Based on conserv ative assumption: molecule occupies entire bounding sphere
- Negation of necessary conditions for binding

### Step 2: Axiomatize Domain Knowledge

```lean
-- Empirical fact from structural biology
axiom BindingRequiresFitAndReach :
  ∀ (m : Molecule),
    BindsToHERG m → (FitsInCavity m.bounding_radius ∧ ReachesPhe656 m.bounding_radius)
```

**Justification**:
- Based on PDB 7CN0 (cryo-EM structure)
- Pi-stacking with Phe656 required for hERG blockade (literature)
- Conservative: sufficient but not necessary (acceptable false positives)

### Step 3: Refactor Theorems

```lean
theorem ensemble_volume_exclusion
    (molecule : ConformerEnsemble)
    (h_volume : sphere_volume molecule.bounding_radius > herg_cavity_volume) :
    CannotBind molecule := by
  unfold CannotBind FitsInCavity
  intro h_fits_and_reaches
  cases h_fits_and_reaches with
  | intro h_fits h_reaches =>
    unfold sphere_volume at h_fits
    linarith [h_volume, h_fits]

theorem ensemble_reachability_exclusion
    (molecule : ConformerEnsemble)
    (h_reach : molecule.bounding_radius < min_radius_to_reach_phe656) :
    CannotBind molecule := by
  unfold CannotBind ReachesPhe656
  intro h_fits_and_reaches
  cases h_fits_and_reaches with
  | intro h_fits h_reaches =>
    linarith [h_reach, h_reaches]

theorem herg_safety_certificate
    (molecule : ConformerEnsemble)
    (h : sphere_volume molecule.bounding_radius > herg_cavity_volume ∨
         molecule.bounding_radius < min_radius_to_reach_phe656) :
    CannotBind molecule := by
  cases h with
  | inl h_vol => exact ensemble_volume_exclusion molecule h_vol
  | inr h_reach => exact ensemble_reachability_exclusion molecule h_reach
```

**Key Changes**:
- Return type: `True` → `CannotBind molecule`
- Proof tactics: `trivial` → actual reasoning (`linarith`, `cases`)
- Aristotle can still automate (with proper prompts)

---

## Implementation Plan

### Phase 1: Core Predicates (30 min)
- [ ] Create `BiochemFormal/Safety/Core.lean`
- [ ] Define `FitsInCavity`, `ReachesPhe656`, `CannotBind`
- [ ] Add axiom `BindingRequiresFitAndReach`
- [ ] Build and verify (no `sorry`)

### Phase 2: Refactor Theorems (1 hour)
- [ ] Update `BiochemFormal/Theorems/MultiConformer.lean`
- [ ] Change theorem signatures to return `CannotBind`
- [ ] Write proof sketches (detailed comments for Aristotle)
- [ ] Replace `trivial` with `sorry` placeholders

### Phase 3: Aristotle Re-Proof (15 min + wait)
- [ ] Invoke Aristotle on refactored file
- [ ] Verify substantive proofs (not `trivial`)
- [ ] Check axiom usage (`#print axioms`)

### Phase 4: Validation (30 min)
- [ ] Test on pilot molecules (metformin, vancomycin, terfenadine)
- [ ] Verify numeric computations still work
- [ ] Confirm 0% false negative rate maintained

### Phase 5: Documentation (30 min)
- [ ] Update STATUS.md
- [ ] Document axiom justifications (cite PDB, literature)
- [ ] Prepare for pharma audit trail

---

## Alternative Approaches Considered

### Option B: Keep `True` as certificates
**Pros**: Simple, works with current code
**Cons**: Vacuous, not auditable for pharma
**Verdict**: Rejected (insufficient for production)

### Option C: Dependent types for safety
**Pros**: Type-level guarantees, elegant
**Cons**: Complex, harder for Aristotle
**Verdict**: Future work (after Option A proven)

---

## Success Criteria

After refactoring, we should have:

1. ✅ **Non-vacuous proofs**: Theorems prove `CannotBind`, not `True`
2. ✅ **Substantive reasoning**: Proofs use `linarith`, not `trivial`
3. ✅ **Axiom transparency**: Minimal axioms, justified by domain evidence
4. ✅ **Maintained soundness**: 0% false negatives on pilot + validation suite
5. ✅ **Aristotle compatibility**: AI can still automate proofs
6. ✅ **Audit trail**: Proofs exportable for pharma review

---

## Risks and Mitigation

### Risk 1: Aristotle can't prove refactored theorems
**Mitigation**: Provide detailed proof sketches in comments (as we did before)

### Risk 2: Axioms deemed too strong by reviewers
**Mitigation**: Document empirical basis (PDB, literature), use conservative formulations

### Risk 3: Proofs break on edge cases
**Mitigation**: Extensive testing on 20-molecule suite

---

## Timeline

- **Phase 1-2**: 2 hours (manual implementation)
- **Phase 3**: 5-10 min (Aristotle runtime)
- **Phase 4-5**: 1 hour (validation + docs)
- **Total**: ~3-4 hours to production-ready proofs

---

## References

- Grok-4 analysis: `research/grok_theorem_analysis.md`
- Current (vacuous) theorems: `BiochemFormal/Theorems/MultiConformer_aristotle.lean`
- Lean 4 documentation: https://lean-lang.org/theorem_proving_in_lean4/
- Formal verification in pharma: FDA Digital Health Guidelines

---

## Decision

**APPROVED**: Proceed with Option A refactor immediately.

This is critical for:
- Pharma validation (FDA compliance)
- Publication (Nature Methods quality)
- Scientific integrity (actual formal verification)

The pilot study results remain valid (0% false negatives), but need to be re-expressed as substantive proofs.
