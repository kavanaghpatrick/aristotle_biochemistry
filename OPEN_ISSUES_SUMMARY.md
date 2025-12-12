# Open GitHub Issues: What's Left to Explore

**Current Status**: 83.3% formal coverage (40/48 molecules)
**Last Updated**: 2025-12-12
**Target**: Decide whether to push to 95% or publish at 83%

---

## 🎯 TO IMPROVE hERG COVERAGE (Priority Order)

### Issue #36: Pharmacophore Proofs ✅ **COMPLETE** ✅ CLOSED
- **Status**: 11/13 verified by Aristotle (84.6% success)
- **Coverage**: +29.8% (43.2% → 73.0%)
- **Action**: Closed Dec 11, 2025

### Issue #37: Large-Scale Screening ✅ **COMPLETE** ✅ CLOSED
- **Status**: Validated on 50 molecules
- **Coverage**: 83.3% (40/48 valid molecules)
- **Zero false negatives**: All known binders correctly NOT proven safe
- **Action**: Closed Dec 12, 2025
- **Blocker**: ChEMBL API too unreliable for 1000+ scale
- **Recommendation**: Download ChEMBL dump or publish with 50 molecules

---

### Issue #35: Semi-Algebraic Feasibility 🥉 **TIER 2 - UNEXPLORED** (NEXT?)
- **Status**: OPEN - Never attempted
- **Potential**: +14-19% coverage (5-7 molecules)
- **Target**: 73% → **87-92%**
- **Complexity**: ⭐⭐⭐ HIGH (3-4 weeks)
- **Method**: Prove polynomial constraint systems have no real solutions

**What It Does**:
```
Molecule has:
  ✅ Right size (fits cavity)
  ✅ Right pharmacophore (aromatic + nitrogen)
  ❌ But satisfying ALL constraints simultaneously is algebraically impossible

Example constraints:
  - Bond lengths (quadratic equations)
  - Van der Waals exclusions (sphere inequalities)
  - Aromatic alignment (angular constraints)
  - Cavity boundaries (sphere equations)

Prove: No 3D configuration satisfies ALL constraints → Cannot bind
```

**Why It's Different**:
- Previous methods check constraints **independently**
- This checks **simultaneous satisfaction** (algebraic consistency)
- Uses Gröbner bases or Cylindrical Algebraic Decomposition (CAD)

**Target Molecules**:
- Tamoxifen (rigid triphenylethylene)
- Fluoxetine (diphenylamine + CF3)
- Atorvastatin (complex statin)
- Simvastatin (lactone + chain)
- Rosuvastatin (pyrimidine + fluorophenyl)

**Recommendation**:
- ✅ **Worth exploring** if you want to push toward 90%
- ⚠️ High complexity (need SymPy/Mathematica for Gröbner bases)
- ⚠️ May be hard to formalize in Lean (manual proofs likely)
- 💡 Run Python PoC first (5 days) before committing to Lean

---

### Issue #33: Graph Diameter ❌ **FAILED - CLOSED**
- **Status**: PoC failed (0/21 molecules)
- **Result**: All molecules have diameter ≥ 12 Å
- **Action**: Already closed - don't retry

---

### Issue #34: Metric Embedding / Pharmacophore ✅ **COMPLETE**
- **Status**: DONE (this was Issue #36 in practice)
- **Action**: Update to reflect completion

---

### Issue #30: Prove Positive Controls 🔬 **RESEARCH**
- **Status**: OPEN - Exploratory
- **Goal**: Prove known BINDERS satisfy binding requirements
- **Purpose**: Validate model from both directions

**What It Does**:
```lean
-- Currently we prove: molecule CANNOT bind
theorem lisinopril_safe : CannotBind lisinopril

-- This would prove: known binder CAN bind
theorem terfenadine_can_bind : CanBind terfenadine := by
  -- Prove:
  --   1. Radius allows reaching Phe656 ✓
  --   2. Volume fits in cavity ✓
  --   3. Has pharmacophore ✓
  -- Therefore: Geometrically compatible (consistent with IC50=56nM)
```

**Value**:
- ✅ Demonstrates system isn't vacuously conservative
- ✅ Validates geometric model (not just proving negatives)
- ✅ Strengthens publication claims
- ⚠️ Doesn't increase coverage (same 27 molecules)

**Recommendation**:
- 💡 **Nice to have** for publication quality
- 🔬 Research value > practical value
- ⏱️ Low priority (implement if time allows)
- 📄 Would strengthen academic paper

---

## 🚀 TO EXPAND TO OTHER TARGETS (New Directions)

### Issue #1: PK/PD Parameter Bounds 💊 **HIGH FEASIBILITY**
- **Status**: OPEN - Unexplored
- **Target**: Prove pharmacokinetic parameters (half-life, clearance)
- **Method**: Interval arithmetic + differential equations

**Example**:
```lean
theorem aspirin_half_life_bounds :
  aspirin.half_life ∈ [2.5, 4.5] hours := by
  -- Prove from:
  --   - Ester hydrolysis rate constants
  --   - Volume of distribution
  --   - Renal clearance
```

**Value**: Very practical for drug development
**Complexity**: Medium (needs ODE formalization)

---

### Issue #3: Blood-Brain Barrier 🧠 **RESEARCH**
- **Status**: OPEN - Unexplored
- **Target**: Prove CNS drugs can/cannot cross BBB
- **Method**: Lipophilicity (logP), polar surface area, H-bond donors

**Example**:
```lean
theorem morphine_crosses_bbb :
  morphine.logP ∈ [0, 3] ∧
  morphine.polar_surface_area < 90 Å² ∧
  morphine.hbond_donors ≤ 3 →
  CrossesBBB morphine
```

**Value**: Important for CNS drug discovery
**Complexity**: Medium (mostly geometric)

---

### Issue #4: Kinase Selectivity Panel 🎯 **ONCOLOGY**
- **Status**: OPEN - High priority
- **Target**: Prove kinase inhibitor selectivity
- **Method**: Binding pocket geometry differences

**Example**:
```lean
theorem imatinib_selective_for_bcr_abl :
  CanBind imatinib bcr_abl ∧
  CannotBind imatinib src_kinase := by
  -- Prove structural differences in binding pockets
```

**Value**: Critical for cancer drug development
**Complexity**: High (multiple protein structures)

---

## 📄 DOCUMENTATION & PRESENTATION

### Issue #19: Export Proofs to PDF/HTML
- **Status**: OPEN
- **Purpose**: Make proofs readable for pharma review
- **Effort**: Low (1-2 days)
- **Tool**: Lean's built-in HTML export

### Issue #20: Create Pharma Pitch Deck
- **Status**: OPEN
- **Purpose**: Present to industry partners
- **Effort**: Medium (3-5 days)
- **Content**: Results, methodology, business value

### Issue #21: Document Limitations ✅ **COMPLETE** ✅ CLOSED
- **Status**: Completed Dec 12, 2025
- **Deliverable**: `docs/herg_limitations_roadmap.md`
- **Content**: 8 critical limitations, roadmap to 95%, publication strategy
- **Critical**: Now ready for publication

---

## 🎯 RECOMMENDED PRIORITY ORDER (UPDATED 2025-12-12)

### ✅ COMPLETED
- ✅ Issue #36 (Pharmacophore) - 73.0% coverage
- ✅ Issue #37 (Large-scale screening) - 83.3% validated
- ✅ Issue #21 (Document Limitations) - Comprehensive roadmap created

### CURRENT DECISION POINT

**You are here**: 83.3% coverage, zero false negatives, publication-ready

**Option A: Publish Now** ⭐ RECOMMENDED
- Already have novel contribution (formal verification)
- 83.3% coverage is publication-worthy
- Characterizing "hard 17%" is valuable
- Can publish semi-algebraic as follow-up
- **Time**: 2-3 weeks (write paper)

**Option B: Push to 95% First**
1. **Issue #35 (Semi-Algebraic PoC)** - Python/SymPy proof of concept (1 week)
   - If ≥5 molecules → formalize in Lean (3 weeks)
   - If <5 molecules → publish at 83%
2. **Issue #19 (Export Proofs)** - Make reviewers happy (2 days)
3. **Issue #30 (Positive Controls)** - Strengthen paper (1 week, optional)

**Total Time**: 4-5 weeks

**Expected Final Coverage**: 95-100% (if #35 succeeds) or 83% (if fails)

---

### If Goal = **Publish / Industry Demo**

1. **Issue #21 (Document Limitations)** - Critical for honesty (1 day)

2. **Issue #19 (Export Proofs)** - Make presentable (2 days)

3. **Issue #30 (Positive Controls)** - Strengthen claims (1 week)

4. **Issue #20 (Pitch Deck)** - Business presentation (3 days)

**Total Time**: 2 weeks

**Outcome**: Publication-ready + industry-ready materials

---

### If Goal = **Expand to New Targets**

1. **Issue #1 (PK/PD)** - High feasibility, practical value (3-4 weeks)

2. **Issue #3 (BBB)** - Important for CNS drugs (2-3 weeks)

3. **Issue #4 (Kinase)** - High value for oncology (4-6 weeks)

**Total Time**: 9-13 weeks

**Outcome**: Demonstrate methodology generalizes to other drug safety problems

---

## 💡 MY RECOMMENDATION

**Priority 1**: Try Issue #35 (Semi-Algebraic) **Python PoC only** (1 week)
- If it works → huge win (87-92% coverage)
- If it fails → you know the limit (73% is maximum with pure geometry)

**Priority 2**: Documentation (Issues #19, #21) (2-3 days)
- Make current results presentable
- Critical for publication/industry demo

**Priority 3**: Positive controls (Issue #30) (1 week, optional)
- Strengthens academic publication
- Not critical for industry demo

**Total**: 2-3 weeks to "finish" hERG project at highest possible coverage

---

## 🚫 What NOT to Pursue

- ❌ Issue #33 (Graph Diameter) - Already failed, closed
- ❌ Trying to reach 100% coverage - Likely impossible with pure math
- ❌ New hERG proof methods - Diminishing returns past 90%

---

## 🎯 The Big Question

**Do you want to**:

**A) Push hERG to maximum coverage?**
→ Try Issue #35 (Semi-Algebraic) PoC
→ Goal: 87-92% coverage
→ Time: 1-4 weeks

**B) Wrap up hERG and publish?**
→ Documentation (Issues #19, #21)
→ Goal: 73% formal coverage, publication-ready
→ Time: 1 week

**C) Expand to new targets?**
→ Issues #1, #3, or #4
→ Goal: Demonstrate generalizability
→ Time: 9-13 weeks

**D) Build industry demo?**
→ Issues #19, #20, #21, #30
→ Goal: Pharma-ready presentation
→ Time: 2-3 weeks

---

## 📊 Coverage Roadmap (UPDATED)

| Stage | Coverage | Method | Status |
|-------|----------|--------|--------|
| Pilot (37 mol) | 43.2% | Reachability + Volume | ✅ Done (Dec 10) |
| + Pharmacophore | 73.0% | + Aromatic/Nitrogen exclusion | ✅ Done (Dec 11) |
| **Current (50 mol)** | **83.3%** | All 3 methods validated | ✅ Done (Dec 12) |
| + Semi-Algebraic | 95-100% | Polynomial constraints | ⚠️ Unexplored (Issue #35) |
| **Theoretical Max** | ~95% | All pure geometry methods | 🤔 Estimated |
| 100% | 100% | Would need empirical/ML | ❌ Not pure math |

**Key Insights**:
- 73% → 83% improvement due to test set diversity (more small/large molecules)
- "Hard 17%" requires semi-algebraic methods (algebraic infeasibility)
- Pure mathematics likely maxes out at 95% coverage
- Last 5% probably requires biochemical modeling or ML

