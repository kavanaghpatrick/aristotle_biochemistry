# GitHub Issues for Geometric Reachability Approach

**Epic**: Geometric Breakthrough - Formal Proofs from Protein Structure

---

## Issue #1: [EPIC] Geometric Reachability for hERG Safety Proofs

**Labels**: `epic`, `breakthrough`, `geometry`

**Description**:
Pivot from axiom-based pharmacophore approach to geometric impossibility proofs.

**Goal**: Prove molecules CANNOT bind hERG by showing geometric impossibility (steric clash, volume exclusion, reachability) from PDB structure.

**Why Breakthrough**:
- First-ever formal geometric proofs for protein-ligand binding
- Axiom-free (built on Mathlib geometry)
- Generalizes to ANY target with crystal structure
- Aristotle-compatible (no custom axioms)

**Timeline**: 2-3 weeks
**Dependencies**: PDB 7CN0, Lean 4, Mathlib geometry

**Child Issues**: #2-#10

---

## Phase 1: Structure Acquisition

### Issue #2: Extract hERG Binding Site from PDB

**Labels**: `phase-1`, `pdb`, `data`

**Description**:
Download and parse hERG cryo-EM structure (PDB: 7CN0) to extract binding site residues.

**Tasks**:
- [ ] Download `7cn0.pdb` and `7cn0.cif` from RCSB PDB
- [ ] Parse with BioPython
- [ ] Extract S6 helix residues (620-660, all 4 chains)
- [ ] Identify key residues (Phe656, Tyr652, Thr623, etc.)
- [ ] Save to `data/pdb/7cn0.pdb`
- [ ] Generate `data/herg_binding_site.json`

**Acceptance Criteria**:
- JSON contains coordinates for 40+ residues (4 chains × 10 key residues)
- Phe656 coordinates for all 4 chains extracted
- Visual confirmation in PyMOL

**Dependencies**: None
**Estimated Time**: 4 hours

---

### Issue #3: Measure hERG Pocket Geometry

**Labels**: `phase-1`, `geometry`, `analysis`

**Description**:
Calculate geometric properties of hERG binding pocket from PDB structure.

**Tasks**:
- [ ] Calculate cavity center (centroid of key residues)
- [ ] Estimate cavity radius (max distance from center to wall)
- [ ] Calculate cavity volume (sphere approximation)
- [ ] Measure Phe656-Phe656 distances (inter-chain spacing)
- [ ] Identify minimum aperture (narrowest entrance)
- [ ] Document in `docs/herg_pocket_geometry.md`

**Measurements Needed**:
- Cavity volume: ~400-600 Å³
- Cavity radius: ~12 Å
- Phe656 spacing: ~15-20 Å (opposite chains)

**Acceptance Criteria**:
- Documented measurements with error margins
- PyMOL visualization showing cavity
- Comparison to literature values (validation)

**Dependencies**: #2
**Estimated Time**: 4 hours

---

## Phase 2: Lean Geometric Formalization

### Issue #4: Build Lean Geometry Library

**Labels**: `phase-2`, `lean`, `geometry`, `core`

**Description**:
Create geometric primitives library built on Mathlib (axiom-free).

**Tasks**:
- [ ] Create `BiochemFormal/Geometry/Core.lean`
- [ ] Define `Point3D` type (ℝ × ℝ × ℝ)
- [ ] Implement `distance` function (Euclidean)
- [ ] Implement `sphere_overlap` predicate
- [ ] Implement `point_in_sphere` test
- [ ] Add docstrings with proofs sketches
- [ ] Verify builds with `lake build`

**Code Structure**:
```lean
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Analysis.Normed.Group.Basic

def Point3D := ℝ × ℝ × ℝ
def distance (p1 p2 : Point3D) : ℝ := ...
def sphere_overlap (c1 c2 : Point3D) (r1 r2 : ℝ) : Prop := ...
```

**Acceptance Criteria**:
- All definitions compile
- No custom axioms (verify with `#print axioms`)
- Basic test theorems prove

**Dependencies**: None
**Estimated Time**: 6 hours

---

### Issue #5: Formalize hERG Structure in Lean

**Labels**: `phase-2`, `lean`, `protein`

**Description**:
Represent hERG binding site structure in Lean using data from #3.

**Tasks**:
- [ ] Create `BiochemFormal/Structures/Protein.lean`
- [ ] Define `AminoAcid` structure (name, chain, coords, VDW radius)
- [ ] Define `BindingSite` structure (residues list, cavity info)
- [ ] Create `herg_site : BindingSite` with PDB coordinates
- [ ] Include all 4 Phe656 copies
- [ ] Add helper functions (`get_residue_by_name`, etc.)
- [ ] Verify builds

**Acceptance Criteria**:
- `herg_site` contains 40+ residues
- Coordinates match PDB (±0.1 Å tolerance)
- Type-checks successfully

**Dependencies**: #3, #4
**Estimated Time**: 8 hours

---

### Issue #6: Formalize Molecular Geometry in Lean

**Labels**: `phase-2`, `lean`, `molecule`

**Description**:
Represent molecules as collections of atoms with 3D coordinates.

**Tasks**:
- [ ] Create `BiochemFormal/Structures/Molecule.lean`
- [ ] Define `Atom` structure (element, coord, VDW radius)
- [ ] Define `Molecule` structure (atoms list)
- [ ] Implement `molecular_volume` function
- [ ] Implement `bounding_sphere` function
- [ ] Implement `min_distance_to_point` function
- [ ] Add helper for finding closest atom to residue

**Acceptance Criteria**:
- Test molecule compiles (e.g., water)
- Volume calculation produces reasonable values
- Bounding sphere computation works

**Dependencies**: #4
**Estimated Time**: 6 hours

---

## Phase 3: Geometric Theorems

### Issue #7: Prove Steric Clash Theorem

**Labels**: `phase-3`, `lean`, `theorem`, `proof`

**Description**:
Formalize and prove: molecules with atomic overlaps cannot bind.

**Tasks**:
- [ ] Create `BiochemFormal/DrugSafety/hERG/GeometricTheorems.lean`
- [ ] Define `has_steric_clash` predicate
- [ ] Define `CanBind` predicate (abstract for now)
- [ ] State theorem: `steric_clash_prevents_binding`
- [ ] Prove theorem (or mark as axiom if too complex for MVP)
- [ ] Create 2 concrete examples (molecules with known clashes)
- [ ] Verify Aristotle can handle proof (if simple enough)

**Theorem**:
```lean
theorem steric_clash_prevents_binding (m : Molecule) (site : BindingSite) :
  has_steric_clash m site = true → ¬ CanBind m site
```

**Acceptance Criteria**:
- Theorem compiles
- 2 concrete proofs complete
- No custom axioms except `CanBind` definition

**Dependencies**: #5, #6
**Estimated Time**: 8 hours

---

### Issue #8: Prove Volume Exclusion Theorem

**Labels**: `phase-3`, `lean`, `theorem`, `proof`

**Description**:
Formalize and prove: molecules larger than cavity cannot fit.

**Tasks**:
- [ ] Define `cavity_volume` function
- [ ] State theorem: `volume_exclusion`
- [ ] Prove theorem using arithmetic on volumes
- [ ] Test Aristotle automation (should work - just arithmetic!)
- [ ] Create 3 concrete examples:
  - [ ] Vancomycin (MW 1449 Da, should fail)
  - [ ] Azithromycin (MW 749 Da, critical test!)
  - [ ] Erythromycin (MW 734 Da, critical test!)

**Theorem**:
```lean
theorem volume_exclusion (m : Molecule) (site : BindingSite) :
  molecular_volume m > cavity_volume site → ¬ CanBind m site
```

**Acceptance Criteria**:
- Theorem compiles and proves
- Aristotle automates concrete proofs (via `norm_num`)
- Macrolides (azithromycin, erythromycin) proven safe

**Dependencies**: #6, #7
**Estimated Time**: 8 hours

---

### Issue #9: Prove Reachability Theorem

**Labels**: `phase-3`, `lean`, `theorem`, `proof`

**Description**:
Formalize and prove: molecules that can't reach key residues cannot bind.

**Tasks**:
- [ ] Define `min_distance_to_residue` function
- [ ] Define `CanBindWithAromatic` predicate (aromatic stacking)
- [ ] State theorem: `cannot_reach_aromatic`
- [ ] Prove theorem
- [ ] Create 2 concrete examples:
  - [ ] Metformin (short, rigid, can't reach Phe656)
  - [ ] Aspirin (also short)

**Theorem**:
```lean
theorem cannot_reach_aromatic (m : Molecule) (site : BindingSite) :
  (∀ phe ∈ site.residues, phe.name = "PHE" →
    min_distance_to_residue m phe > 6.0) →
  ¬ CanBindWithAromatic m site
```

**Acceptance Criteria**:
- Theorem compiles
- 2 concrete proofs complete
- Aristotle can automate (distance comparisons)

**Dependencies**: #6, #7
**Estimated Time**: 6 hours

---

## Phase 4: Automation

### Issue #10: Build PDB → Lean Converter

**Labels**: `phase-4`, `automation`, `python`

**Description**:
Automate conversion of PDB structures to Lean binding site definitions.

**Tasks**:
- [ ] Create `scripts/pdb_to_lean.py`
- [ ] Parse PDB with BioPython
- [ ] Extract specified residues
- [ ] Generate Lean `BindingSite` code
- [ ] Add CLI: `python pdb_to_lean.py 7cn0.pdb --residues 656,652 --output hERG.lean`
- [ ] Test on hERG structure
- [ ] Document usage

**Acceptance Criteria**:
- Generated Lean code compiles
- Coordinates match PDB source
- Works on multiple PDB files

**Dependencies**: #5
**Estimated Time**: 6 hours

---

### Issue #11: Enhanced SMILES → Lean Geometric Converter

**Labels**: `phase-4`, `automation`, `python`

**Description**:
Extend RDKit pipeline to generate full atomic geometry for Lean.

**Tasks**:
- [ ] Create `scripts/molecule_to_lean_geometric.py`
- [ ] Generate 3D conformer (ETKDG)
- [ ] Extract all atom coordinates
- [ ] Include VDW radii
- [ ] Generate Lean `Molecule` code
- [ ] Calculate volume, bounding sphere
- [ ] Add CLI: `python molecule_to_lean_geometric.py "CCO" ethanol`
- [ ] Test on 5 molecules

**Acceptance Criteria**:
- Generated Lean molecules compile
- Volume calculations reasonable
- Works with 100+ atom molecules

**Dependencies**: #6
**Estimated Time**: 6 hours

---

### Issue #12: Aristotle Batch Proof Automation

**Labels**: `phase-4`, `automation`, `aristotle`

**Description**:
Test Aristotle automation on geometric theorems and create batch pipeline.

**Tasks**:
- [ ] Test Aristotle on volume_exclusion theorem (should work!)
- [ ] Test Aristotle on steric_clash theorem
- [ ] Test Aristotle on reachability theorem
- [ ] Measure success rate (target: >50%)
- [ ] Create batch script: `scripts/batch_geometric_proofs.sh`
- [ ] Process 10 molecules through pipeline
- [ ] Document which proof types Aristotle can handle

**Acceptance Criteria**:
- Aristotle proves ≥5/10 molecules automatically
- Batch script processes molecules end-to-end
- Clear documentation of what Aristotle can/can't do

**Dependencies**: #8, #9, #11
**Estimated Time**: 8 hours

---

## Phase 5: Validation

### Issue #13: Geometric Test Suite (20 Molecules)

**Labels**: `phase-5`, `validation`, `testing`

**Description**:
Create comprehensive test suite across molecular size/shape spectrum.

**Tasks**:
- [ ] Select 20 test molecules:
  - 5 large (>1000 Da): Expected to fail volume test
  - 5 small/rigid: Expected to fail reachability
  - 5 known binders: Expected to pass (no proof)
  - 5 custom designs: Steric clash tests
- [ ] Process all through pipeline
- [ ] Generate Lean proofs for certifiable molecules
- [ ] Run Aristotle automation
- [ ] Document results in `docs/geometric_validation_results.md`

**Critical Tests**:
- [ ] Vancomycin: Large, should fail volume
- [ ] **Azithromycin**: MW 749 Da, macrolide FALSE NEGATIVE test
- [ ] **Erythromycin**: MW 734 Da, macrolide FALSE NEGATIVE test
- [ ] Metformin: Small, should fail reachability
- [ ] Terfenadine: Known binder, should NOT be provable

**Acceptance Criteria**:
- ≥10 molecules proven CANNOT bind
- 0 false negatives (no proven-safe molecules that actually bind)
- Macrolide hypothesis validated (do they fail volume test?)

**Dependencies**: #12
**Estimated Time**: 12 hours

---

### Issue #14: Compare Coverage: Geometric vs Axiom Approach

**Labels**: `phase-5`, `analysis`

**Description**:
Quantify coverage difference between geometric and axiom-based approaches.

**Tasks**:
- [ ] Load axiom results (14.9% coverage, 7/47 molecules)
- [ ] Count geometric coverage (how many provable?)
- [ ] Compare false negative rates
- [ ] Analyze which molecules each approach catches
- [ ] Create comparison table
- [ ] Document in `docs/approach_comparison.md`

**Questions**:
- Does geometric catch more or fewer molecules?
- Does geometric solve macrolide false negatives?
- Is there overlap (molecules caught by both)?

**Acceptance Criteria**:
- Clear quantitative comparison
- False negative analysis
- Recommendation: which approach is better

**Dependencies**: #13
**Estimated Time**: 4 hours

---

## Phase 6: Documentation

### Issue #15: Pharma-Facing Documentation

**Labels**: `phase-6`, `documentation`

**Description**:
Create clear documentation explaining geometric approach for pharma audience.

**Tasks**:
- [ ] Write `docs/geometric_approach_explained.md`:
  - Why geometric > pharmacophore
  - How proofs work (non-technical)
  - Examples (vancomycin, metformin)
  - Limitations and scope
- [ ] Create visual diagrams:
  - hERG pocket with molecule overlaid
  - Volume comparison diagram
  - Steric clash illustration
- [ ] Document automation pipeline
- [ ] Create FAQ section

**Acceptance Criteria**:
- Readable by medicinal chemist (no Lean expertise needed)
- Visual aids clear and professional
- Limitations stated transparently

**Dependencies**: #13, #14
**Estimated Time**: 8 hours

---

### Issue #16: 10-Slide Demo Presentation

**Labels**: `phase-6`, `presentation`

**Description**:
Create investor/pharma pitch deck for geometric breakthrough.

**Slides**:
1. Problem: hERG toxicity costs $500M+ per failure
2. Current Solutions: QSAR (80% accuracy), patch clamp (expensive)
3. Our Approach: Formal geometric proofs from structure
4. Breakthrough: First-ever formal protein-ligand proofs
5. Example 1: Vancomycin (too large)
6. Example 2: Metformin (can't reach)
7. Results: X molecules proven safe, 0% false negatives
8. Comparison: Geometric vs axiom vs QSAR
9. Generalization: Any target with crystal structure
10. Next Steps: Multi-conformer, more targets

**Acceptance Criteria**:
- Professional design (not just bullet points)
- Real molecular visualizations
- Quantitative results
- Clear value proposition

**Dependencies**: #13, #14, #15
**Estimated Time**: 6 hours

---

## Issue #17: GitHub Release & Public Announcement

**Labels**: `phase-6`, `release`

**Description**:
Package everything for public release and announcement.

**Tasks**:
- [ ] Clean up codebase (remove debug code)
- [ ] Write comprehensive README.md
- [ ] Add installation instructions
- [ ] Create LICENSE file (MIT or Apache 2.0)
- [ ] Tag release: `v1.0.0-geometric-mvp`
- [ ] Write release notes
- [ ] Prepare Twitter/LinkedIn announcement
- [ ] Submit to Hacker News / Reddit r/programming

**Release Contents**:
- All Lean code (geometry library + hERG proofs)
- All Python scripts (automation pipeline)
- Documentation (pharma-facing + technical)
- Test suite results
- Demo presentation

**Acceptance Criteria**:
- Clean, professional repository
- Easy to reproduce results
- Clear contribution guidelines

**Dependencies**: #15, #16
**Estimated Time**: 6 hours

---

## Summary

**Total Issues**: 17 (1 epic + 16 implementation)
**Total Estimated Time**: 120 hours (~3 weeks with buffer)

**Critical Path**:
1. PDB extraction (#2, #3) → 8 hours
2. Lean formalization (#4, #5, #6) → 20 hours
3. Theorems (#7, #8, #9) → 22 hours
4. Automation (#10, #11, #12) → 20 hours
5. Validation (#13, #14) → 16 hours
6. Documentation (#15, #16, #17) → 20 hours

**Milestones**:
- Day 3: Structure extraction complete
- Day 7: All theorems formalized
- Day 10: Automation working
- Day 14: Validation complete
- Day 17: Documentation & release

**Risk Mitigation**:
- Test Aristotle early (Day 7) - know if automation works
- Macrolide test early (Day 10) - validate hypothesis
- Fallback: Manual proofs if Aristotle fails
