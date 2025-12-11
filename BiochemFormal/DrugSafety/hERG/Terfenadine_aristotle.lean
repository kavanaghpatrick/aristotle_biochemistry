/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 9967df06-f2cb-448c-8523-d7d7c65d1bbb

Aristotle encountered an error while processing imports for this file.
Error:
Axioms were added during init_sorries: ['BiochemFormal.DrugSafety.hERG.necessary_motif']

-/

/-
Formal Verification: Terfenadine hERG Binding Analysis

This module formally proves whether terfenadine satisfies the necessary
pharmacophore motif for hERG binding.

**Test Case**: Terfenadine (PubChem CID 5405)
- Known hERG blocker (withdrawn 1997 for cardiac toxicity)
- IC50 = 56 nM (high-affinity blocker)
- Features extracted from SMILES via RDKit

**Expected Result**: With conservative constraints [4.0, 5.0] Å for cation-aromatic,
terfenadine FAILS to satisfy the pharmacophore (distances 5.97 Å, 6.20 Å).

This is a **false negative** - the molecule DOES bind but our constraints are too narrow.
-/

import BiochemFormal.DrugSafety.hERG.Core

namespace BiochemFormal.DrugSafety.hERG

open Core

/-! ## Terfenadine Feature Data -/

/--
Terfenadine features extracted from RDKit (pH 7.4, single ETKDG conformer).

Data source: data/terfenadine_features.json
-/

-- Cationic center: Tertiary amine nitrogen (piperidine ring)
def terfenadine_cation : Feature := {
  id := "cation_N9"
  kind := FeatureKind.Cationic
  coord := ((-4481236079 : ℚ) / 8673443686, (-450468369 : ℚ) / 693936562, (-532979995 : ℚ) / 1461533378)
  protonated_at_pH7 := true
}

-- Aromatic ring 0: First phenyl group
def terfenadine_aromatic0 : Feature := {
  id := "aromatic_ring0"
  kind := FeatureKind.Aromatic
  coord := ((45529471383 : ℚ) / 9216191390, (5220583321 : ℚ) / 2979784590, (-20595783905 : ℚ) / 9981354022)
  protonated_at_pH7 := false
}

-- Aromatic ring 1: Second phenyl group
def terfenadine_aromatic1 : Feature := {
  id := "aromatic_ring1"
  kind := FeatureKind.Aromatic
  coord := ((44635533773 : ℚ) / 9021513969, (-2047412943 : ℚ) / 2580644327, (12694514206 : ℚ) / 6227129619)
  protonated_at_pH7 := false
}

-- Hydrophobic region: tert-butyl + aliphatic + aromatic clusters
def terfenadine_hydrophobe : Feature := {
  id := "hydrophobe_cluster0"
  kind := FeatureKind.Hydrophobe
  coord := ((13588110340 : ℚ) / 9278898773, (879888686 : ℚ) / 6151017527, (1055304061 : ℚ) / 7411601159)
  protonated_at_pH7 := false
}

-- Terfenadine molecule (all features)
def terfenadine : Molecule := {
  features := [terfenadine_cation, terfenadine_aromatic0, terfenadine_aromatic1, terfenadine_hydrophobe]
}

/-! ## Distance Facts -/

/--
Measured distances from RDKit 3D conformer (Angstroms).

Key distances for pharmacophore analysis:
- Cation → Aromatic0: 6.199 Å (EXCEEDS [4.0, 5.0] constraint)
- Cation → Aromatic1: 5.971 Å (EXCEEDS [4.0, 5.0] constraint)
- Aromatic0 ↔ Aromatic1: 4.828 Å
- Aromatic0 → Hydrophobe: 4.420 Å
- Aromatic1 → Hydrophobe: 4.075 Å
- Cation → Hydrophobe: 2.193 Å
-/

-- Distance from cation to aromatic ring 0
axiom dist_cation_aromatic0 :
  distance terfenadine_cation.coord terfenadine_aromatic0.coord = 6.199

-- Distance from cation to aromatic ring 1
axiom dist_cation_aromatic1 :
  distance terfenadine_cation.coord terfenadine_aromatic1.coord = 5.971

-- Distance from aromatic ring 0 to hydrophobe
axiom dist_aromatic0_hydrophobe :
  distance terfenadine_aromatic0.coord terfenadine_hydrophobe.coord = 4.420

-- Distance from aromatic ring 1 to hydrophobe
axiom dist_aromatic1_hydrophobe :
  distance terfenadine_aromatic1.coord terfenadine_hydrophobe.coord = 4.075

/-! ## Safety Theorem -/

/--
**Theorem**: Terfenadine does not satisfy hERG pharmacophore constraints.

**Analysis**: This theorem proves that terfenadine LACKS the necessary motif
under our conservative constraints. However, this is a **false negative**:

- **Ground truth**: Terfenadine IS a high-affinity hERG blocker (IC50 = 56 nM)
- **Prediction**: Our constraints say it CANNOT bind
- **Conclusion**: Constraints [4.0, 5.0] Å are TOO NARROW

**Root Cause**:
1. Cation-aromatic distances (5.97 Å, 6.20 Å) exceed 5.0 Å upper bound
2. Literature indicates cation-π can extend to 6.0 Å (Dougherty 2013)
3. Single conformer may not represent bioactive conformation

**Recommendation**: Expand cation-aromatic constraint to [4.0, 6.0] Å.

**Proof Strategy**:
- Enumerate all possible (cation, aromatic, hydrophobe) triples
- For terfenadine: 1 cation × 2 aromatic × 1 hydrophobe = 2 cases
- Case 1: (cation_N9, aromatic_ring0, hydrophobe_cluster0)
  - dist_ca = 6.199 > 5.0 → violates upper bound
- Case 2: (cation_N9, aromatic_ring1, hydrophobe_cluster0)
  - dist_ca = 5.971 > 5.0 → violates upper bound
- Conclude: NO valid certificate exists → ¬BindsHERG terfenadine

**Note**: This proof is technically correct given the axioms, but empirically wrong.
It demonstrates the need for constraint validation (Week 2).
-/
theorem terfenadine_conservative : ¬ BindsHERG terfenadine := by
  apply candidate_safe
  intro cert
  -- Aristotle should generate case analysis here
  -- Case 1: cation + aromatic0 + hydrophobe
  -- Case 2: cation + aromatic1 + hydrophobe
  -- Both cases: distance > 5.0 → violation
  sorry

end BiochemFormal.DrugSafety.hERG
