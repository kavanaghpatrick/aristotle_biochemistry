/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 74d0f672-cb73-42b3-996a-4fb915c04743
-/

import BiochemFormal.Geometry.Core
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic


/-!
# Pharmacophore Safety Proofs

Proves molecules cannot bind hERG if they lack the required pharmacophore
(toxicophore): aromatic ring + basic nitrogen at 5-7 Å distance.

## Mathematical Foundation

This is pure metric space theory:
- Define hERG toxicophore as metric constraint
- For each molecule, enumerate ALL possible aromatic-nitrogen pairs
- Prove NONE satisfy the distance constraint [5.0, 7.0] Å
- Therefore molecule cannot bind (no valid embedding exists)

## Foundation from Literature

F656A mutagenesis abolishes hERG binding (Mitcheson et al. 2000).
→ Phe656 π-stacking is REQUIRED for binding
→ Molecules without aromatic-nitrogen geometry cannot bind

Cavalli et al. (2002): hERG blockers require aromatic + basic nitrogen at 5-7 Å
Sanguinetti & Mitcheson (2005): Validated pharmacophore model

This has ~90% confidence (experimental validation, not pure geometry).

## Why This Works for Aristotle

Aristotle excels at:
1. Finite case analysis (enumerate all aromatic-N pairs)
2. Distance calculations (`norm_num` for arithmetic)
3. Proving non-existence (∀ pairs, distance ∉ [5,7])

Each proof is structurally identical, perfect for automation!
-/

namespace BiochemFormal

-- Use AromaticRing and BasicNitrogen from Geometry.Core
open BiochemFormal.Geometry

/-! ## Pharmacophoric Feature Types -/

inductive PharmacophoreType where
  | aromatic_ring : PharmacophoreType
  | basic_nitrogen : PharmacophoreType
  | hydrophobic : PharmacophoreType

/-! ## hERG Toxicophore (from literature) -/

structure Toxicophore where
  aromatic_nitrogen_min : ℝ := 5.0  -- Angstroms
  aromatic_nitrogen_max : ℝ := 7.0

-- Angstroms

def herg_toxicophore : Toxicophore := {
  aromatic_nitrogen_min := 5.0
  aromatic_nitrogen_max := 7.0
}

/-! ## Distance Calculation -/

noncomputable def aromatic_nitrogen_distance (ar : AromaticRing) (n : BasicNitrogen) : ℝ :=
  BiochemFormal.Geometry.distance ar.centroid n.position

/-! ## Pharmacophore Satisfaction Predicate -/

def satisfies_toxicophore (ar : AromaticRing) (n : BasicNitrogen) : Prop :=
  let d := aromatic_nitrogen_distance ar n
  herg_toxicophore.aromatic_nitrogen_min ≤ d ∧
  d ≤ herg_toxicophore.aromatic_nitrogen_max

/-! ## Pharmacophore Geometry Predicate -/

/--
A molecule has valid pharmacophore geometry if it contains at least one
aromatic-nitrogen pair satisfying the toxicophore distance constraint [5.0, 7.0] Å.

This is a PURE GEOMETRIC definition - it makes no claims about hERG binding.
The biochemical interpretation comes from experimental data (see below).
-/
def has_valid_pharmacophore (m : BiochemFormal.Geometry.Molecule) : Prop :=
  ∃ (ar : AromaticRing) (n : BasicNitrogen),
    ar ∈ m.aromatic_rings ∧
    n ∈ m.basic_nitrogens ∧
    satisfies_toxicophore ar n

/-! ## Binding Predicates (Geometric Definition) -/

/--
CanBind: Defined geometrically as having valid pharmacophore geometry.

BIOCHEMICAL INTERPRETATION (from experimental data, ~90% confidence):
- F656A mutagenesis (Mitcheson 2000): Phe656 π-stacking required for hERG binding
- hERG blocker pharmacophore (Cavalli 2002): aromatic + basic nitrogen at 5-7 Å
- Therefore: pharmacophore geometry is NECESSARY for hERG binding

WHAT WE PROVE FORMALLY: Geometric constraint satisfaction
WHAT WE INTERPRET: Geometry → hERG binding capability
-/
def CanBind (m : BiochemFormal.Geometry.Molecule) : Prop :=
  has_valid_pharmacophore m

/--
CannotBind: Lacks valid pharmacophore geometry.

BIOCHEMICAL INTERPRETATION: Cannot bind hERG (based on pharmacophore necessity)
FORMAL CLAIM: Lacks the aromatic-nitrogen geometry at 5-7 Å distance
-/
def CannotBind (m : BiochemFormal.Geometry.Molecule) : Prop :=
  ¬has_valid_pharmacophore m

/-! ## Helper Lemmas -/

/-- Helper: nothing can be a member of an empty list -/
lemma not_mem_nil {α : Type} (x : α) : x ∉ ([] : List α) := by
  intro h
  cases h

/-! ## Main Theorem: No Aromatic Rings -/

/--
If a molecule has no aromatic rings, it lacks valid pharmacophore geometry.

FORMAL CLAIM: aromatic_rings = [] → ¬has_valid_pharmacophore m
BIOCHEMICAL INTERPRETATION: Therefore cannot bind hERG (F656A mutagenesis evidence)

Proof: Trivial contradiction - can't have aromatic ring from empty list.
-/
theorem no_aromatic_exclusion
    {m : BiochemFormal.Geometry.Molecule}
    (h : m.aromatic_rings = []) :
    CannotBind m := by
  -- CannotBind m := ¬has_valid_pharmacophore m := ¬∃ ar, n, ...
  intro ⟨ar, n, h_ar_in, h_n_in, h_sat⟩
  -- ar ∈ m.aromatic_rings, but m.aromatic_rings = []
  rw [h] at h_ar_in
  -- Contradiction: ar ∈ []
  exact not_mem_nil ar h_ar_in

/-! ## Main Theorem: No Basic Nitrogen -/

/--
If a molecule has no basic nitrogens, it lacks valid pharmacophore geometry.

FORMAL CLAIM: basic_nitrogens = [] → ¬has_valid_pharmacophore m
BIOCHEMICAL INTERPRETATION: Therefore cannot bind hERG (pharmacophore model evidence)

Proof: Trivial contradiction - can't have nitrogen from empty list.
-/
theorem no_nitrogen_exclusion
    {m : BiochemFormal.Geometry.Molecule}
    (h : m.basic_nitrogens = []) :
    CannotBind m := by
  -- CannotBind m := ¬has_valid_pharmacophore m := ¬∃ ar, n, ...
  intro ⟨ar, n, h_ar_in, h_n_in, h_sat⟩
  -- n ∈ m.basic_nitrogens, but m.basic_nitrogens = []
  rw [h] at h_n_in
  -- Contradiction: n ∈ []
  exact not_mem_nil n h_n_in

/-! ## Main Theorem: Distance Violation -/

/--
If all aromatic-nitrogen pairs violate the toxicophore distance constraint [5, 7] Å,
then the molecule lacks valid pharmacophore geometry.

FORMAL CLAIM: (∀ pairs, distance ∉ [5,7]) → ¬has_valid_pharmacophore m
BIOCHEMICAL INTERPRETATION: Therefore cannot bind hERG (pharmacophore model evidence)

Proof: Direct contradiction - no pair satisfies the constraint.
-/
theorem distance_violation_exclusion
    {m : BiochemFormal.Geometry.Molecule}
    (h_viol : ∀ (ar : AromaticRing) (n : BasicNitrogen),
              ar ∈ m.aromatic_rings → n ∈ m.basic_nitrogens →
              ¬satisfies_toxicophore ar n) :
    CannotBind m := by
  -- CannotBind m := ¬has_valid_pharmacophore m := ¬∃ ar, n, ...
  intro ⟨ar, n, h_ar_in, h_n_in, h_sat⟩
  -- Apply h_viol to this specific pair
  have h_not_sat := h_viol ar n h_ar_in h_n_in
  -- Contradiction: satisfies_toxicophore ar n and ¬satisfies_toxicophore ar n
  exact h_not_sat h_sat

end BiochemFormal