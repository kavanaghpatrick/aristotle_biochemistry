/-
Negative Safety Proofs: Metformin and Aspirin

Demonstrates the simplified feature-absence approach with real drugs.
-/

import BiochemFormal.DrugSafety.hERG.CoreSimple

namespace BiochemFormal.DrugSafety.hERG.Examples

open Simple

/-! ## Metformin (No Aromatic Rings) -/

/--
Metformin: CN(C)C(=N)NC(=N)N

Features:
- Cationic: ✓ (multiple basic nitrogens)
- Aromatic: ✗ (NO aromatic rings)
- Hydrophobe: Minimal (small molecule)

IC50: > 100 μM (no hERG binding)
-/
def metformin : Molecule := {
  features := [
    ⟨"cation_N1", FeatureKind.Cationic⟩,
    ⟨"cation_N2", FeatureKind.Cationic⟩,
    ⟨"cation_N3", FeatureKind.Cationic⟩,
    ⟨"cation_N4", FeatureKind.Cationic⟩,
    ⟨"cation_N5", FeatureKind.Cationic⟩
  ]
}

-- Fact: Metformin has no aromatic features
theorem metformin_no_aromatic : has_aromatic metformin = false := by
  rfl

/--
**THEOREM**: Metformin is provably safe (cannot bind hERG).

**Proof**: Metformin lacks aromatic rings → Cannot bind ✅

**Real-world validation**: Metformin IC50 > 100 μM (no hERG liability)
-/
theorem metformin_is_safe : ¬ BindsHERG metformin := by
  apply no_aromatic_is_safe
  exact metformin_no_aromatic

/-! ## Aspirin (No Basic Nitrogen) -/

/--
Aspirin: CC(=O)OC1=CC=CC=C1C(=O)O

Features:
- Cationic: ✗ (NO basic nitrogens, has carboxylic acid)
- Aromatic: ✓ (benzene ring)
- Hydrophobe: ✓ (aromatic ring)

IC50: > 100 μM (no hERG binding)
-/
def aspirin : Molecule := {
  features := [
    ⟨"aromatic_ring0", FeatureKind.Aromatic⟩,
    ⟨"hydrophobe_cluster0", FeatureKind.Hydrophobe⟩
  ]
}

-- Fact: Aspirin has no cationic features
theorem aspirin_no_cationic : has_cationic aspirin = false := by
  rfl

/--
**THEOREM**: Aspirin is provably safe (cannot bind hERG).

**Proof**: Aspirin lacks basic nitrogen → Cannot bind ✅

**Real-world validation**: Aspirin IC50 > 100 μM (no hERG liability)
-/
theorem aspirin_is_safe : ¬ BindsHERG aspirin := by
  apply no_cationic_is_safe
  exact aspirin_no_cationic

/-! ## Ethanol (Minimal Pharmacophore) -/

/--
Ethanol: CCO

Features:
- Cationic: ✗ (NO nitrogens)
- Aromatic: ✗ (NO rings)
- Hydrophobe: Minimal (just ethyl group)

No hERG binding (obviously safe)
-/
def ethanol : Molecule := {
  features := [
    ⟨"hydrophobe_ethyl", FeatureKind.Hydrophobe⟩
  ]
}

-- Facts
theorem ethanol_no_cationic : has_cationic ethanol = false := by
  rfl

theorem ethanol_no_aromatic : has_aromatic ethanol = false := by
  rfl

/--
**THEOREM**: Ethanol is provably safe (lacks multiple features).

**Proof**: Ethanol lacks both cationic center AND aromatic ring → Cannot bind ✅
-/
theorem ethanol_is_safe : ¬ BindsHERG ethanol := by
  apply missing_feature_is_safe
  left  -- Use no_cationic case
  exact ethanol_no_cationic

/-! ## General Pattern for Negative Proofs -/

/--
Template theorem for proving safety of any molecule lacking features.

**Usage**: For new molecule X:
1. Define molecule structure
2. Prove feature absence (should be `rfl`)
3. Apply this template

**Automation**: Aristotle can generate these proofs automatically from JSON.
-/
theorem prove_safety_template (m : Molecule)
    (h_no_aro : has_aromatic m = false) :
    ¬ BindsHERG m := by
  apply no_aromatic_is_safe
  exact h_no_aro

end BiochemFormal.DrugSafety.hERG.Examples
