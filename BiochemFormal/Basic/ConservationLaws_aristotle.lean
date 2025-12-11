/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: ddd74fd3-21c0-4800-9f4c-916cf5c3a868

The following was proved by Aristotle:

- theorem two_component_conservation (A B A' B' total : ℝ)
    (h_initial : A + B = total)
    (h_final : A' + B' = total) :
    A' - A = -(B' - B)

- theorem multicomponent_conservation (n : ℕ) (conc conc' : Fin n → ℝ) (total : ℝ)
    (h_initial : ∑ i, conc i = total)
    (h_final : ∑ i, conc' i = total) :
    ∑ i, (conc' i - conc i) = 0

- theorem simple_reaction_mass_balance (S P S' P' : ℝ)
    (h_nonneg_S : S ≥ 0) (h_nonneg_P : P ≥ 0)
    (h_nonneg_S' : S' ≥ 0) (h_nonneg_P' : P' ≥ 0)
    (h_conservation : S + P = S' + P') :
    S - S' = P' - P
-/

/-
  Basic Conservation Laws for Biochemical Systems

  Fundamental principles that must hold in all biochemical reactions:
  - Mass conservation
  - Charge conservation
  - Energy conservation (thermodynamics)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Defs


namespace BiochemFormal.ConservationLaws

/--
  Two-component conservation theorem.
  In a closed system with two molecular species A and B,
  if the total amount is constant, then any increase in A
  must equal the decrease in B.

  This is foundational for modeling simple reactions like:
  A ⇌ B (isomerization)
-/
theorem two_component_conservation (A B A' B' total : ℝ)
    (h_initial : A + B = total)
    (h_final : A' + B' = total) :
    A' - A = -(B' - B) := by
  linarith

/-
  Extension to N-component systems.
  In metabolic pathways, we often have multiple intermediates.
  This theorem states that the sum of all concentrations remains constant.
-/
theorem multicomponent_conservation (n : ℕ) (conc conc' : Fin n → ℝ) (total : ℝ)
    (h_initial : ∑ i, conc i = total)
    (h_final : ∑ i, conc' i = total) :
    ∑ i, (conc' i - conc i) = 0 := by
  aesop

/-
  Mass balance for a simple reaction: S → P
  The decrease in substrate equals the increase in product.
-/
theorem simple_reaction_mass_balance (S P S' P' : ℝ)
    (h_nonneg_S : S ≥ 0) (h_nonneg_P : P ≥ 0)
    (h_nonneg_S' : S' ≥ 0) (h_nonneg_P' : P' ≥ 0)
    (h_conservation : S + P = S' + P') :
    S - S' = P' - P := by
  linarith

/-
  Charge conservation in biochemical reactions.
  Important for ensuring balanced ionic equations.
-/
def net_charge (concentrations : List ℝ) (charges : List ℤ) : ℝ :=
  (List.zipWith (fun c z => c * (z : ℝ)) concentrations charges).sum

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Application type mismatch: The argument
  i
has type
  Fin charges.length
but is expected to have type
  Fin conc.length
in the application
  conc.get i
Application type mismatch: The argument
  i
has type
  Fin charges.length
but is expected to have type
  Fin conc'.length
in the application
  conc'.get i-/
theorem charge_conservation
    (conc conc' : List ℝ)
    (charges : List ℤ)
    (h_same_length : conc.length = charges.length)
    (h_same_length' : conc'.length = charges.length) :
    net_charge conc charges = net_charge conc' charges →
    ∑ i : Fin charges.length, (conc.get i - conc'.get i) * (charges.get i : ℝ) = 0 := by
  sorry

end BiochemFormal.ConservationLaws