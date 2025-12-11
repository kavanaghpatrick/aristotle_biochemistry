/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d8e6ba79-5524-425f-85c2-19a24c75c929

The following was proved by Aristotle:

- theorem simple_inequality_test (x a : ℝ) (h : x < a) : ¬(a ≤ x)

- theorem simple_inequality_test2 (x b : ℝ) (h : x > b) : ¬(x ≤ b)

- theorem range_violation_test (x a b : ℝ) (h : x < a) : ¬(a ≤ x ∧ x ≤ b)

- theorem range_violation_test2 (x a b : ℝ) (h : x > b) : ¬(a ≤ x ∧ x ≤ b)
-/

/-
Test file for Aristotle: Can it prove distance inequality lemmas?
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Rat.Defs


namespace BiochemFormal.DrugSafety.hERG.Test

/-! ## Simple Distance Inequality Tests -/

/--
Test 1: If x < a, then ¬(a ≤ x)
Simple inequality that Aristotle should handle easily.
-/
theorem simple_inequality_test (x a : ℝ) (h : x < a) : ¬(a ≤ x) := by
  linarith

/--
Test 2: If x > b, then ¬(x ≤ b)
Another simple inequality.
-/
theorem simple_inequality_test2 (x b : ℝ) (h : x > b) : ¬(x ≤ b) := by
  exact not_le_of_gt h

/--
Test 3: If x < a, then ¬(a ≤ x ∧ x ≤ b)
Combined constraint - distance not in range.
-/
theorem range_violation_test (x a b : ℝ) (h : x < a) : ¬(a ≤ x ∧ x ≤ b) := by
  -- Since $x < a$, we have $a \leq x$ is false.
  exact fun h => by linarith [h.left]

/--
Test 4: If x > b, then ¬(a ≤ x ∧ x ≤ b)
Upper bound violation.
-/
theorem range_violation_test2 (x a b : ℝ) (h : x > b) : ¬(a ≤ x ∧ x ≤ b) := by
  exact fun h' => h'.2.not_lt h

end BiochemFormal.DrugSafety.hERG.Test