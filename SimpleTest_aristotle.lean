/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d782810d-e7e4-4126-ae30-0a43e3a229eb

The following was proved by Aristotle:

- theorem conservation_simple (a b : ℝ) : a + b - a = b

- theorem nonneg_product (x y : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) : x * y ≥ 0

- theorem fraction_le_one (x y : ℝ) (hx : x ≥ 0) (hy : y > 0) : x / (x + y) ≤ 1
-/

/-
  Ultra-simple test for Aristotle
  This tests basic arithmetic properties we'll need for biochemistry.
-/

import Mathlib.Tactic


-- Test 1: Basic algebra for conservation laws
theorem conservation_simple (a b : ℝ) : a + b - a = b := by
  ring

-- Test 2: Non-negativity (reaction rates must be >= 0)
theorem nonneg_product (x y : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) : x * y ≥ 0 := by
  -- The product of two non-negative numbers is non-negative.
  apply mul_nonneg hx hy

-- Test 3: Fraction bound (for Michaelis-Menten)
theorem fraction_le_one (x y : ℝ) (hx : x ≥ 0) (hy : y > 0) : x / (x + y) ≤ 1 := by
  exact div_le_one_of_le₀ ( by linarith ) ( by linarith )