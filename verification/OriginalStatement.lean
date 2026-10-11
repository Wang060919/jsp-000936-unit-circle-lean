/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.FinalClassification

/-!
# A literal original-statement challenge

The specification below independently writes out the complex cardinal products,
the supremum on all unit-modulus complex evaluation points, and the regular
complex exponential coordinates. The proved project theorem must elaborate
against this statement; no angular ordering occurs among its hypotheses.
This is an additional Lean statement check, not an external proof checker.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace OriginalUnitCircleStatement

noncomputable section

variable {n : ℕ}

def literalLebesgue (z : Fin n → ℂ) (w : ℂ) : ℝ :=
  ∑ j : Fin n, ‖∏ k ∈ Finset.univ.erase j, (w - z k) / (z j - z k)‖

def literalMaximum (z : Fin n → ℂ) : ℝ :=
  sSup (literalLebesgue z '' {w : ℂ | ‖w‖ = 1})

def literalMinimizer (z : Fin n → ℂ) : Prop :=
  ∀ other : Fin n → ℂ, (∀ i, ‖other i‖ = 1) → Function.Injective other →
    literalMaximum z ≤ literalMaximum other

def regularCoordinates (n : ℕ) (i : Fin n) : ℂ :=
  Complex.exp (((2 * Real.pi * ((i.val : ℝ) / (n : ℝ)) : ℝ) : ℂ) * Complex.I)

def literalRegular (z : Fin n → ℂ) : Prop :=
  ∃ rotation : ℂ, ‖rotation‖ = 1 ∧ ∃ permutation : Equiv.Perm (Fin n),
    ∀ i, z i = rotation * regularCoordinates n (permutation i)

lemma literalMaximum_eq (z : Fin n → ℂ) :
    literalMaximum z = UnitCircleInterpolation.complexAmplification z := by
  rw [UnitCircleInterpolation.complexAmplification_eq_sSup_image]
  rfl

lemma literalMinimizer_iff (z : Fin n → ℂ) :
    literalMinimizer z ↔ UnitCircleInterpolation.IsComplexMinimizer z := by
  simp only [literalMinimizer, UnitCircleInterpolation.IsComplexMinimizer, literalMaximum_eq]

lemma literalRegular_iff (z : Fin n → ℂ) :
    literalRegular z ↔ UnitCircleInterpolation.IsComplexRegularRotation z := by
  simp only [literalRegular, regularCoordinates,
    UnitCircleInterpolation.IsComplexRegularRotation, Circle.coe_exp]

/-- All positive sizes, arbitrary distinct complex unit nodes, and both classification directions. -/
theorem original_classification (n : ℕ) (hn : 0 < n) (z : Fin n → ℂ)
    (hunit : ∀ i, ‖z i‖ = 1) (hinj : Function.Injective z) :
    literalMinimizer z ↔ literalRegular z := by
  rw [literalMinimizer_iff, literalRegular_iff]
  exact UnitCircleInterpolation.complex_minimizer_iff_regular n hn z hunit hinj

/-- The original literal lower bound against the regular complex exponentials. -/
theorem original_lower_bound (n : ℕ) (hn : 0 < n) (z : Fin n → ℂ)
    (hunit : ∀ i, ‖z i‖ = 1) (hinj : Function.Injective z) :
    literalMaximum (regularCoordinates n) ≤ literalMaximum z := by
  have hcoord : (UnitCircleInterpolation.regularNodes n hn).coordinates = regularCoordinates n := by
    funext i
    exact Circle.coe_exp _
  rw [literalMaximum_eq, literalMaximum_eq, ← hcoord]
  exact UnitCircleInterpolation.complexAmplification_regular_le n hn z hunit hinj

#check original_classification
#check original_lower_bound
#print axioms literalMaximum_eq
#print axioms literalMinimizer_iff
#print axioms literalRegular_iff
#print axioms original_classification
#print axioms original_lower_bound

end

end OriginalUnitCircleStatement
