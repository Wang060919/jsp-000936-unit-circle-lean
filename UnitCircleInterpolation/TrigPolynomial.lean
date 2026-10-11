/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.CayleyPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace UnitCircleInterpolation

noncomputable section

open Polynomial

/-- A sine factor in the real Cayley coordinate, with no division by `cos a`. -/
def sineFactor (a : ℝ) : ℝ[X] :=
  C (Real.cos a) * X - C (Real.sin a)

@[simp]
theorem sineFactor_eval (a x : ℝ) :
    (sineFactor a).eval x = Real.cos a * x - Real.sin a := by
  simp [sineFactor]

theorem sineFactor_natDegree_le (a : ℝ) : (sineFactor a).natDegree ≤ 1 := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · simpa only [pow_one] using
      (Polynomial.natDegree_C_mul_X_pow_le (Real.cos a) 1)
  · simp

theorem cos_mul_sineFactor_eval_tan (a t : ℝ) (ht : Real.cos t ≠ 0) :
    Real.cos t * (sineFactor a).eval (Real.tan t) = Real.sin (t - a) := by
  rw [sineFactor_eval, Real.sin_sub, ← Real.tan_mul_cos ht]
  ring

/-- The literal polynomial product associated with a finite family of sine factors. -/
def sineProductPolynomial {ι : Type*} (s : Finset ι) (a : ι → ℝ) : ℝ[X] :=
  ∏ i ∈ s, sineFactor (a i)

theorem sineProductPolynomial_natDegree_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (sineProductPolynomial s a).natDegree ≤ s.card := by
  unfold sineProductPolynomial
  calc
    (∏ i ∈ s, sineFactor (a i)).natDegree ≤
        ∑ i ∈ s, (sineFactor (a i)).natDegree := Polynomial.natDegree_prod_le s _
    _ ≤ ∑ _i ∈ s, 1 := Finset.sum_le_sum fun i _hi => sineFactor_natDegree_le (a i)
    _ = s.card := by simp

theorem cos_pow_mul_sineProductPolynomial_eval_tan {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (t : ℝ) (ht : Real.cos t ≠ 0) :
    Real.cos t ^ s.card * (sineProductPolynomial s a).eval (Real.tan t) =
      ∏ i ∈ s, Real.sin (t - a i) := by
  simp only [sineProductPolynomial, Polynomial.eval_prod]
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _hi
  exact cos_mul_sineFactor_eval_tan (a i) t ht

/-- A weighted polynomial pulled back along the tangent coordinate. -/
def cosineWeighted (p : ℕ) (P : ℝ[X]) (t : ℝ) : ℝ :=
  Real.cos t ^ p * P.eval (Real.tan t)

private theorem hasDerivAt_tan_normalized {t : ℝ} (ht : Real.cos t ≠ 0) :
    HasDerivAt Real.tan (1 + Real.tan t ^ 2) t := by
  apply (Real.hasDerivAt_tan ht).congr_deriv
  rw [one_div, ← Real.inv_one_add_tan_sq ht, inv_inv]

private theorem hasDerivAt_cos_pow (p : ℕ) {t : ℝ} (ht : Real.cos t ≠ 0) :
    HasDerivAt (fun u : ℝ => Real.cos u ^ p)
      (-(p : ℝ) * Real.tan t * Real.cos t ^ p) t := by
  apply ((Real.hasDerivAt_cos t).pow p).congr_deriv
  cases p with
  | zero => simp
  | succ n =>
      simp only [Nat.add_sub_cancel, pow_succ,
        Nat.cast_add, Nat.cast_one]
      rw [← Real.tan_mul_cos ht]
      ring

/-- Differentiation is represented by the same degree-bounded Cayley operator for every `p`. -/
theorem hasDerivAt_cosineWeighted (p : ℕ) (P : ℝ[X]) (t : ℝ)
    (ht : Real.cos t ≠ 0) :
    HasDerivAt (cosineWeighted p P)
      (Real.cos t ^ p * (cayleyOperator p P).eval (Real.tan t)) t := by
  have hpoly := (P.hasDerivAt (Real.tan t)).comp t (hasDerivAt_tan_normalized ht)
  have hprod := (hasDerivAt_cos_pow p ht).mul hpoly
  have hrate :
      (-(p : ℝ) * Real.tan t * Real.cos t ^ p) * P.eval (Real.tan t) +
          Real.cos t ^ p * (P.derivative.eval (Real.tan t) * (1 + Real.tan t ^ 2)) =
        Real.cos t ^ p * (cayleyOperator p P).eval (Real.tan t) := by
    rw [cayleyOperator_eval]
    ring
  unfold cosineWeighted
  convert! hprod.congr_deriv hrate using 1

end

end UnitCircleInterpolation
