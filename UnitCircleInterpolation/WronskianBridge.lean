/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.CayleyCardinal
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Wronskians on the Cayley coordinate chart

The same Cayley differentiation operator acts on every polynomial representing
a sine interpolant of a fixed node family. Its common zeroth-order term cancels
in the Wronskian, leaving the positive factor `1 + x ^ 2`.

The trigonometric bridge below applies only where `cos (t / 2) ≠ 0`. It supplies
an exact identity and transfers the sign of an already known polynomial
Wronskian. It does not construct positive Markov residues or cover chart poles.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

open Polynomial

/-- The evaluation of the ordinary polynomial Wronskian, in a fixed orientation. -/
def polynomialWronskian (P Q : ℝ[X]) (x : ℝ) : ℝ :=
  P.eval x * Q.derivative.eval x - P.derivative.eval x * Q.eval x

/-- The common weighted differentiation term cancels for two polynomials. -/
lemma cayleyOperator_wronskian (p : ℕ) (P Q : ℝ[X]) (x : ℝ) :
    P.eval x * (cayleyOperator p Q).eval x -
        (cayleyOperator p P).eval x * Q.eval x =
      (1 + x ^ 2) * polynomialWronskian P Q x := by
  rw [cayleyOperator_eval, cayleyOperator_eval, polynomialWronskian]
  ring

variable {n : ℕ}

/-- The Wronskian of the actual signed sine interpolants, using their derivatives. -/
def sineWronskian (θ a b : Fin n → ℝ) (t : ℝ) : ℝ :=
  sineInterpolant θ a t * deriv (sineInterpolant θ b) t -
    deriv (sineInterpolant θ a) t * sineInterpolant θ b t

/-- Exact Wronskian identity on a tangent chart; the chart-pole hypothesis is explicit. -/
lemma sineWronskian_eq_polynomialWronskian_on_chart
    (θ a b : Fin n → ℝ) (t : ℝ) (ht : Real.cos (t / 2) ≠ 0) :
    sineWronskian θ a b t =
      (Real.cos (t / 2) ^ (n - 1)) ^ 2 *
        (1 + Real.tan (t / 2) ^ 2) / 2 *
          polynomialWronskian (interpolantPolynomial θ a)
            (interpolantPolynomial θ b) (Real.tan (t / 2)) := by
  unfold sineWronskian
  rw [(hasDerivAt_sineInterpolant_on_chart θ a t ht).deriv,
    (hasDerivAt_sineInterpolant_on_chart θ b t ht).deriv,
    ← cos_pow_mul_interpolantPolynomial_eval_tan θ a t ht,
    ← cos_pow_mul_interpolantPolynomial_eval_tan θ b t ht,
    cayleyOperator_eval, cayleyOperator_eval, polynomialWronskian]
  ring

/-- The chart factor is strictly positive, including when the degree bound is zero. -/
lemma sineWronskian_chart_factor_pos (n : ℕ) (t : ℝ)
    (ht : Real.cos (t / 2) ≠ 0) :
    0 < (Real.cos (t / 2) ^ (n - 1)) ^ 2 *
      (1 + Real.tan (t / 2) ^ 2) / 2 := by
  have hcos : 0 < (Real.cos (t / 2) ^ (n - 1)) ^ 2 :=
    sq_pos_of_ne_zero (pow_ne_zero _ ht)
  have htan : 0 < 1 + Real.tan (t / 2) ^ 2 :=
    add_pos_of_pos_of_nonneg (by norm_num) (sq_nonneg _)
  exact div_pos (mul_pos hcos htan) (by norm_num)

/-- The negative-Wronskian condition is equivalent on the stated coordinate chart. -/
lemma sineWronskian_neg_on_chart_iff
    (θ a b : Fin n → ℝ) (t : ℝ) (ht : Real.cos (t / 2) ≠ 0) :
    sineWronskian θ a b t < 0 ↔
      polynomialWronskian (interpolantPolynomial θ a)
        (interpolantPolynomial θ b) (Real.tan (t / 2)) < 0 := by
  rw [sineWronskian_eq_polynomialWronskian_on_chart θ a b t ht]
  have hiff :
      ((Real.cos (t / 2) ^ (n - 1)) ^ 2 *
        (1 + Real.tan (t / 2) ^ 2) / 2) *
          polynomialWronskian (interpolantPolynomial θ a)
            (interpolantPolynomial θ b) (Real.tan (t / 2)) <
      ((Real.cos (t / 2) ^ (n - 1)) ^ 2 *
        (1 + Real.tan (t / 2) ^ 2) / 2) * 0 ↔
      polynomialWronskian (interpolantPolynomial θ a)
        (interpolantPolynomial θ b) (Real.tan (t / 2)) < 0 :=
    mul_lt_mul_iff_right₀ (sineWronskian_chart_factor_pos n t ht)
  simpa only [mul_zero] using hiff

/-- A known polynomial Wronskian sign transfers to the literal sine interpolants on chart. -/
lemma sineWronskian_neg_of_polynomialWronskian_neg
    (θ a b : Fin n → ℝ) (t : ℝ) (ht : Real.cos (t / 2) ≠ 0)
    (hW : polynomialWronskian (interpolantPolynomial θ a)
      (interpolantPolynomial θ b) (Real.tan (t / 2)) < 0) :
    sineWronskian θ a b t < 0 :=
  (sineWronskian_neg_on_chart_iff θ a b t ht).mpr hW

end

end UnitCircleInterpolation
