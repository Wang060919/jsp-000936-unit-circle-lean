/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.CayleyCardinal
import UnitCircleInterpolation.SineDerivative

/-! # Global calculus and full-turn signs of the actual sine interpolants -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ}

def sineInterpolantDerivative (θ : Fin n → ℝ) (c : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ j, c j * sineCardinalDerivative θ j t

lemma hasDerivAt_sineInterpolant (θ : Fin n → ℝ) (c : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (sineInterpolant θ c) (sineInterpolantDerivative θ c t) t := by
  unfold sineInterpolant sineInterpolantDerivative
  convert! HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) =>
    (hasDerivAt_sineCardinal θ j t).const_mul (c j)) using 1

lemma differentiable_sineInterpolant (θ : Fin n → ℝ) (c : Fin n → ℝ) :
    Differentiable ℝ (sineInterpolant θ c) :=
  fun t => (hasDerivAt_sineInterpolant θ c t).differentiableAt

lemma deriv_sineInterpolant (θ : Fin n → ℝ) (c : Fin n → ℝ) (t : ℝ) :
    deriv (sineInterpolant θ c) t = sineInterpolantDerivative θ c t :=
  (hasDerivAt_sineInterpolant θ c t).deriv

lemma continuous_sineInterpolant (θ : Fin n → ℝ) (c : Fin n → ℝ) :
    Continuous (sineInterpolant θ c) :=
  (differentiable_sineInterpolant θ c).continuous

lemma continuous_sineCardinalDerivative (θ : Fin n → ℝ) (j : Fin n) :
    Continuous (sineCardinalDerivative θ j) := by
  unfold sineCardinalDerivative
  apply continuous_finsetSum
  intro k hk
  apply Continuous.mul
  · apply continuous_finsetProd
    intro l hl
    exact (Real.continuous_sin.comp
      ((continuous_id.sub continuous_const).div_const 2)).div_const _
  · exact ((Real.continuous_cos.comp
      ((continuous_id.sub continuous_const).div_const 2)).div_const 2).div_const _

lemma continuous_sineInterpolantDerivative (θ : Fin n → ℝ) (c : Fin n → ℝ) :
    Continuous (sineInterpolantDerivative θ c) := by
  apply continuous_finsetSum
  intro j hj
  exact continuous_const.mul (continuous_sineCardinalDerivative θ j)

lemma sineInterpolant_add_two_pi (θ : Fin n → ℝ) (c : Fin n → ℝ) (t : ℝ) :
    sineInterpolant θ c (t + 2 * Real.pi) =
      (-1 : ℝ) ^ (n - 1) * sineInterpolant θ c t := by
  unfold sineInterpolant
  simp_rw [sineCardinal_add_two_pi]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma sineInterpolantDerivative_add_two_pi (θ : Fin n → ℝ) (c : Fin n → ℝ) (t : ℝ) :
    sineInterpolantDerivative θ c (t + 2 * Real.pi) =
      (-1 : ℝ) ^ (n - 1) * sineInterpolantDerivative θ c t := by
  have hl := (hasDerivAt_sineInterpolant θ c (t + 2 * Real.pi)).comp t
    ((hasDerivAt_id t).add_const (2 * Real.pi))
  have hr := (hasDerivAt_sineInterpolant θ c t).const_mul ((-1 : ℝ) ^ (n - 1))
  have heq : (fun u => sineInterpolant θ c (u + 2 * Real.pi)) =
      (fun u => (-1 : ℝ) ^ (n - 1) * sineInterpolant θ c u) :=
    funext (sineInterpolant_add_two_pi θ c)
  simp only [Function.comp_def, id_eq, mul_one] at hl
  rw [heq] at hl
  exact hl.unique hr

lemma sineInterpolant_add_two_pi_eq_zero_iff (θ : Fin n → ℝ) (c : Fin n → ℝ) (t : ℝ) :
    sineInterpolant θ c (t + 2 * Real.pi) = 0 ↔ sineInterpolant θ c t = 0 := by
  rw [sineInterpolant_add_two_pi, mul_eq_zero]
  simp only [pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0), false_or]

lemma sineInterpolantDerivative_add_two_pi_eq_zero_iff
    (θ : Fin n → ℝ) (c : Fin n → ℝ) (t : ℝ) :
    sineInterpolantDerivative θ c (t + 2 * Real.pi) = 0 ↔
      sineInterpolantDerivative θ c t = 0 := by
  rw [sineInterpolantDerivative_add_two_pi, mul_eq_zero]
  simp only [pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0), false_or]

end

end UnitCircleInterpolation
