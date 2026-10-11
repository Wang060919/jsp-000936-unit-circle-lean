/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.PhaseBridge
import UnitCircleInterpolation.TrigPolynomial

/-! # Degree-bounded Cayley polynomials for the actual sine cardinals -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open Polynomial

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ}

def cardinalPolynomial (θ : Fin n → ℝ) (j : Fin n) : ℝ[X] :=
  C ((∏ k ∈ Finset.univ.erase j, Real.sin ((θ j - θ k) / 2))⁻¹) *
    sineProductPolynomial (Finset.univ.erase j) (fun k => θ k / 2)

lemma cardinalPolynomial_natDegree_le (θ : Fin n → ℝ) (j : Fin n) :
    (cardinalPolynomial θ j).natDegree ≤ n - 1 := by
  have hcard : (Finset.univ.erase j).card = n - 1 := by simp
  unfold cardinalPolynomial
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    ((sineProductPolynomial_natDegree_le _ _).trans_eq hcard)

/-- The entire literal cardinal is represented on every tangent chart where it is defined. -/
lemma cos_pow_mul_cardinalPolynomial_eval_tan (θ : Fin n → ℝ) (j : Fin n)
    (t : ℝ) (ht : Real.cos (t / 2) ≠ 0) :
    Real.cos (t / 2) ^ (n - 1) * (cardinalPolynomial θ j).eval (Real.tan (t / 2)) =
      sineCardinal θ j t := by
  have hcard : (Finset.univ.erase j).card = n - 1 := by simp
  have hprod := cos_pow_mul_sineProductPolynomial_eval_tan
    (Finset.univ.erase j) (fun k => θ k / 2) (t / 2) ht
  rw [hcard] at hprod
  unfold cardinalPolynomial
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  calc
    Real.cos (t / 2) ^ (n - 1) *
        ((∏ k ∈ Finset.univ.erase j, Real.sin ((θ j - θ k) / 2))⁻¹ *
          (sineProductPolynomial (Finset.univ.erase j) (fun k => θ k / 2)).eval
            (Real.tan (t / 2))) =
      (Real.cos (t / 2) ^ (n - 1) *
        (sineProductPolynomial (Finset.univ.erase j) (fun k => θ k / 2)).eval
          (Real.tan (t / 2))) *
        (∏ k ∈ Finset.univ.erase j, Real.sin ((θ j - θ k) / 2))⁻¹ := by ring
    _ = (∏ k ∈ Finset.univ.erase j, Real.sin (t / 2 - θ k / 2)) *
        (∏ k ∈ Finset.univ.erase j, Real.sin ((θ j - θ k) / 2))⁻¹ := by rw [hprod]
    _ = sineCardinal θ j t := by
      unfold sineCardinal
      rw [Finset.prod_div_distrib, div_eq_mul_inv]
      congr 1
      apply Finset.prod_congr rfl
      intro k hk
      congr 1
      ring

/-- The signed trigonometric interpolant, with arbitrary real nodal values. -/
def sineInterpolant (θ : Fin n → ℝ) (c : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ j, c j * sineCardinal θ j t

def interpolantPolynomial (θ : Fin n → ℝ) (c : Fin n → ℝ) : ℝ[X] :=
  ∑ j, C (c j) * cardinalPolynomial θ j

lemma interpolantPolynomial_natDegree_le (θ : Fin n → ℝ) (c : Fin n → ℝ) :
    (interpolantPolynomial θ c).natDegree ≤ n - 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact (Polynomial.natDegree_C_mul_le _ _).trans (cardinalPolynomial_natDegree_le θ j)

lemma cos_pow_mul_interpolantPolynomial_eval_tan (θ : Fin n → ℝ) (c : Fin n → ℝ)
    (t : ℝ) (ht : Real.cos (t / 2) ≠ 0) :
    Real.cos (t / 2) ^ (n - 1) *
        (interpolantPolynomial θ c).eval (Real.tan (t / 2)) = sineInterpolant θ c t := by
  unfold interpolantPolynomial sineInterpolant
  rw [Polynomial.eval_finsetSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Polynomial.eval_mul, Polynomial.eval_C, mul_left_comm,
    cos_pow_mul_cardinalPolynomial_eval_tan θ j t ht]

lemma sineInterpolant_at_node (θ : Fin n → ℝ) (hθ : Function.Injective (phaseNodes θ))
    (c : Fin n → ℝ) (i : Fin n) : sineInterpolant θ c (θ i) = c i := by
  unfold sineInterpolant
  rw [Finset.sum_eq_single i]
  · rw [sineCardinal_self θ hθ, mul_one]
  · intro j hj hji
    rw [sineCardinal_other θ (Ne.symm hji), mul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

lemma hasDerivAt_sineInterpolant_on_chart (θ : Fin n → ℝ) (c : Fin n → ℝ)
    (t : ℝ) (ht : Real.cos (t / 2) ≠ 0) :
    HasDerivAt (sineInterpolant θ c)
      ((Real.cos (t / 2) ^ (n - 1) *
        (cayleyOperator (n - 1) (interpolantPolynomial θ c)).eval (Real.tan (t / 2))) / 2)
      t := by
  have hhalf : HasDerivAt (fun u : ℝ => u / 2) (1 / 2) t :=
    (hasDerivAt_id t).div_const 2
  have hweighted :=
    (hasDerivAt_cosineWeighted (n - 1) (interpolantPolynomial θ c) (t / 2) ht).comp t hhalf
  have hevent : ∀ᶠ u in nhds t, Real.cos (u / 2) ≠ 0 :=
    (Real.continuous_cos.comp (continuous_id.div_const 2)).continuousAt.eventually_ne ht
  have heq : sineInterpolant θ c =ᶠ[nhds t]
      (fun u : ℝ => cosineWeighted (n - 1) (interpolantPolynomial θ c) (u / 2)) := by
    filter_upwards [hevent] with u hu
    exact (cos_pow_mul_interpolantPolynomial_eval_tan θ c u hu).symm
  have hr := hweighted.congr_of_eventuallyEq heq
  simpa only [Function.comp_def, mul_one_div] using hr

lemma derivativePolynomial_natDegree_le (θ : Fin n → ℝ) (c : Fin n → ℝ) :
    (cayleyOperator (n - 1) (interpolantPolynomial θ c)).natDegree ≤ n - 1 :=
  cayleyOperator_natDegree_le _ _ (interpolantPolynomial_natDegree_le θ c)

lemma sineFactor_coeff_one (a : ℝ) : (sineFactor a).coeff 1 = Real.cos a := by
  simp [sineFactor]

lemma sineProductPolynomial_coeff_card {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (sineProductPolynomial s a).coeff s.card = ∏ i ∈ s, Real.cos (a i) := by
  simpa only [sineProductPolynomial, Nat.mul_one, sineFactor_coeff_one] using
    (Polynomial.coeff_prod_of_natDegree_le s (fun i => sineFactor (a i)) 1
      (fun i _ => sineFactor_natDegree_le (a i)))

/-- The chart's missing circle point is encoded by the top polynomial coefficient. -/
lemma cardinalPolynomial_coeff_top (θ : Fin n → ℝ) (j : Fin n) :
    (cardinalPolynomial θ j).coeff (n - 1) = sineCardinal θ j Real.pi := by
  have hcard : (Finset.univ.erase j).card = n - 1 := by simp
  have hcos : (sineProductPolynomial (Finset.univ.erase j) (fun k => θ k / 2)).coeff
      (n - 1) = ∏ k ∈ Finset.univ.erase j, Real.cos (θ k / 2) := by
    rw [← hcard]
    exact sineProductPolynomial_coeff_card _ _
  unfold cardinalPolynomial sineCardinal
  rw [Polynomial.coeff_C_mul, hcos, Finset.prod_div_distrib]
  have hsin (k : Fin n) : Real.sin ((Real.pi - θ k) / 2) = Real.cos (θ k / 2) := by
    rw [show (Real.pi - θ k) / 2 = Real.pi / 2 - θ k / 2 from by ring,
      Real.sin_pi_div_two_sub]
  simp_rw [hsin]
  rw [div_eq_mul_inv, mul_comm]

lemma interpolantPolynomial_coeff_top (θ : Fin n → ℝ) (c : Fin n → ℝ) :
    (interpolantPolynomial θ c).coeff (n - 1) = sineInterpolant θ c Real.pi := by
  simp only [interpolantPolynomial, sineInterpolant, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, cardinalPolynomial_coeff_top]

/-- A zero at the missing circle point decreases the available polynomial degree. -/
lemma interpolantPolynomial_degree_drop_at_pi (θ : Fin n → ℝ) (c : Fin n → ℝ)
    (hpole : sineInterpolant θ c Real.pi = 0) :
    (interpolantPolynomial θ c).natDegree ≤ n - 2 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  by_cases hkp : k = n - 1
  · rw [hkp, interpolantPolynomial_coeff_top, hpole]
  · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mp
      (interpolantPolynomial_natDegree_le θ c) k (by omega)

lemma interpolantPolynomial_ne_zero_of_value_on_chart (θ : Fin n → ℝ) (c : Fin n → ℝ)
    (t : ℝ) (ht : Real.cos (t / 2) ≠ 0) (hvalue : sineInterpolant θ c t ≠ 0) :
    interpolantPolynomial θ c ≠ 0 := by
  intro hzero
  have h := cos_pow_mul_interpolantPolynomial_eval_tan θ c t ht
  rw [hzero, Polynomial.eval_zero, mul_zero] at h
  exact hvalue h.symm

lemma interpolantPolynomial_ne_zero_of_value_at_pi (θ : Fin n → ℝ) (c : Fin n → ℝ)
    (hvalue : sineInterpolant θ c Real.pi ≠ 0) : interpolantPolynomial θ c ≠ 0 := by
  intro hzero
  have h := interpolantPolynomial_coeff_top θ c
  rw [hzero, Polynomial.coeff_zero] at h
  exact hvalue h.symm

lemma interpolantPolynomial_ne_zero_of_node_on_chart (θ : Fin n → ℝ)
    (hθ : Function.Injective (phaseNodes θ)) (c : Fin n → ℝ) (i : Fin n)
    (ht : Real.cos (θ i / 2) ≠ 0) (hci : c i ≠ 0) : interpolantPolynomial θ c ≠ 0 := by
  apply interpolantPolynomial_ne_zero_of_value_on_chart θ c (θ i) ht
  rwa [sineInterpolant_at_node θ hθ]

lemma interpolantPolynomial_natDegree_lt_of_zero_at_pi (θ : Fin n → ℝ) (c : Fin n → ℝ)
    (hP : interpolantPolynomial θ c ≠ 0) (hpole : sineInterpolant θ c Real.pi = 0) :
    (interpolantPolynomial θ c).natDegree < n - 1 := by
  by_contra hlt
  have heq : (interpolantPolynomial θ c).natDegree = n - 1 :=
    le_antisymm (interpolantPolynomial_natDegree_le θ c) (not_lt.mp hlt)
  have hcoeff : (interpolantPolynomial θ c).coeff
      (interpolantPolynomial θ c).natDegree ≠ 0 := by
    simpa only [Polynomial.coeff_natDegree] using Polynomial.leadingCoeff_ne_zero.mpr hP
  rw [heq, interpolantPolynomial_coeff_top, hpole] at hcoeff
  exact hcoeff rfl

end

end UnitCircleInterpolation
