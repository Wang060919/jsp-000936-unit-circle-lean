/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.HomogeneousTrig
import UnitCircleInterpolation.CayleyCircleChart
import Mathlib.Algebra.Polynomial.Div

/-!
# Global division-free removal of one sine root

A root of a homogeneous trigonometric polynomial removes one sine factor and
lowers the homogeneous degree. The tangent-chart pole is included explicitly,
and no simplicity or nonzero-polynomial hypothesis is required.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace UnitCircleInterpolation

noncomputable section

open Polynomial

/-- Multiplication of homogeneous pullbacks holds at every real angle. -/
lemma homogeneousTrig_mul (m n : ℕ) (P Q : ℝ[X])
    (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n) (t : ℝ) :
    homogeneousTrig (m + n) (P * Q) t =
      homogeneousTrig m P t * homogeneousTrig n Q t := by
  have heq : homogeneousTrig (m + n) (P * Q) =
      fun u => homogeneousTrig m P u * homogeneousTrig n Q u := by
    apply Continuous.ext_on dense_cos_half_ne_zero
      (continuous_homogeneousTrig _ _)
      ((continuous_homogeneousTrig _ _).mul (continuous_homogeneousTrig _ _))
    intro u hu
    change homogeneousTrig (m + n) (P * Q) u =
      homogeneousTrig m P u * homogeneousTrig n Q u
    rw [homogeneousTrig_eq_cos_pow_eval_tan _ _
        (Polynomial.natDegree_mul_le_of_le hP hQ) u hu,
      homogeneousTrig_eq_cos_pow_eval_tan _ _ hP u hu,
      homogeneousTrig_eq_cos_pow_eval_tan _ _ hQ u hu,
      Polynomial.eval_mul, pow_add]
    ring
  exact congrFun heq t

/-- Raising the homogeneous degree multiplies the pullback by a half-angle cosine. -/
lemma homogeneousTrig_succ (p : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ p) (t : ℝ) :
    homogeneousTrig (p + 1) P t = Real.cos (t / 2) * homogeneousTrig p P t := by
  have heq : homogeneousTrig (p + 1) P =
      fun u => Real.cos (u / 2) * homogeneousTrig p P u := by
    apply Continuous.ext_on dense_cos_half_ne_zero
      (continuous_homogeneousTrig _ _)
      ((Real.continuous_cos.comp (continuous_id.div_const 2)).mul
        (continuous_homogeneousTrig _ _))
    intro u hu
    change homogeneousTrig (p + 1) P u = Real.cos (u / 2) * homogeneousTrig p P u
    rw [homogeneousTrig_eq_cos_pow_eval_tan _ _ (by omega) u hu,
      homogeneousTrig_eq_cos_pow_eval_tan _ _ hP u hu, pow_succ]
    ring
  exact congrFun heq t

/-- Negating polynomial coefficients negates the global homogeneous pullback. -/
@[simp]
lemma homogeneousTrig_neg (p : ℕ) (P : ℝ[X]) (t : ℝ) :
    homogeneousTrig p (-P) t = -homogeneousTrig p P t := by
  simp only [homogeneousTrig, Polynomial.coeff_neg, neg_mul, Finset.sum_neg_distrib]

/-- The homogeneous linear sine factor is the literal half-angle sine everywhere. -/
lemma homogeneousTrig_sineFactor (r t : ℝ) :
    homogeneousTrig 1 (sineFactor (r / 2)) t = Real.sin ((t - r) / 2) := by
  simp only [homogeneousTrig, Finset.sum_range_succ, Finset.sum_range_zero,
    sineFactor, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X,
    Polynomial.coeff_C, pow_zero, pow_one]
  rw [show (t - r) / 2 = t / 2 - r / 2 by ring, Real.sin_sub]
  norm_num
  ring

/-- A zero top coefficient lowers a positive degree bound, including the zero polynomial. -/
lemma natDegree_le_pred_of_coeff_top_eq_zero (p : ℕ) (P : ℝ[X]) (hp : 0 < p)
    (hP : P.natDegree ≤ p) (htop : P.coeff p = 0) : P.natDegree ≤ p - 1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  by_cases hkp : k = p
  · simpa [hkp] using htop
  · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mp hP k (by omega)

private lemma sineFactor_eq_C_mul_X_sub_C_tan (a : ℝ) (ha : Real.cos a ≠ 0) :
    sineFactor a = C (Real.cos a) * (X - C (Real.tan a)) := by
  rw [sineFactor, mul_sub, ← C_mul, mul_comm (Real.cos a), Real.tan_mul_cos ha]

/-- A finite-chart root admits a literal polynomial sine-factor quotient. -/
lemma exists_sineFactor_quotient_of_eval_tan_eq_zero (p : ℕ) (P : ℝ[X])
    (hp : 0 < p) (hP : P.natDegree ≤ p) (a : ℝ) (ha : Real.cos a ≠ 0)
    (hroot : P.eval (Real.tan a) = 0) :
    ∃ Q : ℝ[X], Q.natDegree ≤ p - 1 ∧ P = sineFactor a * Q := by
  obtain ⟨R, hR⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
  have hdegR : R.natDegree ≤ p - 1 := by
    by_cases hRzero : R = 0
    · simp [hRzero]
    · rw [hR, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hRzero,
        Polynomial.natDegree_X_sub_C] at hP
      omega
  refine ⟨C (Real.cos a)⁻¹ * R,
    (Polynomial.natDegree_C_mul_le _ _).trans hdegR, ?_⟩
  rw [sineFactor_eq_C_mul_X_sub_C_tan a ha]
  calc
    P = (X - C (Real.tan a)) * R := hR
    _ = (C (Real.cos a) * C (Real.cos a)⁻¹) *
        ((X - C (Real.tan a)) * R) := by
      rw [← C_mul, mul_inv_cancel₀ ha, C_1, one_mul]
    _ = C (Real.cos a) * (X - C (Real.tan a)) *
        (C (Real.cos a)⁻¹ * R) := by ring

/-- Every canonical circle root removes one global sine factor and one degree. -/
lemma exists_homogeneousTrig_sine_quotient (p : ℕ) (P : ℝ[X])
    (hp : 0 < p) (hP : P.natDegree ≤ p) (r : ℝ)
    (hr : r ∈ Set.Ico 0 (2 * Real.pi)) (hroot : homogeneousTrig p P r = 0) :
    ∃ Q : ℝ[X], Q.natDegree ≤ p - 1 ∧
      ∀ t : ℝ, homogeneousTrig p P t =
        Real.sin ((t - r) / 2) * homogeneousTrig (p - 1) Q t := by
  by_cases hcos : Real.cos (r / 2) = 0
  · have hrpi : r = Real.pi := (cos_half_eq_zero_iff_of_mem_Ico r hr).mp hcos
    subst r
    have htop : P.coeff p = 0 := by simpa only [homogeneousTrig_pi] using hroot
    have hdeg := natDegree_le_pred_of_coeff_top_eq_zero p P hp hP htop
    refine ⟨-P, by simpa only [Polynomial.natDegree_neg] using hdeg, ?_⟩
    intro t
    have hraise := homogeneousTrig_succ (p - 1) P hdeg t
    rw [Nat.sub_add_cancel hp] at hraise
    rw [homogeneousTrig_neg, hraise]
    rw [show (t - Real.pi) / 2 = t / 2 - Real.pi / 2 by ring,
      Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  · have hcos' : Real.cos (r / 2) ≠ 0 := hcos
    have heval : P.eval (Real.tan (r / 2)) = 0 := by
      rw [homogeneousTrig_eq_cos_pow_eval_tan p P hP r hcos'] at hroot
      exact (mul_eq_zero.mp hroot).resolve_left (pow_ne_zero _ hcos')
    obtain ⟨Q, hQ, hPQ⟩ :=
      exists_sineFactor_quotient_of_eval_tan_eq_zero p P hp hP (r / 2) hcos' heval
    refine ⟨Q, hQ, ?_⟩
    intro t
    calc
      homogeneousTrig p P t =
          homogeneousTrig (1 + (p - 1)) (sineFactor (r / 2) * Q) t := by
        rw [show 1 + (p - 1) = p by omega, hPQ]
      _ = Real.sin ((t - r) / 2) * homogeneousTrig (p - 1) Q t := by
        rw [homogeneousTrig_mul 1 (p - 1) _ _ (sineFactor_natDegree_le _) hQ t,
          homogeneousTrig_sineFactor]

/-- A second global derivative is still represented by the twice-applied Cayley operator. -/
lemma hasDerivAt_deriv_homogeneousTrig (p : ℕ) (P : ℝ[X])
    (hP : P.natDegree ≤ p) (t : ℝ) :
    HasDerivAt (deriv (homogeneousTrig p P))
      (homogeneousTrig p (cayleyOperator p (cayleyOperator p P)) t / 4) t := by
  have heq : deriv (homogeneousTrig p P) =
      fun u => homogeneousTrig p (cayleyOperator p P) u / 2 :=
    funext (deriv_homogeneousTrig p P hP)
  rw [heq]
  apply ((hasDerivAt_homogeneousTrig p (cayleyOperator p P)
    (cayleyOperator_natDegree_le p P hP) t).div_const 2).congr_deriv
  ring

private lemma hasDerivAt_sine_half_sub (r t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.sin ((u - r) / 2))
      (Real.cos ((t - r) / 2) / 2) t := by
  have hhalf : HasDerivAt (fun u : ℝ => (u - r) / 2) (1 / 2) t := by
    simpa only [id_eq] using ((hasDerivAt_id t).sub_const r).div_const 2
  exact hhalf.sin.congr_deriv (by ring)

private lemma hasDerivAt_cosine_half_sub_div_two (r t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.cos ((u - r) / 2) / 2)
      (-Real.sin ((t - r) / 2) / 4) t := by
  have hhalf : HasDerivAt (fun u : ℝ => (u - r) / 2) (1 / 2) t := by
    simpa only [id_eq] using ((hasDerivAt_id t).sub_const r).div_const 2
  exact (hhalf.cos.div_const 2).congr_deriv (by ring)

/-- The continuous sine quotient has the removable-root value `2 F′(r)`. -/
lemma homogeneousTrig_sine_quotient_value_at_root (p : ℕ) (P Q : ℝ[X])
    (hQ : Q.natDegree ≤ p - 1) (r : ℝ)
    (hfactor : ∀ t : ℝ, homogeneousTrig p P t =
      Real.sin ((t - r) / 2) * homogeneousTrig (p - 1) Q t) :
    homogeneousTrig (p - 1) Q r = 2 * deriv (homogeneousTrig p P) r := by
  have hprod := (hasDerivAt_sine_half_sub r r).mul
    (hasDerivAt_homogeneousTrig (p - 1) Q hQ r)
  have heq : homogeneousTrig p P = fun t : ℝ =>
      Real.sin ((t - r) / 2) * homogeneousTrig (p - 1) Q t := funext hfactor
  change HasDerivAt (fun t : ℝ => Real.sin ((t - r) / 2) *
    homogeneousTrig (p - 1) Q t) _ r at hprod
  rw [← heq] at hprod
  have hd := hprod.deriv
  simp only [sub_self, zero_div, Real.cos_zero, Real.sin_zero, zero_mul, add_zero] at hd
  linarith

/-- The derivative of the continuous sine quotient at its removed root is `F″(r)`. -/
lemma deriv_homogeneousTrig_sine_quotient_at_root (p : ℕ) (P Q : ℝ[X])
    (hQ : Q.natDegree ≤ p - 1) (r : ℝ)
    (hfactor : ∀ t : ℝ, homogeneousTrig p P t =
      Real.sin ((t - r) / 2) * homogeneousTrig (p - 1) Q t) :
    deriv (homogeneousTrig (p - 1) Q) r = deriv (deriv (homogeneousTrig p P)) r := by
  have heq : homogeneousTrig p P = fun t : ℝ =>
      Real.sin ((t - r) / 2) * homogeneousTrig (p - 1) Q t := funext hfactor
  have hderiv : deriv (homogeneousTrig p P) = fun t : ℝ =>
      Real.cos ((t - r) / 2) / 2 * homogeneousTrig (p - 1) Q t +
      Real.sin ((t - r) / 2) * deriv (homogeneousTrig (p - 1) Q) t := by
    funext t
    have hg := (hasDerivAt_homogeneousTrig (p - 1) Q hQ t).differentiableAt.hasDerivAt
    have hprod := (hasDerivAt_sine_half_sub r t).mul hg
    change HasDerivAt (fun u : ℝ => Real.sin ((u - r) / 2) *
      homogeneousTrig (p - 1) Q u) _ t at hprod
    rw [← heq] at hprod
    exact hprod.deriv
  have hg := (hasDerivAt_homogeneousTrig (p - 1) Q hQ r).differentiableAt.hasDerivAt
  have hgg := hasDerivAt_deriv_homogeneousTrig (p - 1) Q hQ r
  have hsum := ((hasDerivAt_cosine_half_sub_div_two r r).mul hg).add
    ((hasDerivAt_sine_half_sub r r).mul hgg)
  change HasDerivAt (fun t : ℝ =>
    Real.cos ((t - r) / 2) / 2 * homogeneousTrig (p - 1) Q t +
    Real.sin ((t - r) / 2) * deriv (homogeneousTrig (p - 1) Q) t) _ r at hsum
  rw [← hderiv] at hsum
  have hd := hsum.deriv
  simp only [sub_self, zero_div, Real.cos_zero, Real.sin_zero, neg_zero,
    zero_mul, zero_add, add_zero] at hd
  linarith

/-- One degree lower provides the sine quotient, its root value, and its root derivative. -/
lemma exists_homogeneousTrig_sine_quotient_with_root_data (p : ℕ) (P : ℝ[X])
    (hp : 0 < p) (hP : P.natDegree ≤ p) (r : ℝ)
    (hr : r ∈ Set.Ico 0 (2 * Real.pi)) (hroot : homogeneousTrig p P r = 0) :
    ∃ Q : ℝ[X], Q.natDegree ≤ p - 1 ∧
      (∀ t : ℝ, homogeneousTrig p P t =
        Real.sin ((t - r) / 2) * homogeneousTrig (p - 1) Q t) ∧
      homogeneousTrig (p - 1) Q r = 2 * deriv (homogeneousTrig p P) r ∧
      deriv (homogeneousTrig (p - 1) Q) r =
        deriv (deriv (homogeneousTrig p P)) r := by
  obtain ⟨Q, hQ, hfactor⟩ := exists_homogeneousTrig_sine_quotient p P hp hP r hr hroot
  exact ⟨Q, hQ, hfactor,
    homogeneousTrig_sine_quotient_value_at_root p P Q hQ r hfactor,
    deriv_homogeneousTrig_sine_quotient_at_root p P Q hQ r hfactor⟩

end

end UnitCircleInterpolation
