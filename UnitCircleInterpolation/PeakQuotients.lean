/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.PeakSigns
import UnitCircleInterpolation.HomogeneousFactor
import UnitCircleInterpolation.HomogeneousLinear

/-!
# Actual continuous critical quotients in physical peak order

The derivative of each actual positive gap interpolant removes its own peak
sine factor. The quotient is a global homogeneous polynomial of degree `n-2`,
including at the removed root and at the tangent-chart pole.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

open Polynomial

variable {n : ℕ} {hn : 0 < n}

def orderedGapDerivativePolynomial (angles : CyclicAngles n hn) (i : Fin n) : ℝ[X] :=
  C (1 / 2) * cayleyOperator (n - 1)
    (interpolantPolynomial angles.angle (cyclicGapCoefficient (physicalGapCut hn i)))

lemma orderedGapDerivativePolynomial_natDegree_le (angles : CyclicAngles n hn)
    (i : Fin n) : (orderedGapDerivativePolynomial angles i).natDegree ≤ n - 1 := by
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    (derivativePolynomial_natDegree_le angles.angle
      (cyclicGapCoefficient (physicalGapCut hn i)))

lemma deriv_orderedGapInterpolant_homogeneousTrig (angles : CyclicAngles n hn)
    (i : Fin n) :
    deriv (orderedGapInterpolant angles i) =
      homogeneousTrig (n - 1) (orderedGapDerivativePolynomial angles i) := by
  funext t
  change deriv (sineInterpolant angles.angle
    (cyclicGapCoefficient (physicalGapCut hn i))) t = _
  rw [deriv_sineInterpolant_globalCayley, orderedGapDerivativePolynomial,
    homogeneousTrig_C_mul]
  ring

/-- The witness contains the removable-root value, rather than a `0/0` definition. -/
lemma exists_orderedPeakQuotientPolynomial (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (i : Fin n) :
    ∃ Q : ℝ[X], Q.natDegree ≤ n - 2 ∧
      (∀ t, deriv (orderedGapInterpolant angles i) t =
        Real.sin ((t - orderedPeak angles hsize i) / 2) *
          homogeneousTrig (n - 2) Q t) ∧
      homogeneousTrig (n - 2) Q (orderedPeak angles hsize i) =
        2 * deriv (deriv (orderedGapInterpolant angles i)) (orderedPeak angles hsize i) := by
  have hrepr := deriv_orderedGapInterpolant_homogeneousTrig angles i
  have hroot : homogeneousTrig (n - 1) (orderedGapDerivativePolynomial angles i)
      (orderedPeak angles hsize i) = 0 := by
    rw [← hrepr]
    exact (orderedPeak_hasDerivAt_zero angles hsize i).deriv
  have hb := orderedPeak_mem_Ioo angles hsize i
  obtain ⟨Q, hQ, hfactor, hvalue, _⟩ :=
    exists_homogeneousTrig_sine_quotient_with_root_data (n - 1)
      (orderedGapDerivativePolynomial angles i) (by omega)
      (orderedGapDerivativePolynomial_natDegree_le angles i)
      (orderedPeak angles hsize i) ⟨hb.1.le, hb.2⟩ hroot
  have he : n - 1 - 1 = n - 2 := by omega
  rw [he] at hQ hfactor hvalue
  refine ⟨Q, hQ, ?_, ?_⟩
  · intro t
    rw [hrepr]
    exact hfactor t
  · rw [hrepr]
    exact hvalue

def orderedPeakQuotientPolynomial (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (i : Fin n) : ℝ[X] :=
  (exists_orderedPeakQuotientPolynomial angles hsize i).choose

def orderedPeakQuotient (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (i : Fin n) : ℝ → ℝ :=
  homogeneousTrig (n - 2) (orderedPeakQuotientPolynomial angles hsize i)

lemma orderedPeakQuotientPolynomial_natDegree_le (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (i : Fin n) :
    (orderedPeakQuotientPolynomial angles hsize i).natDegree ≤ n - 2 :=
  (exists_orderedPeakQuotientPolynomial angles hsize i).choose_spec.1

lemma deriv_orderedGapInterpolant_sine_factor (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (i : Fin n) (t : ℝ) :
    deriv (orderedGapInterpolant angles i) t =
      Real.sin ((t - orderedPeak angles hsize i) / 2) *
        orderedPeakQuotient angles hsize i t :=
  (exists_orderedPeakQuotientPolynomial angles hsize i).choose_spec.2.1 t

lemma orderedPeakQuotient_value_at_peak (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (i : Fin n) :
    orderedPeakQuotient angles hsize i (orderedPeak angles hsize i) =
      2 * deriv (deriv (orderedGapInterpolant angles i)) (orderedPeak angles hsize i) :=
  (exists_orderedPeakQuotientPolynomial angles hsize i).choose_spec.2.2

lemma continuous_orderedPeakQuotient (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (i : Fin n) : Continuous (orderedPeakQuotient angles hsize i) :=
  continuous_homogeneousTrig _ _

lemma orderedPeakQuotient_mem_space (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (i : Fin n) :
    orderedPeakQuotient angles hsize i ∈ homogeneousTrigSpace (n - 2) :=
  homogeneousTrig_mem_space _ _ (orderedPeakQuotientPolynomial_natDegree_le angles hsize i)

lemma orderedPeakQuotient_diag_neg (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (i : Fin n) :
    orderedPeakQuotient angles hsize i (orderedPeak angles hsize i) < 0 := by
  rw [orderedPeakQuotient_value_at_peak]
  exact mul_neg_of_pos_of_neg (by norm_num) (orderedPeak_second_deriv_neg angles hsize i)

lemma sin_half_orderedPeak_sub_pos (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (i j : Fin n) (hij : i < j) :
    0 < Real.sin ((orderedPeak angles hsize j - orderedPeak angles hsize i) / 2) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact div_pos (sub_pos.mpr (orderedPeak_strictMono angles hsize hij)) (by norm_num)
  · have hi := orderedPeak_mem_Ioo angles hsize i
    have hj := orderedPeak_mem_Ioo angles hsize j
    linarith [hi.1, hj.2]

lemma sin_half_orderedPeak_sub_neg (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (i j : Fin n) (hij : i < j) :
    Real.sin ((orderedPeak angles hsize i - orderedPeak angles hsize j) / 2) < 0 := by
  rw [show (orderedPeak angles hsize i - orderedPeak angles hsize j) / 2 =
    -((orderedPeak angles hsize j - orderedPeak angles hsize i) / 2) by ring, Real.sin_neg]
  exact neg_neg_of_pos (sin_half_orderedPeak_sub_pos angles hsize i j hij)

/-- The actual quotient sign table: all off-diagonal entries have positive
checkerboard phase, while every diagonal entry is strictly negative. -/
theorem orderedPeakQuotient_offdiag_phase_pos (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (i j : Fin n) (hij : i ≠ j) :
    0 < (-1 : ℝ) ^ (i.val + j.val) *
      orderedPeakQuotient angles hsize i (orderedPeak angles hsize j) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have h := orderedPeak_first_derivative_phase_pos angles hsize i j hlt
    rw [deriv_orderedGapInterpolant_sine_factor angles hsize i] at h
    have hs := sin_half_orderedPeak_sub_pos angles hsize i j hlt
    have he : (-1 : ℝ) ^ (i.val + j.val) *
        (Real.sin ((orderedPeak angles hsize j - orderedPeak angles hsize i) / 2) *
          orderedPeakQuotient angles hsize i (orderedPeak angles hsize j)) =
        Real.sin ((orderedPeak angles hsize j - orderedPeak angles hsize i) / 2) *
          ((-1 : ℝ) ^ (i.val + j.val) *
            orderedPeakQuotient angles hsize i (orderedPeak angles hsize j)) := by ring
    rw [he] at h
    exact (mul_pos_iff_of_pos_left hs).mp h
  · have h := orderedPeak_other_derivative_phase_neg angles hsize j i hgt
    rw [deriv_orderedGapInterpolant_sine_factor angles hsize i,
      Nat.add_comm j.val i.val] at h
    have hs := sin_half_orderedPeak_sub_neg angles hsize j i hgt
    have he : (-1 : ℝ) ^ (i.val + j.val) *
        (Real.sin ((orderedPeak angles hsize j - orderedPeak angles hsize i) / 2) *
          orderedPeakQuotient angles hsize i (orderedPeak angles hsize j)) =
        Real.sin ((orderedPeak angles hsize j - orderedPeak angles hsize i) / 2) *
          ((-1 : ℝ) ^ (i.val + j.val) *
            orderedPeakQuotient angles hsize i (orderedPeak angles hsize j)) := by ring
    rw [he] at h
    by_contra hpos
    have hp := mul_nonneg_of_nonpos_of_nonpos hs.le (le_of_not_gt hpos)
    exact (not_le_of_gt h) hp

end

end UnitCircleInterpolation
