/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.PeakOrder

/-!
# Cross-Wronskian and derivative signs in physical peak order

After ordering the actual positive gaps clockwise, the pairwise phase is
`(-1)^(i+j)`, including pairs involving the final wrap gap. Evaluating the
proved global Wronskian at either positive peak gives its strict derivative sign.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ} {hn : 0 < n}

lemma sineWronskian_comm (θ a b : Fin n → ℝ) (t : ℝ) :
    sineWronskian θ a b t = -sineWronskian θ b a t := by
  unfold sineWronskian
  ring

lemma physicalGapCut_phase_before_last (hn : 0 < n) (i j : Fin n)
    (hij : i < j) (hj : j.val + 1 < n) :
    cyclicCrossGapPhase (physicalGapCut hn i) (physicalGapCut hn j) =
      (-1 : ℝ) ^ (i.val + j.val) := by
  have hi : i.val + 1 < n := by have h := (show i.val < j.val from hij); omega
  rw [physicalGapCut_of_next_lt hn i hi, physicalGapCut_of_next_lt hn j hj]
  unfold cyclicCrossGapPhase crossGapPhase gapPhaseSign
  simp only [if_neg (by omega : i.val + 1 ≠ 0),
    if_neg (by omega : j.val + 1 ≠ 0), mul_one]
  rw [show (j.val + 1) - (i.val + 1) = j.val - i.val from by
    have h := (show i.val < j.val from hij); omega]
  have he : i.val + j.val = (j.val - i.val) + 2 * i.val := by
    have h := (show i.val < j.val from hij); omega
  rw [he, pow_add, pow_mul]
  norm_num

lemma physicalGapCut_phase_at_last (hn : 0 < n) (i j : Fin n)
    (hij : i < j) (hj : j.val + 1 = n) :
    cyclicCrossGapPhase (physicalGapCut hn j) (physicalGapCut hn i) =
      -((-1 : ℝ) ^ (i.val + j.val)) := by
  have hi : i.val + 1 < n := by have h := (show i.val < j.val from hij); omega
  rw [physicalGapCut_of_last hn j hj, physicalGapCut_of_next_lt hn i hi]
  unfold cyclicCrossGapPhase crossGapPhase gapPhaseSign
  simp only [Nat.sub_zero, if_true,
    if_neg (by omega : i.val + 1 ≠ 0), mul_one]
  rw [← pow_add]
  have he : (i.val + 1) + (n - 1) = i.val + j.val + 1 := by omega
  rw [he, pow_succ]
  ring

/-- The actual physical-order Wronskian has the checkerboard phase globally. -/
theorem orderedGap_sineWronskian_neg (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) (t : ℝ) :
    (-1 : ℝ) ^ (i.val + j.val) *
      sineWronskian angles.angle (cyclicGapCoefficient (physicalGapCut hn i))
        (cyclicGapCoefficient (physicalGapCut hn j)) t < 0 := by
  by_cases hj : j.val + 1 < n
  · have hi : i.val + 1 < n := by have h := (show i.val < j.val from hij); omega
    have hcuts : physicalGapCut hn i < physicalGapCut hn j := by
      rw [physicalGapCut_of_next_lt hn i hi, physicalGapCut_of_next_lt hn j hj]
      change i.val + 1 < j.val + 1
      exact Nat.add_lt_add_right hij 1
    have h := cyclicGap_phase_sineWronskian_neg angles
      (physicalGapCut hn i) (physicalGapCut hn j) hcuts t
    rw [physicalGapCut_phase_before_last hn i j hij hj] at h
    exact h
  · have hjlast : j.val + 1 = n := by have h := j.isLt; omega
    have hi : i.val + 1 < n := by have h := (show i.val < j.val from hij); omega
    have hcuts : physicalGapCut hn j < physicalGapCut hn i := by
      rw [physicalGapCut_of_last hn j hjlast, physicalGapCut_of_next_lt hn i hi]
      change 0 < i.val + 1
      omega
    have h := cyclicGap_phase_sineWronskian_neg angles
      (physicalGapCut hn j) (physicalGapCut hn i) hcuts t
    rw [physicalGapCut_phase_at_last hn i j hij hjlast, sineWronskian_comm] at h
    simpa only [neg_mul_neg] using h

theorem orderedPeak_first_derivative_phase_pos (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (i j : Fin n) (hij : i < j) :
    0 < (-1 : ℝ) ^ (i.val + j.val) *
      deriv (orderedGapInterpolant angles i) (orderedPeak angles hsize j) := by
  have hcritical := (orderedPeak_hasDerivAt_zero angles hsize j).deriv
  have h := orderedGap_sineWronskian_neg angles i j hij (orderedPeak angles hsize j)
  unfold sineWronskian at h
  change (-1 : ℝ) ^ (i.val + j.val) *
    (orderedGapInterpolant angles i (orderedPeak angles hsize j) *
      deriv (orderedGapInterpolant angles j) (orderedPeak angles hsize j) -
        deriv (orderedGapInterpolant angles i) (orderedPeak angles hsize j) *
          orderedGapInterpolant angles j (orderedPeak angles hsize j)) < 0 at h
  rw [hcritical, mul_zero, zero_sub] at h
  have hv : 0 < orderedGapInterpolant angles j (orderedPeak angles hsize j) :=
    lt_trans (by norm_num : (0 : ℝ) < 1) (one_lt_orderedHeight angles hsize j)
  by_contra hpos
  have hnpos := le_of_not_gt hpos
  have hp := mul_nonpos_of_nonpos_of_nonneg hnpos hv.le
  have he : (-1 : ℝ) ^ (i.val + j.val) *
      -(deriv (orderedGapInterpolant angles i) (orderedPeak angles hsize j) *
        orderedGapInterpolant angles j (orderedPeak angles hsize j)) =
      -(((-1 : ℝ) ^ (i.val + j.val) *
        deriv (orderedGapInterpolant angles i) (orderedPeak angles hsize j)) *
          orderedGapInterpolant angles j (orderedPeak angles hsize j)) := by ring
  rw [he] at h
  linarith

theorem orderedPeak_other_derivative_phase_neg (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (i j : Fin n) (hij : i < j) :
    (-1 : ℝ) ^ (i.val + j.val) *
      deriv (orderedGapInterpolant angles j) (orderedPeak angles hsize i) < 0 := by
  have hcritical := (orderedPeak_hasDerivAt_zero angles hsize i).deriv
  have h := orderedGap_sineWronskian_neg angles i j hij (orderedPeak angles hsize i)
  unfold sineWronskian at h
  change (-1 : ℝ) ^ (i.val + j.val) *
    (orderedGapInterpolant angles i (orderedPeak angles hsize i) *
      deriv (orderedGapInterpolant angles j) (orderedPeak angles hsize i) -
        deriv (orderedGapInterpolant angles i) (orderedPeak angles hsize i) *
          orderedGapInterpolant angles j (orderedPeak angles hsize i)) < 0 at h
  rw [hcritical, zero_mul, sub_zero] at h
  have hv : 0 < orderedGapInterpolant angles i (orderedPeak angles hsize i) :=
    lt_trans (by norm_num : (0 : ℝ) < 1) (one_lt_orderedHeight angles hsize i)
  by_contra hneg
  have hp := mul_nonneg hv.le (le_of_not_gt hneg)
  have he : orderedGapInterpolant angles i (orderedPeak angles hsize i) *
      ((-1 : ℝ) ^ (i.val + j.val) *
        deriv (orderedGapInterpolant angles j) (orderedPeak angles hsize i)) =
      (-1 : ℝ) ^ (i.val + j.val) *
        (orderedGapInterpolant angles i (orderedPeak angles hsize i) *
          deriv (orderedGapInterpolant angles j) (orderedPeak angles hsize i)) := by ring
  rw [he] at hp
  exact (not_le_of_gt h) hp

end

end UnitCircleInterpolation
