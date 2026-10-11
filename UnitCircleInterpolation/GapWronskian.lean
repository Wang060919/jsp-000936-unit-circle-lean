/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.CrossInterlacing
import UnitCircleInterpolation.GapPeaks

/-!
# Cross-Wronskian signs for the literal gap peaks

At cut zero the actual wrap interpolant differs from the translated-wrap
coefficient convention by `(-1)^(n-1)`. This phase is included explicitly when
transferring the proved global cross-Wronskian to the actual gap functions and
their positive peaks. Both parities are covered.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ} {hn : 0 < n}

/-- The full-turn sign converting the zero cut to the actual wrap gap. -/
def gapPhaseSign (cut : Fin n) : ℝ :=
  if cut.val = 0 then (-1 : ℝ) ^ (n - 1) else 1

lemma gapPhaseSign_mul_self (cut : Fin n) : gapPhaseSign cut * gapPhaseSign cut = 1 := by
  unfold gapPhaseSign
  split_ifs
  · rw [← mul_pow]
    norm_num
  · norm_num

lemma cyclicGapCoefficient_eq_phase_mul (cut k : Fin n) :
    cyclicGapCoefficient cut k = gapPhaseSign cut * gapCoefficient cut k := by
  by_cases hz : cut.val = 0
  · have hpositive : 0 < n := Nat.zero_lt_of_lt cut.isLt
    have heq : cut = (⟨0, hpositive⟩ : Fin n) := Fin.ext hz
    simp only [cyclicGapCoefficient, gapPhaseSign, hz, if_true]
    rw [wrapCoefficient_eq_phaseSign_mul_gapCoefficient hpositive k, heq]
  · simp only [cyclicGapCoefficient, gapPhaseSign, hz, if_false, one_mul]

lemma gapInterpolant_eq_phase_mul (angles : CyclicAngles n hn) (cut : Fin n) (t : ℝ) :
    gapInterpolant angles cut t =
      gapPhaseSign cut * sineInterpolant angles.angle (gapCoefficient cut) t := by
  unfold gapInterpolant sineInterpolant
  simp_rw [cyclicGapCoefficient_eq_phase_mul, mul_assoc]
  rw [Finset.mul_sum]

lemma deriv_gapInterpolant_eq_phase_mul (angles : CyclicAngles n hn)
    (cut : Fin n) (t : ℝ) :
    deriv (gapInterpolant angles cut) t =
      gapPhaseSign cut * deriv (sineInterpolant angles.angle (gapCoefficient cut)) t := by
  have h := (hasDerivAt_sineInterpolant angles.angle (gapCoefficient cut) t).const_mul
    (gapPhaseSign cut)
  have heq : gapInterpolant angles cut =
      (fun u => gapPhaseSign cut * sineInterpolant angles.angle (gapCoefficient cut) u) :=
    funext (gapInterpolant_eq_phase_mul angles cut)
  rw [← heq] at h
  simpa only [deriv_sineInterpolant] using h.deriv

lemma cyclicGap_sineWronskian_eq (angles : CyclicAngles n hn) (i j : Fin n) (t : ℝ) :
    sineWronskian angles.angle (cyclicGapCoefficient i) (cyclicGapCoefficient j) t =
      gapPhaseSign i * gapPhaseSign j *
        sineWronskian angles.angle (gapCoefficient i) (gapCoefficient j) t := by
  unfold sineWronskian
  change gapInterpolant angles i t * deriv (gapInterpolant angles j) t -
    deriv (gapInterpolant angles i) t * gapInterpolant angles j t = _
  rw [gapInterpolant_eq_phase_mul, gapInterpolant_eq_phase_mul,
    deriv_gapInterpolant_eq_phase_mul, deriv_gapInterpolant_eq_phase_mul]
  ring

/-- The cross-cut phase corrected for the actual wrap function. -/
def cyclicCrossGapPhase (i j : Fin n) : ℝ :=
  crossGapPhase i j * gapPhaseSign i * gapPhaseSign j

theorem cyclicGap_phase_sineWronskian_neg (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) (t : ℝ) :
    cyclicCrossGapPhase i j *
      sineWronskian angles.angle (cyclicGapCoefficient i) (cyclicGapCoefficient j) t < 0 := by
  have heq : cyclicCrossGapPhase i j *
      sineWronskian angles.angle (cyclicGapCoefficient i) (cyclicGapCoefficient j) t =
      crossGapPhase i j * sineWronskian angles.angle (gapCoefficient i) (gapCoefficient j) t := by
    rw [cyclicGap_sineWronskian_eq]
    unfold cyclicCrossGapPhase
    calc
      crossGapPhase i j * gapPhaseSign i * gapPhaseSign j *
          (gapPhaseSign i * gapPhaseSign j *
            sineWronskian angles.angle (gapCoefficient i) (gapCoefficient j) t) =
        crossGapPhase i j * (gapPhaseSign i * gapPhaseSign i) *
          (gapPhaseSign j * gapPhaseSign j) *
            sineWronskian angles.angle (gapCoefficient i) (gapCoefficient j) t := by ring
      _ = _ := by rw [gapPhaseSign_mul_self, gapPhaseSign_mul_self]; ring
  rw [heq]
  exact crossGap_phase_sineWronskian_neg angles i j hij t

/-- At the first gap's own positive peak, the other derivative has the prescribed
strict phase sign. No residue or Wronskian hypothesis remains. -/
theorem gapPeak_other_derivative_phase_neg (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (i j : Fin n) (hij : i < j) :
    cyclicCrossGapPhase i j * deriv (gapInterpolant angles j) (gapPeak angles hsize i) < 0 := by
  have hcritical := (gapPeak_strictIntervalPeak angles hsize i).hasDerivAt_zero.deriv
  have hW := cyclicGap_phase_sineWronskian_neg angles i j hij (gapPeak angles hsize i)
  unfold sineWronskian at hW
  change cyclicCrossGapPhase i j *
    (gapInterpolant angles i (gapPeak angles hsize i) *
      deriv (gapInterpolant angles j) (gapPeak angles hsize i) -
        deriv (gapInterpolant angles i) (gapPeak angles hsize i) *
          gapInterpolant angles j (gapPeak angles hsize i)) < 0 at hW
  rw [hcritical, zero_mul, sub_zero] at hW
  have hheight : 0 < gapInterpolant angles i (gapPeak angles hsize i) :=
    lt_trans (by norm_num : (0 : ℝ) < 1) (one_lt_gapHeight angles hsize i)
  by_contra hneg
  have hnneg : 0 ≤ cyclicCrossGapPhase i j *
      deriv (gapInterpolant angles j) (gapPeak angles hsize i) := le_of_not_gt hneg
  have hprod := mul_nonneg hheight.le hnneg
  have heq : gapInterpolant angles i (gapPeak angles hsize i) *
      (cyclicCrossGapPhase i j * deriv (gapInterpolant angles j) (gapPeak angles hsize i)) =
      cyclicCrossGapPhase i j * (gapInterpolant angles i (gapPeak angles hsize i) *
        deriv (gapInterpolant angles j) (gapPeak angles hsize i)) := by ring
  rw [heq] at hprod
  exact (not_le_of_gt hW) hprod

theorem gapPeak_other_derivative_ne_zero (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (i j : Fin n) (hij : i < j) :
    deriv (gapInterpolant angles j) (gapPeak angles hsize i) ≠ 0 := by
  intro hzero
  have h := gapPeak_other_derivative_phase_neg angles hsize i j hij
  rw [hzero, mul_zero] at h
  exact (lt_irrefl 0) h

/-- The reversed evaluation has the opposite strict phase sign. -/
theorem gapPeak_first_derivative_phase_pos (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (i j : Fin n) (hij : i < j) :
    0 < cyclicCrossGapPhase i j *
      deriv (gapInterpolant angles i) (gapPeak angles hsize j) := by
  have hcritical := (gapPeak_strictIntervalPeak angles hsize j).hasDerivAt_zero.deriv
  have hW := cyclicGap_phase_sineWronskian_neg angles i j hij (gapPeak angles hsize j)
  unfold sineWronskian at hW
  change cyclicCrossGapPhase i j *
    (gapInterpolant angles i (gapPeak angles hsize j) *
      deriv (gapInterpolant angles j) (gapPeak angles hsize j) -
        deriv (gapInterpolant angles i) (gapPeak angles hsize j) *
          gapInterpolant angles j (gapPeak angles hsize j)) < 0 at hW
  rw [hcritical, mul_zero, zero_sub] at hW
  have hheight : 0 < gapInterpolant angles j (gapPeak angles hsize j) :=
    lt_trans (by norm_num : (0 : ℝ) < 1) (one_lt_gapHeight angles hsize j)
  by_contra hpos
  have hnpos : cyclicCrossGapPhase i j *
      deriv (gapInterpolant angles i) (gapPeak angles hsize j) ≤ 0 := le_of_not_gt hpos
  have hprod := mul_nonpos_of_nonpos_of_nonneg hnpos hheight.le
  have heq : cyclicCrossGapPhase i j *
      -(deriv (gapInterpolant angles i) (gapPeak angles hsize j) *
        gapInterpolant angles j (gapPeak angles hsize j)) =
      -((cyclicCrossGapPhase i j * deriv (gapInterpolant angles i) (gapPeak angles hsize j)) *
        gapInterpolant angles j (gapPeak angles hsize j)) := by ring
  rw [heq] at hW
  linarith

theorem gapPeak_first_derivative_ne_zero (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (i j : Fin n) (hij : i < j) :
    deriv (gapInterpolant angles i) (gapPeak angles hsize j) ≠ 0 := by
  intro hzero
  have h := gapPeak_first_derivative_phase_pos angles hsize i j hij
  rw [hzero, mul_zero] at h
  exact (lt_irrefl 0) h

/-- A gap function is never critical at another gap's unique peak. -/
theorem gapPeak_distinct_gap_derivative_ne_zero (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (i j : Fin n) (hij : i ≠ j) :
    deriv (gapInterpolant angles j) (gapPeak angles hsize i) ≠ 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact gapPeak_other_derivative_ne_zero angles hsize i j h
  · exact gapPeak_first_derivative_ne_zero angles hsize j i h

end

end UnitCircleInterpolation
