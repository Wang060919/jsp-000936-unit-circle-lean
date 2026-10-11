/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.CrossGapCoefficients
import UnitCircleInterpolation.InterpolantCalculus
import UnitCircleInterpolation.WronskianBridge

/-!
# The Wronskian of the actual cross-gap difference and sum

These are exact identities for the literal signed interpolants. A negative
cross-difference/sum Wronskian gives the phase-oriented gap Wronskian and its
critical-point sign consequences. This module does not assume or assert that
the particular cross-gap residues needed by the Markov kernel have been proved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ}

lemma deriv_crossDifferenceInterpolant (θ : Fin n → ℝ) (i j : Fin n) (t : ℝ) :
    deriv (sineInterpolant θ (crossDifferenceCoefficient i j)) t =
      deriv (sineInterpolant θ (gapCoefficient i)) t -
        crossGapPhase i j * deriv (sineInterpolant θ (gapCoefficient j)) t := by
  have h := (hasDerivAt_sineInterpolant θ (gapCoefficient i) t).sub
    ((hasDerivAt_sineInterpolant θ (gapCoefficient j) t).const_mul (crossGapPhase i j))
  have heq : sineInterpolant θ (crossDifferenceCoefficient i j) =
      (fun u => sineInterpolant θ (gapCoefficient i) u -
        crossGapPhase i j * sineInterpolant θ (gapCoefficient j) u) :=
    funext (crossDifferenceInterpolant_identity θ i j)
  change HasDerivAt (fun u => sineInterpolant θ (gapCoefficient i) u -
    crossGapPhase i j * sineInterpolant θ (gapCoefficient j) u)
    (sineInterpolantDerivative θ (gapCoefficient i) t -
      crossGapPhase i j * sineInterpolantDerivative θ (gapCoefficient j) t) t at h
  rw [← heq] at h
  simpa only [deriv_sineInterpolant] using h.deriv

lemma deriv_crossSumInterpolant (θ : Fin n → ℝ) (i j : Fin n) (t : ℝ) :
    deriv (sineInterpolant θ (crossSumCoefficient i j)) t =
      deriv (sineInterpolant θ (gapCoefficient i)) t +
        crossGapPhase i j * deriv (sineInterpolant θ (gapCoefficient j)) t := by
  have h := (hasDerivAt_sineInterpolant θ (gapCoefficient i) t).add
    ((hasDerivAt_sineInterpolant θ (gapCoefficient j) t).const_mul (crossGapPhase i j))
  have heq : sineInterpolant θ (crossSumCoefficient i j) =
      (fun u => sineInterpolant θ (gapCoefficient i) u +
        crossGapPhase i j * sineInterpolant θ (gapCoefficient j) u) :=
    funext (crossSumInterpolant_identity θ i j)
  change HasDerivAt (fun u => sineInterpolant θ (gapCoefficient i) u +
    crossGapPhase i j * sineInterpolant θ (gapCoefficient j) u)
    (sineInterpolantDerivative θ (gapCoefficient i) t +
      crossGapPhase i j * sineInterpolantDerivative θ (gapCoefficient j) t) t at h
  rw [← heq] at h
  simpa only [deriv_sineInterpolant] using h.deriv

/-- `W(F_i - ε F_j, F_i + ε F_j) = 2 ε W(F_i, F_j)` globally. -/
lemma crossWronskian_eq (θ : Fin n → ℝ) (i j : Fin n) (t : ℝ) :
    sineWronskian θ (crossDifferenceCoefficient i j) (crossSumCoefficient i j) t =
      2 * crossGapPhase i j * sineWronskian θ (gapCoefficient i) (gapCoefficient j) t := by
  unfold sineWronskian
  rw [crossDifferenceInterpolant_identity, crossSumInterpolant_identity,
    deriv_crossDifferenceInterpolant, deriv_crossSumInterpolant]
  ring

lemma crossWronskian_neg_iff (θ : Fin n → ℝ) (i j : Fin n) (t : ℝ) :
    sineWronskian θ (crossDifferenceCoefficient i j) (crossSumCoefficient i j) t < 0 ↔
      crossGapPhase i j * sineWronskian θ (gapCoefficient i) (gapCoefficient j) t < 0 := by
  rw [crossWronskian_eq]
  constructor <;> intro h <;> nlinarith

/-- At a critical point of the first gap interpolant, the other derivative's
orientation is the sign prescribed by the phase-oriented Wronskian. -/
lemma crossGap_critical_derivative_orientation (θ : Fin n → ℝ) (i j : Fin n) (t : ℝ)
    (hW : sineWronskian θ (crossDifferenceCoefficient i j) (crossSumCoefficient i j) t < 0)
    (hcritical : deriv (sineInterpolant θ (gapCoefficient i)) t = 0) :
    crossGapPhase i j * sineInterpolant θ (gapCoefficient i) t *
      deriv (sineInterpolant θ (gapCoefficient j)) t < 0 := by
  have h := (crossWronskian_neg_iff θ i j t).mp hW
  simpa only [sineWronskian, hcritical, zero_mul, sub_zero, mul_assoc] using h

lemma crossGap_no_common_critical (θ : Fin n → ℝ) (i j : Fin n) (t : ℝ)
    (hW : sineWronskian θ (crossDifferenceCoefficient i j) (crossSumCoefficient i j) t < 0)
    (hcritical : deriv (sineInterpolant θ (gapCoefficient i)) t = 0) :
    deriv (sineInterpolant θ (gapCoefficient j)) t ≠ 0 := by
  intro hzero
  have h := crossGap_critical_derivative_orientation θ i j t hW hcritical
  rw [hzero, mul_zero] at h
  exact (lt_irrefl (0 : ℝ)) h

end

end UnitCircleInterpolation
