/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.GapWidths
import UnitCircleInterpolation.GapHeightComparison
import UnitCircleInterpolation.FiniteHeightDifferences
import UnitCircleInterpolation.PeakHeightDerivative
import Mathlib.Order.Filter.AtTopBot.Tendsto

/-!
# Quantitative boundary bounds for the actual height-difference map

An actual gap has at least the average width. Comparing its height with that
of a smallest gap, then bounding their difference by the actual adjacent-height
vector, yields an explicit reciprocal-width estimate. A bounded vector keeps
every gap uniformly positive. These statements prove the boundary estimates;
global properness of the height-difference map is a separate assertion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace UnitCircleInterpolation

noncomputable section

variable {d : ℕ}

/-- The fixed coefficient supplied by the mean width of the `d+1` actual gaps. -/
def heightDifferenceBoundaryCoefficient (d : ℕ) : ℝ :=
  2 * Real.sin ((2 * Real.pi / ((d + 1 : ℕ) : ℝ)) / 4) ^ d

lemma heightDifferenceBoundaryCoefficient_pos (d : ℕ) :
    0 < heightDifferenceBoundaryCoefficient d := by
  have hn : 0 < ((d + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos d)
  have hn1 : (1 : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_one] using
      (show ((1 : ℕ) : ℝ) ≤ ((d + 1 : ℕ) : ℝ) from Nat.cast_le.mpr (by omega))
  have havg : 0 < 2 * Real.pi / ((d + 1 : ℕ) : ℝ) :=
    div_pos (mul_pos (by norm_num) Real.pi_pos) hn
  have havg_le : 2 * Real.pi / ((d + 1 : ℕ) : ℝ) ≤ 2 * Real.pi := by
    apply (div_le_iff₀ hn).mpr
    have h := mul_le_mul_of_nonneg_left hn1 (by positivity : 0 ≤ 2 * Real.pi)
    simpa only [mul_one] using h
  have hsin : 0 < Real.sin ((2 * Real.pi / ((d + 1 : ℕ) : ℝ)) / 4) := by
    simpa only [sub_zero] using
      sin_quarter_gap_pos 0 (2 * Real.pi / ((d + 1 : ℕ) : ℝ)) havg
        (by simpa only [sub_zero] using havg_le)
  exact mul_pos (by norm_num) (pow_pos hsin _)

lemma finiteHeightDifferences_parameterOrderedHeightMap (hsize : 2 ≤ d + 1)
    (u : Fin d → ℝ) :
    finiteHeightDifferences (parameterOrderedHeightMap hsize u) =
      parameterAdjacentHeightDifferences hsize u := rfl

/-- The actual chart vector controls heights of any two actual raw circular gaps. -/
lemma parameter_gapHeight_difference_le_two_dim_norm (hsize : 2 ≤ d + 1)
    (u : Fin d → ℝ) (hu : u ∈ angularParameterDomain d) (large small : Fin (d + 1)) :
    gapHeight (cyclicAnglesOfParameters u hu) hsize large -
        gapHeight (cyclicAnglesOfParameters u hu) hsize small ≤
      2 * (d : ℝ) * ‖parameterAdjacentHeightDifferences hsize u‖ := by
  obtain ⟨i, hi⟩ := physicalGapCut_surjective (Nat.succ_pos d) large
  obtain ⟨j, hj⟩ := physicalGapCut_surjective (Nat.succ_pos d) small
  have h := height_sub_le_two_dim_mul_norm (parameterOrderedHeightMap hsize u) i j
  rw [finiteHeightDifferences_parameterOrderedHeightMap] at h
  change parameterOrderedHeight hsize i u - parameterOrderedHeight hsize j u ≤ _ at h
  simpa only [parameterOrderedHeight_of_mem_domain u hu, orderedHeight, hi, hj] using h

/-- The unconditional reciprocal estimate uses the actual minimum gap and actual difference norm. -/
theorem minimumGapWidth_reciprocal_le_adjacent_height_norm (hsize : 2 ≤ d + 1)
    (u : Fin d → ℝ) (hu : u ∈ angularParameterDomain d) :
    heightDifferenceBoundaryCoefficient d /
        minimumGapWidth (cyclicAnglesOfParameters u hu) - 1 ≤
      2 * (d : ℝ) * ‖parameterAdjacentHeightDifferences hsize u‖ := by
  let angles := cyclicAnglesOfParameters u hu
  have hmin : 0 < minimumGapWidth angles := minimumGapWidth_pos angles
  have hn : 0 < ((d + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos d)
  have havg : 0 < 2 * Real.pi / ((d + 1 : ℕ) : ℝ) :=
    div_pos (mul_pos (by norm_num) Real.pi_pos) hn
  have hcoeff : 2 * Real.sin ((2 * Real.pi / ((d + 1 : ℕ) : ℝ)) / 4) ^ ((d + 1) - 1) =
      heightDifferenceBoundaryCoefficient d := by
    simp only [Nat.add_sub_cancel, heightDifferenceBoundaryCoefficient]
  by_cases hsmall : minimumGapWidth angles ≤ heightDifferenceBoundaryCoefficient d
  · obtain ⟨large, hlarge⟩ := exists_gapWidth_ge_average angles
    obtain ⟨small, heq⟩ := exists_gapWidth_eq_minimum angles
    have hgap : gapWidth angles small ≤
        2 * Real.sin ((2 * Real.pi / ((d + 1 : ℕ) : ℝ)) / 4) ^ ((d + 1) - 1) := by
      rw [heq, hcoeff]
      exact hsmall
    have h := gapHeight_difference_lower_bound angles hsize large small
      (2 * Real.pi / ((d + 1 : ℕ) : ℝ)) havg hlarge hgap
    rw [hcoeff, heq] at h
    exact h.trans (parameter_gapHeight_difference_le_two_dim_norm hsize u hu large small)
  · have hdiv : heightDifferenceBoundaryCoefficient d / minimumGapWidth angles ≤ 1 :=
      (div_le_one hmin).mpr (le_of_lt (lt_of_not_ge hsmall))
    have hnorm : 0 ≤ 2 * (d : ℝ) * ‖parameterAdjacentHeightDifferences hsize u‖ :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) (norm_nonneg _)
    exact (sub_nonpos.mpr hdiv).trans hnorm

lemma heightDifferenceBoundaryMargin_pos (d : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    0 < heightDifferenceBoundaryCoefficient d / (1 + 2 * (d : ℝ) * R) := by
  exact div_pos (heightDifferenceBoundaryCoefficient_pos d) (by positivity)

/-- A bounded actual adjacent-height vector forces an explicit positive minimum width. -/
theorem minimumGapWidth_lower_of_adjacent_height_norm_le (hsize : 2 ≤ d + 1)
    (u : Fin d → ℝ) (hu : u ∈ angularParameterDomain d) (R : ℝ) (hR : 0 ≤ R)
    (hnorm : ‖parameterAdjacentHeightDifferences hsize u‖ ≤ R) :
    heightDifferenceBoundaryCoefficient d / (1 + 2 * (d : ℝ) * R) ≤
      minimumGapWidth (cyclicAnglesOfParameters u hu) := by
  have h := minimumGapWidth_reciprocal_le_adjacent_height_norm hsize u hu
  have hm := minimumGapWidth_pos (cyclicAnglesOfParameters u hu)
  have hscaled := mul_le_mul_of_nonneg_left hnorm
    (by positivity : 0 ≤ 2 * (d : ℝ))
  have hquot : heightDifferenceBoundaryCoefficient d /
      minimumGapWidth (cyclicAnglesOfParameters u hu) ≤ 1 + 2 * (d : ℝ) * R := by
    linarith
  have hmul := (div_le_iff₀ hm).mp hquot
  apply (div_le_iff₀ (by positivity : 0 < 1 + 2 * (d : ℝ) * R)).mpr
  simpa only [mul_comm] using hmul

/-- The same fixed positive lower width controls every literal gap in the ambient chart. -/
theorem parameterGapWidth_lower_of_adjacent_height_norm_le (hsize : 2 ≤ d + 1)
    (u : Fin d → ℝ) (hu : u ∈ angularParameterDomain d) (R : ℝ) (hR : 0 ≤ R)
    (hnorm : ‖parameterAdjacentHeightDifferences hsize u‖ ≤ R) (cut : Fin (d + 1)) :
    heightDifferenceBoundaryCoefficient d / (1 + 2 * (d : ℝ) * R) ≤
      parameterGapWidth cut u := by
  rw [parameterGapWidth_of_mem_domain u hu]
  exact (minimumGapWidth_lower_of_adjacent_height_norm_le hsize u hu R hR hnorm).trans
    (minimumGapWidth_le (cyclicAnglesOfParameters u hu) cut)

/-- Crossing the explicit minimum-width threshold forces the actual norm above `R`. -/
theorem lt_adjacent_height_norm_of_minimumGapWidth_lt (hsize : 2 ≤ d + 1)
    (u : Fin d → ℝ) (hu : u ∈ angularParameterDomain d) (R : ℝ) (hR : 0 ≤ R)
    (hwidth : minimumGapWidth (cyclicAnglesOfParameters u hu) <
      heightDifferenceBoundaryCoefficient d / (1 + 2 * (d : ℝ) * R)) :
    R < ‖parameterAdjacentHeightDifferences hsize u‖ := by
  by_contra h
  have hnorm : ‖parameterAdjacentHeightDifferences hsize u‖ ≤ R := le_of_not_gt h
  exact (not_le_of_gt hwidth)
    (minimumGapWidth_lower_of_adjacent_height_norm_le hsize u hu R hR hnorm)

/-- Along any family in the actual chart, minimum width tending to zero forces norm divergence. -/
theorem adjacent_height_norm_tendsto_atTop_of_minimumGapWidth_tendsto_zero
    {α : Type*} (hsize : 2 ≤ d + 1) (u : α → Fin d → ℝ)
    (hu : ∀ a, u a ∈ angularParameterDomain d) (l : Filter α)
    (hwidth : Filter.Tendsto (fun a => minimumGapWidth (cyclicAnglesOfParameters (u a) (hu a)))
      l (nhds (0 : ℝ))) :
    Filter.Tendsto (fun a => ‖parameterAdjacentHeightDifferences hsize (u a)‖)
      l Filter.atTop := by
  apply Filter.tendsto_atTop.mpr
  intro R
  have hR : 0 ≤ max R 0 := le_max_right _ _
  have hmargin := heightDifferenceBoundaryMargin_pos d (max R 0) hR
  have hevent := hwidth.eventually (gt_mem_nhds hmargin)
  filter_upwards [hevent] with a ha
  exact (le_max_left R 0).trans
    (lt_adjacent_height_norm_of_minimumGapWidth_lt hsize (u a) (hu a) (max R 0) hR ha).le

end

end UnitCircleInterpolation
