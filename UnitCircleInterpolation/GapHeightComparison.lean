/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.GapChordBounds
import UnitCircleInterpolation.CardinalComparison

/-!
# Quantitative comparison of actual gap heights

The midpoint of a wide actual empty gap is separated from every node. At the
actual peak of a small gap, every cardinal has another nearby endpoint node.
The literal cardinal comparison therefore gives an explicit height inequality,
including for either selected wrap gap. These are quantitative estimates;
the global properness and minimizer theorems remain separate steps.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ} {hn : 0 < n}

lemma lebesgueFunction_gapMidpoint_le_gapHeight (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (cut : Fin n) :
    lebesgueFunction (phaseNodes angles.angle) (Circle.exp (gapMidpoint angles cut) : ℂ) ≤
      gapHeight angles hsize cut := by
  rw [lebesgueFunction_on_gapInterval angles cut (gapMidpoint_mem_gapInterval angles cut)]
  exact (gapPeak_strictIntervalPeak angles hsize cut).isMaxOn
    (Set.Ioo_subset_Icc_self (gapMidpoint_mem_gapInterval angles cut))

/-- The actual large-gap height dominates the small-gap height with a reciprocal-width factor. -/
theorem gapHeight_width_comparison (angles : CyclicAngles n hn) (hsize : 2 ≤ n)
    (large small : Fin n) (width : ℝ) (hw : 0 < width)
    (hwidth : width ≤ gapWidth angles large) :
    2 * Real.sin (width / 4) ^ (n - 1) * gapHeight angles hsize small ≤
      gapWidth angles small * gapHeight angles hsize large := by
  have hsep := gapMidpoint_uniform_chord_lower_bound angles large width hw hwidth
  have hnear := gapInterval_near_other_node angles hsize small
    (gapPeak_mem_gapInterval angles hsize small)
  have h := circle_lebesgue_comparison hsize angles.toNodeFamily.point
    angles.toNodeFamily.injective (Circle.exp (gapMidpoint angles large))
    (Circle.exp (gapPeak angles hsize small)) (2 * Real.sin (width / 4))
    (gapWidth angles small) hsep.1 (gapWidth_pos angles small) hsep.2 hnear
  have hsmall := (gapHeight_eq_lebesgueFunction angles hsize small).symm
  change lebesgueFunction (phaseNodes angles.angle)
    (Circle.exp (gapPeak angles hsize small) : ℂ) = gapHeight angles hsize small at hsmall
  change 2 * ((2 * Real.sin (width / 4)) / 2) ^ (n - 1) *
    lebesgueFunction (phaseNodes angles.angle) (Circle.exp (gapPeak angles hsize small) : ℂ) ≤
      gapWidth angles small * lebesgueFunction (phaseNodes angles.angle)
        (Circle.exp (gapMidpoint angles large) : ℂ) at h
  rw [hsmall, show (2 * Real.sin (width / 4)) / 2 = Real.sin (width / 4) by ring] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (lebesgueFunction_gapMidpoint_le_gapHeight angles hsize large)
    (gapWidth_pos angles small).le)

/-- An explicit lower bound for the actual range of gap heights when a small
gap is narrower than the fixed positive comparison coefficient. -/
theorem gapHeight_difference_lower_bound (angles : CyclicAngles n hn) (hsize : 2 ≤ n)
    (large small : Fin n) (width : ℝ) (hw : 0 < width)
    (hwidth : width ≤ gapWidth angles large)
    (hsmall : gapWidth angles small ≤ 2 * Real.sin (width / 4) ^ (n - 1)) :
    (2 * Real.sin (width / 4) ^ (n - 1)) / gapWidth angles small - 1 ≤
      gapHeight angles hsize large - gapHeight angles hsize small := by
  have h := gapHeight_width_comparison angles hsize large small width hw hwidth
  have hv := (one_lt_gapHeight angles hsize small).le
  have hmul := mul_le_mul_of_nonneg_left hv
    (sub_nonneg.mpr hsmall)
  have hweighted : 2 * Real.sin (width / 4) ^ (n - 1) - gapWidth angles small ≤
      gapWidth angles small *
        (gapHeight angles hsize large - gapHeight angles hsize small) := by
    nlinarith
  have hb := gapWidth_pos angles small
  have hdiv : (2 * Real.sin (width / 4) ^ (n - 1) - gapWidth angles small) /
      gapWidth angles small ≤ gapHeight angles hsize large - gapHeight angles hsize small :=
    (div_le_iff₀ hb).mpr (by nlinarith [hweighted])
  have he : (2 * Real.sin (width / 4) ^ (n - 1) - gapWidth angles small) /
      gapWidth angles small =
        (2 * Real.sin (width / 4) ^ (n - 1)) / gapWidth angles small - 1 := by
    rw [sub_div, div_self hb.ne']
  rwa [he] at hdiv

end

end UnitCircleInterpolation
