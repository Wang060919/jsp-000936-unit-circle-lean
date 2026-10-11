/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.AngularProperness
import UnitCircleInterpolation.AngularDomainTopology
import UnitCircleInterpolation.GapHeightMaximum
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice

/-!
# Existence of a minimum for the literal circle objective

The actual full-circle amplification is the finite maximum of the smooth gap
heights. Its sublevel sets are compact because they have bounded actual height
differences, whose preimages are compact by the proved collision estimates.
An explicit regular configuration makes one such sublevel set nonempty. The
extreme value theorem then gives a minimum over the full admissible domain.
No equal-height or minimizer-classification hypothesis is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {d : ℕ}

/-- The literal full-circle objective on the actual normalized angular domain. -/
def angularParameterAmplification (_hsize : 2 ≤ d + 1)
    (u : angularParameterDomain d) : ℝ :=
  angularAmplification (cyclicAnglesOfParameters u.val u.property)

lemma parameterOrderedHeight_le_angularParameterAmplification (hsize : 2 ≤ d + 1)
    (u : angularParameterDomain d) (i : Fin (d + 1)) :
    parameterOrderedHeight hsize i u.val ≤ angularParameterAmplification hsize u := by
  rw [parameterOrderedHeight_of_mem_domain u.val u.property]
  exact gapHeight_le_angularAmplification (cyclicAnglesOfParameters u.val u.property)
    hsize (physicalGapCut (Nat.succ_pos d) i)

lemma one_lt_angularParameterAmplification (hsize : 2 ≤ d + 1)
    (u : angularParameterDomain d) : 1 < angularParameterAmplification hsize u :=
  one_lt_angularAmplification (cyclicAnglesOfParameters u.val u.property) hsize

/-- Reordering the actual gaps does not change the literal objective's finite maximum. -/
theorem angularParameterAmplification_eq_orderedHeightMaximum (hsize : 2 ≤ d + 1)
    (u : angularParameterDomain d) :
    angularParameterAmplification hsize u =
      Finset.univ.sup' ⟨0, Finset.mem_univ (0 : Fin (d + 1))⟩
        (fun i => parameterOrderedHeight hsize i u.val) := by
  apply le_antisymm
  · rw [angularParameterAmplification, angularAmplification_eq_gapHeightMaximum]
    apply Finset.sup'_le
    intro cut _
    obtain ⟨i, hi⟩ := physicalGapCut_surjective (Nat.succ_pos d) cut
    have h := Finset.le_sup' (fun i => parameterOrderedHeight hsize i u.val)
      (Finset.mem_univ i)
    simpa only [parameterOrderedHeight_of_mem_domain u.val u.property,
      orderedHeight, hi] using h
  · apply Finset.sup'_le
    intro i _
    exact parameterOrderedHeight_le_angularParameterAmplification hsize u i

lemma continuous_parameterOrderedHeight_on_domain (hsize : 2 ≤ d + 1)
    (i : Fin (d + 1)) :
    Continuous (fun u : angularParameterDomain d => parameterOrderedHeight hsize i u.val) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  exact (contDiffAt_parameterOrderedHeight_of_mem_domain u.val u.property hsize i).continuousAt.comp
    continuous_subtype_val.continuousAt

/-- Continuity concerns the supremum over the entire circle, via the proved maximum formula. -/
theorem continuous_angularParameterAmplification (hsize : 2 ≤ d + 1) :
    Continuous (angularParameterAmplification hsize) := by
  have heq : angularParameterAmplification hsize =
      fun u : angularParameterDomain d =>
        Finset.univ.sup' ⟨0, Finset.mem_univ (0 : Fin (d + 1))⟩
          (fun i => parameterOrderedHeight hsize i u.val) := by
    funext u
    exact angularParameterAmplification_eq_orderedHeightMaximum hsize u
  rw [heq]
  exact Continuous.finset_sup'_apply _ (fun i _ =>
    continuous_parameterOrderedHeight_on_domain hsize i)

/-- Every actual adjacent-height difference is bounded by twice the literal objective. -/
theorem norm_heightDifferenceMap_le_twice_amplification (hsize : 2 ≤ d + 1)
    (u : angularParameterDomain d) :
    ‖heightDifferenceMap hsize u‖ ≤ 2 * angularParameterAmplification hsize u := by
  have hamp : 0 < angularParameterAmplification hsize u :=
    zero_lt_one.trans (one_lt_angularParameterAmplification hsize u)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hpos (j : Fin (d + 1)) : 0 < parameterOrderedHeight hsize j u.val := by
    rw [parameterOrderedHeight_of_mem_domain u.val u.property]
    exact zero_lt_one.trans (one_lt_orderedHeight _ hsize j)
  change ‖parameterOrderedHeight hsize i.succ u.val -
      parameterOrderedHeight hsize i.castSucc u.val‖ ≤ _
  calc
    _ ≤ ‖parameterOrderedHeight hsize i.succ u.val‖ +
        ‖parameterOrderedHeight hsize i.castSucc u.val‖ := norm_sub_le _ _
    _ = parameterOrderedHeight hsize i.succ u.val +
        parameterOrderedHeight hsize i.castSucc u.val := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hpos i.succ),
        abs_of_pos (hpos i.castSucc)]
    _ ≤ angularParameterAmplification hsize u + angularParameterAmplification hsize u :=
      add_le_add (parameterOrderedHeight_le_angularParameterAmplification hsize u i.succ)
        (parameterOrderedHeight_le_angularParameterAmplification hsize u i.castSucc)
    _ = 2 * angularParameterAmplification hsize u := by ring

/-- Actual objective sublevels are compact; nodes cannot collide in a bounded sublevel. -/
theorem isCompact_sublevel_angularParameterAmplification (hsize : 2 ≤ d + 1) (M : ℝ) :
    IsCompact {u : angularParameterDomain d | angularParameterAmplification hsize u ≤ M} := by
  apply (isCompact_preimage_heightDifferenceMap hsize
    (isCompact_closedBall (0 : Fin d → ℝ) (2 * M))).of_isClosed_subset
      (isClosed_le (continuous_angularParameterAmplification hsize) continuous_const)
  intro u hu
  apply Metric.mem_closedBall.mpr
  simpa only [dist_zero_right] using
    (norm_heightDifferenceMap_le_twice_amplification hsize u).trans
      (mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 2))

/-- For every number of nodes at least two, the literal full-circle objective has a global minimum. -/
theorem exists_minimum_angularParameterAmplification (hsize : 2 ≤ d + 1) :
    ∃ u : angularParameterDomain d, ∀ v : angularParameterDomain d,
      angularParameterAmplification hsize u ≤ angularParameterAmplification hsize v := by
  let u₀ : angularParameterDomain d :=
    ⟨regularAngularParameters d, regularAngularParameters_mem_domain d⟩
  let M := angularParameterAmplification hsize u₀
  let S : Set (angularParameterDomain d) :=
    {u | angularParameterAmplification hsize u ≤ M}
  have hu₀ : u₀ ∈ S := by
    change angularParameterAmplification hsize u₀ ≤ angularParameterAmplification hsize u₀
    exact le_refl _
  obtain ⟨u, hu, hmin⟩ :=
    (isCompact_sublevel_angularParameterAmplification hsize M).exists_isMinOn
      ⟨u₀, hu₀⟩ (continuous_angularParameterAmplification hsize).continuousOn
  refine ⟨u, fun v => ?_⟩
  by_cases hv : v ∈ S
  · exact hmin hv
  · have hv' : M < angularParameterAmplification hsize v := lt_of_not_ge hv
    exact (hmin hu₀).trans hv'.le

end

end UnitCircleInterpolation
