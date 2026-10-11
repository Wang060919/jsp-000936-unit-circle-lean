/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.GapPeaks
import UnitCircleInterpolation.CyclicGapCover
import Mathlib.Data.Finset.Lattice.Fold

/-!
# The literal full-circle objective is the maximum of the actual gap heights

The circle coverage lemma includes the nodes and the wrap gap. Thus the finite
height maximum accounts for every circle point, rather than only sampled angles.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ} {hn : 0 < n}

/-- A finite maximum of the actual, proved gap heights. -/
def gapHeightMaximum (angles : CyclicAngles n hn) (hsize : 2 ≤ n) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (gapHeight angles hsize)

lemma gapHeight_le_gapHeightMaximum (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (cut : Fin n) : gapHeight angles hsize cut ≤ gapHeightMaximum angles hsize :=
  Finset.le_sup' (gapHeight angles hsize) (Finset.mem_univ cut)

lemma one_lt_gapHeightMaximum (angles : CyclicAngles n hn) (hsize : 2 ≤ n) :
    1 < gapHeightMaximum angles hsize :=
  (one_lt_gapHeight angles hsize ⟨0, hn⟩).trans_le
    (gapHeight_le_gapHeightMaximum angles hsize ⟨0, hn⟩)

lemma circleLebesgue_le_gapHeightMaximum (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (t : ℝ) (ht : t ∈ Set.Ico 0 (2 * Real.pi)) :
    lebesgueFunction (phaseNodes angles.angle) (Circle.exp t : ℂ) ≤
      gapHeightMaximum angles hsize := by
  rcases angles.exists_node_or_gap t ht with ⟨i, rfl⟩ | ⟨cut, hcut, hgap⟩ | hwrap
  · have hnode : (Circle.exp (angles.angle i) : ℂ) = phaseNodes angles.angle i := rfl
    rw [hnode, lebesgueFunction_at_node _ angles.phaseNodes_injective i]
    exact (one_lt_gapHeightMaximum angles hsize).le
  · have hinterval : t ∈ gapInterval angles cut := by
      rwa [gapInterval_of_pos angles cut hcut]
    rw [lebesgueFunction_on_gapInterval angles cut hinterval]
    exact (gapInterpolant_le_gapHeight angles hsize cut
      (Set.Ioo_subset_Icc_self hinterval)).trans (gapHeight_le_gapHeightMaximum angles hsize cut)
  · have hinterval : t ∈ gapInterval angles ⟨0, hn⟩ := by
      rwa [gapInterval_zero]
    rw [lebesgueFunction_on_gapInterval angles ⟨0, hn⟩ hinterval]
    exact (gapInterpolant_le_gapHeight angles hsize ⟨0, hn⟩
      (Set.Ioo_subset_Icc_self hinterval)).trans
        (gapHeight_le_gapHeightMaximum angles hsize ⟨0, hn⟩)

/-- The original supremum over all unit complex points equals the finite gap maximum. -/
theorem angularAmplification_eq_gapHeightMaximum (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) : angularAmplification angles = gapHeightMaximum angles hsize := by
  apply le_antisymm
  · apply (amplification_le_iff angles.toNodeFamily _).mpr
    intro w
    rw [CyclicAngles.toNodeFamily_coordinates]
    have h := circleLebesgue_le_gapHeightMaximum angles hsize (cyclicPhase w)
      (cyclicPhase_mem_Ico w)
    rwa [exp_cyclicPhase] at h
  · apply Finset.sup'_le
    intro cut hcut
    exact gapHeight_le_angularAmplification angles hsize cut

lemma one_lt_angularAmplification (angles : CyclicAngles n hn) (hsize : 2 ≤ n) :
    1 < angularAmplification angles := by
  rw [angularAmplification_eq_gapHeightMaximum angles hsize]
  exact one_lt_gapHeightMaximum angles hsize

/-- Sorting and rotation preserve the original objective, so the finite height
formula also holds for every admissible input enumeration. -/
theorem amplification_eq_ordered_gapHeightMaximum (nodes : NodeFamily n) (hn : 0 < n)
    (hsize : 2 ≤ n) :
    amplification nodes = gapHeightMaximum (orderedAngles nodes hn) hsize := by
  let rotated := anchoredNodes nodes hn
  let normalized := rotated.reindex rotated.sortedPermutation
  have hcoordinates : normalized.coordinates = (orderedAngles nodes hn).toNodeFamily.coordinates := by
    funext i
    change ((anchoredNodes nodes hn).point ((anchoredNodes nodes hn).sortedPermutation i) : ℂ) =
      (Circle.exp ((anchoredNodes nodes hn).sortedPhase i) : ℂ)
    exact congrArg ((↑) : Circle → ℂ) ((anchoredNodes nodes hn).exp_sortedPhase i).symm
  have hinvariant : amplification normalized = amplification nodes := by
    dsimp only [normalized]
    rw [amplification_reindex]
    exact amplification_rotate nodes (nodes.point ⟨0, hn⟩)⁻¹
  calc
    amplification nodes = amplification normalized := hinvariant.symm
    _ = angularAmplification (orderedAngles nodes hn) := by
      unfold angularAmplification amplification
      rw [hcoordinates]
    _ = gapHeightMaximum (orderedAngles nodes hn) hsize :=
      angularAmplification_eq_gapHeightMaximum _ hsize

lemma one_lt_amplification_of_two_le (nodes : NodeFamily n) (hsize : 2 ≤ n) :
    1 < amplification nodes := by
  have hn : 0 < n := by omega
  rw [amplification_eq_ordered_gapHeightMaximum nodes hn hsize]
  exact one_lt_gapHeightMaximum _ hsize

end

end UnitCircleInterpolation
