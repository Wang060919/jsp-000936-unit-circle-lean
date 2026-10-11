/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.GapChordBounds
import UnitCircleInterpolation.PeakOrder
import UnitCircleInterpolation.AngularParameters
import Mathlib.Data.Finset.Max

/-!
# Widths of the actual circular node gaps

All actual positive widths add to one full turn, so one gap is at least the
average width. Their finite minimum is attained and positive. Literal gap
widths also extend continuously to the ambient normalized angular chart.
All statements include the single-node configuration.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ} {hn : 0 < n} {d : ℕ}

lemma sum_gapLeft (angles : CyclicAngles n hn) :
    (∑ cut, gapLeft angles cut) = ∑ k, angles.angle k := by
  have heq := (physicalGapEquiv hn).sum_comp (gapLeft angles)
  calc
    (∑ cut, gapLeft angles cut) =
        ∑ k, gapLeft angles (physicalGapCut hn k) := heq.symm
    _ = ∑ k, angles.angle k := by simp only [gapLeft_physicalGapCut]

lemma sum_gapRight (angles : CyclicAngles n hn) :
    (∑ cut, gapRight angles cut) = 2 * Real.pi + ∑ k, angles.angle k := by
  cases n with
  | zero => omega
  | succ d =>
    have hz : angles.angle 0 = 0 := angles.first_eq_zero
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, hz]
    simp only [gapRight, Fin.val_zero, Fin.val_succ, Nat.succ_ne_zero,
      if_true, if_false, zero_add]

/-- The literal positive cyclic gap widths exhaust one full turn. -/
theorem sum_gapWidth (angles : CyclicAngles n hn) :
    (∑ cut, gapWidth angles cut) = 2 * Real.pi := by
  simp only [gapWidth, Finset.sum_sub_distrib, sum_gapRight, sum_gapLeft, add_sub_cancel_right]

/-- Some actual gap is at least the mean width, also when there is only one gap. -/
theorem exists_gapWidth_ge_average (angles : CyclicAngles n hn) :
    ∃ cut, 2 * Real.pi / (n : ℝ) ≤ gapWidth angles cut := by
  have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsum : (∑ _cut : Fin n, 2 * Real.pi / (n : ℝ)) = 2 * Real.pi := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨cut, _, hcut⟩ := Finset.exists_le_of_sum_le huniv
    (show (∑ _cut : Fin n, 2 * Real.pi / (n : ℝ)) ≤ ∑ cut, gapWidth angles cut by
      rw [hsum, sum_gapWidth])
  exact ⟨cut, hcut⟩

/-- The literal finite set of all actual gap widths. -/
def gapWidthSet (angles : CyclicAngles n hn) : Finset ℝ :=
  Finset.univ.image (gapWidth angles)

lemma gapWidthSet_nonempty (angles : CyclicAngles n hn) : (gapWidthSet angles).Nonempty :=
  ⟨gapWidth angles ⟨0, hn⟩, Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩

def minimumGapWidth (angles : CyclicAngles n hn) : ℝ :=
  (gapWidthSet angles).min' (gapWidthSet_nonempty angles)

lemma minimumGapWidth_le (angles : CyclicAngles n hn) (cut : Fin n) :
    minimumGapWidth angles ≤ gapWidth angles cut := by
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨cut, Finset.mem_univ cut, rfl⟩

lemma exists_gapWidth_eq_minimum (angles : CyclicAngles n hn) :
    ∃ cut, gapWidth angles cut = minimumGapWidth angles := by
  obtain ⟨cut, _, heq⟩ := Finset.mem_image.mp
    (Finset.min'_mem (gapWidthSet angles) (gapWidthSet_nonempty angles))
  exact ⟨cut, heq⟩

lemma minimumGapWidth_pos (angles : CyclicAngles n hn) : 0 < minimumGapWidth angles := by
  obtain ⟨cut, heq⟩ := exists_gapWidth_eq_minimum angles
  rw [← heq]
  exact gapWidth_pos angles cut

lemma minimumGapWidth_le_average (angles : CyclicAngles n hn) :
    minimumGapWidth angles ≤ 2 * Real.pi / (n : ℝ) := by
  have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  apply (le_div_iff₀ hnreal).mpr
  have hsum := Finset.sum_le_sum (fun cut (_ : cut ∈ (Finset.univ : Finset (Fin n))) =>
    minimumGapWidth_le angles cut)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    sum_gapWidth, mul_comm] using hsum

/-- Literal gap width in the ambient normalized parameter chart. -/
def parameterGapWidth (cut : Fin (d + 1)) (u : Fin d → ℝ) : ℝ :=
  (if cut.val = 0 then 2 * Real.pi else angularParameterAngles u cut) -
    angularParameterAngles u (gapLeftNodeIndex (Nat.succ_pos d) cut)

lemma continuous_parameterGapWidth (cut : Fin (d + 1)) : Continuous (parameterGapWidth cut) := by
  unfold parameterGapWidth
  split_ifs
  · exact continuous_const.sub (continuous_angularParameterAngle _)
  · exact (continuous_angularParameterAngle cut).sub (continuous_angularParameterAngle _)

lemma parameterGapWidth_of_mem_domain (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (cut : Fin (d + 1)) :
    parameterGapWidth cut u = gapWidth (cyclicAnglesOfParameters u hu) cut := by
  unfold parameterGapWidth gapWidth gapRight gapLeft gapLeftNodeIndex
  split_ifs <;> rfl

end

end UnitCircleInterpolation
