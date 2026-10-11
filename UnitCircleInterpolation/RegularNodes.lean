/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.Definitions
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.NormNum

/-! # The regular polygon is an admissible node family for every positive size -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

lemma regular_angle_mem_Ico (n : ℕ) (hn : 0 < n) (i : Fin n) :
    2 * Real.pi * ((i.val : ℝ) / (n : ℝ)) ∈ Set.Ico 0 (2 * Real.pi) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hiR : (i.val : ℝ) < n := by exact_mod_cast i.isLt
  have hpi : (0 : ℝ) < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  constructor
  · exact mul_nonneg hpi.le (div_nonneg (Nat.cast_nonneg _) hnR.le)
  · have hdiv : (i.val : ℝ) / (n : ℝ) < 1 := (div_lt_one hnR).mpr hiR
    simpa only [mul_one] using mul_lt_mul_of_pos_left hdiv hpi

lemma regularPoint_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (regularPoint n) := by
  intro i j hij
  have hangle := Circle.exp_injOn_Ico
    (a := 0) (b := 2 * Real.pi) (by simp)
    (regular_angle_mem_Ico n hn i) (regular_angle_mem_Ico n hn j) hij
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hquot : (i.val : ℝ) / (n : ℝ) = (j.val : ℝ) / (n : ℝ) :=
    mul_left_cancel₀ hpi hangle
  have hval : (i.val : ℝ) = (j.val : ℝ) := (div_left_inj' hnR).mp hquot
  apply Fin.ext
  exact_mod_cast hval

/-- The canonical regular polygon, with its distinctness proved rather than assumed. -/
def regularNodes (n : ℕ) (hn : 0 < n) : NodeFamily n where
  point := regularPoint n
  injective := regularPoint_injective n hn

lemma regularNodes_isRegularRotation (n : ℕ) (hn : 0 < n) :
    IsRegularRotation (regularNodes n hn) := by
  exact ⟨1, Equiv.refl _, fun i => (one_mul _).symm⟩

@[simp] lemma regularPoint_zero (n : ℕ) (hn : 0 < n) :
    regularPoint n ⟨0, hn⟩ = 1 := by
  simp [regularPoint]

end

end UnitCircleInterpolation
