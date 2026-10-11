/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.AngularDomainTopology
import UnitCircleInterpolation.PeakHeightDerivative
import UnitCircleInterpolation.Symmetry
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Equal actual peak heights of the regular polygon

Rotation by any regular node permutes the literal complex cardinal family.
Translating each actual regular gap to the first gap therefore transports its
Lebesgue maximum. This includes the last gap, whose right endpoint is `2π`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace UnitCircleInterpolation

noncomputable section

lemma regularPoint_add {n : ℕ} [NeZero n] (i j : Fin n) :
    regularPoint n (i + j) = regularPoint n i * regularPoint n j := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  unfold regularPoint
  rw [← Circle.exp_add, Fin.val_add_eq_ite]
  by_cases h : n ≤ i.val + j.val
  · simp only [h, ↓reduceIte, Nat.cast_sub h, Nat.cast_add]
    have heq : 2 * Real.pi * (((i.val : ℝ) + j.val - n) / n) =
        (2 * Real.pi * (i.val / n) + 2 * Real.pi * (j.val / n)) - 2 * Real.pi := by
      field_simp
    rw [heq, Circle.exp_sub_two_pi]
  · simp only [h, ↓reduceIte, Nat.cast_add]
    congr 1
    ring

/-- The full literal Lebesgue function of regular nodes is invariant under
rotation by any node, with no assumption on the evaluation point. -/
theorem regular_lebesgueFunction_rotate {n : ℕ} (hn : 0 < n)
    (i : Fin n) (w : Circle) :
    lebesgueFunction (regularNodes n hn).coordinates
      ((regularPoint n i * w : Circle) : ℂ) =
      lebesgueFunction (regularNodes n hn).coordinates (w : ℂ) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let p : Equiv.Perm (Fin n) := Equiv.addLeft i
  have hcoord : ((regularNodes n hn).rotate (regularPoint n i)).coordinates =
      ((regularNodes n hn).reindex p).coordinates := by
    funext j
    change ((regularPoint n i : ℂ) * (regularPoint n j : ℂ)) =
      (regularPoint n (i + j) : ℂ)
    rw [regularPoint_add, Circle.coe_mul]
  have h := lebesgueFunction_rotate (regularNodes n hn) (regularPoint n i) w
  rw [hcoord, lebesgueFunction_reindex] at h
  exact h

theorem regular_lebesgueFunction_shift {n : ℕ} (hn : 0 < n)
    (i : Fin n) (t : ℝ) :
    lebesgueFunction (regularNodes n hn).coordinates
      (Circle.exp (t + 2 * Real.pi * ((i.val : ℝ) / n)) : ℂ) =
      lebesgueFunction (regularNodes n hn).coordinates (Circle.exp t : ℂ) := by
  rw [Circle.exp_add, mul_comm (Circle.exp t)]
  exact regular_lebesgueFunction_rotate hn i (Circle.exp t)

/-- The canonical normalized angular configuration of the regular polygon. -/
def regularCyclicAngles (d : ℕ) : CyclicAngles (d + 1) (Nat.succ_pos d) :=
  cyclicAnglesOfParameters (regularAngularParameters d)
    (regularAngularParameters_mem_domain d)

lemma regularCyclicAngles_angle (d : ℕ) (i : Fin (d + 1)) :
    (regularCyclicAngles d).angle i =
      2 * Real.pi * ((i.val : ℝ) / ((d + 1 : ℕ) : ℝ)) :=
  angularParameterAngles_regular d i

lemma regularCyclicAngles_coordinates (d : ℕ) :
    phaseNodes (regularCyclicAngles d).angle =
      (regularNodes (d + 1) (Nat.succ_pos d)).coordinates := by
  funext i
  change (Circle.exp ((regularCyclicAngles d).angle i) : ℂ) = _
  rw [regularCyclicAngles_angle]
  rfl

theorem regularCyclicAngles_isRegularRotation (d : ℕ) :
    IsRegularRotation (regularCyclicAngles d).toNodeFamily := by
  refine ⟨1, Equiv.refl _, ?_⟩
  intro i
  change Circle.exp ((regularCyclicAngles d).angle i) = 1 * regularPoint (d + 1) i
  rw [regularCyclicAngles_angle, one_mul]
  rfl

lemma regularCyclicGapRight (d : ℕ) (i : Fin (d + 1)) :
    cyclicGapRight (regularCyclicAngles d) i =
      2 * Real.pi * (((i.val : ℝ) + 1) / ((d + 1 : ℕ) : ℝ)) := by
  have hn : ((d + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  by_cases hi : i.val + 1 < d + 1
  · rw [cyclicGapRight, dif_pos hi, regularCyclicAngles_angle]
    simp only [Nat.cast_add, Nat.cast_one]
  · have heq : i.val + 1 = d + 1 := by have h := i.isLt; omega
    have heqR : (i.val : ℝ) + 1 = ((d + 1 : ℕ) : ℝ) := by exact_mod_cast heq
    rw [cyclicGapRight, dif_neg hi, heqR, div_self hn, mul_one]

variable {d : ℕ}

lemma regular_ordered_gap_translate (k : Fin (d + 1)) {t : ℝ}
    (ht : t ∈ Set.Ioo ((regularCyclicAngles d).angle k)
      (cyclicGapRight (regularCyclicAngles d) k)) :
    t - (regularCyclicAngles d).angle k ∈
      Set.Ioo ((regularCyclicAngles d).angle 0)
        (cyclicGapRight (regularCyclicAngles d) 0) := by
  rw [regularCyclicAngles_angle, regularCyclicGapRight] at ht ⊢
  simp only [Fin.val_zero, Nat.cast_zero, zero_div, mul_zero, zero_add]
  rw [regularCyclicAngles_angle]
  have heq : 2 * Real.pi * (((k.val : ℝ) + 1) / ((d + 1 : ℕ) : ℝ)) =
      2 * Real.pi * ((k.val : ℝ) / ((d + 1 : ℕ) : ℝ)) +
        2 * Real.pi * (1 / ((d + 1 : ℕ) : ℝ)) := by ring
  rw [heq] at ht
  rcases ht with ⟨ht₁, ht₂⟩
  constructor <;> linarith

lemma regular_ordered_gap_translate_back (k : Fin (d + 1)) {t : ℝ}
    (ht : t ∈ Set.Ioo ((regularCyclicAngles d).angle 0)
      (cyclicGapRight (regularCyclicAngles d) 0)) :
    t + (regularCyclicAngles d).angle k ∈
      Set.Ioo ((regularCyclicAngles d).angle k)
        (cyclicGapRight (regularCyclicAngles d) k) := by
  rw [regularCyclicAngles_angle, regularCyclicGapRight] at ht ⊢
  simp only [Fin.val_zero, Nat.cast_zero, zero_div, mul_zero, zero_add] at ht
  have heq : 2 * Real.pi * (((k.val : ℝ) + 1) / ((d + 1 : ℕ) : ℝ)) =
      2 * Real.pi * ((k.val : ℝ) / ((d + 1 : ℕ) : ℝ)) +
        2 * Real.pi * (1 / ((d + 1 : ℕ) : ℝ)) := by ring
  rw [heq]
  rcases ht with ⟨ht₁, ht₂⟩
  constructor <;> linarith

lemma regular_orderedHeight_eq_literal (hsize : 2 ≤ d + 1) (k : Fin (d + 1)) :
    orderedHeight (regularCyclicAngles d) hsize k =
      lebesgueFunction (regularNodes (d + 1) (Nat.succ_pos d)).coordinates
        (Circle.exp (orderedPeak (regularCyclicAngles d) hsize k) : ℂ) := by
  rw [orderedHeight, gapHeight_eq_lebesgueFunction, regularCyclicAngles_coordinates]
  rfl

lemma regular_literal_le_orderedHeight (hsize : 2 ≤ d + 1) (k : Fin (d + 1))
    {t : ℝ} (ht : t ∈ Set.Ioo ((regularCyclicAngles d).angle k)
      (cyclicGapRight (regularCyclicAngles d) k)) :
    lebesgueFunction (regularNodes (d + 1) (Nat.succ_pos d)).coordinates
      (Circle.exp t : ℂ) ≤ orderedHeight (regularCyclicAngles d) hsize k := by
  have hgap : t ∈ gapInterval (regularCyclicAngles d)
      (physicalGapCut (Nat.succ_pos d) k) := by
    rw [gapInterval, gapLeft_physicalGapCut, gapRight_physicalGapCut]
    exact ht
  rw [← regularCyclicAngles_coordinates, lebesgueFunction_on_gapInterval _ _ hgap]
  exact gapInterpolant_le_gapHeight _ hsize _ (Set.Ioo_subset_Icc_self hgap)

/-- Every actual regular-polygon gap has the same peak height, including the wrap gap. -/
theorem regular_orderedHeight_eq (hsize : 2 ≤ d + 1) (k : Fin (d + 1)) :
    orderedHeight (regularCyclicAngles d) hsize k =
      orderedHeight (regularCyclicAngles d) hsize 0 := by
  apply le_antisymm
  · rw [regular_orderedHeight_eq_literal]
    let t := orderedPeak (regularCyclicAngles d) hsize k - (regularCyclicAngles d).angle k
    have ht := regular_ordered_gap_translate k
      (orderedPeak_mem_node_gap (regularCyclicAngles d) hsize k)
    have hshift := regular_lebesgueFunction_shift (Nat.succ_pos d) k t
    rw [← regularCyclicAngles_angle] at hshift
    have heq : t + (regularCyclicAngles d).angle k =
        orderedPeak (regularCyclicAngles d) hsize k := by dsimp [t]; ring
    rw [heq] at hshift
    rw [hshift]
    exact regular_literal_le_orderedHeight hsize 0 ht
  · let t := orderedPeak (regularCyclicAngles d) hsize 0
    have ht := regular_ordered_gap_translate_back k
      (orderedPeak_mem_node_gap (regularCyclicAngles d) hsize 0)
    have hshift := regular_lebesgueFunction_shift (Nat.succ_pos d) k t
    rw [← regularCyclicAngles_angle] at hshift
    rw [regular_orderedHeight_eq_literal, ← hshift]
    exact regular_literal_le_orderedHeight hsize k ht

theorem regular_gapHeight_eq (hsize : 2 ≤ d + 1) (i j : Fin (d + 1)) :
    gapHeight (regularCyclicAngles d) hsize i =
      gapHeight (regularCyclicAngles d) hsize j := by
  obtain ⟨k, rfl⟩ := physicalGapCut_surjective (Nat.succ_pos d) i
  obtain ⟨l, rfl⟩ := physicalGapCut_surjective (Nat.succ_pos d) j
  exact (regular_orderedHeight_eq hsize k).trans (regular_orderedHeight_eq hsize l).symm

theorem parameterOrderedHeight_regular_eq (hsize : 2 ≤ d + 1) (i j : Fin (d + 1)) :
    parameterOrderedHeight hsize i (regularAngularParameters d) =
      parameterOrderedHeight hsize j (regularAngularParameters d) := by
  rw [parameterOrderedHeight_of_mem_domain _ (regularAngularParameters_mem_domain d),
    parameterOrderedHeight_of_mem_domain _ (regularAngularParameters_mem_domain d)]
  exact (regular_orderedHeight_eq hsize i).trans (regular_orderedHeight_eq hsize j).symm

/-- The actual height-difference map sends the canonical regular polygon to zero. -/
theorem parameterAdjacentHeightDifferences_regular_eq_zero (hsize : 2 ≤ d + 1) :
    parameterAdjacentHeightDifferences hsize (regularAngularParameters d) = 0 := by
  funext i
  change parameterOrderedHeight hsize i.succ (regularAngularParameters d) -
    parameterOrderedHeight hsize i.castSucc (regularAngularParameters d) = 0
  rw [parameterOrderedHeight_regular_eq hsize i.succ i.castSucc, sub_self]

end

end UnitCircleInterpolation
