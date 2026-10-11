/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.GapSigns
import UnitCircleInterpolation.InterpolantCalculus
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-!
# Ordered cyclic zeros of the actual signed gap interpolants

The nodal coefficients of each signed gap interpolant alternate on every
other cyclic gap. The intermediate value theorem therefore constructs one
zero in each of those `n - 1` open gaps. Their disjoint, cyclically ordered
locations give a strictly increasing list in `[0, 2π)`.

Both ordinary selected gaps and the final wrap gap are included. The wrap
endpoint uses the proved full-turn phase sign; no roots are assumed as input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ} {hn : 0 < n}

private lemma exists_zero_between_opposite_values (f : ℝ → ℝ)
    (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (hopposite : f b = -f a) (hne : f a ≠ 0) :
    ∃ t, t ∈ Set.Ioo a b ∧ f t = 0 := by
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hright : 0 < f b := by rw [hopposite]; linarith
    exact intermediate_value_Ioo hab.le hf.continuousOn ⟨hneg, hright⟩
  · have hright : f b < 0 := by rw [hopposite]; linarith
    exact intermediate_value_Ioo' hab.le hf.continuousOn ⟨hright, hpos⟩

/-- Each other ordinary gap contains a zero of the ordinary selected-gap interpolant. -/
lemma exists_gapInterpolant_zero_on_other_gap (angles : CyclicAngles n hn)
    (cut l : Fin n) (hl : 0 < l.val) (hlcut : l ≠ cut) :
    ∃ t, t ∈ ordinaryGap angles l hl ∧
      sineInterpolant angles.angle (gapCoefficient cut) t = 0 := by
  have hpred : (gapPredecessor l).val + 1 = l.val := by
    change l.val - 1 + 1 = l.val
    omega
  have hlt : gapPredecessor l < l := by
    show l.val - 1 < l.val
    omega
  apply exists_zero_between_opposite_values
    (sineInterpolant angles.angle (gapCoefficient cut))
    (continuous_sineInterpolant angles.angle (gapCoefficient cut))
    (angles.strictMono hlt)
  · rw [gapInterpolant_at_node, gapInterpolant_at_node]
    exact gapCoefficient_consecutive_flip cut (gapPredecessor l) l hpred hlcut
  · rw [gapInterpolant_at_node]
    rcases gapCoefficient_eq_one_or_neg_one cut (gapPredecessor l) with h | h <;>
      rw [h] <;> norm_num

/-- The final open gap contains a zero of every ordinary selected-gap interpolant. -/
lemma exists_gapInterpolant_zero_on_wrapGap (angles : CyclicAngles n hn)
    (cut : Fin n) (hcut : 0 < cut.val) :
    ∃ t, t ∈ wrapGap angles ∧
      sineInterpolant angles.angle (gapCoefficient cut) t = 0 := by
  have hzero : sineInterpolant angles.angle (gapCoefficient cut) 0 =
      gapCoefficient cut (⟨0, hn⟩ : Fin n) := by
    rw [← angles.first_eq_zero, gapInterpolant_at_node]
  have htwo : sineInterpolant angles.angle (gapCoefficient cut) (2 * Real.pi) =
      -gapCoefficient cut (lastNodeIndex hn) := by
    have h := sineInterpolant_add_two_pi angles.angle (gapCoefficient cut) 0
    rw [zero_add, hzero, gapCoefficient_wrap_flip hn cut hcut] at h
    exact h
  apply exists_zero_between_opposite_values
    (sineInterpolant angles.angle (gapCoefficient cut))
    (continuous_sineInterpolant angles.angle (gapCoefficient cut))
    (angles.lt_two_pi (lastNodeIndex hn))
  · rw [htwo, gapInterpolant_at_node]
  · rw [gapInterpolant_at_node]
    rcases gapCoefficient_eq_one_or_neg_one cut (lastNodeIndex hn) with h | h <;>
      rw [h] <;> norm_num

/-- Every ordinary gap contains a zero when the selected gap is the wrap gap. -/
lemma exists_wrapInterpolant_zero_on_ordinaryGap (angles : CyclicAngles n hn)
    (l : Fin n) (hl : 0 < l.val) :
    ∃ t, t ∈ ordinaryGap angles l hl ∧
      sineInterpolant angles.angle wrapCoefficient t = 0 := by
  have hpred : (gapPredecessor l).val + 1 = l.val := by
    change l.val - 1 + 1 = l.val
    omega
  have hlt : gapPredecessor l < l := by
    show l.val - 1 < l.val
    omega
  apply exists_zero_between_opposite_values
    (sineInterpolant angles.angle wrapCoefficient)
    (continuous_sineInterpolant angles.angle wrapCoefficient)
    (angles.strictMono hlt)
  · rw [wrapInterpolant_at_node, wrapInterpolant_at_node]
    exact wrapCoefficient_consecutive_flip hn (gapPredecessor l) l hpred
  · rw [wrapInterpolant_at_node]
    rcases wrapCoefficient_eq_one_or_neg_one (gapPredecessor l) with h | h <;>
      rw [h] <;> norm_num

/-- The right endpoint of the cyclic gap after `j`, including `2π` after the last node. -/
def cyclicGapRight (angles : CyclicAngles n hn) (j : Fin n) : ℝ :=
  if hj : j.val + 1 < n then angles.angle ⟨j.val + 1, hj⟩ else 2 * Real.pi

private lemma cyclicGapRight_le_two_pi (angles : CyclicAngles n hn) (j : Fin n) :
    cyclicGapRight angles j ≤ 2 * Real.pi := by
  unfold cyclicGapRight
  split_ifs with hj
  · exact (angles.lt_two_pi _).le
  · exact le_rfl

private lemma cyclicGapRight_le_angle (angles : CyclicAngles n hn)
    {j l : Fin n} (hjl : j < l) : cyclicGapRight angles j ≤ angles.angle l := by
  have hval : j.val < l.val := hjl
  have hj : j.val + 1 < n := by have := l.isLt; omega
  rw [cyclicGapRight, dif_pos hj]
  exact angles.strictMono.monotone (show (⟨j.val + 1, hj⟩ : Fin n) ≤ l from hjl)

private lemma ordered_roots_from_cyclic_gaps (angles : CyclicAngles n hn)
    (f : ℝ → ℝ) (index : Fin (n - 1) → Fin n) (hindex : StrictMono index)
    (hz : ∀ k, ∃ t, t ∈ Set.Ioo (angles.angle (index k))
      (cyclicGapRight angles (index k)) ∧ f t = 0) :
    ∃ root : Fin (n - 1) → ℝ, StrictMono root ∧
      (∀ k, root k ∈ Set.Ioo (angles.angle (index k))
        (cyclicGapRight angles (index k))) ∧
      (∀ k, root k ∈ Set.Ico 0 (2 * Real.pi)) ∧ (∀ k, f (root k) = 0) := by
  classical
  let root : Fin (n - 1) → ℝ := fun k => Classical.choose (hz k)
  have hspec (k : Fin (n - 1)) : root k ∈
      Set.Ioo (angles.angle (index k)) (cyclicGapRight angles (index k)) ∧
      f (root k) = 0 := Classical.choose_spec (hz k)
  refine ⟨root, ?_, fun k => (hspec k).1, ?_, fun k => (hspec k).2⟩
  · intro k l hkl
    exact ((hspec k).1.2.trans_le (cyclicGapRight_le_angle angles (hindex hkl))).trans
      (hspec l).1.1
  · intro k
    exact ⟨(angles.nonneg (index k)).trans (hspec k).1.1.le,
      (hspec k).1.2.trans_le (cyclicGapRight_le_two_pi angles (index k))⟩

omit hn in
/-- Increasingly enumerate cyclic gaps while skipping the selected gap after `cut - 1`. -/
def otherGapIndex (cut : Fin n) (k : Fin (n - 1)) : Fin n :=
  ⟨if k.val < cut.val - 1 then k.val else k.val + 1, by
    clear hn
    split_ifs <;> have := k.isLt <;> omega⟩

omit hn in
private lemma otherGapIndex_strictMono (cut : Fin n) : StrictMono (otherGapIndex cut) := by
  intro k l hkl
  change (if k.val < cut.val - 1 then k.val else k.val + 1) <
    (if l.val < cut.val - 1 then l.val else l.val + 1)
  have hval : k.val < l.val := hkl
  split_ifs <;> omega

omit hn in
private lemma otherGapIndex_next_ne_cut (cut : Fin n) (k : Fin (n - 1)) :
    (otherGapIndex cut k).val + 1 ≠ cut.val := by
  change (if k.val < cut.val - 1 then k.val else k.val + 1) + 1 ≠ cut.val
  split_ifs <;> omega

/-- Ordinary selected-gap zeros retain their exact locations in the other cyclic gaps. -/
theorem exists_gapInterpolant_ordered_cyclic_zeros_with_locations
    (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (cut : Fin n) (hcut : 0 < cut.val) :
    ∃ root : Fin (n - 1) → ℝ, StrictMono root ∧
      (∀ k, root k ∈ Set.Ioo (angles.angle (otherGapIndex cut k))
        (cyclicGapRight angles (otherGapIndex cut k))) ∧
      (∀ k, root k ∈ Set.Ico 0 (2 * Real.pi)) ∧
      (∀ k, sineInterpolant angles.angle (gapCoefficient cut) (root k) = 0) := by
  apply ordered_roots_from_cyclic_gaps angles
    (sineInterpolant angles.angle (gapCoefficient cut))
    (otherGapIndex cut) (otherGapIndex_strictMono cut)
  intro k
  let j : Fin n := otherGapIndex cut k
  by_cases hj : j.val + 1 < n
  · let l : Fin n := ⟨j.val + 1, hj⟩
    have hl : 0 < l.val := by dsimp only [l]; omega
    have hlcut : l ≠ cut := by
      intro heq
      have heqval := congrArg Fin.val heq
      exact otherGapIndex_next_ne_cut cut k heqval
    have hpred : gapPredecessor l = j := by
      apply Fin.ext
      simp only [gapPredecessor, l]
      omega
    have hright : cyclicGapRight angles j = angles.angle l := by
      rw [cyclicGapRight, dif_pos hj]
    have hz := exists_gapInterpolant_zero_on_other_gap angles cut l hl hlcut
    unfold ordinaryGap at hz
    rw [hpred, ← hright] at hz
    exact hz
  · have hjlast : j = lastNodeIndex hn := by
      apply Fin.ext
      change j.val = n - 1
      have := j.isLt
      omega
    have hright : cyclicGapRight angles j = 2 * Real.pi := by
      rw [cyclicGapRight, dif_neg hj]
    change ∃ t, t ∈ Set.Ioo (angles.angle j) (cyclicGapRight angles j) ∧
      sineInterpolant angles.angle (gapCoefficient cut) t = 0
    rw [hright, hjlast]
    exact exists_gapInterpolant_zero_on_wrapGap angles cut hcut

/-- The signed wrap-gap zeros retain their exact adjacent-node locations. -/
theorem exists_wrapInterpolant_ordered_cyclic_zeros_with_locations
    (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) :
    ∃ root : Fin (n - 1) → ℝ, StrictMono root ∧
      (∀ k, root k ∈ Set.Ioo
        (angles.angle ⟨k.val, by have := k.isLt; omega⟩)
        (angles.angle ⟨k.val + 1, by have := k.isLt; omega⟩)) ∧
      (∀ k, root k ∈ Set.Ico 0 (2 * Real.pi)) ∧
      (∀ k, sineInterpolant angles.angle wrapCoefficient (root k) = 0) := by
  let index : Fin (n - 1) → Fin n := fun k => ⟨k.val, by have := k.isLt; omega⟩
  have hindex : StrictMono index := by
    intro k l hkl
    exact hkl
  have hz : ∀ k, ∃ t, t ∈ Set.Ioo (angles.angle (index k))
      (cyclicGapRight angles (index k)) ∧
      sineInterpolant angles.angle wrapCoefficient t = 0 := by
    intro k
    have hj : (index k).val + 1 < n := by have := k.isLt; dsimp only [index]; omega
    let l : Fin n := ⟨(index k).val + 1, hj⟩
    have hl : 0 < l.val := by dsimp only [l]; omega
    have hpred : gapPredecessor l = index k := by
      apply Fin.ext
      simp only [gapPredecessor, l]
      omega
    have hright : cyclicGapRight angles (index k) = angles.angle l := by
      rw [cyclicGapRight, dif_pos hj]
    have hzero := exists_wrapInterpolant_zero_on_ordinaryGap angles l hl
    unfold ordinaryGap at hzero
    rw [hpred, ← hright] at hzero
    exact hzero
  obtain ⟨root, hmono, hlocations, hbounds, hroots⟩ :=
    ordered_roots_from_cyclic_gaps angles
      (sineInterpolant angles.angle wrapCoefficient) index hindex hz
  refine ⟨root, hmono, ?_, hbounds, hroots⟩
  intro k
  have hj : k.val + 1 < n := by have := k.isLt; omega
  simpa only [index, cyclicGapRight, Fin.val_mk, dif_pos hj] using hlocations k

/-- A selected ordinary signed interpolant has `n - 1` distinct, increasing cyclic zeros. -/
theorem exists_gapInterpolant_ordered_cyclic_zeros (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (cut : Fin n) (hcut : 0 < cut.val) :
    ∃ root : Fin (n - 1) → ℝ, StrictMono root ∧
      (∀ k, root k ∈ Set.Ico 0 (2 * Real.pi)) ∧
      (∀ k, sineInterpolant angles.angle (gapCoefficient cut) (root k) = 0) := by
  obtain ⟨root, hmono, _hlocations, hbounds, hroots⟩ :=
    exists_gapInterpolant_ordered_cyclic_zeros_with_locations angles hsize cut hcut
  exact ⟨root, hmono, hbounds, hroots⟩

/-- The signed wrap-gap interpolant has one zero in every ordinary gap, in cyclic order. -/
theorem exists_wrapInterpolant_ordered_cyclic_zeros (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) :
    ∃ root : Fin (n - 1) → ℝ, StrictMono root ∧
      (∀ k, root k ∈ Set.Ico 0 (2 * Real.pi)) ∧
      (∀ k, sineInterpolant angles.angle wrapCoefficient (root k) = 0) := by
  obtain ⟨root, hmono, _hlocations, hbounds, hroots⟩ :=
    exists_wrapInterpolant_ordered_cyclic_zeros_with_locations angles hsize
  exact ⟨root, hmono, hbounds, hroots⟩

end

end UnitCircleInterpolation
