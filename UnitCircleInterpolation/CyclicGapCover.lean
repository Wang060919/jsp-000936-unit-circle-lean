/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.GapSigns

/-! # Coverage of the entire circle by its nodes and open cyclic gaps -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ} {hn : 0 < n}

/-- Every cyclic representative is an actual node or belongs to one of the actual
open node gaps. This includes the one-node configuration. -/
lemma CyclicAngles.exists_node_or_gap (angles : CyclicAngles n hn) (t : ℝ)
    (ht : t ∈ Set.Ico 0 (2 * Real.pi)) :
    (∃ i, t = angles.angle i) ∨
      (∃ cut : Fin n, ∃ hcut : 0 < cut.val, t ∈ ordinaryGap angles cut hcut) ∨
      t ∈ wrapGap angles := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun i => angles.angle i ≤ t)
  have hs : s.Nonempty := by
    refine ⟨⟨0, hn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [angles.first_eq_zero]
    exact ht.1
  let i : Fin n := s.max' hs
  have himem : i ∈ s := Finset.max'_mem s hs
  have hi : angles.angle i ≤ t := (Finset.mem_filter.mp himem).2
  by_cases heq : t = angles.angle i
  · exact Or.inl ⟨i, heq⟩
  · have hilower : angles.angle i < t := lt_of_le_of_ne hi (Ne.symm heq)
    by_cases hnext : i.val + 1 < n
    · let cut : Fin n := ⟨i.val + 1, hnext⟩
      have hcut : 0 < cut.val := by dsimp [cut]; omega
      have hpred : gapPredecessor cut = i := by
        apply Fin.ext
        simp [gapPredecessor, cut]
      have hupper : t < angles.angle cut := by
        by_contra h
        have hcutmem : cut ∈ s :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_lt.mp h⟩
        have hle : cut ≤ i := Finset.le_max' s cut hcutmem
        change i.val + 1 ≤ i.val at hle
        omega
      apply Or.inr
      apply Or.inl
      refine ⟨cut, hcut, ?_⟩
      change t ∈ Set.Ioo (angles.angle (gapPredecessor cut)) (angles.angle cut)
      rw [hpred]
      exact ⟨hilower, hupper⟩
    · have hilast : i = lastNodeIndex hn := by
        apply Fin.ext
        have hi_lt := i.isLt
        change i.val = n - 1
        omega
      apply Or.inr
      apply Or.inr
      change t ∈ Set.Ioo (angles.angle (lastNodeIndex hn)) (2 * Real.pi)
      rw [hilast] at hilower
      exact ⟨hilower, ht.2⟩

end

end UnitCircleInterpolation
