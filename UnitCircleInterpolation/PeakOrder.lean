/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.GapWronskian

/-!
# Peaks in their physical order around the circle

The gap cuts are ordered as `1, ..., n - 1, 0`. The final entry is the actual
positive wrap-gap interpolant. Every peak lies strictly after its left node
and before the next node, or before `2π` in the final gap.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ} {hn : 0 < n}

/-- The gap after a physical nodal index, with the final index sent to cut zero. -/
def physicalGapCut (hn : 0 < n) (k : Fin n) : Fin n :=
  if h : k.val + 1 < n then ⟨k.val + 1, h⟩ else ⟨0, hn⟩

lemma physicalGapCut_of_next_lt (hn : 0 < n) (k : Fin n) (h : k.val + 1 < n) :
    physicalGapCut hn k = ⟨k.val + 1, h⟩ := by
  simp only [physicalGapCut, dif_pos h]

lemma physicalGapCut_of_last (hn : 0 < n) (k : Fin n) (h : k.val + 1 = n) :
    physicalGapCut hn k = ⟨0, hn⟩ := by
  simp [physicalGapCut, h]

lemma physicalGapCut_injective (hn : 0 < n) : Function.Injective (physicalGapCut hn) := by
  intro k l heq
  apply Fin.ext
  have hkn := k.isLt
  have hln := l.isLt
  by_cases hk : k.val + 1 < n
  · by_cases hl : l.val + 1 < n
    · rw [physicalGapCut_of_next_lt hn k hk, physicalGapCut_of_next_lt hn l hl] at heq
      have hv : k.val + 1 = l.val + 1 := congrArg Fin.val heq
      omega
    · have hl' : l.val + 1 = n := by omega
      rw [physicalGapCut_of_next_lt hn k hk, physicalGapCut_of_last hn l hl'] at heq
      have hv : k.val + 1 = 0 := congrArg Fin.val heq
      omega
  · by_cases hl : l.val + 1 < n
    · have hk' : k.val + 1 = n := by omega
      rw [physicalGapCut_of_last hn k hk', physicalGapCut_of_next_lt hn l hl] at heq
      have hv : 0 = l.val + 1 := congrArg Fin.val heq
      omega
    · omega

lemma physicalGapCut_surjective (hn : 0 < n) : Function.Surjective (physicalGapCut hn) :=
  Finite.surjective_of_injective (physicalGapCut_injective hn)

def physicalGapEquiv (hn : 0 < n) : Fin n ≃ Fin n :=
  Equiv.ofBijective (physicalGapCut hn)
    ⟨physicalGapCut_injective hn, physicalGapCut_surjective hn⟩

lemma gapLeft_physicalGapCut (angles : CyclicAngles n hn) (k : Fin n) :
    gapLeft angles (physicalGapCut hn k) = angles.angle k := by
  by_cases hk : k.val + 1 < n
  · have hpred : gapPredecessor (⟨k.val + 1, hk⟩ : Fin n) = k := by
      apply Fin.ext
      simp [gapPredecessor]
    rw [physicalGapCut_of_next_lt hn k hk, gapLeft_of_pos angles _ (by simp), hpred]
  · have hlast : k = lastNodeIndex hn := by
      apply Fin.ext
      change k.val = n - 1
      have hkn := k.isLt
      omega
    have hkn : k.val + 1 = n := by have h := k.isLt; omega
    rw [physicalGapCut_of_last hn k hkn, gapLeft_zero, hlast]

lemma gapRight_physicalGapCut (angles : CyclicAngles n hn) (k : Fin n) :
    gapRight angles (physicalGapCut hn k) = cyclicGapRight angles k := by
  by_cases hk : k.val + 1 < n
  · rw [physicalGapCut_of_next_lt hn k hk, gapRight_of_pos angles _ (by simp)]
    simp only [cyclicGapRight, dif_pos hk]
  · have hkn : k.val + 1 = n := by have h := k.isLt; omega
    rw [physicalGapCut_of_last hn k hkn, gapRight_zero]
    simp only [cyclicGapRight, dif_neg hk]

def orderedGapInterpolant (angles : CyclicAngles n hn) (k : Fin n) : ℝ → ℝ :=
  gapInterpolant angles (physicalGapCut hn k)

def orderedPeak (angles : CyclicAngles n hn) (hsize : 2 ≤ n) (k : Fin n) : ℝ :=
  gapPeak angles hsize (physicalGapCut hn k)

def orderedHeight (angles : CyclicAngles n hn) (hsize : 2 ≤ n) (k : Fin n) : ℝ :=
  gapHeight angles hsize (physicalGapCut hn k)

lemma orderedPeak_mem_node_gap (angles : CyclicAngles n hn) (hsize : 2 ≤ n) (k : Fin n) :
    orderedPeak angles hsize k ∈ Set.Ioo (angles.angle k) (cyclicGapRight angles k) := by
  have h := gapPeak_mem_Ioo angles hsize (physicalGapCut hn k)
  rw [gapLeft_physicalGapCut, gapRight_physicalGapCut] at h
  exact h

lemma cyclicGapRight_le_angle_of_lt (angles : CyclicAngles n hn) {k l : Fin n}
    (hkl : k < l) : cyclicGapRight angles k ≤ angles.angle l := by
  have hk : k.val + 1 < n := by
    have hklval : k.val < l.val := hkl
    have hln := l.isLt
    omega
  rw [cyclicGapRight, dif_pos hk]
  exact angles.strictMono.monotone (show (⟨k.val + 1, hk⟩ : Fin n) ≤ l from hkl)

lemma orderedPeak_strictMono (angles : CyclicAngles n hn) (hsize : 2 ≤ n) :
    StrictMono (orderedPeak angles hsize) := by
  intro k l hkl
  exact ((orderedPeak_mem_node_gap angles hsize k).2.trans_le
    (cyclicGapRight_le_angle_of_lt angles hkl)).trans
      (orderedPeak_mem_node_gap angles hsize l).1

lemma orderedPeak_mem_Ioo (angles : CyclicAngles n hn) (hsize : 2 ≤ n) (k : Fin n) :
    orderedPeak angles hsize k ∈ Set.Ioo 0 (2 * Real.pi) := by
  have h := gapPeak_mem_turn angles hsize (physicalGapCut hn k)
  exact h

lemma orderedPeak_hasDerivAt_zero (angles : CyclicAngles n hn) (hsize : 2 ≤ n)
    (k : Fin n) : HasDerivAt (orderedGapInterpolant angles k) 0 (orderedPeak angles hsize k) :=
  (gapPeak_strictIntervalPeak angles hsize (physicalGapCut hn k)).hasDerivAt_zero

lemma orderedHeight_eq_value (angles : CyclicAngles n hn) (hsize : 2 ≤ n) (k : Fin n) :
    orderedHeight angles hsize k = orderedGapInterpolant angles k (orderedPeak angles hsize k) :=
  rfl

lemma one_lt_orderedHeight (angles : CyclicAngles n hn) (hsize : 2 ≤ n) (k : Fin n) :
    1 < orderedHeight angles hsize k :=
  one_lt_gapHeight angles hsize (physicalGapCut hn k)

lemma orderedPeak_second_deriv_neg (angles : CyclicAngles n hn) (hsize : 2 ≤ n)
    (k : Fin n) : deriv (deriv (orderedGapInterpolant angles k)) (orderedPeak angles hsize k) < 0 :=
  gapPeak_second_deriv_neg angles hsize (physicalGapCut hn k)

end

end UnitCircleInterpolation
