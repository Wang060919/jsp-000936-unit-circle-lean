/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.PeakOrder

/-!
# Critical-point uniqueness in the actual selected cyclic gap

The actual zero lists put every point of the selected node gap in a single
cyclic root arc. Saturated critical interlacing then identifies any two
critical points there. This is stronger than uniqueness of the maximum value
and supplies the branch identification needed for the implicit function theorem.
The first ordinary gap and the final wrap gap use the last cyclic root arc,
including the one-root case `n = 2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ} {hn : 0 < n}

/-- Two critical points in the actual selected ordinary gap coincide. -/
lemma ordinaryGap_critical_unique (angles : CyclicAngles n hn) (hsize : 2 ≤ n)
    (cut : Fin n) (hcut : 0 < cut.val) {x y : ℝ}
    (hx : x ∈ ordinaryGap angles cut hcut) (hy : y ∈ ordinaryGap angles cut hcut)
    (hzx : deriv (sineInterpolant angles.angle (gapCoefficient cut)) x = 0)
    (hzy : deriv (sineInterpolant angles.angle (gapCoefficient cut)) y = 0) : x = y := by
  have hp : 0 < n - 1 := by omega
  obtain ⟨root, hmono, hloc, hbound, hroot⟩ :=
    exists_gapInterpolant_ordered_cyclic_zeros_with_locations angles hsize cut hcut
  have hP : cayleyOperator (n - 1)
      (interpolantPolynomial angles.angle (gapCoefficient cut)) ≠ 0 := by
    apply cayleyOperator_interpolant_ne_zero_of_ne angles.angle (gapCoefficient cut)
      (angles.angle cut) (root ⟨0, hp⟩)
    rw [hroot, gapInterpolant_at_node, gapCoefficient_at_cut]
    norm_num
  obtain ⟨critical, _, _, _, _, hcritical⟩ :=
    sineInterpolant_cyclic_critical_interlacing hsize angles.angle (gapCoefficient cut)
      hP root hmono hbound hroot
  by_cases hfirst : cut.val = 1
  · let first : Fin (n - 1) := ⟨0, hp⟩
    let last : Fin (n - 1) := lastNodeIndex hp
    have hfirstIndex : otherGapIndex cut first = cut := by
      apply Fin.ext
      simp only [otherGapIndex, first, Fin.val_mk, hfirst, Nat.sub_self,
        Nat.not_lt_zero, if_false]
    have hfirstRoot : angles.angle cut < root first := by
      have h := (hloc first).1
      rwa [hfirstIndex] at h
    have hlast_final : ¬last.val + 1 < n - 1 := by
      dsimp only [last, lastNodeIndex]
      omega
    have hpredZero : angles.angle (gapPredecessor cut) = 0 := by
      have hpred : gapPredecessor cut = ⟨0, hn⟩ := by
        apply Fin.ext
        simp only [gapPredecessor, Fin.val_mk, hfirst, Nat.sub_self]
      rw [hpred, angles.first_eq_zero]
    have hmem (t : ℝ) (ht : t ∈ ordinaryGap angles cut hcut) :
        t ∈ cyclicRootArc hp root (2 * Real.pi) last := by
      rw [cyclicRootArc, dif_neg hlast_final]
      have htpos : 0 < t := by simpa only [hpredZero] using ht.1
      exact ⟨⟨htpos.le, ht.2.trans (angles.lt_two_pi cut)⟩,
        Or.inr (ht.2.trans hfirstRoot)⟩
    exact (hcritical last x (hmem x hx) hzx).trans
      (hcritical last y (hmem y hy) hzy).symm
  · have hcut2 : 2 ≤ cut.val := by omega
    let i : Fin (n - 1) := ⟨cut.val - 2, by have := cut.isLt; omega⟩
    have hinext : i.val + 1 < n - 1 := by dsimp [i]; have := cut.isLt; omega
    let j : Fin (n - 1) := ⟨i.val + 1, hinext⟩
    have hipivot : i.val < cut.val - 1 := by dsimp [i]; omega
    have hival : (otherGapIndex cut i).val = i.val := by
      simp only [otherGapIndex, if_pos hipivot]
    have hrightIndex : (otherGapIndex cut i).val + 1 < n := by
      rw [hival]; dsimp [i]; have := cut.isLt; omega
    have hright : cyclicGapRight angles (otherGapIndex cut i) =
        angles.angle (gapPredecessor cut) := by
      rw [cyclicGapRight, dif_pos hrightIndex]
      congr 1
      apply Fin.ext
      simp only [Fin.val_mk, gapPredecessor]
      rw [hival]
      dsimp [i]
      omega
    have hjpivot : ¬j.val < cut.val - 1 := by dsimp [j, i]; omega
    have hjindex : otherGapIndex cut j = cut := by
      apply Fin.ext
      simp only [otherGapIndex, Fin.val_mk, if_neg hjpivot]
      dsimp [j, i]
      omega
    have hleft : root i < angles.angle (gapPredecessor cut) := by
      have h := (hloc i).2
      rwa [hright] at h
    have hrightRoot : angles.angle cut < root j := by
      have h := (hloc j).1
      rwa [hjindex] at h
    have hmem (t : ℝ) (ht : t ∈ ordinaryGap angles cut hcut) :
        t ∈ cyclicRootArc hp root (2 * Real.pi) i := by
      rw [cyclicRootArc, dif_pos hinext]
      exact ⟨hleft.trans ht.1, ht.2.trans hrightRoot⟩
    exact (hcritical i x (hmem x hx) hzx).trans
      (hcritical i y (hmem y hy) hzy).symm

/-- Two critical points in the actual final wrap gap coincide. -/
lemma wrapGap_critical_unique (angles : CyclicAngles n hn) (hsize : 2 ≤ n)
    {x y : ℝ} (hx : x ∈ wrapGap angles) (hy : y ∈ wrapGap angles)
    (hzx : deriv (sineInterpolant angles.angle wrapCoefficient) x = 0)
    (hzy : deriv (sineInterpolant angles.angle wrapCoefficient) y = 0) : x = y := by
  have hp : 0 < n - 1 := by omega
  let first : Fin (n - 1) := ⟨0, hp⟩
  let last : Fin (n - 1) := lastNodeIndex hp
  obtain ⟨root, hmono, hloc, hbound, hroot⟩ :=
    exists_wrapInterpolant_ordered_cyclic_zeros_with_locations angles hsize
  have hlast_succ : last.val + 1 = n - 1 := by
    dsimp only [last, lastNodeIndex]
    omega
  have hlast_node :
      (⟨last.val + 1, by have := last.isLt; omega⟩ : Fin n) = lastNodeIndex hn := by
    apply Fin.ext
    exact hlast_succ
  have hlast_lt_node : root last < angles.angle (lastNodeIndex hn) := by
    have h := (hloc last).2
    rwa [hlast_node] at h
  have hlast_final : ¬last.val + 1 < n - 1 := by omega
  have hP : cayleyOperator (n - 1)
      (interpolantPolynomial angles.angle wrapCoefficient) ≠ 0 := by
    apply cayleyOperator_interpolant_ne_zero_of_ne angles.angle wrapCoefficient
      (angles.angle (lastNodeIndex hn)) (root first)
    rw [wrapInterpolant_at_last, hroot first]
    norm_num
  obtain ⟨critical, _, _, _, _, hcritical⟩ :=
    sineInterpolant_cyclic_critical_interlacing hsize angles.angle wrapCoefficient
      hP root hmono hbound hroot
  have hmem (t : ℝ) (ht : t ∈ wrapGap angles) :
      t ∈ cyclicRootArc hp root (2 * Real.pi) last := by
    rw [cyclicRootArc, dif_neg hlast_final]
    exact ⟨⟨(angles.nonneg _).trans ht.1.le, ht.2⟩,
      Or.inl (hlast_lt_node.trans ht.1)⟩
  exact (hcritical last x (hmem x hx) hzx).trans
    (hcritical last y (hmem y hy) hzy).symm

/-- Critical-point uniqueness covers both actual cyclic gap types. -/
lemma gapInterpolant_critical_unique (angles : CyclicAngles n hn) (hsize : 2 ≤ n)
    (cut : Fin n) {x y : ℝ}
    (hx : x ∈ gapInterval angles cut) (hy : y ∈ gapInterval angles cut)
    (hzx : deriv (gapInterpolant angles cut) x = 0)
    (hzy : deriv (gapInterpolant angles cut) y = 0) : x = y := by
  by_cases hcut : cut.val = 0
  · rw [gapInterval_of_zero angles cut hcut] at hx hy
    rw [gapInterpolant_of_zero angles cut hcut] at hzx hzy
    exact wrapGap_critical_unique angles hsize hx hy hzx hzy
  · have hpos : 0 < cut.val := by omega
    rw [gapInterval_of_pos angles cut hpos] at hx hy
    rw [gapInterpolant_of_pos angles cut hpos] at hzx hzy
    exact ordinaryGap_critical_unique angles hsize cut hpos hx hy hzx hzy

/-- Every own-gap critical point is the actual compactly chosen peak. -/
lemma eq_gapPeak_of_deriv_eq_zero (angles : CyclicAngles n hn) (hsize : 2 ≤ n)
    (cut : Fin n) {t : ℝ} (ht : t ∈ gapInterval angles cut)
    (hz : deriv (gapInterpolant angles cut) t = 0) : t = gapPeak angles hsize cut :=
  gapInterpolant_critical_unique angles hsize cut ht
    (gapPeak_mem_gapInterval angles hsize cut) hz
    (gapPeak_strictIntervalPeak angles hsize cut).hasDerivAt_zero.deriv

/-- The same uniqueness uses the physical increasing gap order. -/
lemma eq_orderedPeak_of_deriv_eq_zero (angles : CyclicAngles n hn) (hsize : 2 ≤ n)
    (k : Fin n) {t : ℝ} (ht : t ∈ Set.Ioo (angles.angle k) (cyclicGapRight angles k))
    (hz : deriv (orderedGapInterpolant angles k) t = 0) :
    t = orderedPeak angles hsize k := by
  apply eq_gapPeak_of_deriv_eq_zero angles hsize (physicalGapCut hn k) ?_ hz
  rw [gapInterval, gapLeft_physicalGapCut, gapRight_physicalGapCut]
  exact ht

end

end UnitCircleInterpolation
