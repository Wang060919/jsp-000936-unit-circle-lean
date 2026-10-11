/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.GapCritical
import UnitCircleInterpolation.PeakUniqueness

/-!
# Strict peaks of the actual ordinary signed gap interpolants

The zeros are constructed in the other node gaps, and their saturated cyclic
interlacing supplies critical-point uniqueness. An enclosing interval between
zeros has endpoint value zero and contains a selected node of value one. Its
strict maximum therefore restricts to the selected node gap and exceeds one.
The first ordinary gap uses a translated last root, including `n = 2`.

These are actual gap-interpolant peak statements; they do not assert the final
classification of optimal node configurations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ} {hn : 0 < n}

private lemma ordinary_gap_rolle (angles : CyclicAngles n hn) (cut : Fin n)
    (hcut : 0 < cut.val) :
    ∃ peak, peak ∈ ordinaryGap angles cut hcut ∧
      deriv (sineInterpolant angles.angle (gapCoefficient cut)) peak = 0 := by
  have hab : angles.angle (gapPredecessor cut) < angles.angle cut :=
    angles.strictMono (show gapPredecessor cut < cut from by
      change cut.val - 1 < cut.val
      omega)
  apply exists_deriv_eq_zero hab
    (continuous_sineInterpolant angles.angle (gapCoefficient cut)).continuousOn
  rw [gapInterpolant_at_node, gapInterpolant_at_node,
    gapCoefficient_at_predecessor cut hcut, gapCoefficient_at_cut]

private lemma gap_derivative_polynomial_ne_zero (angles : CyclicAngles n hn)
    (cut : Fin n) {r : ℝ}
    (hr : sineInterpolant angles.angle (gapCoefficient cut) r = 0) :
    cayleyOperator (n - 1) (interpolantPolynomial angles.angle (gapCoefficient cut)) ≠ 0 := by
  apply cayleyOperator_interpolant_ne_zero_of_ne angles.angle (gapCoefficient cut)
    (angles.angle cut) r
  rw [hr, gapInterpolant_at_node, gapCoefficient_at_cut]
  norm_num

private lemma ordinary_peak_from_enclosing_zeros (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (cut : Fin n) (hcut : 0 < cut.val) {a b peak : ℝ}
    (ha : a < angles.angle (gapPredecessor cut)) (hb : angles.angle cut < b)
    (haz : sineInterpolant angles.angle (gapCoefficient cut) a = 0)
    (hbz : sineInterpolant angles.angle (gapCoefficient cut) b = 0)
    (hpeak : peak ∈ ordinaryGap angles cut hcut)
    (hz : deriv (sineInterpolant angles.angle (gapCoefficient cut)) peak = 0)
    (hunique : ∀ x ∈ Set.Ioo a b,
      deriv (sineInterpolant angles.angle (gapCoefficient cut)) x = 0 → x = peak) :
    StrictIntervalPeak (sineInterpolant angles.angle (gapCoefficient cut))
      (angles.angle (gapPredecessor cut)) (angles.angle cut) peak ∧
      1 < sineInterpolant angles.angle (gapCoefficient cut) peak ∧
      deriv (deriv (sineInterpolant angles.angle (gapCoefficient cut))) peak < 0 := by
  have hab : a < b := ha.trans (hpeak.1.trans (hpeak.2.trans hb))
  have hnode : angles.angle (gapPredecessor cut) ∈ Set.Ioo a b :=
    ⟨ha, hpeak.1.trans (hpeak.2.trans hb)⟩
  have hnodeValue : sineInterpolant angles.angle (gapCoefficient cut)
      (angles.angle (gapPredecessor cut)) = 1 := by
    rw [gapInterpolant_at_node, gapCoefficient_at_predecessor cut hcut]
  obtain ⟨houter, _⟩ := strict_interval_peak_of_unique_critical hab
    (continuous_sineInterpolant angles.angle (gapCoefficient cut)).continuousOn
    (differentiable_sineInterpolant angles.angle (gapCoefficient cut)).differentiableOn
    haz hbz hunique ⟨_, hnode, by rw [hnodeValue]; norm_num⟩
  have hsubset : Set.Icc (angles.angle (gapPredecessor cut)) (angles.angle cut) ⊆
      Set.Icc a b := by
    intro x hx
    exact ⟨ha.le.trans hx.1, hx.2.trans hb.le⟩
  have hinner : StrictIntervalPeak (sineInterpolant angles.angle (gapCoefficient cut))
      (angles.angle (gapPredecessor cut)) (angles.angle cut) peak :=
    ⟨hpeak, houter.hasDerivAt_zero, fun x hx => houter.isMaxOn (hsubset hx),
      fun x hx => houter.eq_iff x (hsubset hx)⟩
  have hgt : 1 < sineInterpolant angles.angle (gapCoefficient cut) peak := by
    rw [← hnodeValue]
    exact houter.lt_of_ne (Set.Ioo_subset_Icc_self hnode) (ne_of_lt hpeak.1)
  have hturn := ordinaryGap_mem_Ioo angles cut hcut hpeak
  have hnondegenerate := gapInterpolant_critical_non_degenerate angles hsize cut hcut
    peak ⟨hturn.1.le, hturn.2⟩ hz
  exact ⟨hinner, hgt, hinner.second_deriv_neg
    (continuous_sineInterpolant angles.angle (gapCoefficient cut)).continuousOn
    hnondegenerate⟩

/-- Ordinary cuts after the first gap have a unique strict peak, exceeding one
and with negative second derivative, on the literal closed node gap. -/
theorem exists_ordinaryGap_strict_peak_of_two_le_cut (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (cut : Fin n) (hcut : 2 ≤ cut.val) :
    ∃ peak, StrictIntervalPeak (sineInterpolant angles.angle (gapCoefficient cut))
      (angles.angle (gapPredecessor cut)) (angles.angle cut) peak ∧
      1 < sineInterpolant angles.angle (gapCoefficient cut) peak ∧
      deriv (deriv (sineInterpolant angles.angle (gapCoefficient cut))) peak < 0 := by
  have hcutpos : 0 < cut.val := by omega
  have hp : 0 < n - 1 := by omega
  obtain ⟨root, hmono, hloc, hbound, hroot⟩ :=
    exists_gapInterpolant_ordered_cyclic_zeros_with_locations angles hsize cut hcutpos
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
  have hP := gap_derivative_polynomial_ne_zero angles cut (hroot ⟨0, hp⟩)
  obtain ⟨critical, _, _, _, _, hcritical⟩ :=
    sineInterpolant_cyclic_critical_interlacing hsize angles.angle (gapCoefficient cut)
      hP root hmono hbound hroot
  obtain ⟨peak, hpeak, hz⟩ := ordinary_gap_rolle angles cut hcutpos
  have hpeakArc : peak ∈ cyclicRootArc hp root (2 * Real.pi) i := by
    rw [cyclicRootArc, dif_pos hinext]
    exact ⟨hleft.trans hpeak.1, hpeak.2.trans hrightRoot⟩
  have heq := hcritical i peak hpeakArc hz
  refine ⟨peak, ordinary_peak_from_enclosing_zeros angles hsize cut hcutpos
    hleft hrightRoot (hroot i) (hroot j) hpeak hz ?_⟩
  intro x hx hxzero
  have hxarc : x ∈ cyclicRootArc hp root (2 * Real.pi) i := by
    rw [cyclicRootArc, dif_pos hinext]
    exact hx
  exact (hcritical i x hxarc hxzero).trans heq.symm

/-- The first ordinary gap also has a strict peak above one, including the
single-root cyclic case `n = 2`. -/
theorem exists_ordinaryGap_strict_peak_of_cut_eq_one (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (cut : Fin n) (hcut : cut.val = 1) :
    ∃ peak, StrictIntervalPeak (sineInterpolant angles.angle (gapCoefficient cut))
      (angles.angle (gapPredecessor cut)) (angles.angle cut) peak ∧
      1 < sineInterpolant angles.angle (gapCoefficient cut) peak ∧
      deriv (deriv (sineInterpolant angles.angle (gapCoefficient cut))) peak < 0 := by
  have hcutpos : 0 < cut.val := by omega
  have hp : 0 < n - 1 := by omega
  let first : Fin (n - 1) := ⟨0, hp⟩
  let last : Fin (n - 1) := lastNodeIndex hp
  obtain ⟨root, hmono, hloc, hbound, hroot⟩ :=
    exists_gapInterpolant_ordered_cyclic_zeros_with_locations angles hsize cut hcutpos
  have hfirstIndex : otherGapIndex cut first = cut := by
    apply Fin.ext
    simp only [otherGapIndex, first, Fin.val_mk, hcut, Nat.sub_self,
      Nat.not_lt_zero, if_false]
  have hfirstRoot : angles.angle cut < root first := by
    have h := (hloc first).1
    rwa [hfirstIndex] at h
  have hfirst_le_last : root first ≤ root last :=
    hmono.monotone (show first ≤ last from Nat.zero_le last.val)
  have hlast_final : ¬last.val + 1 < n - 1 := by
    dsimp only [last, lastNodeIndex]
    omega
  have hpredZero : angles.angle (gapPredecessor cut) = 0 := by
    have hpred : gapPredecessor cut = ⟨0, hn⟩ := by
      apply Fin.ext
      simp only [gapPredecessor, Fin.val_mk, hcut, Nat.sub_self]
    rw [hpred, angles.first_eq_zero]
  have hleft : root last - 2 * Real.pi < angles.angle (gapPredecessor cut) := by
    rw [hpredZero]
    linarith [(hbound last).2]
  have hleftRoot : sineInterpolant angles.angle (gapCoefficient cut)
      (root last - 2 * Real.pi) = 0 := by
    apply (sineInterpolant_add_two_pi_eq_zero_iff angles.angle (gapCoefficient cut)
      (root last - 2 * Real.pi)).mp
    simpa only [sub_add_cancel] using hroot last
  have hP := gap_derivative_polynomial_ne_zero angles cut (hroot first)
  obtain ⟨critical, _, _, _, _, hcritical⟩ :=
    sineInterpolant_cyclic_critical_interlacing hsize angles.angle (gapCoefficient cut)
      hP root hmono hbound hroot
  obtain ⟨peak, hpeak, hz⟩ := ordinary_gap_rolle angles cut hcutpos
  have hpeakpos : 0 < peak := by simpa only [hpredZero] using hpeak.1
  have hpeakArc : peak ∈ cyclicRootArc hp root (2 * Real.pi) last := by
    rw [cyclicRootArc, dif_neg hlast_final]
    exact ⟨⟨hpeakpos.le, hpeak.2.trans (angles.lt_two_pi cut)⟩,
      Or.inr (hpeak.2.trans hfirstRoot)⟩
  have heq := hcritical last peak hpeakArc hz
  refine ⟨peak, ordinary_peak_from_enclosing_zeros angles hsize cut hcutpos
    hleft hfirstRoot hleftRoot (hroot first) hpeak hz ?_⟩
  intro x hx hxzero
  by_cases hxnonneg : 0 ≤ x
  · have hxarc : x ∈ cyclicRootArc hp root (2 * Real.pi) last := by
      rw [cyclicRootArc, dif_neg hlast_final]
      exact ⟨⟨hxnonneg, hx.2.trans (hbound first).2⟩, Or.inr hx.2⟩
    exact (hcritical last x hxarc hxzero).trans heq.symm
  · have hxnegative : x < 0 := lt_of_not_ge hxnonneg
    have hxplus_gt_last : root last < x + 2 * Real.pi := by linarith [hx.1]
    have hxarc : x + 2 * Real.pi ∈ cyclicRootArc hp root (2 * Real.pi) last := by
      rw [cyclicRootArc, dif_neg hlast_final]
      exact ⟨⟨(hbound last).1.trans hxplus_gt_last.le, by linarith⟩,
        Or.inl hxplus_gt_last⟩
    have hxpluszero : deriv (sineInterpolant angles.angle (gapCoefficient cut))
        (x + 2 * Real.pi) = 0 := by
      rw [deriv_sineInterpolant] at hxzero ⊢
      exact (sineInterpolantDerivative_add_two_pi_eq_zero_iff angles.angle
        (gapCoefficient cut) x).mpr hxzero
    have hxpluseq := (hcritical last _ hxarc hxpluszero).trans heq.symm
    have hpeak_lt_last : peak < root last :=
      (hpeak.2.trans hfirstRoot).trans_le hfirst_le_last
    exact False.elim (by linarith)

/-- Every positive ordinary cut has a unique strict interior peak on its
literal node interval, with value above one and negative second derivative. -/
theorem exists_ordinaryGap_strict_peak (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (cut : Fin n) (hcut : 0 < cut.val) :
    ∃ peak, StrictIntervalPeak (sineInterpolant angles.angle (gapCoefficient cut))
      (angles.angle (gapPredecessor cut)) (angles.angle cut) peak ∧
      1 < sineInterpolant angles.angle (gapCoefficient cut) peak ∧
      deriv (deriv (sineInterpolant angles.angle (gapCoefficient cut))) peak < 0 := by
  by_cases hfirst : cut.val = 1
  · exact exists_ordinaryGap_strict_peak_of_cut_eq_one angles hsize cut hfirst
  · exact exists_ordinaryGap_strict_peak_of_two_le_cut angles hsize cut (by omega)

end

end UnitCircleInterpolation
