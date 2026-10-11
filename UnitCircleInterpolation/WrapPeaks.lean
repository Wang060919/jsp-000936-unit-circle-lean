/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.GapCritical
import UnitCircleInterpolation.PeakUniqueness

/-!
# Unique nondegenerate peaks of the actual wrap-gap interpolant

The other node gaps supply all `n - 1` zeros. Their cyclic critical-point
interlacing identifies the Rolle point in the selected wrap gap. The larger
interval between the last zero and the next copy of the first zero has endpoint
values zero and contains a node with value one. Its actual compact maximum
therefore gives strictness and an overshoot above one on the selected gap.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ} {hn : 0 < n}

/-- Every actual wrap-gap signed interpolant has a unique strict interior peak,
with value above one and strictly negative second derivative, also for `n = 2`. -/
theorem exists_wrapInterpolant_strict_peak (angles : CyclicAngles n hn) (hsize : 2 ≤ n) :
    ∃ peak : ℝ,
      StrictIntervalPeak (sineInterpolant angles.angle wrapCoefficient)
        (angles.angle (lastNodeIndex hn)) (2 * Real.pi) peak ∧
      1 < sineInterpolant angles.angle wrapCoefficient peak ∧
      deriv (deriv (sineInterpolant angles.angle wrapCoefficient)) peak < 0 := by
  have hp : 0 < n - 1 := by omega
  let first : Fin (n - 1) := ⟨0, hp⟩
  let last : Fin (n - 1) := lastNodeIndex hp
  let f : ℝ → ℝ := sineInterpolant angles.angle wrapCoefficient
  obtain ⟨root, hmono, hlocations, hbound, hroot⟩ :=
    exists_wrapInterpolant_ordered_cyclic_zeros_with_locations angles hsize
  have hfirst_pos : 0 < root first := by
    have h := (hlocations first).1
    simpa only [first, Fin.val_mk, angles.first_eq_zero] using h
  have hlast_succ : last.val + 1 = n - 1 := by
    dsimp only [last, lastNodeIndex]
    omega
  have hlast_node :
      (⟨last.val + 1, by have := last.isLt; omega⟩ : Fin n) = lastNodeIndex hn := by
    apply Fin.ext
    exact hlast_succ
  have hlast_lt_node : root last < angles.angle (lastNodeIndex hn) := by
    have h := (hlocations last).2
    rwa [hlast_node] at h
  have hfirst_le_last : root first ≤ root last :=
    hmono.monotone (show first ≤ last from Nat.zero_le last.val)
  have hlast_final : ¬last.val + 1 < n - 1 := by omega
  have hnode : f (angles.angle (lastNodeIndex hn)) = 1 := wrapInterpolant_at_last angles
  have hturn : f (2 * Real.pi) = 1 := wrapInterpolant_at_two_pi angles
  have hcont : Continuous f := continuous_sineInterpolant angles.angle wrapCoefficient
  have hdiff : Differentiable ℝ f := differentiable_sineInterpolant angles.angle wrapCoefficient
  have hP : cayleyOperator (n - 1) (interpolantPolynomial angles.angle wrapCoefficient) ≠ 0 := by
    apply cayleyOperator_interpolant_ne_zero_of_ne angles.angle wrapCoefficient
      (angles.angle (lastNodeIndex hn)) (root first)
    rw [wrapInterpolant_at_last, hroot first]
    norm_num
  obtain ⟨critical, _hinj, _hcriticalBound, _hcriticalZero, _hcriticalArc, hcriticalUnique⟩ :=
    sineInterpolant_cyclic_critical_interlacing hsize angles.angle wrapCoefficient hP
      root hmono hbound hroot
  obtain ⟨peak, hpeakGap, hpeakZero⟩ := exists_hasDerivAt_eq_zero
    (angles.lt_two_pi (lastNodeIndex hn)) hcont.continuousOn (hnode.trans hturn.symm)
    (fun t _ => (hdiff t).hasDerivAt)
  have hpeakArc : peak ∈ cyclicRootArc hp root (2 * Real.pi) last := by
    rw [cyclicRootArc, dif_neg hlast_final]
    exact ⟨⟨(angles.nonneg _).trans hpeakGap.1.le, hpeakGap.2⟩,
      Or.inl (hlast_lt_node.trans hpeakGap.1)⟩
  have hcritical_peak : critical last = peak :=
    (hcriticalUnique last peak hpeakArc hpeakZero).symm
  have harc_unique (t : ℝ) (ht : t ∈ cyclicRootArc hp root (2 * Real.pi) last)
      (hz : deriv f t = 0) : t = peak :=
    (hcriticalUnique last t ht hz).trans hcritical_peak
  have houter_unique (t : ℝ) (ht : t ∈ Set.Ioo (root last) (root first + 2 * Real.pi))
      (hz : deriv f t = 0) : t = peak := by
    by_cases htturn : t < 2 * Real.pi
    · apply harc_unique t
      · rw [cyclicRootArc, dif_neg hlast_final]
        exact ⟨⟨(hbound last).1.trans ht.1.le, htturn⟩, Or.inl ht.1⟩
      · exact hz
    · have hreduce_nonneg : 0 ≤ t - 2 * Real.pi := by linarith
      have hreduce_first : t - 2 * Real.pi < root first := by linarith [ht.2]
      have hreduceArc : t - 2 * Real.pi ∈ cyclicRootArc hp root (2 * Real.pi) last := by
        rw [cyclicRootArc, dif_neg hlast_final]
        exact ⟨⟨hreduce_nonneg, hreduce_first.trans (hbound first).2⟩, Or.inr hreduce_first⟩
      have hreduceZero : deriv f (t - 2 * Real.pi) = 0 := by
        change deriv (sineInterpolant angles.angle wrapCoefficient) (t - 2 * Real.pi) = 0
        change deriv (sineInterpolant angles.angle wrapCoefficient) t = 0 at hz
        rw [deriv_sineInterpolant] at hz ⊢
        apply (sineInterpolantDerivative_add_two_pi_eq_zero_iff angles.angle wrapCoefficient
          (t - 2 * Real.pi)).mp
        simpa only [sub_add_cancel] using hz
      have hreduce_eq := harc_unique _ hreduceArc hreduceZero
      have hfirst_lt_peak : root first < peak :=
        hfirst_le_last.trans_lt (hlast_lt_node.trans hpeakGap.1)
      rw [hreduce_eq] at hreduce_first
      exact False.elim ((not_lt_of_ge hfirst_lt_peak.le) hreduce_first)
  have hnodeOuter : angles.angle (lastNodeIndex hn) ∈
      Set.Ioo (root last) (root first + 2 * Real.pi) := by
    constructor
    · exact hlast_lt_node
    · have h := angles.lt_two_pi (lastNodeIndex hn)
      linarith
  have houterRoot : f (root first + 2 * Real.pi) = 0 :=
    (sineInterpolant_add_two_pi_eq_zero_iff angles.angle wrapCoefficient (root first)).mpr
      (hroot first)
  obtain ⟨houterPeak, _hpositive⟩ := strict_interval_peak_of_unique_critical
    (hnodeOuter.1.trans hnodeOuter.2) hcont.continuousOn hdiff.differentiableOn
    (hroot last) houterRoot houter_unique
    (show ∃ x ∈ Set.Ioo (root last) (root first + 2 * Real.pi), (0 : ℝ) < f x from
      ⟨_, hnodeOuter, by rw [hnode]; norm_num⟩)
  have hvalue : 1 < f peak := by
    have h := houterPeak.lt_of_ne (Set.Ioo_subset_Icc_self hnodeOuter) (ne_of_lt hpeakGap.1)
    rwa [hnode] at h
  have hsubset : Set.Icc (angles.angle (lastNodeIndex hn)) (2 * Real.pi) ⊆
      Set.Icc (root last) (root first + 2 * Real.pi) := by
    intro t ht
    constructor
    · exact hlast_lt_node.le.trans ht.1
    · have hfirst_nonneg := hfirst_pos.le
      linarith [ht.2]
  have hpeak : StrictIntervalPeak f (angles.angle (lastNodeIndex hn)) (2 * Real.pi) peak := by
    refine ⟨hpeakGap, houterPeak.hasDerivAt_zero, ?_, ?_⟩
    · intro t ht
      exact houterPeak.isMaxOn (hsubset ht)
    · intro t ht
      exact houterPeak.eq_iff t (hsubset ht)
  have hpeakBound : peak ∈ Set.Ico 0 (2 * Real.pi) :=
    ⟨(angles.nonneg _).trans hpeakGap.1.le, hpeakGap.2⟩
  have hsecond := wrapInterpolant_critical_non_degenerate angles hsize peak hpeakBound hpeakZero
  exact ⟨peak, hpeak, hvalue, hpeak.second_deriv_neg hcont.continuousOn hsecond⟩

end

end UnitCircleInterpolation
