/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.CyclicRolle
import Mathlib.Topology.Order.Compact

/-!
# A strict interval maximum from a unique critical point

This is a generic calculus bridge. The caller must establish the actual
critical-point uniqueness and an interior value above the endpoint level.
The maximum is obtained from compactness, then identified with the unique
critical point. No maximizer or minimizer property is assumed of that point.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

/-- Evidence for a unique strict maximum on an actual closed interval. -/
structure StrictIntervalPeak (f : ℝ → ℝ) (a b peak : ℝ) : Prop where
  mem_Ioo : peak ∈ Set.Ioo a b
  hasDerivAt_zero : HasDerivAt f 0 peak
  isMaxOn : IsMaxOn f (Set.Icc a b) peak
  eq_iff : ∀ x ∈ Set.Icc a b, f x = f peak ↔ x = peak

lemma StrictIntervalPeak.isLocalMax {f : ℝ → ℝ} {a b peak : ℝ}
    (hpeak : StrictIntervalPeak f a b peak) : IsLocalMax f peak :=
  hpeak.isMaxOn.isLocalMax (Icc_mem_nhds hpeak.mem_Ioo.1 hpeak.mem_Ioo.2)

lemma StrictIntervalPeak.lt_of_ne {f : ℝ → ℝ} {a b peak x : ℝ}
    (hpeak : StrictIntervalPeak f a b peak) (hx : x ∈ Set.Icc a b) (hne : x ≠ peak) :
    f x < f peak := by
  apply lt_of_le_of_ne (hpeak.isMaxOn hx)
  intro heq
  exact hne ((hpeak.eq_iff x hx).mp heq)

lemma StrictIntervalPeak.second_deriv_neg {f : ℝ → ℝ} {a b peak : ℝ}
    (hpeak : StrictIntervalPeak f a b peak) (hcont : ContinuousOn f (Set.Icc a b))
    (hne : deriv (deriv f) peak ≠ 0) : deriv (deriv f) peak < 0 :=
  second_deriv_neg_of_localMax hpeak.isLocalMax
    (hcont.continuousAt (Icc_mem_nhds hpeak.mem_Ioo.1 hpeak.mem_Ioo.2))
    hpeak.hasDerivAt_zero.deriv hne

/-- Compactness and an interior overshoot turn uniqueness of critical points
into a unique strict maximum. The common endpoint level can be `1` for a node
gap, or `0` for the larger interval between adjacent zeros. -/
theorem strict_interval_peak_of_unique_critical {f : ℝ → ℝ} {a b peak level : ℝ}
    (hab : a < b) (hcont : ContinuousOn f (Set.Icc a b))
    (hdiff : DifferentiableOn ℝ f (Set.Ioo a b))
    (ha : f a = level) (hb : f b = level)
    (hunique : ∀ x ∈ Set.Ioo a b, deriv f x = 0 → x = peak)
    (hovershoot : ∃ x ∈ Set.Ioo a b, level < f x) :
    StrictIntervalPeak f a b peak ∧ level < f peak := by
  have hinterior (x : ℝ) (hx : x ∈ Set.Icc a b) (hxlevel : level < f x) :
      x ∈ Set.Ioo a b := by
    have hxa : x ≠ a := by
      intro heq
      rw [heq, ha] at hxlevel
      exact (lt_irrefl _) hxlevel
    have hxb : x ≠ b := by
      intro heq
      rw [heq, hb] at hxlevel
      exact (lt_irrefl _) hxlevel
    exact ⟨lt_of_le_of_ne hx.1 hxa.symm, lt_of_le_of_ne hx.2 hxb⟩
  obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Set.Icc a b).Nonempty from ⟨a, le_rfl, hab.le⟩) hcont
  obtain ⟨x, hx, hxlevel⟩ := hovershoot
  have hmlevel : level < f m := hxlevel.trans_le (hmax (Set.Ioo_subset_Icc_self hx))
  have hminterior := hinterior m hm hmlevel
  have hmlocal := hmax.isLocalMax (Icc_mem_nhds hminterior.1 hminterior.2)
  have hmdiff := hdiff.differentiableAt (Ioo_mem_nhds hminterior.1 hminterior.2)
  have hmzero : deriv f m = 0 := hmlocal.hasDerivAt_eq_zero hmdiff.hasDerivAt
  have hmpeak := hunique m hminterior hmzero
  subst m
  refine ⟨⟨hminterior, ?_, hmax, ?_⟩, hmlevel⟩
  · simpa only [hmzero] using hmdiff.hasDerivAt
  · intro y hy
    constructor
    · intro hyeq
      have hylevel : level < f y := by rwa [hyeq]
      have hyinterior := hinterior y hy hylevel
      have hymax : IsMaxOn f (Set.Icc a b) y := by
        intro z hz
        rw [hyeq]
        exact hmax hz
      have hylocal := hymax.isLocalMax (Icc_mem_nhds hyinterior.1 hyinterior.2)
      have hydiff := hdiff.differentiableAt (Ioo_mem_nhds hyinterior.1 hyinterior.2)
      exact hunique y hyinterior (hylocal.hasDerivAt_eq_zero hydiff.hasDerivAt)
    · rintro rfl
      rfl

/-- The node-gap specialization with the literal endpoint values `1`. -/
theorem strict_gap_peak_of_unique_critical {f : ℝ → ℝ} {a b peak : ℝ}
    (hab : a < b) (hcont : ContinuousOn f (Set.Icc a b))
    (hdiff : DifferentiableOn ℝ f (Set.Ioo a b))
    (ha : f a = 1) (hb : f b = 1)
    (hunique : ∀ x ∈ Set.Ioo a b, deriv f x = 0 → x = peak)
    (hovershoot : ∃ x ∈ Set.Ioo a b, 1 < f x) :
    StrictIntervalPeak f a b peak ∧ 1 < f peak :=
  strict_interval_peak_of_unique_critical hab hcont hdiff ha hb hunique hovershoot

end

end UnitCircleInterpolation
