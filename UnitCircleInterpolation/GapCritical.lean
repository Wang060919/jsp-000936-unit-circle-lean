/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.GapZeros
import UnitCircleInterpolation.CircularSimpleRoots

/-!
# Nondegenerate critical points of the actual signed gap interpolants

The zeros used here are constructed by intermediate values in the other node
gaps. Cyclic Rolle then saturates the derivative-root bound. Nonzero values at
the selected gap nodes supply the nonconstant-function evidence, rather than
assuming the derivative polynomial is nonzero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ}

lemma sineInterpolant_critical_non_degenerate_of_ordered_zeros (hsize : 2 ≤ n)
    (θ : Fin n → ℝ) (c : Fin n → ℝ) (root : Fin (n - 1) → ℝ)
    (hmono : StrictMono root) (hbound : ∀ i, root i ∈ Set.Ico 0 (2 * Real.pi))
    (hroot : ∀ i, sineInterpolant θ c (root i) = 0) (a : ℝ)
    (ha : sineInterpolant θ c a ≠ 0) (t : ℝ) (ht : t ∈ Set.Ico 0 (2 * Real.pi))
    (hz : deriv (sineInterpolant θ c) t = 0) :
    deriv (deriv (sineInterpolant θ c)) t ≠ 0 := by
  let i : Fin (n - 1) := ⟨0, by omega⟩
  have hne : sineInterpolant θ c a ≠ sineInterpolant θ c (root i) := by
    rwa [hroot i]
  have hP := cayleyOperator_interpolant_ne_zero_of_ne θ c a (root i) hne
  obtain ⟨point, hinj, hpoint, hpointZero⟩ :=
    exists_sineInterpolant_cyclic_deriv_roots (by omega) θ c root hmono hbound hroot
  exact second_deriv_sineInterpolant_ne_zero_at_critical θ c hP
    point hinj hpoint hpointZero t ht hz

variable {hn : 0 < n}

/-- Every full-turn critical point of an ordinary signed gap interpolant is nondegenerate. -/
lemma gapInterpolant_critical_non_degenerate (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (cut : Fin n) (hcut : 0 < cut.val) (t : ℝ)
    (ht : t ∈ Set.Ico 0 (2 * Real.pi))
    (hz : deriv (sineInterpolant angles.angle (gapCoefficient cut)) t = 0) :
    deriv (deriv (sineInterpolant angles.angle (gapCoefficient cut))) t ≠ 0 := by
  obtain ⟨root, hmono, hbound, hroot⟩ :=
    exists_gapInterpolant_ordered_cyclic_zeros angles hsize cut hcut
  have ha : sineInterpolant angles.angle (gapCoefficient cut) (angles.angle cut) ≠ 0 := by
    rw [gapInterpolant_at_node, gapCoefficient_at_cut]
    norm_num
  exact sineInterpolant_critical_non_degenerate_of_ordered_zeros hsize _ _
    root hmono hbound hroot _ ha t ht hz

/-- The same nondegeneracy holds for the wrap gap, including both parities at the pole. -/
lemma wrapInterpolant_critical_non_degenerate (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (t : ℝ) (ht : t ∈ Set.Ico 0 (2 * Real.pi))
    (hz : deriv (sineInterpolant angles.angle wrapCoefficient) t = 0) :
    deriv (deriv (sineInterpolant angles.angle wrapCoefficient)) t ≠ 0 := by
  obtain ⟨root, hmono, hbound, hroot⟩ :=
    exists_wrapInterpolant_ordered_cyclic_zeros angles hsize
  have ha : sineInterpolant angles.angle wrapCoefficient
      (angles.angle (lastNodeIndex hn)) ≠ 0 := by
    rw [wrapInterpolant_at_last]
    norm_num
  exact sineInterpolant_critical_non_degenerate_of_ordered_zeros hsize _ _
    root hmono hbound hroot _ ha t ht hz

end

end UnitCircleInterpolation
