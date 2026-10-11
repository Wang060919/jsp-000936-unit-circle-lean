/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.AngularProperness
import UnitCircleInterpolation.AngularDomainTopology
import UnitCircleInterpolation.GenericGlobalInverse

/-!
# Global inversion of the actual circular height differences

The actual angular domain is convex and nonempty. Its actual difference map
is a proper local homeomorphism. The generic covering argument therefore gives
a global homeomorphism onto the entire real difference space, and in particular
exactly one normalized configuration with all its actual gap heights equal.
Identifying that configuration and proving minimizer classification are separate
steps.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {d : ℕ}

/-- The actual circular difference map is a global homeomorphism. -/
theorem isHomeomorph_heightDifferenceMap (hsize : 2 ≤ d + 1) :
    IsHomeomorph (heightDifferenceMap hsize) := by
  let : PreconnectedSpace (angularParameterDomain d) :=
    Subtype.preconnectedSpace (isPreconnected_angularParameterDomain d)
  let : Nonempty (angularParameterDomain d) :=
    ⟨⟨regularAngularParameters d, regularAngularParameters_mem_domain d⟩⟩
  exact euclideanTarget_isHomeomorph_of_localHomeomorph_of_proper
    (isLocalHomeomorph_heightDifferenceMap hsize) (isProperMap_heightDifferenceMap hsize)

theorem heightDifferenceMap_injective (hsize : 2 ≤ d + 1) :
    Function.Injective (heightDifferenceMap hsize) :=
  (isHomeomorph_heightDifferenceMap hsize).injective

theorem heightDifferenceMap_surjective (hsize : 2 ≤ d + 1) :
    Function.Surjective (heightDifferenceMap hsize) :=
  (isHomeomorph_heightDifferenceMap hsize).surjective

lemma heightDifferenceMap_eq_zero_iff (hsize : 2 ≤ d + 1)
    (u : angularParameterDomain d) :
    heightDifferenceMap hsize u = 0 ↔
      ∀ i, parameterOrderedHeight hsize i u.val = parameterOrderedHeight hsize 0 u.val := by
  change parameterAdjacentHeightDifferences hsize u.val = 0 ↔ _
  rw [← finiteHeightDifferences_parameterOrderedHeightMap]
  exact finiteHeightDifferences_eq_zero_iff (parameterOrderedHeightMap hsize u.val)

/-- Every prescribed real difference vector occurs at exactly one normalized node configuration. -/
theorem existsUnique_heightDifferenceMap_eq (hsize : 2 ≤ d + 1) (y : Fin d → ℝ) :
    ∃! u : angularParameterDomain d, heightDifferenceMap hsize u = y := by
  obtain ⟨u, hu⟩ := heightDifferenceMap_surjective hsize y
  exact ⟨u, hu, fun v hv => heightDifferenceMap_injective hsize (hv.trans hu.symm)⟩

/-- There is exactly one actual normalized configuration with equal heights. -/
theorem existsUnique_equal_parameterOrderedHeights (hsize : 2 ≤ d + 1) :
    ∃! u : angularParameterDomain d,
      ∀ i, parameterOrderedHeight hsize i u.val = parameterOrderedHeight hsize 0 u.val := by
  obtain ⟨u, hu, huniq⟩ := existsUnique_heightDifferenceMap_eq hsize 0
  exact ⟨u, (heightDifferenceMap_eq_zero_iff hsize u).mp hu,
    fun v hv => huniq v ((heightDifferenceMap_eq_zero_iff hsize v).mpr hv)⟩

end

end UnitCircleInterpolation
