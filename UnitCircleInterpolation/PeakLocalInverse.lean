/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.PeakHeightDerivative
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Local inverses of the actual height-difference map

The already proved actual Jacobian determinant gives a continuous linear
equivalence. The smooth inverse function theorem then supplies a local inverse
whose source lies in the admissible angular domain. Global injectivity and
properness are separate results.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ContDiff

namespace UnitCircleInterpolation

noncomputable section

variable {d : ℕ}

theorem contDiffAt_parameterAdjacentHeightDifferences_of_mem_domain (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) :
    ContDiffAt ℝ ∞ (parameterAdjacentHeightDifferences hsize) u := by
  exact contDiffAt_pi.mpr (fun i =>
    (contDiffAt_parameterOrderedHeight_of_mem_domain u hu hsize i.succ).sub
      (contDiffAt_parameterOrderedHeight_of_mem_domain u hu hsize i.castSucc))

lemma parameterAdjacentHeightJacobian_mulVec (hsize : 2 ≤ d + 1)
    (u v : Fin d → ℝ) :
    (parameterAdjacentHeightJacobian hsize u).mulVec v =
      fderiv ℝ (parameterAdjacentHeightDifferences hsize) u v := by
  have hm : LinearMap.toMatrix'
      (fderiv ℝ (parameterAdjacentHeightDifferences hsize) u).toLinearMap =
        parameterAdjacentHeightJacobian hsize u := by
    ext i j
    rfl
  rw [← hm]
  exact LinearMap.toMatrix'_mulVec
    (fderiv ℝ (parameterAdjacentHeightDifferences hsize) u).toLinearMap v

theorem fderiv_parameterAdjacentHeightDifferences_bijective (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) :
    Function.Bijective (fderiv ℝ (parameterAdjacentHeightDifferences hsize) u) := by
  have hinj : Function.Injective
      (fderiv ℝ (parameterAdjacentHeightDifferences hsize) u) := by
    intro v w hvw
    apply Matrix.mulVec_injective_of_det_ne_zero
      (parameterAdjacentHeightJacobian_det_ne_zero u hu hsize)
    simpa only [parameterAdjacentHeightJacobian_mulVec] using hvw
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- The literal actual differential, packaged as a continuous linear equivalence. -/
def heightDifferenceDerivativeEquiv (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) :
    (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearEquiv.ofBijective
    (fderiv ℝ (parameterAdjacentHeightDifferences hsize) u)
    (LinearMap.ker_eq_bot.mpr
      (fderiv_parameterAdjacentHeightDifferences_bijective u hu hsize).1)
    (LinearMap.range_eq_top.mpr
      (fderiv_parameterAdjacentHeightDifferences_bijective u hu hsize).2)

lemma heightDifferenceDerivativeEquiv_coe (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) :
    (heightDifferenceDerivativeEquiv u hu hsize :
      (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) =
      fderiv ℝ (parameterAdjacentHeightDifferences hsize) u :=
  ContinuousLinearEquiv.coe_ofBijective _ _ _

lemma hasFDerivAt_heightDifferenceDerivativeEquiv (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) :
    HasFDerivAt (parameterAdjacentHeightDifferences hsize)
      (heightDifferenceDerivativeEquiv u hu hsize :
        (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) u := by
  rw [heightDifferenceDerivativeEquiv_coe,
    fderiv_parameterAdjacentHeightDifferences_of_mem_domain u hu]
  exact hasFDerivAt_parameterAdjacentHeightDifferences_of_mem_domain u hu hsize

/-- An actual local inverse chart restricted to the admissible angular domain. -/
def heightDifferenceLocalChart (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) :
    OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ) :=
  ((contDiffAt_parameterAdjacentHeightDifferences_of_mem_domain u hu hsize).toOpenPartialHomeomorph
    (parameterAdjacentHeightDifferences hsize)
    (hasFDerivAt_heightDifferenceDerivativeEquiv u hu hsize) (by norm_num)).restrOpen
      (angularParameterDomain d) (isOpen_angularParameterDomain d)

@[simp] lemma heightDifferenceLocalChart_coe (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) :
    (heightDifferenceLocalChart u hu hsize : (Fin d → ℝ) → (Fin d → ℝ)) =
      parameterAdjacentHeightDifferences hsize := rfl

lemma mem_heightDifferenceLocalChart_source (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) :
    u ∈ (heightDifferenceLocalChart u hu hsize).source := by
  exact ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _, hu⟩

lemma heightDifferenceLocalChart_source_subset (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) :
    (heightDifferenceLocalChart u hu hsize).source ⊆ angularParameterDomain d :=
  fun _ hx => hx.2

lemma heightDifferenceLocalChart_left_inv (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1)
    (v : Fin d → ℝ) (hv : v ∈ (heightDifferenceLocalChart u hu hsize).source) :
    (heightDifferenceLocalChart u hu hsize).symm
      (parameterAdjacentHeightDifferences hsize v) = v :=
  (heightDifferenceLocalChart u hu hsize).left_inv hv

lemma heightDifferenceLocalChart_right_inv (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1)
    (y : Fin d → ℝ) (hy : y ∈ (heightDifferenceLocalChart u hu hsize).target) :
    parameterAdjacentHeightDifferences hsize
      ((heightDifferenceLocalChart u hu hsize).symm y) = y :=
  (heightDifferenceLocalChart u hu hsize).right_inv hy

/-- The actual adjacent-height difference map on its admissible domain. -/
def heightDifferenceMap (hsize : 2 ≤ d + 1) (u : angularParameterDomain d) : Fin d → ℝ :=
  parameterAdjacentHeightDifferences hsize u.val

theorem isLocalHomeomorph_heightDifferenceMap (hsize : 2 ≤ d + 1) :
    IsLocalHomeomorph (heightDifferenceMap hsize) := by
  intro u
  let S : TopologicalSpace.Opens (Fin d → ℝ) :=
    ⟨angularParameterDomain d, isOpen_angularParameterDomain d⟩
  have hS : Nonempty S := ⟨u⟩
  let e := heightDifferenceLocalChart u.val u.property hsize
  refine ⟨e.subtypeRestr hS, ?_, ?_⟩
  · simpa only [OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using
      mem_heightDifferenceLocalChart_source u.val u.property hsize
  · rfl

theorem continuous_heightDifferenceMap (hsize : 2 ≤ d + 1) :
    Continuous (heightDifferenceMap hsize) :=
  (isLocalHomeomorph_heightDifferenceMap hsize).continuous

end

end UnitCircleInterpolation
