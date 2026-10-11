/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.PeakLocalInverse
import UnitCircleInterpolation.AngularMinimum
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Equioscillation at an actual angular minimum

If one actual gap height is below the current maximum, the nonsingular
Jacobian obtained by deleting that row supplies a direction decreasing every
other height. The omitted height stays below the old maximum by continuity.
A sufficiently small admissible perturbation then decreases the finite maximum.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Topology
open Filter Set

namespace UnitCircleInterpolation

noncomputable section

variable {d : ℕ}

/-- A strictly negative real derivative gives strict decrease immediately to the right. -/
lemma eventually_lt_at_zero_of_hasDerivAt_neg {f : ℝ → ℝ} {f' : ℝ}
    (hf : HasDerivAt f f' 0) (hf' : f' < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f t < f 0 := by
  have hslope := hf.tendsto_slope_zero_right.eventually_lt_const hf'
  filter_upwards [hslope, self_mem_nhdsWithin] with t ht hpos
  simp only [Set.mem_Ioi] at hpos
  simp only [zero_add, smul_eq_mul] at ht
  have hdiff : f t - f 0 < 0 := neg_of_mul_neg_right ht (le_of_lt (inv_pos.mpr hpos))
  linarith

/-- A direction lowering every row except a strictly submaximal one lowers the finite maximum. -/
theorem exists_finite_height_descent
    (H : (Fin d → ℝ) → Fin (d + 1) → ℝ)
    (L : (Fin d → ℝ) →L[ℝ] (Fin (d + 1) → ℝ))
    (s : Set (Fin d → ℝ)) (hs : IsOpen s) (u : Fin d → ℝ) (hu : u ∈ s)
    (hH : HasFDerivAt H L u) (M : ℝ) (hbound : ∀ i, H u i ≤ M)
    (omitted : Fin (d + 1)) (homitted : H u omitted < M)
    (v : Fin d → ℝ) (hdir : ∀ i, i ≠ omitted → L v i < 0) :
    ∃ w ∈ s, ∀ i, H w i < M := by
  let p : ℝ → (Fin d → ℝ) := fun t => u + t • v
  have hp : HasDerivAt p v 0 := by
    simpa [p] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
  have hp0 : p 0 = u := by simp [p]
  have hrows : ∀ i : Fin (d + 1), ∀ᶠ t in 𝓝[>] (0 : ℝ), H (p t) i < M := by
    intro i
    have hHi : HasFDerivAt (fun w => H w i)
        ((ContinuousLinearMap.proj i).comp L) u :=
      by
        simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
          ((ContinuousLinearMap.proj i : (Fin (d + 1) → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp u hH)
    have hcomp : HasDerivAt (fun t => H (p t) i) (L v i) 0 := by
      simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using
        hHi.comp_hasDerivAt_of_eq 0 hp hp0.symm
    by_cases hi : i = omitted
    · subst i
      have hevent := hcomp.continuousAt.eventually_lt_const (by simpa [hp0] using homitted)
      exact hevent.filter_mono nhdsWithin_le_nhds
    · have hevent := eventually_lt_at_zero_of_hasDerivAt_neg hcomp (hdir i hi)
      exact hevent.mono fun t ht => ht.trans_le (by simpa [hp0] using hbound i)
  have hsEvent₀ : ∀ᶠ t in 𝓝 (0 : ℝ), p t ∈ s :=
    hp.continuousAt (hs.mem_nhds (by simpa [hp0] using hu))
  have hsEvent : ∀ᶠ t in 𝓝[>] (0 : ℝ), p t ∈ s :=
    hsEvent₀.filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht, hrows_t⟩ := (hsEvent.and (Filter.eventually_all.mpr hrows)).exists
  exact ⟨p t, ht, hrows_t⟩

/-- The actual height differential after deleting one chosen row. -/
def deletedHeightDerivative (hsize : 2 ≤ d + 1) (u : Fin d → ℝ)
    (omitted : Fin (d + 1)) : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  (ContinuousLinearMap.pi (fun i : Fin d => ContinuousLinearMap.proj (omitted.succAbove i))).comp
    (fderiv ℝ (parameterOrderedHeightMap hsize) u)

lemma deletedHeightDerivative_apply (hsize : 2 ≤ d + 1) (u v : Fin d → ℝ)
    (omitted : Fin (d + 1)) (i : Fin d) :
    deletedHeightDerivative hsize u omitted v i =
      fderiv ℝ (parameterOrderedHeightMap hsize) u v (omitted.succAbove i) := rfl

lemma deletedHeightJacobian_mulVec (hsize : 2 ≤ d + 1) (u v : Fin d → ℝ)
    (omitted : Fin (d + 1)) :
    ((parameterHeightJacobian hsize u).submatrix omitted.succAbove id).mulVec v =
      deletedHeightDerivative hsize u omitted v := by
  have hm : LinearMap.toMatrix' (deletedHeightDerivative hsize u omitted).toLinearMap =
      (parameterHeightJacobian hsize u).submatrix omitted.succAbove id := by
    ext i j
    rfl
  rw [← hm]
  exact LinearMap.toMatrix'_mulVec (deletedHeightDerivative hsize u omitted).toLinearMap v

theorem deletedHeightDerivative_bijective (hsize : 2 ≤ d + 1) (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (omitted : Fin (d + 1)) :
    Function.Bijective (deletedHeightDerivative hsize u omitted) := by
  have hinj : Function.Injective (deletedHeightDerivative hsize u omitted) := by
    intro v w hvw
    apply Matrix.mulVec_injective_of_det_ne_zero
      (parameterHeightJacobian_deleted_det_ne_zero u hu hsize omitted)
    simpa only [deletedHeightJacobian_mulVec] using hvw
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- Every chosen deleted-row family admits a common strictly decreasing actual direction. -/
theorem exists_decreasing_actual_height_direction (hsize : 2 ≤ d + 1) (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (omitted : Fin (d + 1)) :
    ∃ v : Fin d → ℝ, ∀ i, i ≠ omitted →
      fderiv ℝ (parameterOrderedHeightMap hsize) u v i = -1 := by
  obtain ⟨v, hv⟩ := (deletedHeightDerivative_bijective hsize u hu omitted).2 (fun _ => -1)
  refine ⟨v, ?_⟩
  intro i hi
  obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
  exact congrFun hv j

/-- Every actual ordered gap height at a global angular minimum reaches the literal maximum. -/
theorem parameterOrderedHeight_eq_amplification_of_minimum (hsize : 2 ≤ d + 1)
    (u : angularParameterDomain d)
    (hmin : ∀ v : angularParameterDomain d,
      angularParameterAmplification hsize u ≤ angularParameterAmplification hsize v)
    (i : Fin (d + 1)) :
    parameterOrderedHeight hsize i u.val = angularParameterAmplification hsize u := by
  apply le_antisymm (parameterOrderedHeight_le_angularParameterAmplification hsize u i)
  by_contra hnot
  have hi : parameterOrderedHeight hsize i u.val < angularParameterAmplification hsize u :=
    lt_of_not_ge hnot
  obtain ⟨v, hv⟩ := exists_decreasing_actual_height_direction hsize u.val u.property i
  have hH : HasFDerivAt (parameterOrderedHeightMap hsize)
      (fderiv ℝ (parameterOrderedHeightMap hsize) u.val) u.val := by
    exact (hasFDerivAt_parameterOrderedHeightMap_of_mem_domain u.val u.property hsize).differentiableAt.hasFDerivAt
  obtain ⟨w, hw, hrows⟩ := exists_finite_height_descent
    (parameterOrderedHeightMap hsize) (fderiv ℝ (parameterOrderedHeightMap hsize) u.val)
    (angularParameterDomain d) (isOpen_angularParameterDomain d) u.val u.property hH
    (angularParameterAmplification hsize u)
    (fun j => parameterOrderedHeight_le_angularParameterAmplification hsize u j) i hi v
    (fun j hj => by rw [hv j hj]; norm_num)
  have hless : angularParameterAmplification hsize ⟨w, hw⟩ < angularParameterAmplification hsize u := by
    rw [angularParameterAmplification_eq_orderedHeightMaximum]
    exact (Finset.sup'_lt_iff _).mpr (fun j _ => hrows j)
  exact (not_lt_of_ge (hmin ⟨w, hw⟩)) hless

/-- A global minimum of the literal full-circle objective has equal actual gap heights. -/
theorem equal_parameterOrderedHeights_of_minimum (hsize : 2 ≤ d + 1)
    (u : angularParameterDomain d)
    (hmin : ∀ v : angularParameterDomain d,
      angularParameterAmplification hsize u ≤ angularParameterAmplification hsize v) :
    ∀ i, parameterOrderedHeight hsize i u.val = parameterOrderedHeight hsize 0 u.val := by
  intro i
  exact (parameterOrderedHeight_eq_amplification_of_minimum hsize u hmin i).trans
    (parameterOrderedHeight_eq_amplification_of_minimum hsize u hmin 0).symm

end

end UnitCircleInterpolation
