/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.AngularCalculus
import UnitCircleInterpolation.PeakSensitivityDifferences
import UnitCircleInterpolation.PeakImplicit

/-!
# The actual differential of the circular gap-height map

The moving peak contributes no first-order term because the actual interpolant
has zero angle derivative there. The remaining free-node differential is the
literal sensitivity matrix. Its already-proved deleted minors and adjacent
differences therefore describe the actual height differential.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ContDiff Matrix

namespace UnitCircleInterpolation

noncomputable section

variable {d : ℕ}

/-- Chain-rule cancellation at a critical evaluation point in the actual angular chart. -/
lemma hasFDerivAt_angularInterpolant_envelope (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (c : Fin (d + 1) → ℝ)
    (p : (Fin d → ℝ) → ℝ) (p' : (Fin d → ℝ) →L[ℝ] ℝ)
    (hp : HasFDerivAt p p' u)
    (hcritical : deriv (sineInterpolant (angularParameterAngles u) c) (p u) = 0) :
    HasFDerivAt (fun v : Fin d → ℝ => sineInterpolant (angularParameterAngles v) c (p v))
      (angularInterpolantParameterDerivative u c (p u)) u := by
  have hθ := (cyclicAnglesOfParameters u hu).phaseNodes_injective
  have houter := hasFDerivAt_sineInterpolant_joint (angularParameterAngles u) c (p u) hθ
    (angularParameterAngle_mem_Ico u hu)
  have hcomp := houter.comp u ((hasFDerivAt_angularParameterAngles u).prodMk hp)
  have heq :
      (sineInterpolantJointDerivative (angularParameterAngles u) c (p u)).comp
        (angularParameterEmbedding.prod p') = angularInterpolantParameterDerivative u c (p u) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
    rw [sineInterpolantJointDerivative_apply, angularParameterEmbedding_apply,
      angularInterpolantParameterDerivative_apply, Fin.sum_univ_succ]
    simp only [angularParameterAngles_zero, angularParameterAngles_succ, zero_mul, zero_add,
      hcritical, mul_zero, add_zero]
  rwa [heq] at hcomp

/-- One actual sensitivity row, as a continuous linear form on the free angles. -/
def peakSensitivityRowDerivative (angles : CyclicAngles (d + 1) (Nat.succ_pos d))
    (hsize : 2 ≤ d + 1) (i : Fin (d + 1)) : (Fin d → ℝ) →L[ℝ] ℝ :=
  ∑ j : Fin d, peakSensitivityMatrix angles hsize i j • ContinuousLinearMap.proj j

lemma peakSensitivityRowDerivative_apply (angles : CyclicAngles (d + 1) (Nat.succ_pos d))
    (hsize : 2 ≤ d + 1) (i : Fin (d + 1)) (v : Fin d → ℝ) :
    peakSensitivityRowDerivative angles hsize i v =
      ∑ j : Fin d, v j * peakSensitivityMatrix angles hsize i j := by
  simp only [peakSensitivityRowDerivative, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- All actual sensitivity rows as one map between the finite-dimensional coordinate spaces. -/
def peakSensitivityLinearMap (angles : CyclicAngles (d + 1) (Nat.succ_pos d))
    (hsize : 2 ≤ d + 1) : (Fin d → ℝ) →L[ℝ] (Fin (d + 1) → ℝ) :=
  ContinuousLinearMap.pi (peakSensitivityRowDerivative angles hsize)

lemma peakSensitivityLinearMap_apply (angles : CyclicAngles (d + 1) (Nat.succ_pos d))
    (hsize : 2 ≤ d + 1) (v : Fin d → ℝ) (i : Fin (d + 1)) :
    peakSensitivityLinearMap angles hsize v i =
      ∑ j : Fin d, v j * peakSensitivityMatrix angles hsize i j :=
  peakSensitivityRowDerivative_apply angles hsize i v

/-- The angular interpolant's free-node differential at the actual peak is its sensitivity row. -/
lemma angularInterpolantParameterDerivative_at_peak_eq
    (angles : CyclicAngles (d + 1) (Nat.succ_pos d))
    (hsize : 2 ≤ d + 1) (i : Fin (d + 1)) :
    angularInterpolantParameterDerivative angles.interiorParameters
        (cyclicGapCoefficient (physicalGapCut (Nat.succ_pos d) i))
        (orderedPeak angles hsize i) = peakSensitivityRowDerivative angles hsize i := by
  ext v
  rw [angularInterpolantParameterDerivative_apply, peakSensitivityRowDerivative_apply]
  simp only [angularParameterAngles_interiorParameters, CyclicAngles.interiorParameters_apply,
    peakSensitivityMatrix, orderedGapInterpolant, gapInterpolant]

lemma peakSensitivityRowDerivative_single
    (angles : CyclicAngles (d + 1) (Nat.succ_pos d))
    (hsize : 2 ≤ d + 1) (i : Fin (d + 1)) (j : Fin d) :
    peakSensitivityRowDerivative angles hsize i (Pi.single j 1) =
      peakSensitivityMatrix angles hsize i j := by
  rw [peakSensitivityRowDerivative_apply]
  simp [Pi.single_apply]

/-- The actual selected height has the literal sensitivity row as its derivative. -/
theorem hasFDerivAt_parameterOrderedHeight_of_mem_domain (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) (i : Fin (d + 1)) :
    HasFDerivAt (parameterOrderedHeight hsize i)
      (peakSensitivityRowDerivative (cyclicAnglesOfParameters u hu) hsize i) u := by
  have hpeak := (contDiffAt_parameterOrderedPeak_of_mem_domain u hu hsize i).differentiableAt
    (by norm_num)
  have hcritical : deriv (sineInterpolant (angularParameterAngles u)
      (cyclicGapCoefficient (physicalGapCut (Nat.succ_pos d) i)))
      (parameterOrderedPeak hsize i u) = 0 := by
    rw [parameterOrderedPeak_of_mem_domain u hu]
    exact (orderedPeak_hasDerivAt_zero (cyclicAnglesOfParameters u hu) hsize i).deriv
  have henvelope := hasFDerivAt_angularInterpolant_envelope u hu
    (cyclicGapCoefficient (physicalGapCut (Nat.succ_pos d) i))
    (parameterOrderedPeak hsize i) _ hpeak.hasFDerivAt hcritical
  have hactual : HasFDerivAt (parameterOrderedHeight hsize i)
      (angularInterpolantParameterDerivative u
        (cyclicGapCoefficient (physicalGapCut (Nat.succ_pos d) i))
        (parameterOrderedPeak hsize i u)) u := by
    apply henvelope.congr_of_eventuallyEq
    filter_upwards [(isOpen_angularParameterDomain d).eventually_mem hu] with v hv
    exact parameterOrderedHeight_eq_value_at_peak v hv hsize i
  have heq := angularInterpolantParameterDerivative_at_peak_eq
    (cyclicAnglesOfParameters u hu) hsize i
  simp only [CyclicAngles.interiorParameters_ofParameters] at heq
  rw [parameterOrderedPeak_of_mem_domain u hu, heq] at hactual
  exact hactual

/-- The total extension of all actual ordered gap heights. -/
def parameterOrderedHeightMap (hsize : 2 ≤ d + 1) (u : Fin d → ℝ) :
    Fin (d + 1) → ℝ :=
  fun i => parameterOrderedHeight hsize i u

theorem hasFDerivAt_parameterOrderedHeightMap_of_mem_domain (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) :
    HasFDerivAt (parameterOrderedHeightMap hsize)
      (peakSensitivityLinearMap (cyclicAnglesOfParameters u hu) hsize) u := by
  exact hasFDerivAt_pi.mpr (fun i => hasFDerivAt_parameterOrderedHeight_of_mem_domain u hu hsize i)

lemma fderiv_parameterOrderedHeightMap_of_mem_domain (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) :
    fderiv ℝ (parameterOrderedHeightMap hsize) u =
      peakSensitivityLinearMap (cyclicAnglesOfParameters u hu) hsize :=
  (hasFDerivAt_parameterOrderedHeightMap_of_mem_domain u hu hsize).fderiv

/-- The actual height Jacobian, evaluated on the standard free-angle coordinate vectors. -/
def parameterHeightJacobian (hsize : 2 ≤ d + 1) (u : Fin d → ℝ) :
    Matrix (Fin (d + 1)) (Fin d) ℝ :=
  fun i j => fderiv ℝ (parameterOrderedHeightMap hsize) u (Pi.single j 1) i

theorem parameterHeightJacobian_eq_peakSensitivityMatrix (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) :
    parameterHeightJacobian hsize u = peakSensitivityMatrix (cyclicAnglesOfParameters u hu) hsize := by
  ext i j
  simp only [parameterHeightJacobian, fderiv_parameterOrderedHeightMap_of_mem_domain u hu,
    peakSensitivityLinearMap, ContinuousLinearMap.pi_apply, peakSensitivityRowDerivative_single]

/-- Every deleted maximal minor of the actual height differential is nonzero. -/
theorem parameterHeightJacobian_deleted_det_ne_zero (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) (omitted : Fin (d + 1)) :
    ((parameterHeightJacobian hsize u).submatrix omitted.succAbove id).det ≠ 0 := by
  rw [parameterHeightJacobian_eq_peakSensitivityMatrix u hu]
  exact peakSensitivityMatrix_deleted_det_ne_zero (cyclicAnglesOfParameters u hu) hsize omitted

/-- The actual adjacent differences of the ordered gap heights. -/
def parameterAdjacentHeightDifferences (hsize : 2 ≤ d + 1) (u : Fin d → ℝ) : Fin d → ℝ :=
  fun i => parameterOrderedHeight hsize i.succ u - parameterOrderedHeight hsize i.castSucc u

def peakSensitivityDifferenceLinearMap
    (angles : CyclicAngles (d + 1) (Nat.succ_pos d)) (hsize : 2 ≤ d + 1) :
    (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi (fun i => peakSensitivityRowDerivative angles hsize i.succ -
    peakSensitivityRowDerivative angles hsize i.castSucc)

theorem hasFDerivAt_parameterAdjacentHeightDifferences_of_mem_domain (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) :
    HasFDerivAt (parameterAdjacentHeightDifferences hsize)
      (peakSensitivityDifferenceLinearMap (cyclicAnglesOfParameters u hu) hsize) u := by
  exact hasFDerivAt_pi.mpr (fun i =>
    (hasFDerivAt_parameterOrderedHeight_of_mem_domain u hu hsize i.succ).sub
      (hasFDerivAt_parameterOrderedHeight_of_mem_domain u hu hsize i.castSucc))

lemma fderiv_parameterAdjacentHeightDifferences_of_mem_domain (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) :
    fderiv ℝ (parameterAdjacentHeightDifferences hsize) u =
      peakSensitivityDifferenceLinearMap (cyclicAnglesOfParameters u hu) hsize :=
  (hasFDerivAt_parameterAdjacentHeightDifferences_of_mem_domain u hu hsize).fderiv

def parameterAdjacentHeightJacobian (hsize : 2 ≤ d + 1) (u : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => fderiv ℝ (parameterAdjacentHeightDifferences hsize) u (Pi.single j 1) i

theorem parameterAdjacentHeightJacobian_eq (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) :
    parameterAdjacentHeightJacobian hsize u =
      adjacentRowDifferenceMatrix (peakSensitivityMatrix (cyclicAnglesOfParameters u hu) hsize) := by
  ext i j
  simp only [parameterAdjacentHeightJacobian, fderiv_parameterAdjacentHeightDifferences_of_mem_domain u hu,
    peakSensitivityDifferenceLinearMap, ContinuousLinearMap.pi_apply, sub_apply,
    peakSensitivityRowDerivative_single, adjacentRowDifferenceMatrix]

/-- The actual adjacent-height difference map has a nonsingular Jacobian everywhere in the chart. -/
theorem parameterAdjacentHeightJacobian_det_ne_zero (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) :
    (parameterAdjacentHeightJacobian hsize u).det ≠ 0 := by
  rw [parameterAdjacentHeightJacobian_eq u hu]
  exact peakSensitivity_adjacent_difference_det_ne_zero (cyclicAnglesOfParameters u hu) hsize

end

end UnitCircleInterpolation
