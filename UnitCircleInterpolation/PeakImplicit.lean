/-
Unit-circle project integration and adaptations: wang060919.
Developed with Codex assistance. Original authors and MIT notices are retained below.
-/

/-
Pinned original Jacobian.lean SHA256: 081a8a26cf99643afa728c2cd560b1bee6cd9b1b912c0534376a0b00deceff08
Pinned original Git blob: 85d4db52973b3b3e6a7c49ad60c70cc4ea3a4c05
-/

/-
Copyright (c) 2026 Ethan Yang
Copyright (c) 2026 randyxian08 (free-node extension and repairs)

The scalar vertical-derivative helper below is adapted from
randyxian08/jsp000936-lean, commit 0ced15a2630c5c68b23de896d7e6ad1e7cfeda01,
Erdos1153/DeBoorPinkus/Jacobian.lean, fderiv_comp_inr_eq_of_hasDeriv.
https://github.com/randyxian08/jsp000936-lean/blob/0ced15a2630c5c68b23de896d7e6ad1e7cfeda01/Erdos1153/DeBoorPinkus/Jacobian.lean

MIT License

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

import UnitCircleInterpolation.GapCriticalUniqueness
import UnitCircleInterpolation.InterpolantParameters
import UnitCircleInterpolation.AngularCalculus
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Smooth implicit branches of the actual circular gap peaks

The vertical differential is the already-proved negative second derivative
at the actual own-gap peak. No invertibility or branch hypothesis is assumed.
The full-angle implicit branch is restricted to the open normalized angular
chart, where own-gap critical uniqueness identifies it with the chosen peak.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff Topology
open Filter

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ} {hn : 0 < n} {d : ℕ}

/-- A scalar vertical section determines the vertical part of the joint derivative. -/
lemma fderiv_comp_inr_eq_smul_of_hasDeriv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E × ℝ → ℝ} {u : E} {x c : ℝ}
    (hf : DifferentiableAt ℝ f (u, x))
    (hx : HasDerivAt (fun y => f (u, y)) c x) :
    (fderiv ℝ f (u, x)).comp (ContinuousLinearMap.inr ℝ E ℝ) =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c := by
  have hcurve : HasFDerivAt (fun y : ℝ => (u, y))
      (ContinuousLinearMap.inr ℝ E ℝ) x := by
    convert (hasFDerivAt_const (x := x) (c := u)).prodMk
      (hasFDerivAt_id x) using 1 <;> rfl
  have hcomp := hf.hasFDerivAt.comp x hcurve
  exact hcomp.unique hx

/-- Nonzero scalar multiplication is a genuinely invertible vertical differential. -/
lemma isInvertible_smulRight_of_ne_zero (c : ℝ) (hc : c ≠ 0) :
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c⁻¹)
  · ext
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self, smul_eq_mul, ContinuousLinearMap.id_apply]
    field_simp [hc]
  · ext
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self, smul_eq_mul, ContinuousLinearMap.id_apply]
    field_simp [hc]

/-- The literal critical equation for one gap in physical order. -/
def orderedCriticalMap (hn : 0 < n) (k : Fin n) (x : (Fin n → ℝ) × ℝ) : ℝ :=
  deriv (sineInterpolant x.1 (cyclicGapCoefficient (physicalGapCut hn k))) x.2

lemma contDiffAt_orderedCriticalMap (m : ℕ∞ω) (angles : CyclicAngles n hn)
    (t : ℝ) (k : Fin n) :
    ContDiffAt ℝ m (orderedCriticalMap hn k) (angles.angle, t) :=
  contDiffAt_deriv_sineInterpolant_joint m angles.angle t
    (cyclicGapCoefficient (physicalGapCut hn k)) angles.phaseNodes_injective

lemma orderedCriticalMap_vertical (angles : CyclicAngles n hn) (k : Fin n) (t : ℝ) :
    (fderiv ℝ (orderedCriticalMap hn k) (angles.angle, t)).comp
        (ContinuousLinearMap.inr ℝ (Fin n → ℝ) ℝ) =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (deriv (deriv (orderedGapInterpolant angles k)) t) := by
  apply fderiv_comp_inr_eq_smul_of_hasDeriv
    ((contDiffAt_orderedCriticalMap 1 angles t k).differentiableAt (by norm_num))
  have hsection : ContDiffAt ℝ 1 (deriv (orderedGapInterpolant angles k)) t := by
    exact (contDiffAt_orderedCriticalMap 1 angles t k).comp t
      (contDiffAt_const.prodMk contDiffAt_id)
  exact (hsection.differentiableAt (by norm_num)).hasDerivAt

lemma orderedCriticalMap_vertical_isInvertible (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (k : Fin n) :
    (fderiv ℝ (orderedCriticalMap hn k) (angles.angle, orderedPeak angles hsize k) ∘L
      ContinuousLinearMap.inr ℝ (Fin n → ℝ) ℝ).IsInvertible := by
  rw [orderedCriticalMap_vertical]
  exact isInvertible_smulRight_of_ne_zero _
    (ne_of_lt (orderedPeak_second_deriv_neg angles hsize k))

/-- The implicit critical branch around the actual chosen gap peak. -/
def localOrderedPeak (angles : CyclicAngles n hn) (hsize : 2 ≤ n) (k : Fin n) :
    (Fin n → ℝ) → ℝ :=
  (contDiffAt_orderedCriticalMap ∞ angles (orderedPeak angles hsize k) k).implicitFunction
    (by simp) (orderedCriticalMap_vertical_isInvertible angles hsize k)

lemma localOrderedPeak_eq_at_base (angles : CyclicAngles n hn) (hsize : 2 ≤ n)
    (k : Fin n) : localOrderedPeak angles hsize k angles.angle = orderedPeak angles hsize k :=
  ContDiffAt.implicitFunction_apply_self
    (contDiffAt_orderedCriticalMap ∞ angles (orderedPeak angles hsize k) k)
    (by simp) (orderedCriticalMap_vertical_isInvertible angles hsize k)

lemma contDiffAt_localOrderedPeak (angles : CyclicAngles n hn) (hsize : 2 ≤ n)
    (k : Fin n) : ContDiffAt ℝ ∞ (localOrderedPeak angles hsize k) angles.angle :=
  ContDiffAt.contDiffAt_implicitFunction
    (contDiffAt_orderedCriticalMap ∞ angles (orderedPeak angles hsize k) k)
    (by simp) (orderedCriticalMap_vertical_isInvertible angles hsize k)

lemma eventually_orderedCriticalMap_localOrderedPeak_eq_zero (angles : CyclicAngles n hn)
    (hsize : 2 ≤ n) (k : Fin n) :
    ∀ᶠ θ in 𝓝 angles.angle, orderedCriticalMap hn k (θ, localOrderedPeak angles hsize k θ) = 0 := by
  have h := ContDiffAt.eventually_apply_implicitFunction
    (contDiffAt_orderedCriticalMap ∞ angles (orderedPeak angles hsize k) k) (by simp)
      (orderedCriticalMap_vertical_isInvertible angles hsize k)
  have hz : orderedCriticalMap hn k (angles.angle, orderedPeak angles hsize k) = 0 :=
    (orderedPeak_hasDerivAt_zero angles hsize k).deriv
  rwa [hz] at h

/-- The local implicit branch in the actual normalized node chart. -/
def localParameterPeak (angles : CyclicAngles (d + 1) (Nat.succ_pos d))
    (hsize : 2 ≤ d + 1) (k : Fin (d + 1)) (u : Fin d → ℝ) : ℝ :=
  localOrderedPeak angles hsize k (angularParameterAngles u)

lemma localParameterPeak_eq_at_base (angles : CyclicAngles (d + 1) (Nat.succ_pos d))
    (hsize : 2 ≤ d + 1) (k : Fin (d + 1)) :
    localParameterPeak angles hsize k angles.interiorParameters = orderedPeak angles hsize k := by
  rw [localParameterPeak, angularParameterAngles_interiorParameters, localOrderedPeak_eq_at_base]

lemma contDiffAt_localParameterPeak (angles : CyclicAngles (d + 1) (Nat.succ_pos d))
    (hsize : 2 ≤ d + 1) (k : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (localParameterPeak angles hsize k) angles.interiorParameters := by
  have hbase : ContDiffAt ℝ ∞ (localOrderedPeak angles hsize k)
      (angularParameterAngles angles.interiorParameters) := by
    rw [angularParameterAngles_interiorParameters]
    exact contDiffAt_localOrderedPeak angles hsize k
  exact hbase.comp angles.interiorParameters (contDiff_angularParameterAngles ∞).contDiffAt

lemma eventually_orderedCriticalMap_localParameterPeak_eq_zero
    (angles : CyclicAngles (d + 1) (Nat.succ_pos d))
    (hsize : 2 ≤ d + 1) (k : Fin (d + 1)) :
    ∀ᶠ u in 𝓝 angles.interiorParameters,
      orderedCriticalMap (Nat.succ_pos d) k
        (angularParameterAngles u, localParameterPeak angles hsize k u) = 0 := by
  have ht : Tendsto angularParameterAngles (𝓝 angles.interiorParameters) (𝓝 angles.angle) := by
    simpa only [angularParameterAngles_interiorParameters] using
      (continuous_angularParameterAngles.continuousAt
        (x := angles.interiorParameters)).tendsto
  exact ht.eventually (eventually_orderedCriticalMap_localOrderedPeak_eq_zero angles hsize k)

/-- The right endpoint in the ambient angular chart, with a literal final endpoint `2π`. -/
def angularParameterGapRight (k : Fin (d + 1)) (u : Fin d → ℝ) : ℝ :=
  if hk : k.val + 1 < d + 1 then angularParameterAngles u ⟨k.val + 1, hk⟩
  else 2 * Real.pi

lemma continuous_angularParameterGapRight (k : Fin (d + 1)) :
    Continuous (angularParameterGapRight k) := by
  unfold angularParameterGapRight
  split_ifs
  · exact continuous_angularParameterAngle _
  · exact continuous_const

lemma angularParameterGapRight_ofParameters (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (k : Fin (d + 1)) :
    angularParameterGapRight k u = cyclicGapRight (cyclicAnglesOfParameters u hu) k :=
  rfl

/-- The implicit branch remains between its actual moving node endpoints. -/
lemma eventually_localParameterPeak_mem_gap
    (angles : CyclicAngles (d + 1) (Nat.succ_pos d))
    (hsize : 2 ≤ d + 1) (k : Fin (d + 1)) :
    ∀ᶠ u in 𝓝 angles.interiorParameters,
      localParameterPeak angles hsize k u ∈
        Set.Ioo (angularParameterAngles u k) (angularParameterGapRight k u) := by
  have hcont := (contDiffAt_localParameterPeak angles hsize k).continuousAt
  have hgap := orderedPeak_mem_node_gap angles hsize k
  have hleft : angularParameterAngles angles.interiorParameters k <
      localParameterPeak angles hsize k angles.interiorParameters := by
    rw [angularParameterAngles_interiorParameters, localParameterPeak_eq_at_base]
    exact hgap.1
  have hright : localParameterPeak angles hsize k angles.interiorParameters <
      angularParameterGapRight k angles.interiorParameters := by
    rw [localParameterPeak_eq_at_base]
    simpa only [angularParameterGapRight, cyclicGapRight,
      angularParameterAngles_interiorParameters] using hgap.2
  exact ((continuous_angularParameterAngle k).continuousAt.eventually_lt hcont hleft).and
    (hcont.eventually_lt (continuous_angularParameterGapRight k).continuousAt hright)

/-- Actual own-gap critical uniqueness identifies the local implicit branch. -/
lemma eventually_localParameterPeak_eq_orderedPeak
    (angles : CyclicAngles (d + 1) (Nat.succ_pos d))
    (hsize : 2 ≤ d + 1) (k : Fin (d + 1)) :
    ∀ᶠ u in 𝓝 angles.interiorParameters, ∀ hu : u ∈ angularParameterDomain d,
      localParameterPeak angles hsize k u =
        orderedPeak (cyclicAnglesOfParameters u hu) hsize k := by
  filter_upwards [eventually_orderedCriticalMap_localParameterPeak_eq_zero angles hsize k,
    eventually_localParameterPeak_mem_gap angles hsize k] with u hcritical hgap
  intro hu
  apply eq_orderedPeak_of_deriv_eq_zero (cyclicAnglesOfParameters u hu) hsize k
  · simpa only [cyclicAnglesOfParameters_angle, ← angularParameterGapRight_ofParameters u hu k]
      using hgap
  · exact hcritical

/-- A total extension of the actual normalized peak, zero outside the open chart. -/
def parameterOrderedPeak (hsize : 2 ≤ d + 1) (k : Fin (d + 1)) (u : Fin d → ℝ) : ℝ := by
  classical
  exact if hu : u ∈ angularParameterDomain d then
    orderedPeak (cyclicAnglesOfParameters u hu) hsize k else 0

/-- A total extension of the actual normalized gap height, zero outside the open chart. -/
def parameterOrderedHeight (hsize : 2 ≤ d + 1) (k : Fin (d + 1)) (u : Fin d → ℝ) : ℝ := by
  classical
  exact if hu : u ∈ angularParameterDomain d then
    orderedHeight (cyclicAnglesOfParameters u hu) hsize k else 0

lemma parameterOrderedPeak_of_mem_domain (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) (k : Fin (d + 1)) :
    parameterOrderedPeak hsize k u = orderedPeak (cyclicAnglesOfParameters u hu) hsize k := by
  rw [parameterOrderedPeak, dif_pos hu]

lemma parameterOrderedHeight_of_mem_domain (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) (k : Fin (d + 1)) :
    parameterOrderedHeight hsize k u = orderedHeight (cyclicAnglesOfParameters u hu) hsize k := by
  rw [parameterOrderedHeight, dif_pos hu]

lemma parameterOrderedHeight_eq_value_at_peak (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) (k : Fin (d + 1)) :
    parameterOrderedHeight hsize k u =
      sineInterpolant (angularParameterAngles u)
        (cyclicGapCoefficient (physicalGapCut (Nat.succ_pos d) k))
        (parameterOrderedPeak hsize k u) := by
  rw [parameterOrderedHeight_of_mem_domain u hu, parameterOrderedPeak_of_mem_domain u hu]
  rfl

lemma eventually_parameterOrderedPeak_eq_localParameterPeak
    (angles : CyclicAngles (d + 1) (Nat.succ_pos d))
    (hsize : 2 ≤ d + 1) (k : Fin (d + 1)) :
    parameterOrderedPeak hsize k =ᶠ[𝓝 angles.interiorParameters]
      localParameterPeak angles hsize k := by
  filter_upwards [(isOpen_angularParameterDomain d).eventually_mem
      angles.interiorParameters_mem_domain,
    eventually_localParameterPeak_eq_orderedPeak angles hsize k] with u hu heq
  rw [parameterOrderedPeak_of_mem_domain u hu]
  exact (heq hu).symm

lemma contDiffAt_parameterOrderedPeak
    (angles : CyclicAngles (d + 1) (Nat.succ_pos d))
    (hsize : 2 ≤ d + 1) (k : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (parameterOrderedPeak hsize k) angles.interiorParameters :=
  (contDiffAt_localParameterPeak angles hsize k).congr_of_eventuallyEq
    (eventually_parameterOrderedPeak_eq_localParameterPeak angles hsize k)

lemma contDiffAt_parameterOrderedPeak_of_mem_domain (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) (k : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (parameterOrderedPeak hsize k) u := by
  simpa only [CyclicAngles.interiorParameters_ofParameters] using
    contDiffAt_parameterOrderedPeak (cyclicAnglesOfParameters u hu) hsize k

/-- The literal interpolant value along the actual local critical branch. -/
def localParameterHeight (angles : CyclicAngles (d + 1) (Nat.succ_pos d))
    (hsize : 2 ≤ d + 1) (k : Fin (d + 1)) (u : Fin d → ℝ) : ℝ :=
  sineInterpolant (angularParameterAngles u)
    (cyclicGapCoefficient (physicalGapCut (Nat.succ_pos d) k))
    (localParameterPeak angles hsize k u)

lemma contDiffAt_localParameterHeight
    (angles : CyclicAngles (d + 1) (Nat.succ_pos d))
    (hsize : 2 ≤ d + 1) (k : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (localParameterHeight angles hsize k) angles.interiorParameters := by
  have hbase : ContDiffAt ℝ ∞
      (fun x : (Fin (d + 1) → ℝ) × ℝ =>
        sineInterpolant x.1 (cyclicGapCoefficient (physicalGapCut (Nat.succ_pos d) k)) x.2)
      (angularParameterAngles angles.interiorParameters,
        localParameterPeak angles hsize k angles.interiorParameters) := by
    rw [angularParameterAngles_interiorParameters, localParameterPeak_eq_at_base]
    exact contDiffAt_sineInterpolant_joint ∞ angles.angle (orderedPeak angles hsize k)
      (cyclicGapCoefficient (physicalGapCut (Nat.succ_pos d) k)) angles.phaseNodes_injective
  have hcomp := hbase.comp angles.interiorParameters
    ((contDiff_angularParameterAngles ∞).contDiffAt.prodMk
      (contDiffAt_localParameterPeak angles hsize k))
  exact hcomp

lemma eventually_localParameterHeight_eq_orderedHeight
    (angles : CyclicAngles (d + 1) (Nat.succ_pos d))
    (hsize : 2 ≤ d + 1) (k : Fin (d + 1)) :
    ∀ᶠ u in 𝓝 angles.interiorParameters, ∀ hu : u ∈ angularParameterDomain d,
      localParameterHeight angles hsize k u =
        orderedHeight (cyclicAnglesOfParameters u hu) hsize k := by
  filter_upwards [eventually_localParameterPeak_eq_orderedPeak angles hsize k] with u heq
  intro hu
  rw [localParameterHeight, heq hu]
  rfl

lemma eventually_parameterOrderedHeight_eq_localParameterHeight
    (angles : CyclicAngles (d + 1) (Nat.succ_pos d))
    (hsize : 2 ≤ d + 1) (k : Fin (d + 1)) :
    parameterOrderedHeight hsize k =ᶠ[𝓝 angles.interiorParameters]
      localParameterHeight angles hsize k := by
  filter_upwards [(isOpen_angularParameterDomain d).eventually_mem
      angles.interiorParameters_mem_domain,
    eventually_localParameterHeight_eq_orderedHeight angles hsize k] with u hu heq
  rw [parameterOrderedHeight_of_mem_domain u hu]
  exact (heq hu).symm

lemma contDiffAt_parameterOrderedHeight
    (angles : CyclicAngles (d + 1) (Nat.succ_pos d))
    (hsize : 2 ≤ d + 1) (k : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (parameterOrderedHeight hsize k) angles.interiorParameters :=
  (contDiffAt_localParameterHeight angles hsize k).congr_of_eventuallyEq
    (eventually_parameterOrderedHeight_eq_localParameterHeight angles hsize k)

lemma contDiffAt_parameterOrderedHeight_of_mem_domain (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) (k : Fin (d + 1)) :
    ContDiffAt ℝ ∞ (parameterOrderedHeight hsize k) u := by
  simpa only [CyclicAngles.interiorParameters_ofParameters] using
    contDiffAt_parameterOrderedHeight (cyclicAnglesOfParameters u hu) hsize k

end

end UnitCircleInterpolation
