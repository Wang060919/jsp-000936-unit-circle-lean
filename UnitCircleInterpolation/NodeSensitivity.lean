/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.InterpolantParameters
import UnitCircleInterpolation.HomogeneousLinear
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Coordinate sensitivity of the actual sine interpolant

Moving one literal node gives an exact finite difference in its original cardinal
direction. Differentiating that identity and the interpolation value at the moving
node identifies the coordinate derivative. Only the original node family needs
canonical representatives; the perturbed family need not stay in that interval.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators ContDiff

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ}

lemma sineInterpolant_mem_homogeneousTrigSpace (θ c : Fin n → ℝ) :
    sineInterpolant θ c ∈ homogeneousTrigSpace (n - 1) :=
  ⟨interpolantPolynomial θ c, interpolantPolynomial_natDegree_le θ c,
    (homogeneousTrig_interpolantPolynomial θ c).symm⟩

lemma sineCardinal_mem_homogeneousTrigSpace (θ : Fin n → ℝ) (j : Fin n) :
    sineCardinal θ j ∈ homogeneousTrigSpace (n - 1) := by
  have heq : sineInterpolant θ (Pi.single j 1) = sineCardinal θ j := by
    funext t
    simp [sineInterpolant, Pi.single_apply]
  rw [← heq]
  exact sineInterpolant_mem_homogeneousTrigSpace θ (Pi.single j 1)

/-- Values at all distinct canonical nodes determine the actual homogeneous space. -/
lemma homogeneousTrigSpace_eq_of_at_nodes (θ : Fin n → ℝ) (hn : 0 < n)
    (hθ : Function.Injective (phaseNodes θ))
    (hbound : ∀ i, θ i ∈ Set.Ico 0 (2 * Real.pi)) (f g : ℝ → ℝ)
    (hf : f ∈ homogeneousTrigSpace (n - 1))
    (hg : g ∈ homogeneousTrigSpace (n - 1)) (hnode : ∀ i, f (θ i) = g (θ i)) :
    f = g := by
  apply sub_eq_zero.mp
  by_contra hne
  have hinj : Function.Injective θ := by
    intro i k hik
    apply hθ
    simp only [phaseNodes, hik]
  have hcount := distinct_root_count_of_mem_homogeneousTrigSpace (n - 1) (f - g)
    ((homogeneousTrigSpace (n - 1)).sub_mem hf hg) hne θ hinj hbound
    (fun i => by simp [hnode i])
  omega

/-- Changing one node is an exact finite difference along its original cardinal. -/
lemma sineInterpolant_update_node_transport (θ c : Fin n → ℝ) (j : Fin n) (u t : ℝ)
    (hθ : Function.Injective (phaseNodes θ))
    (hbound : ∀ i, θ i ∈ Set.Ico 0 (2 * Real.pi))
    (hu : Function.Injective (phaseNodes (Function.update θ j u))) :
    sineInterpolant (Function.update θ j u) c t = sineInterpolant θ c t +
      (sineInterpolant (Function.update θ j u) c (θ j) - c j) * sineCardinal θ j t := by
  have heq : sineInterpolant (Function.update θ j u) c =
      sineInterpolant θ c +
        (sineInterpolant (Function.update θ j u) c (θ j) - c j) • sineCardinal θ j := by
    apply homogeneousTrigSpace_eq_of_at_nodes θ j.pos hθ hbound
    · exact sineInterpolant_mem_homogeneousTrigSpace _ _
    · exact (homogeneousTrigSpace (n - 1)).add_mem
        (sineInterpolant_mem_homogeneousTrigSpace θ c)
        ((homogeneousTrigSpace (n - 1)).smul_mem _
          (sineCardinal_mem_homogeneousTrigSpace θ j))
    · intro i
      by_cases hij : i = j
      · subst i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          sineInterpolant_at_node θ hθ c j, sineCardinal_self θ hθ j]
        ring
      · have hnode : sineInterpolant (Function.update θ j u) c (θ i) = c i := by
          simpa only [Function.update_of_ne hij] using
            sineInterpolant_at_node (Function.update θ j u) hu c i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hnode,
          sineInterpolant_at_node θ hθ c i, sineCardinal_other θ hij, mul_zero, add_zero]
  exact congrFun heq t

/-- The moving-node interpolation identity differentiates to the actual negative angle slope. -/
lemma hasDerivAt_sineInterpolant_update_at_original_node (θ c : Fin n → ℝ)
    (j : Fin n) (hθ : Function.Injective (phaseNodes θ)) :
    HasDerivAt (fun u : ℝ => sineInterpolant (Function.update θ j u) c (θ j))
      (-deriv (sineInterpolant θ c) (θ j)) (θ j) := by
  let H : ((Fin n → ℝ) × ℝ) → ℝ := fun x => sineInterpolant x.1 c x.2
  let L := fderiv ℝ H (θ, θ j)
  have hH : HasFDerivAt H L (θ, θ j) :=
    (contDiffAt_sineInterpolant_joint 1 θ (θ j) c hθ).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hupdate := hasDerivAt_update θ j (θ j)
  have hcoord := hH.comp_hasDerivAt_of_eq (θ j)
    (hupdate.prodMk (hasDerivAt_const (θ j) (θ j))) (by
      simp only [Function.update_eq_self])
  have hdiag := hH.comp_hasDerivAt_of_eq (θ j)
    (hupdate.prodMk (hasDerivAt_id (θ j))) (by
      simp only [Function.update_eq_self, id_eq])
  have heval := hH.comp_hasDerivAt (θ j)
    ((hasDerivAt_const (θ j) θ).prodMk (hasDerivAt_id (θ j)))
  have hconst : HasDerivAt (fun u : ℝ => sineInterpolant (Function.update θ j u) c u)
      0 (θ j) := by
    apply (hasDerivAt_const (θ j) (c j)).congr_of_eventuallyEq
    filter_upwards [eventually_phaseNodes_injective_update θ j hθ] with u hu
    simpa only [Function.update_self] using
      sineInterpolant_at_node (Function.update θ j u) hu c j
  have heval' : HasDerivAt (sineInterpolant θ c)
      (deriv (sineInterpolant θ c) (θ j)) (θ j) :=
    (differentiable_sineInterpolant θ c (θ j)).hasDerivAt
  have hdiagzero : L (Pi.single j (1 : ℝ), (1 : ℝ)) = 0 := hdiag.unique hconst
  have hevalvalue : L ((0 : Fin n → ℝ), (1 : ℝ)) =
      deriv (sineInterpolant θ c) (θ j) := heval.unique heval'
  have hsplit : L (Pi.single j (1 : ℝ), (1 : ℝ)) =
      L (Pi.single j (1 : ℝ), (0 : ℝ)) + L ((0 : Fin n → ℝ), (1 : ℝ)) := by
    rw [← map_add]
    congr 1
    simp
  have hvalue : L (Pi.single j (1 : ℝ), (0 : ℝ)) =
      -deriv (sineInterpolant θ c) (θ j) := by
    rw [hdiagzero, hevalvalue] at hsplit
    linarith
  exact hvalue ▸ hcoord

/-- Exact coordinate sensitivity of the literal sine interpolant, at every evaluation angle. -/
lemma hasDerivAt_sineInterpolant_update (θ c : Fin n → ℝ) (j : Fin n) (t : ℝ)
    (hθ : Function.Injective (phaseNodes θ))
    (hbound : ∀ i, θ i ∈ Set.Ico 0 (2 * Real.pi)) :
    HasDerivAt (fun u : ℝ => sineInterpolant (Function.update θ j u) c t)
      (-deriv (sineInterpolant θ c) (θ j) * sineCardinal θ j t) (θ j) := by
  have hscalar :=
    (hasDerivAt_sineInterpolant_update_at_original_node θ c j hθ).sub_const (c j)
  have hright := (hasDerivAt_const (θ j) (sineInterpolant θ c t)).add
    (hscalar.mul_const (sineCardinal θ j t))
  simp only [zero_add] at hright
  apply hright.congr_of_eventuallyEq
  filter_upwards [eventually_phaseNodes_injective_update θ j hθ] with u hu
  exact sineInterpolant_update_node_transport θ c j u t hθ hbound hu

/-- The coordinate derivative is written with the actual ordinary angle derivative. -/
lemma deriv_sineInterpolant_update (θ c : Fin n → ℝ) (j : Fin n) (t : ℝ)
    (hθ : Function.Injective (phaseNodes θ))
    (hbound : ∀ i, θ i ∈ Set.Ico 0 (2 * Real.pi)) :
    deriv (fun u : ℝ => sineInterpolant (Function.update θ j u) c t) (θ j) =
      -deriv (sineInterpolant θ c) (θ j) * sineCardinal θ j t :=
  (hasDerivAt_sineInterpolant_update θ c j t hθ hbound).deriv

/-- The actual parameter Fréchet derivative on a coordinate basis vector. -/
lemma fderiv_sineInterpolant_parameters_single (θ c : Fin n → ℝ) (j : Fin n) (t : ℝ)
    (hθ : Function.Injective (phaseNodes θ))
    (hbound : ∀ i, θ i ∈ Set.Ico 0 (2 * Real.pi)) :
    fderiv ℝ (fun η : Fin n → ℝ => sineInterpolant η c t) θ (Pi.single j 1) =
      -deriv (sineInterpolant θ c) (θ j) * sineCardinal θ j t := by
  have hf := (contDiffAt_sineInterpolant_parameters 1 θ c t hθ).differentiableAt
    (by norm_num)
  have hcomp := hf.hasFDerivAt.comp_hasDerivAt_of_eq (θ j)
    (hasDerivAt_update θ j (θ j)) (by simp only [Function.update_eq_self])
  exact hcomp.unique (hasDerivAt_sineInterpolant_update θ c j t hθ hbound)

/-- All parameter directions have the finite sum of the actual cardinal sensitivities. -/
lemma fderiv_sineInterpolant_parameters_apply (θ c : Fin n → ℝ) (t : ℝ)
    (hθ : Function.Injective (phaseNodes θ))
    (hbound : ∀ i, θ i ∈ Set.Ico 0 (2 * Real.pi)) (v : Fin n → ℝ) :
    fderiv ℝ (fun η : Fin n → ℝ => sineInterpolant η c t) θ v =
      ∑ j, v j * (-deriv (sineInterpolant θ c) (θ j) * sineCardinal θ j t) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hsingle : Pi.single j (v j) = v j • Pi.single j (1 : ℝ) := by
    ext k
    by_cases hkj : k = j
    · subst k
      simp
    · simp [Pi.single_eq_of_ne hkj]
  rw [hsingle, map_smul, fderiv_sineInterpolant_parameters_single θ c j t hθ hbound,
    smul_eq_mul]

/-- The exact continuous linear map used by the full parameter derivative. -/
def sineInterpolantParameterDerivative (θ c : Fin n → ℝ) (t : ℝ) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ j, (-deriv (sineInterpolant θ c) (θ j) * sineCardinal θ j t) •
    ContinuousLinearMap.proj j

lemma sineInterpolantParameterDerivative_apply (θ c : Fin n → ℝ) (t : ℝ)
    (v : Fin n → ℝ) :
    sineInterpolantParameterDerivative θ c t v =
      ∑ j, v j * (-deriv (sineInterpolant θ c) (θ j) * sineCardinal θ j t) := by
  simp only [sineInterpolantParameterDerivative, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The full parameter Fréchet derivative, with no missing sensitivity hypothesis. -/
lemma hasFDerivAt_sineInterpolant_parameters (θ c : Fin n → ℝ) (t : ℝ)
    (hθ : Function.Injective (phaseNodes θ))
    (hbound : ∀ i, θ i ∈ Set.Ico 0 (2 * Real.pi)) :
    HasFDerivAt (fun η : Fin n → ℝ => sineInterpolant η c t)
      (sineInterpolantParameterDerivative θ c t) θ := by
  have heq : fderiv ℝ (fun η : Fin n → ℝ => sineInterpolant η c t) θ =
      sineInterpolantParameterDerivative θ c t := by
    ext v
    rw [fderiv_sineInterpolant_parameters_apply θ c t hθ hbound,
      sineInterpolantParameterDerivative_apply]
  rw [← heq]
  exact (contDiffAt_sineInterpolant_parameters 1 θ c t hθ).differentiableAt
    (by norm_num) |>.hasFDerivAt

/-- The exact joint derivative combines the parameter and evaluation directions. -/
def sineInterpolantJointDerivative (θ c : Fin n → ℝ) (t : ℝ) :
    ((Fin n → ℝ) × ℝ) →L[ℝ] ℝ :=
  (sineInterpolantParameterDerivative θ c t).comp (ContinuousLinearMap.fst ℝ _ _) +
    deriv (sineInterpolant θ c) t • ContinuousLinearMap.snd ℝ _ _

lemma sineInterpolantJointDerivative_apply (θ c : Fin n → ℝ) (t : ℝ)
    (v : Fin n → ℝ) (s : ℝ) :
    sineInterpolantJointDerivative θ c t (v, s) =
      (∑ j, v j * (-deriv (sineInterpolant θ c) (θ j) * sineCardinal θ j t)) +
        s * deriv (sineInterpolant θ c) t := by
  simp only [sineInterpolantJointDerivative, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', smul_apply,
    ContinuousLinearMap.coe_snd', smul_eq_mul, sineInterpolantParameterDerivative_apply]
  ring

/-- The full joint derivative is proved for the literal parameter/evaluation function. -/
lemma hasFDerivAt_sineInterpolant_joint (θ c : Fin n → ℝ) (t : ℝ)
    (hθ : Function.Injective (phaseNodes θ))
    (hbound : ∀ i, θ i ∈ Set.Ico 0 (2 * Real.pi)) :
    HasFDerivAt (fun x : (Fin n → ℝ) × ℝ => sineInterpolant x.1 c x.2)
      (sineInterpolantJointDerivative θ c t) (θ, t) := by
  let H : ((Fin n → ℝ) × ℝ) → ℝ := fun x => sineInterpolant x.1 c x.2
  let L := fderiv ℝ H (θ, t)
  have hH : HasFDerivAt H L (θ, t) :=
    (contDiffAt_sineInterpolant_joint 1 θ t c hθ).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hleft := hH.comp θ (hasFDerivAt_prodMk_left (𝕜 := ℝ) θ t)
  have hleftmap := hleft.unique (hasFDerivAt_sineInterpolant_parameters θ c t hθ hbound)
  have heval := hH.comp_hasDerivAt t
    ((hasDerivAt_const t θ).prodMk (hasDerivAt_id t))
  have hevalvalue : L ((0 : Fin n → ℝ), (1 : ℝ)) =
      deriv (sineInterpolant θ c) t := heval.unique
    (differentiable_sineInterpolant θ c t).hasDerivAt
  have heq : L = sineInterpolantJointDerivative θ c t := by
    apply ContinuousLinearMap.ext
    intro x
    rcases x with ⟨v, s⟩
    have hleftvalue : L (v, (0 : ℝ)) = sineInterpolantParameterDerivative θ c t v := by
      have hv := congrArg (fun f : (Fin n → ℝ) →L[ℝ] ℝ => f v) hleftmap
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] using hv
    have hrightvalue : L ((0 : Fin n → ℝ), s) = s * deriv (sineInterpolant θ c) t := by
      calc
        L ((0 : Fin n → ℝ), s) = L (s • ((0 : Fin n → ℝ), (1 : ℝ))) := by
          congr 1
          simp
        _ = s • L ((0 : Fin n → ℝ), (1 : ℝ)) := map_smul L s _
        _ = s * deriv (sineInterpolant θ c) t := by rw [hevalvalue, smul_eq_mul]
    calc
      L (v, s) = L (v, (0 : ℝ)) + L ((0 : Fin n → ℝ), s) := by
        rw [← map_add]
        congr 1
        simp
      _ = sineInterpolantJointDerivative θ c t (v, s) := by
        rw [hleftvalue, hrightvalue, sineInterpolantParameterDerivative_apply,
          sineInterpolantJointDerivative_apply]
  exact heq ▸ hH

end

end UnitCircleInterpolation
