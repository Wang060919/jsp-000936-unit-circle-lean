/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.InterpolantCalculus
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Joint smoothness of the actual sine interpolants

The parameter is the literal finite angle family together with the evaluation
angle. At distinct complex phases every denominator is nonzero, so scalar sine
ratios, their finite products, and the signed finite sum are jointly smooth.
The explicit ordinary derivative is jointly smooth on the same domain.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators ContDiff

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ}

/-- Distinct actual complex phases form an open set of finite real angle parameters. -/
lemma isOpen_phaseNodes_injective :
    IsOpen {θ : Fin n → ℝ | Function.Injective (phaseNodes θ)} := by
  have hcont (i : Fin n) : Continuous (fun θ : Fin n → ℝ => phaseNodes θ i) := by
    unfold phaseNodes
    fun_prop
  have heq : {θ : Fin n → ℝ | Function.Injective (phaseNodes θ)} =
      ⋂ i : Fin n, ⋂ j : Fin n,
        {θ : Fin n → ℝ | i = j ∨ phaseNodes θ i ≠ phaseNodes θ j} := by
    ext θ
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h i j
      by_cases hij : i = j
      · exact Or.inl hij
      · exact Or.inr (fun he => hij (h he))
    · intro h i j he
      rcases h i j with hij | hij
      · exact hij
      · exact (hij he).elim
  rw [heq]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  by_cases hij : i = j
  · simp only [hij, true_or, Set.ofPred_true]
    exact isOpen_univ
  · simp only [hij, false_or]
    exact isOpen_ne_fun (hcont i) (hcont j)

/-- Adding an unrestricted real evaluation angle preserves the open parameter domain. -/
lemma isOpen_joint_phaseNodes_injective :
    IsOpen {x : (Fin n → ℝ) × ℝ | Function.Injective (phaseNodes x.1)} :=
  isOpen_phaseNodes_injective.preimage continuous_fst

/-- Moving one actual node preserves phase distinctness for all sufficiently small moves. -/
lemma eventually_phaseNodes_injective_update (θ : Fin n → ℝ) (j : Fin n)
    (hθ : Function.Injective (phaseNodes θ)) :
    ∀ᶠ u in nhds (θ j), Function.Injective (phaseNodes (Function.update θ j u)) := by
  have hevent : ∀ᶠ η in nhds θ, Function.Injective (phaseNodes η) :=
    isOpen_phaseNodes_injective.eventually_mem hθ
  have hsmooth : ContDiff ℝ 0 (Function.update θ j) := contDiff_update 0 θ j
  have hcont : Continuous (Function.update θ j) := hsmooth.continuous
  have htendsto : Filter.Tendsto (Function.update θ j) (nhds (θ j)) (nhds θ) := by
    have ht : ContinuousAt (Function.update θ j) (θ j) := hcont.continuousAt
    change Filter.Tendsto (Function.update θ j) (nhds (θ j))
      (nhds (Function.update θ j (θ j))) at ht
    simpa only [Function.update_eq_self] using ht
  exact htendsto.eventually hevent

/-- A scalar sine denominator is globally smooth in the actual angle parameters. -/
lemma contDiff_sine_denominator (m : ℕ∞ω) (j k : Fin n) :
    ContDiff ℝ m (fun θ : Fin n → ℝ => Real.sin ((θ j - θ k) / 2)) := by
  exact (((contDiff_apply ℝ ℝ j).sub (contDiff_apply ℝ ℝ k)).div_const 2).sin

/-- Each off-diagonal sine ratio is jointly smooth at every distinct phase family. -/
lemma contDiffAt_sine_ratio_joint (m : ℕ∞ω) (θ : Fin n → ℝ) (t : ℝ)
    (hθ : Function.Injective (phaseNodes θ)) (j k : Fin n) (hjk : j ≠ k) :
    ContDiffAt ℝ m (fun x : (Fin n → ℝ) × ℝ =>
      Real.sin ((x.2 - x.1 k) / 2) / Real.sin ((x.1 j - x.1 k) / 2)) (θ, t) := by
  have hk : ContDiff ℝ m (fun x : (Fin n → ℝ) × ℝ => x.1 k) :=
    (contDiff_apply ℝ ℝ k).comp contDiff_fst
  have hnum : ContDiff ℝ m (fun x : (Fin n → ℝ) × ℝ =>
      Real.sin ((x.2 - x.1 k) / 2)) :=
    ((contDiff_snd.sub hk).div_const 2).sin
  have hden : ContDiff ℝ m (fun x : (Fin n → ℝ) × ℝ =>
      Real.sin ((x.1 j - x.1 k) / 2)) :=
    (contDiff_sine_denominator m j k).comp contDiff_fst
  exact hnum.contDiffAt.div hden.contDiffAt (sine_denominator_ne_zero θ hθ hjk)

/-- The literal finite sine product is jointly smooth, including at its zeros. -/
lemma contDiffAt_sineCardinal_joint (m : ℕ∞ω) (θ : Fin n → ℝ) (t : ℝ)
    (hθ : Function.Injective (phaseNodes θ)) (j : Fin n) :
    ContDiffAt ℝ m (fun x : (Fin n → ℝ) × ℝ => sineCardinal x.1 j x.2) (θ, t) := by
  unfold sineCardinal
  apply contDiffAt_prod
  intro k hk
  exact contDiffAt_sine_ratio_joint m θ t hθ j k (Finset.mem_erase.mp hk).1.symm

/-- For fixed real nodal values, the actual interpolant is jointly smooth to every order. -/
lemma contDiffAt_sineInterpolant_joint (m : ℕ∞ω) (θ : Fin n → ℝ) (t : ℝ)
    (c : Fin n → ℝ) (hθ : Function.Injective (phaseNodes θ)) :
    ContDiffAt ℝ m (fun x : (Fin n → ℝ) × ℝ => sineInterpolant x.1 c x.2) (θ, t) := by
  unfold sineInterpolant
  apply ContDiffAt.sum
  intro j hj
  exact contDiffAt_const.mul (contDiffAt_sineCardinal_joint m θ t hθ j)

/-- The same explicit product-rule formula is jointly smooth in parameters and angle. -/
lemma contDiffAt_sineCardinalDerivative_joint (m : ℕ∞ω) (θ : Fin n → ℝ) (t : ℝ)
    (hθ : Function.Injective (phaseNodes θ)) (j : Fin n) :
    ContDiffAt ℝ m (fun x : (Fin n → ℝ) × ℝ =>
      sineCardinalDerivative x.1 j x.2) (θ, t) := by
  unfold sineCardinalDerivative
  apply ContDiffAt.sum
  intro k hk
  apply ContDiffAt.mul
  · apply contDiffAt_prod
    intro l hl
    exact contDiffAt_sine_ratio_joint m θ t hθ j l
      (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1.symm
  · have hkcoord : ContDiff ℝ m (fun x : (Fin n → ℝ) × ℝ => x.1 k) :=
      (contDiff_apply ℝ ℝ k).comp contDiff_fst
    have hnum : ContDiff ℝ m (fun x : (Fin n → ℝ) × ℝ =>
        Real.cos ((x.2 - x.1 k) / 2) / 2) :=
      (((contDiff_snd.sub hkcoord).div_const 2).cos).div_const 2
    have hden : ContDiff ℝ m (fun x : (Fin n → ℝ) × ℝ =>
        Real.sin ((x.1 j - x.1 k) / 2)) :=
      (contDiff_sine_denominator m j k).comp contDiff_fst
    exact hnum.contDiffAt.div hden.contDiffAt
      (sine_denominator_ne_zero θ hθ (Finset.mem_erase.mp hk).1.symm)

/-- The ordinary derivative of the actual interpolant is jointly smooth to every order. -/
lemma contDiffAt_sineInterpolantDerivative_joint (m : ℕ∞ω)
    (θ : Fin n → ℝ) (t : ℝ) (c : Fin n → ℝ)
    (hθ : Function.Injective (phaseNodes θ)) :
    ContDiffAt ℝ m (fun x : (Fin n → ℝ) × ℝ =>
      sineInterpolantDerivative x.1 c x.2) (θ, t) := by
  unfold sineInterpolantDerivative
  apply ContDiffAt.sum
  intro j hj
  exact contDiffAt_const.mul (contDiffAt_sineCardinalDerivative_joint m θ t hθ j)

/-- Joint smoothness also holds with the ordinary derivative written literally. -/
lemma contDiffAt_deriv_sineInterpolant_joint (m : ℕ∞ω)
    (θ : Fin n → ℝ) (t : ℝ) (c : Fin n → ℝ)
    (hθ : Function.Injective (phaseNodes θ)) :
    ContDiffAt ℝ m (fun x : (Fin n → ℝ) × ℝ =>
      deriv (sineInterpolant x.1 c) x.2) (θ, t) := by
  simpa only [deriv_sineInterpolant] using
    contDiffAt_sineInterpolantDerivative_joint m θ t c hθ

/-- The actual interpolant is smooth on the full open domain of distinct phases. -/
lemma contDiffOn_sineInterpolant_joint (m : ℕ∞ω) (c : Fin n → ℝ) :
    ContDiffOn ℝ m (fun x : (Fin n → ℝ) × ℝ => sineInterpolant x.1 c x.2)
      {x : (Fin n → ℝ) × ℝ | Function.Injective (phaseNodes x.1)} := by
  intro x hx
  exact (contDiffAt_sineInterpolant_joint m x.1 x.2 c hx).contDiffWithinAt

/-- The actual ordinary derivative is smooth on the same full open parameter domain. -/
lemma contDiffOn_deriv_sineInterpolant_joint (m : ℕ∞ω) (c : Fin n → ℝ) :
    ContDiffOn ℝ m (fun x : (Fin n → ℝ) × ℝ => deriv (sineInterpolant x.1 c) x.2)
      {x : (Fin n → ℝ) × ℝ | Function.Injective (phaseNodes x.1)} := by
  intro x hx
  exact (contDiffAt_deriv_sineInterpolant_joint m x.1 x.2 c hx).contDiffWithinAt

/-- Holding the evaluation angle fixed leaves a smooth map of the actual node parameters. -/
lemma contDiffAt_sineInterpolant_parameters (m : ℕ∞ω) (θ : Fin n → ℝ)
    (c : Fin n → ℝ) (t : ℝ) (hθ : Function.Injective (phaseNodes θ)) :
    ContDiffAt ℝ m (fun η : Fin n → ℝ => sineInterpolant η c t) θ := by
  have hmap : ContDiffAt ℝ m (fun η : Fin n → ℝ => (η, t)) θ :=
    contDiffAt_id.prodMk contDiffAt_const
  have hjoint := contDiffAt_sineInterpolant_joint m θ t c hθ
  have hcomp := hjoint.comp θ hmap
  exact hcomp

/-- Updating one node therefore gives a smooth genuine scalar parameter curve. -/
lemma contDiffAt_sineInterpolant_update (m : ℕ∞ω) (θ : Fin n → ℝ)
    (c : Fin n → ℝ) (j : Fin n) (t : ℝ)
    (hθ : Function.Injective (phaseNodes θ)) :
    ContDiffAt ℝ m (fun u : ℝ => sineInterpolant (Function.update θ j u) c t) (θ j) := by
  have hmap : ContDiff ℝ m (Function.update θ j) := contDiff_update m θ j
  have hbase : ContDiffAt ℝ m (fun η : Fin n → ℝ => sineInterpolant η c t)
      (Function.update θ j (θ j)) := by
    simpa only [Function.update_eq_self] using
      contDiffAt_sineInterpolant_parameters m θ c t hθ
  have hcomp := hbase.comp (θ j) hmap.contDiffAt
  exact hcomp

end

end UnitCircleInterpolation
