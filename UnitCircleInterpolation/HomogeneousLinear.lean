/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.CircularSimpleRoots
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Linearity and uniqueness of the homogeneous circular model

All operations use the division-free model on the entire real angle line.
The root uniqueness statement uses canonical representatives in `[0, 2π)`;
it therefore includes the half-angle tangent pole.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace UnitCircleInterpolation

noncomputable section

open Polynomial

@[simp]
lemma homogeneousTrig_zeroPolynomial (p : ℕ) (t : ℝ) :
    homogeneousTrig p (0 : ℝ[X]) t = 0 := by
  simp [homogeneousTrig]

lemma homogeneousTrig_add (p : ℕ) (P Q : ℝ[X]) (t : ℝ) :
    homogeneousTrig p (P + Q) t = homogeneousTrig p P t + homogeneousTrig p Q t := by
  simp only [homogeneousTrig, Polynomial.coeff_add, add_mul, Finset.sum_add_distrib]

lemma homogeneousTrig_C_mul (p : ℕ) (a : ℝ) (P : ℝ[X]) (t : ℝ) :
    homogeneousTrig p (C a * P) t = a * homogeneousTrig p P t := by
  simp only [homogeneousTrig, Polynomial.coeff_C_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma homogeneousTrig_finset_sum {ι : Type*} (p : ℕ) (s : Finset ι)
    (P : ι → ℝ[X]) (t : ℝ) :
    homogeneousTrig p (∑ i ∈ s, P i) t = ∑ i ∈ s, homogeneousTrig p (P i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, homogeneousTrig_add, ih]

lemma homogeneousTrig_linear_combination {ι : Type*} (p : ℕ) (s : Finset ι)
    (a : ι → ℝ) (P : ι → ℝ[X]) (t : ℝ) :
    homogeneousTrig p (∑ i ∈ s, C (a i) * P i) t =
      ∑ i ∈ s, a i * homogeneousTrig p (P i) t := by
  rw [homogeneousTrig_finset_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact homogeneousTrig_C_mul p (a i) (P i) t

lemma homogeneousTrig_natDegree_linear_combination_le {ι : Type*}
    (p : ℕ) (s : Finset ι) (a : ι → ℝ) (P : ι → ℝ[X])
    (hP : ∀ i ∈ s, (P i).natDegree ≤ p) :
    (∑ i ∈ s, C (a i) * P i).natDegree ≤ p := by
  exact Polynomial.natDegree_sum_le_of_forall_le _ _
    (fun i hi => (Polynomial.natDegree_C_mul_le _ _).trans (hP i hi))

/-- `p+1` distinct canonical circle roots force the polynomial itself to vanish. -/
lemma homogeneousTrig_eq_zero_of_distinct_roots (p : ℕ) (P : ℝ[X])
    (hdegree : P.natDegree ≤ p) (root : Fin (p + 1) → ℝ)
    (hinj : Function.Injective root) (hbound : ∀ i, root i ∈ Set.Ico 0 (2 * Real.pi))
    (hroot : ∀ i, homogeneousTrig p P (root i) = 0) : P = 0 := by
  by_contra hP
  have hcount := homogeneousTrig_distinct_root_count p P hP hdegree root hinj hbound hroot
  omega

/-- A bounded-degree homogeneous model is faithful as a function on all angles. -/
lemma homogeneousTrig_eq_zero_iff (p : ℕ) (P : ℝ[X])
    (hdegree : P.natDegree ≤ p) : homogeneousTrig p P = 0 ↔ P = 0 := by
  constructor
  · intro hzero
    let root : Fin (p + 1) → ℝ := fun i => 2 * Real.pi * i.val / (p + 1)
    have hden : (0 : ℝ) < p + 1 := by positivity
    have hmono : StrictMono root := by
      intro i j hij
      dsimp [root]
      apply div_lt_div_of_pos_right _ hden
      exact mul_lt_mul_of_pos_left (by exact_mod_cast hij) (by positivity)
    apply homogeneousTrig_eq_zero_of_distinct_roots p P hdegree root hmono.injective
    · intro i
      constructor
      · dsimp [root]
        positivity
      · dsimp [root]
        apply (div_lt_iff₀ hden).mpr
        have hi : (i.val : ℝ) < p + 1 := by exact_mod_cast i.isLt
        nlinarith [Real.pi_pos]
    · intro i
      exact congrFun hzero (root i)
  · rintro rfl
    funext t
    exact homogeneousTrig_zeroPolynomial p t

/-- A bounded-degree polynomial relation is equivalent to its full-angle relation. -/
lemma homogeneousTrig_linear_combination_eq_zero_iff {ι : Type*} (p : ℕ)
    (s : Finset ι) (a : ι → ℝ) (P : ι → ℝ[X])
    (hP : ∀ i ∈ s, (P i).natDegree ≤ p) :
    (∑ i ∈ s, C (a i) * P i) = 0 ↔
      ∀ t, (∑ i ∈ s, a i * homogeneousTrig p (P i) t) = 0 := by
  constructor
  · intro hzero t
    rw [← homogeneousTrig_linear_combination, hzero]
    exact homogeneousTrig_zeroPolynomial p t
  · intro hzero
    apply (homogeneousTrig_eq_zero_iff p _
      (homogeneousTrig_natDegree_linear_combination_le p s a P hP)).mp
    funext t
    rw [homogeneousTrig_linear_combination]
    exact hzero t

/-- The actual finite-degree continuous-function space used by the circle kernel. -/
def homogeneousTrigSpace (p : ℕ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | ∃ P : ℝ[X], P.natDegree ≤ p ∧ f = homogeneousTrig p P}
  zero_mem' := ⟨0, by simp, by funext t; simp⟩
  add_mem' := by
    rintro f g ⟨P, hP, rfl⟩ ⟨Q, hQ, rfl⟩
    refine ⟨P + Q, Polynomial.natDegree_add_le_of_degree_le hP hQ, ?_⟩
    funext t
    exact (homogeneousTrig_add p P Q t).symm
  smul_mem' := by
    rintro a f ⟨P, hP, rfl⟩
    refine ⟨C a * P, (Polynomial.natDegree_C_mul_le a P).trans hP, ?_⟩
    funext t
    exact (homogeneousTrig_C_mul p a P t).symm

lemma homogeneousTrig_mem_space (p : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ p) :
    homogeneousTrig p P ∈ homogeneousTrigSpace p := ⟨P, hP, rfl⟩

lemma continuous_of_mem_homogeneousTrigSpace (p : ℕ) (f : ℝ → ℝ)
    (hf : f ∈ homogeneousTrigSpace p) : Continuous f := by
  rcases hf with ⟨P, hP, rfl⟩
  exact continuous_homogeneousTrig p P

lemma distinct_root_count_of_mem_homogeneousTrigSpace {m : ℕ} (p : ℕ)
    (f : ℝ → ℝ) (hf : f ∈ homogeneousTrigSpace p) (hne : f ≠ 0)
    (root : Fin m → ℝ) (hinj : Function.Injective root)
    (hbound : ∀ i, root i ∈ Set.Ico 0 (2 * Real.pi))
    (hroot : ∀ i, f (root i) = 0) : m ≤ p := by
  rcases hf with ⟨P, hP, rfl⟩
  have hPne : P ≠ 0 := by
    rintro rfl
    apply hne
    funext t
    exact homogeneousTrig_zeroPolynomial p t
  exact homogeneousTrig_distinct_root_count p P hPne hP root hinj hbound hroot

end

end UnitCircleInterpolation
