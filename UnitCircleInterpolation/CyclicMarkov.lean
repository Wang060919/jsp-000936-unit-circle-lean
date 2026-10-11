/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.InterpolantShift
import UnitCircleInterpolation.MarkovKernel
import UnitCircleInterpolation.SaturatedRoots

/-!
# Conditional cyclic Markov transfer for the actual sine interpolants

A list of `n - 1` distinct cyclic zeros of one actual sine interpolant, together
with a positive product of the other interpolant and its derivative at every
listed zero, implies a strictly negative Wronskian at every real angle. The proof
chooses a translation separately for each evaluation point, so no cyclic root is
lost at a fixed Cayley pole.

The residue signs are explicit hypotheses. This file does not establish them
for the cross-gap interpolants in the minimizer problem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open Polynomial

namespace UnitCircleInterpolation

noncomputable section

/-- Saturation forces a polynomial to be a nonzero constant multiple of the
product of its listed distinct roots. -/
lemma polynomial_eq_finiteRootProduct_mul_C {m : ℕ}
    (P : ℝ[X]) (hP : P ≠ 0) (r : Fin m → ℝ) (hinj : Function.Injective r)
    (hdegree : P.natDegree ≤ m) (hroot : ∀ i, P.eval (r i) = 0) :
    ∃ scale : ℝ, scale ≠ 0 ∧ P = finiteRootProduct r * C scale := by
  classical
  let M : ℝ[X] := finiteRootProduct r
  have hMmonic : M.Monic := by
    change (∏ i ∈ (Finset.univ : Finset (Fin m)), (X - C (r i))).Monic
    exact monic_prod_of_monic _ _ fun i _hi => monic_X_sub_C (r i)
  have hMdegree : M.natDegree = m := by
    change (∏ i ∈ (Finset.univ : Finset (Fin m)), (X - C (r i))).natDegree = m
    rw [natDegree_finsetProd_X_sub_C_eq_card, Finset.card_univ, Fintype.card_fin]
  have hdvd : M ∣ P := by
    change (∏ i : Fin m, (X - C (r i))) ∣ P
    apply Fintype.prod_dvd_of_coprime
    · exact pairwise_coprime_X_sub_C hinj
    · intro i
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
      exact hroot i
  obtain ⟨Q, hQ⟩ := hdvd
  have hQne : Q ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hQ
    exact hP hQ
  have hQdegree : Q.natDegree = 0 := by
    have hproduct : (M * Q).natDegree ≤ m := by rw [← hQ]; exact hdegree
    rw [Polynomial.natDegree_mul hMmonic.ne_zero hQne, hMdegree] at hproduct
    omega
  obtain ⟨scale, hscale⟩ := Polynomial.natDegree_eq_zero.mp hQdegree
  refine ⟨scale, ?_, ?_⟩
  · intro hz
    apply hQne
    rw [← hscale, hz, Polynomial.C_0]
  · rw [← hscale] at hQ
    exact hQ

/-- The finite Markov theorem stated for an arbitrary saturated polynomial,
with the same orientation as `polynomialWronskian`. -/
lemma polynomialWronskian_neg_of_saturated_root_residues {m : ℕ} (hm : 0 < m)
    (P Q : ℝ[X]) (hP : P ≠ 0) (r : Fin m → ℝ) (hinj : Function.Injective r)
    (hPdegree : P.natDegree ≤ m) (hQdegree : Q.natDegree ≤ m)
    (hroot : ∀ i, P.eval (r i) = 0)
    (hresidue : ∀ i, 0 < Q.eval (r i) * P.derivative.eval (r i)) (x : ℝ) :
    polynomialWronskian P Q x < 0 := by
  obtain ⟨scale, hscale, hfactor⟩ :=
    polynomial_eq_finiteRootProduct_mul_C P hP r hinj hPdegree hroot
  rw [hfactor] at hresidue ⊢
  exact finite_markov_wronskian_neg hm r hinj scale hscale Q hQdegree hresidue x

variable {n : ℕ}

/-- A root with a positive trigonometric residue gives a positive polynomial
residue on every chart containing that root. -/
lemma interpolantPolynomial_residue_pos_on_chart
    (θ d c : Fin n → ℝ) (r : ℝ) (hcos : Real.cos (r / 2) ≠ 0)
    (hroot : sineInterpolant θ d r = 0)
    (hresidue : 0 < sineInterpolant θ c r * deriv (sineInterpolant θ d) r) :
    0 < (interpolantPolynomial θ c).eval (Real.tan (r / 2)) *
      (interpolantPolynomial θ d).derivative.eval (Real.tan (r / 2)) := by
  have hPeval : (interpolantPolynomial θ d).eval (Real.tan (r / 2)) = 0 := by
    have hz := (cos_pow_mul_interpolantPolynomial_eval_tan θ d r hcos).trans hroot
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hcos)
  have hW : sineWronskian θ d c r < 0 := by
    unfold sineWronskian
    rw [hroot, zero_mul, zero_sub]
    nlinarith
  have hpolyW := (sineWronskian_neg_on_chart_iff θ d c r hcos).mp hW
  unfold polynomialWronskian at hpolyW
  rw [hPeval, zero_mul, zero_sub] at hpolyW
  nlinarith

/-- The direct finite-chart interface keeps injectivity and all root chart
conditions explicit. The root list has exactly the degree bound `n - 1`. -/
lemma sineWronskian_neg_on_chart_of_saturated_root_residues
    (hn : 2 ≤ n) (θ d c : Fin n → ℝ) (root : Fin (n - 1) → ℝ)
    (htan : Function.Injective (fun i => Real.tan (root i / 2)))
    (hcos : ∀ i, Real.cos (root i / 2) ≠ 0)
    (hroot : ∀ i, sineInterpolant θ d (root i) = 0)
    (hresidue : ∀ i,
      0 < sineInterpolant θ c (root i) * deriv (sineInterpolant θ d) (root i))
    (t : ℝ) (ht : Real.cos (t / 2) ≠ 0) : sineWronskian θ d c t < 0 := by
  have hm : 0 < n - 1 := by omega
  have hPeval : ∀ i,
      (interpolantPolynomial θ d).eval (Real.tan (root i / 2)) = 0 := by
    intro i
    have hz := (cos_pow_mul_interpolantPolynomial_eval_tan θ d (root i) (hcos i)).trans
      (hroot i)
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ (hcos i))
  have hpresidue : ∀ i,
      0 < (interpolantPolynomial θ c).eval (Real.tan (root i / 2)) *
        (interpolantPolynomial θ d).derivative.eval (Real.tan (root i / 2)) :=
    fun i => interpolantPolynomial_residue_pos_on_chart θ d c (root i)
      (hcos i) (hroot i) (hresidue i)
  have hP : interpolantPolynomial θ d ≠ 0 := by
    intro hz
    have hpos := hpresidue ⟨0, hm⟩
    simp only [hz, Polynomial.derivative_zero, Polynomial.eval_zero, mul_zero,
      lt_self_iff_false] at hpos
  apply sineWronskian_neg_of_polynomialWronskian_neg θ d c t ht
  exact polynomialWronskian_neg_of_saturated_root_residues hm
    (interpolantPolynomial θ d) (interpolantPolynomial θ c) hP
    (fun i => Real.tan (root i / 2)) htan
    (interpolantPolynomial_natDegree_le θ d) (interpolantPolynomial_natDegree_le θ c)
    hPeval hpresidue (Real.tan (t / 2))

/-- Conditional Markov transfer on the complete circle. Every evaluation angle,
including an original Cayley pole, is covered by a translation that avoids all
`n - 1` roots and that evaluation point simultaneously. -/
theorem sineWronskian_neg_of_cyclic_root_residues
    (hn : 2 ≤ n) (θ d c : Fin n → ℝ) (root : Fin (n - 1) → ℝ)
    (hinj : Function.Injective root)
    (hbound : ∀ i, root i ∈ Set.Ico 0 (2 * Real.pi))
    (hroot : ∀ i, sineInterpolant θ d (root i) = 0)
    (hresidue : ∀ i,
      0 < sineInterpolant θ c (root i) * deriv (sineInterpolant θ d) (root i))
    (t : ℝ) : sineWronskian θ d c t < 0 := by
  obtain ⟨a, ht, hcos⟩ := exists_shift_cos_half_ne_zero_roots_and_point root t
  rw [← sineWronskian_shift θ d c a t]
  apply sineWronskian_neg_on_chart_of_saturated_root_residues hn
    (shiftedAngles θ a) d c (fun i => root i + a)
    (shifted_tan_half_injective root hinj hbound a hcos) hcos
  · intro i
    rw [sineInterpolant_shift]
    exact hroot i
  · intro i
    rw [sineInterpolant_shift, deriv_sineInterpolant_shift]
    exact hresidue i
  · exact ht

end

end UnitCircleInterpolation
