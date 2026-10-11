/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.CayleyCardinal
import UnitCircleInterpolation.CayleyCircleChart
import Mathlib.Algebra.Polynomial.Roots

/-!
# Root counts on the complete circle

The non-pole roots inject into the real roots of the exact Cayley polynomial.
If the pole itself is a root, its top coefficient vanishes and the polynomial
degree decreases. Thus the bound includes the pole and both parities.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Polynomial

namespace UnitCircleInterpolation

noncomputable section

lemma polynomial_distinct_root_count {ι : Type*} [Fintype ι] (P : ℝ[X]) (hP : P ≠ 0)
    (root : ι → ℝ) (hinj : Function.Injective root) (hroot : ∀ i, P.eval (root i) = 0) :
    Fintype.card ι ≤ P.natDegree := by
  by_contra h
  exact hP (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hinj hroot
    (not_le.mp h))

variable {n m : ℕ}

/-- A complete-turn root bound from an exact finite chart and its pole value. -/
lemma cayley_chart_distinct_root_count (p : ℕ) (f : ℝ → ℝ) (P : ℝ[X])
    (hP : P ≠ 0) (hdegree : P.natDegree ≤ p)
    (hchart : ∀ t, Real.cos (t / 2) ≠ 0 →
      Real.cos (t / 2) ^ p * P.eval (Real.tan (t / 2)) = f t)
    (hpoleValue : P.coeff p = f Real.pi) (root : Fin m → ℝ)
    (hinj : Function.Injective root) (hbound : ∀ i, root i ∈ Set.Ico 0 (2 * Real.pi))
    (hroot : ∀ i, f (root i) = 0) : m ≤ p := by
  classical
  have heval (t : ℝ) (ht : Real.cos (t / 2) ≠ 0)
      (hz : f t = 0) : P.eval (Real.tan (t / 2)) = 0 := by
    have h := (hchart t ht).trans hz
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ ht)
  by_cases hpole : ∃ j, root j = Real.pi
  · obtain ⟨j, hj⟩ := hpole
    let rest := (Finset.univ.erase j : Finset (Fin m))
    have hcos (i : rest) : Real.cos (root i.val / 2) ≠ 0 := by
      apply (cos_half_ne_zero_iff_of_mem_Ico (root i.val) (hbound i.val)).mpr
      intro h
      exact (Finset.mem_erase.mp i.property).1 (hinj (h.trans hj.symm))
    have htan : Function.Injective (fun i : rest => Real.tan (root i.val / 2)) := by
      intro i k h
      apply Subtype.ext
      apply hinj
      exact tan_half_injOn_Ico ⟨hbound i.val, hcos i⟩ ⟨hbound k.val, hcos k⟩ h
    have hc := polynomial_distinct_root_count P hP
      (fun i : rest => Real.tan (root i.val / 2)) htan
      (fun i => heval _ (hcos i) (hroot i.val))
    have hcard : Fintype.card rest = m - 1 := by simp [rest]
    rw [hcard] at hc
    have hz : f Real.pi = 0 := by rw [← hj]; exact hroot j
    have hd : P.natDegree < p := by
      by_contra hlt
      have heq : P.natDegree = p := le_antisymm hdegree (not_lt.mp hlt)
      have hcoeff : P.coeff P.natDegree ≠ 0 := by
        simpa only [Polynomial.coeff_natDegree] using Polynomial.leadingCoeff_ne_zero.mpr hP
      rw [heq, hpoleValue, hz] at hcoeff
      exact hcoeff rfl
    have hm : 0 < m := Nat.zero_lt_of_lt j.isLt
    omega
  · have hcos (i : Fin m) : Real.cos (root i / 2) ≠ 0 :=
      (cos_half_ne_zero_iff_of_mem_Ico (root i) (hbound i)).mpr (fun h => hpole ⟨i, h⟩)
    have htan : Function.Injective (fun i : Fin m => Real.tan (root i / 2)) := by
      intro i j h
      exact hinj (tan_half_injOn_Ico ⟨hbound i, hcos i⟩ ⟨hbound j, hcos j⟩ h)
    have hc := polynomial_distinct_root_count P hP
      (fun i : Fin m => Real.tan (root i / 2)) htan
      (fun i => heval _ (hcos i) (hroot i))
    simpa only [Fintype.card_fin] using hc.trans hdegree

/-- Nonzero nodal data give a nonzero polynomial even when the node is the chart pole. -/
lemma interpolantPolynomial_ne_zero_of_node (θ : Fin n → ℝ)
    (hθ : Function.Injective (phaseNodes θ)) (hbound : ∀ i, θ i ∈ Set.Ico 0 (2 * Real.pi))
    (c : Fin n → ℝ) (i : Fin n) (hci : c i ≠ 0) :
    interpolantPolynomial θ c ≠ 0 := by
  by_cases hpole : θ i = Real.pi
  · apply interpolantPolynomial_ne_zero_of_value_at_pi θ c
    have h := sineInterpolant_at_node θ hθ c i
    rw [hpole] at h
    rwa [h]
  · exact interpolantPolynomial_ne_zero_of_node_on_chart θ hθ c i
      ((cos_half_ne_zero_iff_of_mem_Ico (θ i) (hbound i)).mpr hpole) hci

/-- Exact degree bounds count every distinct zero in a full half-open turn. -/
lemma sineInterpolant_distinct_root_count (θ : Fin n → ℝ) (c : Fin n → ℝ)
    (hP : interpolantPolynomial θ c ≠ 0) (root : Fin m → ℝ)
    (hinj : Function.Injective root) (hbound : ∀ i, root i ∈ Set.Ico 0 (2 * Real.pi))
    (hroot : ∀ i, sineInterpolant θ c (root i) = 0) : m ≤ n - 1 :=
  cayley_chart_distinct_root_count (n - 1) (sineInterpolant θ c)
    (interpolantPolynomial θ c) hP (interpolantPolynomial_natDegree_le θ c)
    (cos_pow_mul_interpolantPolynomial_eval_tan θ c) (interpolantPolynomial_coeff_top θ c)
    root hinj hbound hroot

/-- The circle bound applies directly to actual interpolation data with a nonzero node. -/
lemma sineInterpolant_distinct_root_count_of_node (θ : Fin n → ℝ)
    (hθ : Function.Injective (phaseNodes θ)) (hθbound : ∀ i, θ i ∈ Set.Ico 0 (2 * Real.pi))
    (c : Fin n → ℝ) (i : Fin n) (hci : c i ≠ 0) (root : Fin m → ℝ)
    (hinj : Function.Injective root) (hbound : ∀ k, root k ∈ Set.Ico 0 (2 * Real.pi))
    (hroot : ∀ k, sineInterpolant θ c (root k) = 0) : m ≤ n - 1 :=
  sineInterpolant_distinct_root_count θ c
    (interpolantPolynomial_ne_zero_of_node θ hθ hθbound c i hci) root hinj hbound hroot

end

end UnitCircleInterpolation
