/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.SaturatedRoots
import UnitCircleInterpolation.HomogeneousTrig
import UnitCircleInterpolation.InterpolantCalculus
import UnitCircleInterpolation.CyclicRolle
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Simple saturated roots on the complete circle

Saturation is proved separately on the finite Cayley chart and at its pole.
At a pole root, the top coefficient is zero; the remaining roots force the
previous coefficient to be nonzero. The global pole derivative then proves
simplicity there as well. Both parities and the degree-one edge case are included.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open Polynomial

namespace UnitCircleInterpolation

noncomputable section

lemma homogeneousTrig_distinct_root_count {m : ℕ} (p : ℕ) (P : ℝ[X])
    (hP : P ≠ 0) (hdegree : P.natDegree ≤ p) (root : Fin m → ℝ)
    (hinj : Function.Injective root) (hbound : ∀ i, root i ∈ Set.Ico 0 (2 * Real.pi))
    (hroot : ∀ i, homogeneousTrig p P (root i) = 0) : m ≤ p :=
  cayley_chart_distinct_root_count p (homogeneousTrig p P) P hP hdegree
    (fun t ht => (homogeneousTrig_eq_cos_pow_eval_tan p P hdegree t ht).symm)
    (homogeneousTrig_pi p P).symm root hinj hbound hroot

lemma homogeneousTrig_root_mem_of_saturated_roots (p : ℕ) (P : ℝ[X])
    (hP : P ≠ 0) (hdegree : P.natDegree ≤ p) (root : Fin p → ℝ)
    (hinj : Function.Injective root) (hbound : ∀ i, root i ∈ Set.Ico 0 (2 * Real.pi))
    (hroot : ∀ i, homogeneousTrig p P (root i) = 0) (t : ℝ)
    (ht : t ∈ Set.Ico 0 (2 * Real.pi)) (hz : homogeneousTrig p P t = 0) :
    ∃ i, root i = t :=
  cayley_chart_root_mem_of_saturated_roots p (homogeneousTrig p P) P hP hdegree
    (fun t ht => (homogeneousTrig_eq_cos_pow_eval_tan p P hdegree t ht).symm)
    (homogeneousTrig_pi p P).symm root hinj hbound hroot t ht hz

lemma deriv_homogeneousTrig_ne_zero_of_chart_root (p : ℕ) (P : ℝ[X])
    (hdegree : P.natDegree ≤ p) (t : ℝ) (ht : Real.cos (t / 2) ≠ 0)
    (hz : P.eval (Real.tan (t / 2)) = 0)
    (hd : P.derivative.eval (Real.tan (t / 2)) ≠ 0) :
    deriv (homogeneousTrig p P) t ≠ 0 := by
  rw [deriv_homogeneousTrig p P hdegree,
    homogeneousTrig_eq_cos_pow_eval_tan p (cayleyOperator p P)
      (cayleyOperator_natDegree_le p P hdegree) t ht,
    cayleyOperator_eval, hz, mul_zero, sub_zero]
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ ht)
    (mul_ne_zero (by positivity : (1 : ℝ) + Real.tan (t / 2) ^ 2 ≠ 0) hd))
      (by norm_num)

/-- A nonzero homogeneous trigonometric polynomial with `p` distinct cyclic roots
has a nonzero derivative at every listed root, including a root at `π`. -/
lemma deriv_homogeneousTrig_ne_zero_of_saturated_roots (p : ℕ) (P : ℝ[X])
    (hP : P ≠ 0) (hdegree : P.natDegree ≤ p) (root : Fin p → ℝ)
    (hinj : Function.Injective root) (hbound : ∀ i, root i ∈ Set.Ico 0 (2 * Real.pi))
    (hroot : ∀ i, homogeneousTrig p P (root i) = 0) (i : Fin p) :
    deriv (homogeneousTrig p P) (root i) ≠ 0 := by
  classical
  have heval (t : ℝ) (ht : Real.cos (t / 2) ≠ 0)
      (hz : homogeneousTrig p P t = 0) : P.eval (Real.tan (t / 2)) = 0 := by
    rw [homogeneousTrig_eq_cos_pow_eval_tan p P hdegree t ht] at hz
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ ht)
  by_cases hpole : ∃ j, root j = Real.pi
  · obtain ⟨j, hj⟩ := hpole
    have hp : 0 < p := Nat.zero_lt_of_lt j.isLt
    have htop : P.coeff p = 0 := by
      rw [← homogeneousTrig_pi p P, ← hj]
      exact hroot j
    have hdeglt : P.natDegree < p := by
      by_contra h
      have heq := le_antisymm hdegree (not_lt.mp h)
      have hcoeff := Polynomial.leadingCoeff_ne_zero.mpr hP
      rw [← Polynomial.coeff_natDegree, heq, htop] at hcoeff
      exact hcoeff rfl
    let rest := (Finset.univ.erase j : Finset (Fin p))
    have hcard : Fintype.card rest = p - 1 := by simp [rest]
    have hcos (k : rest) : Real.cos (root k.val / 2) ≠ 0 := by
      apply (cos_half_ne_zero_iff_of_mem_Ico (root k.val) (hbound k.val)).mpr
      intro h
      exact (Finset.mem_erase.mp k.property).1 (hinj (h.trans hj.symm))
    have htan : Function.Injective (fun k : rest => Real.tan (root k.val / 2)) := by
      intro k l h
      apply Subtype.ext
      apply hinj
      exact tan_half_injOn_Ico ⟨hbound k.val, hcos k⟩ ⟨hbound l.val, hcos l⟩ h
    have hrootP (k : rest) : P.eval (Real.tan (root k.val / 2)) = 0 :=
      heval _ (hcos k) (hroot k.val)
    have hdegRest : P.natDegree ≤ Fintype.card rest := by rw [hcard]; omega
    have hsat := polynomial_distinct_root_count P hP _ htan hrootP
    have hdegreeEq : P.natDegree = p - 1 := by rw [hcard] at hsat; omega
    have hprevious : P.coeff (p - 1) ≠ 0 := by
      rw [← hdegreeEq, Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hP
    by_cases hi : root i = Real.pi
    · rw [hi, deriv_homogeneousTrig_pi p P hp hdegree]
      exact div_ne_zero (neg_ne_zero.mpr hprevious) (by norm_num)
    · have hij : i ≠ j := fun h => hi (by rw [h, hj])
      let k : rest := ⟨i, Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩⟩
      exact deriv_homogeneousTrig_ne_zero_of_chart_root p P hdegree (root i)
        (hcos k) (hrootP k)
        (polynomial_derivative_ne_zero_of_saturated_roots P hP _ htan hdegRest hrootP k)
  · have hcos (j : Fin p) : Real.cos (root j / 2) ≠ 0 :=
      (cos_half_ne_zero_iff_of_mem_Ico (root j) (hbound j)).mpr
        (fun h => hpole ⟨j, h⟩)
    have htan : Function.Injective (fun j : Fin p => Real.tan (root j / 2)) := by
      intro j k h
      exact hinj (tan_half_injOn_Ico ⟨hbound j, hcos j⟩ ⟨hbound k, hcos k⟩ h)
    have hrootP (j : Fin p) : P.eval (Real.tan (root j / 2)) = 0 :=
      heval _ (hcos j) (hroot j)
    exact deriv_homogeneousTrig_ne_zero_of_chart_root p P hdegree (root i) (hcos i)
      (hrootP i) (polynomial_derivative_ne_zero_of_saturated_roots P hP _ htan
        (by simpa only [Fintype.card_fin] using hdegree) hrootP i)

variable {n : ℕ}

/-- The homogeneous representation agrees with the literal sine interpolant globally. -/
lemma homogeneousTrig_interpolantPolynomial (θ : Fin n → ℝ) (c : Fin n → ℝ) :
    homogeneousTrig (n - 1) (interpolantPolynomial θ c) = sineInterpolant θ c := by
  apply Continuous.ext_on dense_cos_half_ne_zero
    (continuous_homogeneousTrig _ _) (continuous_sineInterpolant θ c)
  intro t ht
  rw [homogeneousTrig_eq_cos_pow_eval_tan _ _ (interpolantPolynomial_natDegree_le θ c) t ht,
    cos_pow_mul_interpolantPolynomial_eval_tan θ c t ht]

lemma deriv_sineInterpolant_globalCayley (θ : Fin n → ℝ) (c : Fin n → ℝ) (t : ℝ) :
    deriv (sineInterpolant θ c) t =
      homogeneousTrig (n - 1) (cayleyOperator (n - 1) (interpolantPolynomial θ c)) t / 2 := by
  rw [← homogeneousTrig_interpolantPolynomial θ c]
  exact deriv_homogeneousTrig _ _ (interpolantPolynomial_natDegree_le θ c) t

lemma deriv_sineInterpolant_ne_zero_of_saturated_roots (θ : Fin n → ℝ) (c : Fin n → ℝ)
    (hP : interpolantPolynomial θ c ≠ 0) (root : Fin (n - 1) → ℝ)
    (hinj : Function.Injective root) (hbound : ∀ i, root i ∈ Set.Ico 0 (2 * Real.pi))
    (hroot : ∀ i, sineInterpolant θ c (root i) = 0) (i : Fin (n - 1)) :
    deriv (sineInterpolant θ c) (root i) ≠ 0 := by
  rw [← homogeneousTrig_interpolantPolynomial θ c]
  exact deriv_homogeneousTrig_ne_zero_of_saturated_roots _ _ hP
    (interpolantPolynomial_natDegree_le θ c) root hinj hbound
    (by rwa [homogeneousTrig_interpolantPolynomial θ c]) i

lemma cayleyOperator_interpolant_ne_zero_of_ne (θ : Fin n → ℝ) (c : Fin n → ℝ)
    (a b : ℝ) (hab : sineInterpolant θ c a ≠ sineInterpolant θ c b) :
    cayleyOperator (n - 1) (interpolantPolynomial θ c) ≠ 0 := by
  intro hzero
  apply hab
  apply is_const_of_deriv_eq_zero (differentiable_sineInterpolant θ c)
  intro t
  rw [deriv_sineInterpolant_globalCayley, hzero]
  simp [homogeneousTrig]

lemma deriv_sineInterpolant_distinct_root_count {m : ℕ} (θ : Fin n → ℝ) (c : Fin n → ℝ)
    (hP : cayleyOperator (n - 1) (interpolantPolynomial θ c) ≠ 0) (root : Fin m → ℝ)
    (hinj : Function.Injective root) (hbound : ∀ i, root i ∈ Set.Ico 0 (2 * Real.pi))
    (hroot : ∀ i, deriv (sineInterpolant θ c) (root i) = 0) : m ≤ n - 1 := by
  apply homogeneousTrig_distinct_root_count _ _ hP (derivativePolynomial_natDegree_le θ c)
    root hinj hbound
  intro i
  have h := hroot i
  rw [deriv_sineInterpolant_globalCayley] at h
  exact (div_eq_zero_iff.mp h).resolve_right (by norm_num)

lemma second_deriv_sineInterpolant_ne_zero_of_saturated_deriv_roots
    (θ : Fin n → ℝ) (c : Fin n → ℝ)
    (hP : cayleyOperator (n - 1) (interpolantPolynomial θ c) ≠ 0)
    (root : Fin (n - 1) → ℝ) (hinj : Function.Injective root)
    (hbound : ∀ i, root i ∈ Set.Ico 0 (2 * Real.pi))
    (hroot : ∀ i, deriv (sineInterpolant θ c) (root i) = 0) (i : Fin (n - 1)) :
    deriv (deriv (sineInterpolant θ c)) (root i) ≠ 0 := by
  have hrootH (j : Fin (n - 1)) : homogeneousTrig (n - 1)
      (cayleyOperator (n - 1) (interpolantPolynomial θ c)) (root j) = 0 := by
    have h := hroot j
    rw [deriv_sineInterpolant_globalCayley] at h
    exact (div_eq_zero_iff.mp h).resolve_right (by norm_num)
  have hsimple := deriv_homogeneousTrig_ne_zero_of_saturated_roots _ _ hP
    (derivativePolynomial_natDegree_le θ c) root hinj hbound hrootH i
  have heq : deriv (sineInterpolant θ c) = fun t => homogeneousTrig (n - 1)
      (cayleyOperator (n - 1) (interpolantPolynomial θ c)) t / 2 :=
    funext (deriv_sineInterpolant_globalCayley θ c)
  rw [heq, deriv_div_const]
  exact div_ne_zero hsimple (by norm_num)

lemma deriv_sineInterpolant_root_mem_of_saturated_roots (θ : Fin n → ℝ) (c : Fin n → ℝ)
    (hP : cayleyOperator (n - 1) (interpolantPolynomial θ c) ≠ 0)
    (root : Fin (n - 1) → ℝ) (hinj : Function.Injective root)
    (hbound : ∀ i, root i ∈ Set.Ico 0 (2 * Real.pi))
    (hroot : ∀ i, deriv (sineInterpolant θ c) (root i) = 0) (t : ℝ)
    (ht : t ∈ Set.Ico 0 (2 * Real.pi)) (hz : deriv (sineInterpolant θ c) t = 0) :
    ∃ i, root i = t := by
  have hconvert (s : ℝ) (hs : deriv (sineInterpolant θ c) s = 0) : homogeneousTrig (n - 1)
      (cayleyOperator (n - 1) (interpolantPolynomial θ c)) s = 0 := by
    rw [deriv_sineInterpolant_globalCayley] at hs
    exact (div_eq_zero_iff.mp hs).resolve_right (by norm_num)
  exact homogeneousTrig_root_mem_of_saturated_roots _ _ hP
    (derivativePolynomial_natDegree_le θ c) root hinj hbound
    (fun i => hconvert _ (hroot i)) t ht (hconvert t hz)

/-- Saturation makes every critical point in the full turn nondegenerate. -/
lemma second_deriv_sineInterpolant_ne_zero_at_critical (θ : Fin n → ℝ) (c : Fin n → ℝ)
    (hP : cayleyOperator (n - 1) (interpolantPolynomial θ c) ≠ 0)
    (root : Fin (n - 1) → ℝ) (hinj : Function.Injective root)
    (hbound : ∀ i, root i ∈ Set.Ico 0 (2 * Real.pi))
    (hroot : ∀ i, deriv (sineInterpolant θ c) (root i) = 0) (t : ℝ)
    (ht : t ∈ Set.Ico 0 (2 * Real.pi)) (hz : deriv (sineInterpolant θ c) t = 0) :
    deriv (deriv (sineInterpolant θ c)) t ≠ 0 := by
  obtain ⟨i, hi⟩ := deriv_sineInterpolant_root_mem_of_saturated_roots θ c hP
    root hinj hbound hroot t ht hz
  rw [← hi]
  exact second_deriv_sineInterpolant_ne_zero_of_saturated_deriv_roots θ c hP
    root hinj hbound hroot i

lemma exists_sineInterpolant_cyclic_deriv_roots (hn : 1 < n)
    (θ : Fin n → ℝ) (c : Fin n → ℝ) (root : Fin (n - 1) → ℝ)
    (hmono : StrictMono root) (hbound : ∀ i, root i ∈ Set.Ico 0 (2 * Real.pi))
    (hroot : ∀ i, sineInterpolant θ c (root i) = 0) :
    ∃ point : Fin (n - 1) → ℝ, Function.Injective point ∧
      (∀ i, point i ∈ Set.Ico 0 (2 * Real.pi)) ∧
      (∀ i, deriv (sineInterpolant θ c) (point i) = 0) := by
  apply exists_cyclic_deriv_roots (by omega) (2 * Real.pi) (by positivity)
    root hmono hbound _ (differentiable_sineInterpolant θ c) hroot
  · intro t ht
    exact (sineInterpolant_add_two_pi_eq_zero_iff θ c t).mpr ht
  · intro t ht
    rw [deriv_sineInterpolant] at ht ⊢
    exact (sineInterpolantDerivative_add_two_pi_eq_zero_iff θ c t).mp ht

/-- Critical points strictly interlace a saturated ordered zero list. Each cyclic
root arc has exactly one critical representative, rather than merely at least one. -/
lemma sineInterpolant_cyclic_critical_interlacing (hsize : 2 ≤ n)
    (θ : Fin n → ℝ) (c : Fin n → ℝ)
    (hP : cayleyOperator (n - 1) (interpolantPolynomial θ c) ≠ 0)
    (root : Fin (n - 1) → ℝ) (hmono : StrictMono root)
    (hbound : ∀ i, root i ∈ Set.Ico 0 (2 * Real.pi))
    (hroot : ∀ i, sineInterpolant θ c (root i) = 0) :
    ∃ critical : Fin (n - 1) → ℝ, Function.Injective critical ∧
      (∀ i, critical i ∈ Set.Ico 0 (2 * Real.pi)) ∧
      (∀ i, deriv (sineInterpolant θ c) (critical i) = 0) ∧
      (∀ i, critical i ∈ cyclicRootArc (by omega) root (2 * Real.pi) i) ∧
      (∀ i t, t ∈ cyclicRootArc (by omega) root (2 * Real.pi) i →
        deriv (sineInterpolant θ c) t = 0 → t = critical i) := by
  have hp : 0 < n - 1 := by omega
  obtain ⟨point, hpoint, hzero, hinj, hbound', hzero'⟩ :=
    exists_cyclic_rolle_points hp (2 * Real.pi) (by positivity) root hmono hbound
      (sineInterpolant θ c) (differentiable_sineInterpolant θ c) hroot
      (fun t ht => (sineInterpolant_add_two_pi_eq_zero_iff θ c t).mpr ht)
      (fun t ht => by
        rw [deriv_sineInterpolant] at ht ⊢
        exact (sineInterpolantDerivative_add_two_pi_eq_zero_iff θ c t).mp ht)
  let critical := fun i => cyclicRolleReduce (2 * Real.pi) (point i)
  refine ⟨critical, hinj, hbound', hzero', ?_, ?_⟩
  · intro i
    exact cyclicRolleReduce_mem_arc hp root _ hbound point hpoint i
  · intro i t ht hz
    have htbound : t ∈ Set.Ico 0 (2 * Real.pi) :=
      cyclicRootArc_mem_Ico hp root _ hbound ht
    obtain ⟨j, hj⟩ := deriv_sineInterpolant_root_mem_of_saturated_roots θ c hP
      critical hinj hbound' hzero' t htbound hz
    have hji : j = i := cyclicRolleReduce_index_eq_of_mem_arc hp root _ hmono hbound
      point hpoint (by change critical j ∈ _; rwa [hj])
    rw [hji] at hj
    exact hj.symm

end

end UnitCircleInterpolation
