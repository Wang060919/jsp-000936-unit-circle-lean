/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.TrigPolynomial
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# A homogeneous trigonometric pullback without coordinate division

The finite coefficient expansion below is defined at every real angle, including
the tangent-chart poles. On the chart it agrees with the weighted polynomial
representation, and its value at `π` is the top homogeneous coefficient.

The global derivative theorem is obtained from the explicit finite-sum derivative
and equality of continuous functions on the dense finite-coordinate chart.
The degree hypothesis is literal and the degree-zero case is included.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace UnitCircleInterpolation

noncomputable section

open Polynomial

/-- The homogeneous degree-`p` sine/cosine expansion, defined without division everywhere. -/
def homogeneousTrig (p : ℕ) (P : ℝ[X]) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (p + 1),
    P.coeff k * Real.sin (t / 2) ^ k * Real.cos (t / 2) ^ (p - k)

@[simp]
lemma homogeneousTrig_zero (P : ℝ[X]) (t : ℝ) :
    homogeneousTrig 0 P t = P.coeff 0 := by
  simp [homogeneousTrig]

/-- The division-free homogeneous expansion equals its Cayley formula on chart. -/
lemma homogeneousTrig_eq_cos_pow_eval_tan (p : ℕ) (P : ℝ[X])
    (hP : P.natDegree ≤ p) (t : ℝ) (ht : Real.cos (t / 2) ≠ 0) :
    homogeneousTrig p P t = Real.cos (t / 2) ^ p * P.eval (Real.tan (t / 2)) := by
  rw [Polynomial.eval_eq_sum_range' (show P.natDegree < p + 1 from by omega)]
  unfold homogeneousTrig
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkp : k ≤ p := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hpow : Real.cos (t / 2) ^ p =
      Real.cos (t / 2) ^ k * Real.cos (t / 2) ^ (p - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkp]
  rw [Real.tan_eq_sin_div_cos, div_pow, hpow]
  field_simp

/-- At the chart pole the expansion keeps exactly its top homogeneous coefficient. -/
lemma homogeneousTrig_pi (p : ℕ) (P : ℝ[X]) :
    homogeneousTrig p P Real.pi = P.coeff p := by
  simp only [homogeneousTrig, Real.sin_pi_div_two, Real.cos_pi_div_two,
    one_pow, mul_one]
  rw [Finset.sum_eq_single p]
  · simp
  · intro k hk hkp
    have hklt : k < p := by
      have hkle := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      omega
    have hpos : 0 < p - k := Nat.sub_pos_of_lt hklt
    simp [Nat.ne_of_gt hpos]
  · intro hp
    exact (hp (Finset.mem_range.mpr (Nat.lt_succ_self p))).elim

/-- The homogeneous pullback is continuous at every angle, without chart assumptions. -/
lemma continuous_homogeneousTrig (p : ℕ) (P : ℝ[X]) :
    Continuous (homogeneousTrig p P) := by
  unfold homogeneousTrig
  fun_prop

/-- Every angle is a limit of angles with finite half-angle tangent coordinate. -/
lemma dense_cos_half_ne_zero : Dense {t : ℝ | Real.cos (t / 2) ≠ 0} := by
  rw [Metric.dense_iff]
  intro t ε hε
  by_cases ht : Real.cos (t / 2) ≠ 0
  · refine ⟨t, ?_, ht⟩
    simpa only [Metric.mem_ball, dist_self] using hε
  · have hcos : Real.cos (t / 2) = 0 := not_ne_iff.mp ht
    let δ : ℝ := min ε Real.pi / 2
    have hδpos : 0 < δ := div_pos (lt_min hε Real.pi_pos) (by norm_num)
    have hδε : δ < ε := by
      dsimp only [δ]
      have hle := min_le_left ε Real.pi
      linarith
    have hδpi : δ / 2 < Real.pi := by
      dsimp only [δ]
      have hle := min_le_right ε Real.pi
      linarith [Real.pi_pos]
    have hsin : Real.sin (t / 2) ≠ 0 := by
      intro hzero
      have hsum := Real.sin_sq_add_cos_sq (t / 2)
      norm_num [hzero, hcos] at hsum
    have hsinδ : Real.sin (δ / 2) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) hδpi)
    refine ⟨t + δ, ?_, ?_⟩
    · simpa only [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left,
        abs_of_pos hδpos] using hδε
    · change Real.cos ((t + δ) / 2) ≠ 0
      have hangle : (t + δ) / 2 = t / 2 + δ / 2 := by ring
      rw [hangle, Real.cos_add, hcos, zero_mul, zero_sub]
      exact neg_ne_zero.mpr (mul_ne_zero hsin hsinδ)

private def homogeneousTrigDerivative (p : ℕ) (P : ℝ[X]) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (p + 1), P.coeff k *
    ((k : ℝ) * Real.sin (t / 2) ^ (k - 1) * (Real.cos (t / 2) / 2) *
        Real.cos (t / 2) ^ (p - k) +
      Real.sin (t / 2) ^ k * ((p - k : ℕ) : ℝ) *
        Real.cos (t / 2) ^ (p - k - 1) * (-Real.sin (t / 2) / 2))

private lemma hasDerivAt_homogeneousTrig_explicit (p : ℕ) (P : ℝ[X]) (t : ℝ) :
    HasDerivAt (homogeneousTrig p P) (homogeneousTrigDerivative p P t) t := by
  unfold homogeneousTrig homogeneousTrigDerivative
  apply HasDerivAt.fun_sum
  intro k hk
  have hhalf : HasDerivAt (fun u : ℝ => u / 2) (1 / 2) t :=
    (hasDerivAt_id t).div_const 2
  have hterm := ((hhalf.sin.pow k).mul (hhalf.cos.pow (p - k))).const_mul (P.coeff k)
  convert! hterm using 1
  · funext u
    simp only [Pi.mul_apply, Pi.pow_apply]
    ring
  · simp only [Pi.pow_apply]
    ring

private lemma continuous_homogeneousTrigDerivative (p : ℕ) (P : ℝ[X]) :
    Continuous (homogeneousTrigDerivative p P) := by
  unfold homogeneousTrigDerivative
  fun_prop

private lemma hasDerivAt_homogeneousTrig_on_chart (p : ℕ) (P : ℝ[X])
    (hP : P.natDegree ≤ p) (t : ℝ) (ht : Real.cos (t / 2) ≠ 0) :
    HasDerivAt (homogeneousTrig p P)
      (homogeneousTrig p (cayleyOperator p P) t / 2) t := by
  have hhalf : HasDerivAt (fun u : ℝ => u / 2) (1 / 2) t :=
    (hasDerivAt_id t).div_const 2
  have hweighted := (hasDerivAt_cosineWeighted p P (t / 2) ht).comp t hhalf
  have hevent : ∀ᶠ u in nhds t, Real.cos (u / 2) ≠ 0 :=
    (Real.continuous_cos.comp (continuous_id.div_const 2)).continuousAt.eventually_ne ht
  have heq : homogeneousTrig p P =ᶠ[nhds t]
      (fun u : ℝ => cosineWeighted p P (u / 2)) := by
    filter_upwards [hevent] with u hu
    exact homogeneousTrig_eq_cos_pow_eval_tan p P hP u hu
  have hchart : HasDerivAt (homogeneousTrig p P)
      ((Real.cos (t / 2) ^ p *
        (cayleyOperator p P).eval (Real.tan (t / 2))) / 2) t := by
    simpa only [Function.comp_def, mul_one_div] using
      hweighted.congr_of_eventuallyEq heq
  rw [← homogeneousTrig_eq_cos_pow_eval_tan p (cayleyOperator p P)
    (cayleyOperator_natDegree_le p P hP) t ht] at hchart
  exact hchart

private lemma homogeneousTrigDerivative_eq (p : ℕ) (P : ℝ[X])
    (hP : P.natDegree ≤ p) :
    homogeneousTrigDerivative p P =
      (fun t : ℝ => homogeneousTrig p (cayleyOperator p P) t / 2) := by
  apply Continuous.ext_on dense_cos_half_ne_zero
    (continuous_homogeneousTrigDerivative p P)
    ((continuous_homogeneousTrig p (cayleyOperator p P)).div_const 2)
  intro t ht
  exact (hasDerivAt_homogeneousTrig_explicit p P t).unique
    (hasDerivAt_homogeneousTrig_on_chart p P hP t ht)

/-- The Cayley operator gives the derivative at every real angle, including all poles. -/
lemma hasDerivAt_homogeneousTrig (p : ℕ) (P : ℝ[X])
    (hP : P.natDegree ≤ p) (t : ℝ) :
    HasDerivAt (homogeneousTrig p P)
      (homogeneousTrig p (cayleyOperator p P) t / 2) t := by
  have hderiv := hasDerivAt_homogeneousTrig_explicit p P t
  rw [homogeneousTrigDerivative_eq p P hP] at hderiv
  exact hderiv

/-- The literal global derivative formula has no finite-coordinate chart hypothesis. -/
lemma deriv_homogeneousTrig (p : ℕ) (P : ℝ[X])
    (hP : P.natDegree ≤ p) (t : ℝ) :
    deriv (homogeneousTrig p P) t =
      homogeneousTrig p (cayleyOperator p P) t / 2 :=
  (hasDerivAt_homogeneousTrig p P hP t).deriv

/-- In positive homogeneous degree, the Cayley top coefficient is minus the previous one. -/
lemma cayleyOperator_coeff_top (p : ℕ) (P : ℝ[X]) (hp : 0 < p)
    (hP : P.natDegree ≤ p) :
    (cayleyOperator p P).coeff p = -P.coeff (p - 1) := by
  have hpadd : p - 1 + 1 = p := Nat.sub_add_cancel hp
  have htop := cayleyOperator_coeff_succ p P (p - 1)
  rw [hpadd] at htop
  have hhigh : P.coeff (p - 1 + 2) = 0 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mp hP _ (by omega)
  rw [hhigh, zero_mul, zero_add] at htop
  rw [htop]
  have hcast : ((p - 1 : ℕ) : ℝ) + 1 = (p : ℝ) := by
    exact_mod_cast hpadd
  have hdiff : ((p - 1 : ℕ) : ℝ) - (p : ℝ) = -1 := by linarith
  rw [hdiff]
  ring

/-- The global derivative at the tangent pole reads the next-to-top coefficient. -/
lemma deriv_homogeneousTrig_pi (p : ℕ) (P : ℝ[X]) (hp : 0 < p)
    (hP : P.natDegree ≤ p) :
    deriv (homogeneousTrig p P) Real.pi = -P.coeff (p - 1) / 2 := by
  rw [deriv_homogeneousTrig p P hP, homogeneousTrig_pi,
    cayleyOperator_coeff_top p P hp hP]

end

end UnitCircleInterpolation
