/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

open Polynomial

/-- The polynomial numerator of differentiation in the weighted Cayley coordinate. -/
def cayleyOperator (p : ℕ) (P : ℝ[X]) : ℝ[X] :=
  (1 + X ^ 2) * P.derivative - C (p : ℝ) * X * P

private theorem coeff_X_sq_mul_derivative_succ (P : ℝ[X]) (n : ℕ) :
    (X ^ 2 * P.derivative).coeff (n + 1) = P.coeff n * (n : ℝ) := by
  cases n with
  | zero => simp [Polynomial.coeff_X_pow_mul']
  | succ n =>
      simpa only [Polynomial.coeff_derivative, Nat.succ_eq_add_one, Nat.add_assoc,
        Nat.cast_add, Nat.cast_one] using
        (Polynomial.coeff_X_pow_mul P.derivative 2 n)

/-- The constant coefficient has no contribution from either term containing `X`. -/
@[simp]
theorem cayleyOperator_coeff_zero (p : ℕ) (P : ℝ[X]) :
    (cayleyOperator p P).coeff 0 = P.coeff 1 := by
  simp [cayleyOperator, add_mul, mul_assoc, Polynomial.coeff_derivative]

/-- The successor coefficient displays the cancellation at degree `p + 1`. -/
theorem cayleyOperator_coeff_succ (p : ℕ) (P : ℝ[X]) (n : ℕ) :
    (cayleyOperator p P).coeff (n + 1) =
      P.coeff (n + 2) * ((n + 2 : ℕ) : ℝ) + P.coeff n * ((n : ℝ) - (p : ℝ)) := by
  simp only [cayleyOperator, add_mul, one_mul, mul_assoc, Polynomial.coeff_sub,
    Polynomial.coeff_add, Polynomial.coeff_derivative,
    coeff_X_sq_mul_derivative_succ, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul,
    Nat.add_assoc, Nat.cast_add, Nat.cast_ofNat]
  ring

/-- The top coefficient cancels, including when `p = 0` or `P = 0`. -/
theorem cayleyOperator_natDegree_le (p : ℕ) (P : ℝ[X]) (hP : P.natDegree ≤ p) :
    (cayleyOperator p P).natDegree ≤ p := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  cases k with
  | zero => omega
  | succ n =>
      change (cayleyOperator p P).coeff (n + 1) = 0
      rw [cayleyOperator_coeff_succ]
      have hhigh : P.coeff (n + 2) = 0 :=
        Polynomial.natDegree_le_iff_coeff_eq_zero.mp hP _ (by omega)
      rw [hhigh, zero_mul, zero_add]
      by_cases hnp : n = p
      · subst n
        simp
      · have hmid : P.coeff n = 0 :=
          Polynomial.natDegree_le_iff_coeff_eq_zero.mp hP _ (by omega)
        rw [hmid, zero_mul]

/-- Evaluation gives the literal weighted differentiation numerator. -/
@[simp]
theorem cayleyOperator_eval (p : ℕ) (P : ℝ[X]) (x : ℝ) :
    (cayleyOperator p P).eval x =
      (1 + x ^ 2) * P.derivative.eval x - (p : ℝ) * x * P.eval x := by
  simp [cayleyOperator]

end

end UnitCircleInterpolation
