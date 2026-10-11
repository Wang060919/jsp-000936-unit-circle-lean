/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Injectivity of the Cayley coordinate for finite circle root counts

Equal tangent coordinates determine the same doubled-angle point on the circle.
Consequently, `t ↦ tan (t / 2)` is injective on cyclic representatives in
`[0, 2π)` whose half-angle cosine is nonzero. The sole excluded cyclic phase
is `π`.

These are coordinate and pole-identification results for later finite root
counts. They assert no minimizer classification or interpolation optimality.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

/-- Equal finite tangent coordinates give equal doubled-angle circle points. -/
lemma circle_exp_two_mul_eq_of_tan_eq (u v : ℝ)
    (hu : Real.cos u ≠ 0) (hv : Real.cos v ≠ 0)
    (htan : Real.tan u = Real.tan v) :
    Circle.exp (2 * u) = Circle.exp (2 * v) := by
  have hcosSq : Real.cos u ^ 2 = Real.cos v ^ 2 := by
    rw [← Real.inv_one_add_tan_sq hu, ← Real.inv_one_add_tan_sq hv, htan]
  have hcos : Real.cos (2 * u) = Real.cos (2 * v) := by
    rw [Real.cos_two_mul, Real.cos_two_mul, hcosSq]
  have hsin : Real.sin (2 * u) = Real.sin (2 * v) := by
    rw [Real.sin_two_mul, Real.sin_two_mul,
      ← Real.tan_mul_cos hu, ← Real.tan_mul_cos hv]
    calc
      2 * (Real.tan u * Real.cos u) * Real.cos u =
          2 * Real.tan u * Real.cos u ^ 2 := by ring
      _ = 2 * Real.tan v * Real.cos v ^ 2 := by rw [htan, hcosSq]
      _ = 2 * (Real.tan v * Real.cos v) * Real.cos v := by ring
  apply Circle.coe_injective
  apply Complex.ext
  · simpa only [Circle.coe_exp, Complex.exp_ofReal_mul_I_re] using hcos
  · simpa only [Circle.coe_exp, Complex.exp_ofReal_mul_I_im] using hsin

/-- The half-angle tangent coordinate is injective on the explicitly stated chart. -/
lemma tan_half_injOn_Ico :
    Set.InjOn (fun t : ℝ => Real.tan (t / 2))
      {t | t ∈ Set.Ico 0 (2 * Real.pi) ∧ Real.cos (t / 2) ≠ 0} := by
  intro t ht s hs heq
  have heqExp := circle_exp_two_mul_eq_of_tan_eq
    (t / 2) (s / 2) ht.2 hs.2 heq
  have htangle : 2 * (t / 2) = t := by ring
  have hsangle : 2 * (s / 2) = s := by ring
  rw [htangle, hsangle] at heqExp
  exact Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp)
    ht.1 hs.1 heqExp

/-- Among canonical cyclic phases, the half-angle cosine vanishes exactly at `π`. -/
lemma cos_half_eq_zero_iff_of_mem_Ico (t : ℝ)
    (ht : t ∈ Set.Ico 0 (2 * Real.pi)) :
    Real.cos (t / 2) = 0 ↔ t = Real.pi := by
  constructor
  · intro hcos
    have hhalf : t / 2 ∈ Set.Icc 0 Real.pi := by
      constructor <;> linarith [ht.1, ht.2]
    have hpi : Real.pi / 2 ∈ Set.Icc 0 Real.pi := by
      constructor <;> linarith [Real.pi_pos]
    have heq : t / 2 = Real.pi / 2 :=
      Real.injOn_cos hhalf hpi (by rw [hcos, Real.cos_pi_div_two])
    linarith
  · intro heq
    rw [heq, Real.cos_pi_div_two]

/-- Excluding the cyclic phase `π` is exactly the finite-coordinate chart condition. -/
lemma cos_half_ne_zero_iff_of_mem_Ico (t : ℝ)
    (ht : t ∈ Set.Ico 0 (2 * Real.pi)) :
    Real.cos (t / 2) ≠ 0 ↔ t ≠ Real.pi :=
  not_congr (cos_half_eq_zero_iff_of_mem_Ico t ht)

end

end UnitCircleInterpolation
