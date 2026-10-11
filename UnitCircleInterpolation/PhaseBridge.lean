/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.Definitions
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The complex cardinal and its real sine product

These identities hold for arbitrary finite angle families. Distinctness is needed only for
the separate denominator lemma. The period sign retains both parities of the node count.

The proofs below are new bridges for the unit-circle problem, using standard Mathlib facts
about the complex exponential, norms, and finite products.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ}

/-- Complex unit-circle coordinates associated to a finite family of real angles. -/
def phaseNodes (θ : Fin n → ℝ) : Fin n → ℂ :=
  fun j => (Circle.exp (θ j) : ℂ)

/-- The real sine-product cardinal in the angle variable. -/
def sineCardinal (θ : Fin n → ℝ) (j : Fin n) (t : ℝ) : ℝ :=
  ∏ k ∈ Finset.univ.erase j,
    Real.sin ((t - θ k) / 2) / Real.sin ((θ j - θ k) / 2)

/-- The chord length between two phases is twice the absolute half-angle sine. -/
lemma norm_phase_sub (t s : ℝ) :
    ‖(Circle.exp t : ℂ) - (Circle.exp s : ℂ)‖ =
      2 * |Real.sin ((t - s) / 2)| := by
  have hexponent : (s : ℂ) * Complex.I + ((t - s : ℝ) : ℂ) * Complex.I =
      (t : ℂ) * Complex.I := by
    push_cast
    ring
  have hfactor : (Circle.exp t : ℂ) - (Circle.exp s : ℂ) =
      Complex.exp ((s : ℂ) * Complex.I) *
        (Complex.exp (((t - s : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [Circle.coe_exp, Circle.coe_exp, mul_sub, mul_one, ← Complex.exp_add, hexponent]
  calc
    ‖(Circle.exp t : ℂ) - (Circle.exp s : ℂ)‖ =
        ‖Complex.exp ((s : ℂ) * Complex.I) *
          (Complex.exp (((t - s : ℝ) : ℂ) * Complex.I) - 1)‖ :=
      congrArg norm hfactor
    _ = ‖Complex.exp (((t - s : ℝ) : ℂ) * Complex.I) - 1‖ := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    _ = ‖(2 : ℝ) * Real.sin ((t - s) / 2)‖ := by
      rw [mul_comm (((t - s : ℝ) : ℂ)) Complex.I]
      exact Complex.norm_exp_I_mul_ofReal_sub_one (t - s)
    _ = 2 * |Real.sin ((t - s) / 2)| := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- The norm of each literal complex factor is the absolute real sine ratio.
No nonzero-denominator assumption is needed for this identity. -/
lemma norm_phase_ratio (t a b : ℝ) :
    ‖((Circle.exp t : ℂ) - (Circle.exp b : ℂ)) /
      ((Circle.exp a : ℂ) - (Circle.exp b : ℂ))‖ =
      |Real.sin ((t - b) / 2) / Real.sin ((a - b) / 2)| := by
  rw [norm_div, norm_phase_sub, norm_phase_sub, abs_div]
  exact mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)

/-- The norm of the genuine complex cardinal equals the absolute sine product. -/
lemma norm_cardinal_phase (θ : Fin n → ℝ) (j : Fin n) (t : ℝ) :
    ‖cardinal (phaseNodes θ) j (Circle.exp t : ℂ)‖ =
      |sineCardinal θ j t| := by
  unfold cardinal phaseNodes sineCardinal
  rw [← Real.norm_eq_abs, norm_prod, norm_prod]
  apply Finset.prod_congr rfl
  intro k hk
  simpa only [Real.norm_eq_abs] using norm_phase_ratio t (θ j) (θ k)

/-- The literal Lebesgue function is the sum of the absolute sine cardinals. -/
lemma lebesgueFunction_phase (θ : Fin n → ℝ) (t : ℝ) :
    lebesgueFunction (phaseNodes θ) (Circle.exp t : ℂ) =
      ∑ j, |sineCardinal θ j t| := by
  simp only [lebesgueFunction, norm_cardinal_phase]

/-- Distinct complex phases guarantee all off-diagonal sine denominators are nonzero. -/
lemma sine_denominator_ne_zero (θ : Fin n → ℝ)
    (hθ : Function.Injective (phaseNodes θ)) {j k : Fin n} (hjk : j ≠ k) :
    Real.sin ((θ j - θ k) / 2) ≠ 0 := by
  intro hsin
  have hnorm : ‖phaseNodes θ j - phaseNodes θ k‖ = 0 := by
    simpa only [phaseNodes, hsin, abs_zero, mul_zero] using norm_phase_sub (θ j) (θ k)
  exact hjk (hθ (sub_eq_zero.mp (norm_eq_zero.mp hnorm)))

/-- A full turn multiplies every real cardinal by the sign determined by n - 1. -/
lemma sineCardinal_add_two_pi (θ : Fin n → ℝ) (j : Fin n) (t : ℝ) :
    sineCardinal θ j (t + 2 * Real.pi) =
      (-1 : ℝ) ^ (n - 1) * sineCardinal θ j t := by
  have hfactor (k : Fin n) :
      Real.sin ((t + 2 * Real.pi - θ k) / 2) /
          Real.sin ((θ j - θ k) / 2) =
        (-1 : ℝ) * (Real.sin ((t - θ k) / 2) /
          Real.sin ((θ j - θ k) / 2)) := by
    have hangle : (t + 2 * Real.pi - θ k) / 2 = (t - θ k) / 2 + Real.pi := by
      ring
    rw [hangle, Real.sin_add_pi, neg_div, neg_one_mul]
  unfold sineCardinal
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_univ j)]
  simp only [Finset.card_univ, Fintype.card_fin]

/-- Canonical real angle representatives for every admissible node family. -/
def nodesAngles (nodes : NodeFamily n) : Fin n → ℝ :=
  fun j => Complex.arg (nodes.coordinates j)

/-- Canonical phases recover the original complex nodes exactly. -/
lemma phaseNodes_nodesAngles (nodes : NodeFamily n) :
    phaseNodes (nodesAngles nodes) = nodes.coordinates := by
  funext j
  change (Circle.exp (Complex.arg (nodes.point j : ℂ)) : ℂ) = (nodes.point j : ℂ)
  exact congrArg ((↑) : Circle → ℂ) (Circle.exp_arg (nodes.point j))

/-- Canonical angles lie in a single half-open turn. -/
lemma nodesAngles_mem_Ioc (nodes : NodeFamily n) (j : Fin n) :
    nodesAngles nodes j ∈ Set.Ioc (-Real.pi) Real.pi :=
  Complex.arg_mem_Ioc _

/-- Distinct circle nodes have distinct canonical angle representatives. -/
lemma nodesAngles_injective (nodes : NodeFamily n) :
    Function.Injective (nodesAngles nodes) := by
  exact Circle.injective_arg.comp nodes.injective

/-- The reconstructed canonical phase family retains every original distinct node. -/
lemma phaseNodes_nodesAngles_injective (nodes : NodeFamily n) :
    Function.Injective (phaseNodes (nodesAngles nodes)) := by
  rw [phaseNodes_nodesAngles]
  exact Circle.coe_injective.comp nodes.injective

/-- The complex-to-sine cardinal identity for arbitrary admissible nodes. -/
lemma norm_cardinal_nodesAngles (nodes : NodeFamily n) (j : Fin n) (t : ℝ) :
    ‖cardinal nodes.coordinates j (Circle.exp t : ℂ)‖ =
      |sineCardinal (nodesAngles nodes) j t| := by
  simpa only [phaseNodes_nodesAngles] using norm_cardinal_phase (nodesAngles nodes) j t

/-- The full literal objective for arbitrary admissible nodes, evaluated at any angle. -/
lemma lebesgueFunction_nodesAngles (nodes : NodeFamily n) (t : ℝ) :
    lebesgueFunction nodes.coordinates (Circle.exp t : ℂ) =
      ∑ j, |sineCardinal (nodesAngles nodes) j t| := by
  simpa only [phaseNodes_nodesAngles] using lebesgueFunction_phase (nodesAngles nodes) t

/-- The full objective identity at every actual point of the unit circle. -/
lemma lebesgueFunction_nodesAngles_at (nodes : NodeFamily n) (w : Circle) :
    lebesgueFunction nodes.coordinates (w : ℂ) =
      ∑ j, |sineCardinal (nodesAngles nodes) j (Complex.arg (w : ℂ))| := by
  simpa only [Circle.exp_arg] using
    lebesgueFunction_nodesAngles nodes (Complex.arg (w : ℂ))

/-- Every off-diagonal denominator is nonzero for the canonical angle family. -/
lemma nodesAngles_denominator_ne_zero (nodes : NodeFamily n)
    {j k : Fin n} (hjk : j ≠ k) :
    Real.sin ((nodesAngles nodes j - nodesAngles nodes k) / 2) ≠ 0 :=
  sine_denominator_ne_zero _ (phaseNodes_nodesAngles_injective nodes) hjk

/-- Every sine cardinal is one at its own node when the complex phases are distinct. -/
lemma sineCardinal_self (θ : Fin n → ℝ)
    (hθ : Function.Injective (phaseNodes θ)) (j : Fin n) :
    sineCardinal θ j (θ j) = 1 := by
  apply Finset.prod_eq_one
  intro k hk
  exact div_self (sine_denominator_ne_zero θ hθ (Finset.mem_erase.mp hk).1.symm)

/-- Every sine cardinal vanishes at the other nodes; no denominator hypothesis is needed. -/
lemma sineCardinal_other (θ : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j) :
    sineCardinal θ j (θ i) = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
  simp

/-- A sine cardinal is continuous throughout the real angle variable. -/
lemma continuous_sineCardinal (θ : Fin n → ℝ) (j : Fin n) :
    Continuous (sineCardinal θ j) := by
  apply continuous_finsetProd
  intro k hk
  exact (Real.continuous_sin.comp
    ((continuous_id.sub continuous_const).div_const 2)).div_const _

/-- The absolute sine cardinal is unchanged after a full turn for either parity. -/
lemma abs_sineCardinal_add_two_pi (θ : Fin n → ℝ) (j : Fin n) (t : ℝ) :
    |sineCardinal θ j (t + 2 * Real.pi)| = |sineCardinal θ j t| := by
  rw [sineCardinal_add_two_pi, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- Each absolute sine cardinal has period two pi. -/
lemma abs_sineCardinal_periodic (θ : Fin n → ℝ) (j : Fin n) :
    Function.Periodic (fun t => |sineCardinal θ j t|) (2 * Real.pi) :=
  abs_sineCardinal_add_two_pi θ j

/-- The complete sum of absolute sine cardinals is continuous. -/
lemma continuous_sineLebesgueFunction (θ : Fin n → ℝ) :
    Continuous (fun t => ∑ j, |sineCardinal θ j t|) := by
  apply continuous_finsetSum
  intro j hj
  exact (continuous_sineCardinal θ j).abs

/-- The complete sum of absolute sine cardinals has period two pi. -/
lemma sineLebesgueFunction_periodic (θ : Fin n → ℝ) :
    Function.Periodic (fun t => ∑ j, |sineCardinal θ j t|) (2 * Real.pi) := by
  intro t
  simp only [abs_sineCardinal_add_two_pi]

/-- The literal complex Lebesgue function along the circle has period two pi. -/
lemma lebesgueFunction_circle_periodic (z : Fin n → ℂ) :
    Function.Periodic (fun t => lebesgueFunction z (Circle.exp t : ℂ))
      (2 * Real.pi) := by
  intro t
  exact congrArg (fun w : Circle => lebesgueFunction z (w : ℂ)) (Circle.exp_add_two_pi t)

end

end UnitCircleInterpolation
