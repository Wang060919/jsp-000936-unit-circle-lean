/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.InterpolantCalculus
import UnitCircleInterpolation.WronskianBridge
import UnitCircleInterpolation.CayleyCircleChart
import UnitCircleInterpolation.HomogeneousTrig
import Mathlib.Topology.Baire.Lemmas

/-!
# Translation of the literal sine interpolants

Translating every node angle and the evaluation angle by the same amount leaves
the interpolant, its derivative, and its Wronskian unchanged. A translation can
be chosen to avoid the Cayley pole for any finite list, including a separately
specified evaluation point. No residue sign for a particular node construction
is asserted here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ}

def shiftedAngles (θ : Fin n → ℝ) (a : ℝ) : Fin n → ℝ := fun j => θ j + a

lemma sineCardinal_shift (θ : Fin n → ℝ) (a t : ℝ) (j : Fin n) :
    sineCardinal (shiftedAngles θ a) j (t + a) = sineCardinal θ j t := by
  unfold shiftedAngles sineCardinal
  simp only [add_sub_add_right_eq_sub]

lemma sineInterpolant_shift (θ c : Fin n → ℝ) (a t : ℝ) :
    sineInterpolant (shiftedAngles θ a) c (t + a) = sineInterpolant θ c t := by
  unfold sineInterpolant
  simp only [sineCardinal_shift]

lemma sineInterpolantDerivative_shift (θ c : Fin n → ℝ) (a t : ℝ) :
    sineInterpolantDerivative (shiftedAngles θ a) c (t + a) =
      sineInterpolantDerivative θ c t := by
  have hl := (hasDerivAt_sineInterpolant (shiftedAngles θ a) c (t + a)).comp t
    ((hasDerivAt_id t).add_const a)
  have hr := hasDerivAt_sineInterpolant θ c t
  have heq : (fun u => sineInterpolant (shiftedAngles θ a) c (u + a)) =
      sineInterpolant θ c := funext (sineInterpolant_shift θ c a)
  simp only [Function.comp_def, id_eq, mul_one] at hl
  rw [heq] at hl
  exact hl.unique hr

lemma deriv_sineInterpolant_shift (θ c : Fin n → ℝ) (a t : ℝ) :
    deriv (sineInterpolant (shiftedAngles θ a) c) (t + a) =
      deriv (sineInterpolant θ c) t := by
  rw [deriv_sineInterpolant, deriv_sineInterpolant, sineInterpolantDerivative_shift]

lemma sineWronskian_shift (θ d c : Fin n → ℝ) (a t : ℝ) :
    sineWronskian (shiftedAngles θ a) d c (t + a) = sineWronskian θ d c t := by
  unfold sineWronskian
  rw [sineInterpolant_shift, sineInterpolant_shift,
    deriv_sineInterpolant_shift, deriv_sineInterpolant_shift]

/-- The allowable translations for one angle form a dense open set. -/
lemma dense_shifted_cos_half_ne_zero (r : ℝ) :
    Dense {a : ℝ | Real.cos ((r + a) / 2) ≠ 0} :=
  dense_cos_half_ne_zero.preimage (isOpenMap_add_left r)

lemma isOpen_shifted_cos_half_ne_zero (r : ℝ) :
    IsOpen {a : ℝ | Real.cos ((r + a) / 2) ≠ 0} := by
  exact isOpen_ne_fun
    (Real.continuous_cos.comp ((continuous_const.add continuous_id).div_const 2))
    continuous_const

/-- A single translation makes every member of a finite angle list finite in the chart. -/
lemma exists_shift_cos_half_ne_zero {m : ℕ} (r : Fin m → ℝ) :
    ∃ a : ℝ, ∀ i, Real.cos ((r i + a) / 2) ≠ 0 := by
  let chart : Fin m → Set ℝ := fun i => {a | Real.cos ((r i + a) / 2) ≠ 0}
  have hdense : Dense (⋂ i, chart i) := by
    rw [← Set.sInter_range]
    apply (Set.finite_range chart).dense_sInter
    · rintro s ⟨i, rfl⟩
      exact isOpen_shifted_cos_half_ne_zero (r i)
    · rintro s ⟨i, rfl⟩
      exact dense_shifted_cos_half_ne_zero (r i)
  obtain ⟨a, ha⟩ := hdense.nonempty
  exact ⟨a, fun i => Set.mem_iInter.mp ha i⟩

/-- Avoid every listed root and also the separately supplied evaluation point. -/
lemma exists_shift_cos_half_ne_zero_roots_and_point {m : ℕ} (r : Fin m → ℝ) (t : ℝ) :
    ∃ a : ℝ, Real.cos ((t + a) / 2) ≠ 0 ∧
      ∀ i, Real.cos ((r i + a) / 2) ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_shift_cos_half_ne_zero (Fin.cons t r)
  exact ⟨a, by simpa using ha 0, fun i => by simpa using ha i.succ⟩

/-- Translating canonical circle representatives preserves distinct tangent coordinates,
provided all the translated roots avoid the chart pole. The translated real angles
need not themselves belong to the canonical interval. -/
lemma shifted_tan_half_injective {m : ℕ} (r : Fin m → ℝ)
    (hinj : Function.Injective r) (hbound : ∀ i, r i ∈ Set.Ico 0 (2 * Real.pi))
    (a : ℝ) (hcos : ∀ i, Real.cos ((r i + a) / 2) ≠ 0) :
    Function.Injective (fun i => Real.tan ((r i + a) / 2)) := by
  intro i j htan
  have hexp := circle_exp_two_mul_eq_of_tan_eq
    ((r i + a) / 2) ((r j + a) / 2) (hcos i) (hcos j) htan
  have hi : 2 * ((r i + a) / 2) = r i + a := by ring
  have hj : 2 * ((r j + a) / 2) = r j + a := by ring
  rw [hi, hj, Circle.exp_add, Circle.exp_add] at hexp
  apply hinj
  exact Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp)
    (hbound i) (hbound j) (mul_right_cancel hexp)

end

end UnitCircleInterpolation
