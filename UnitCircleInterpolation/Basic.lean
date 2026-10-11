/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.Definitions
import Mathlib.Topology.Order.Compact

/-!
# Elementary properties of the literal interpolation objective

This file proves interpolation at the nodes, continuity, and attainment of the supremum
over the entire unit circle. It does not assert the minimizer classification.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ}

lemma NodeFamily.coordinates_injective (nodes : NodeFamily n) :
    Function.Injective nodes.coordinates :=
  Circle.coe_injective.comp nodes.injective

@[simp] lemma NodeFamily.norm_coordinates (nodes : NodeFamily n) (j : Fin n) :
    ‖nodes.coordinates j‖ = 1 :=
  Circle.norm_coe _

lemma cardinal_self (z : Fin n → ℂ) (hz : Function.Injective z) (j : Fin n) :
    cardinal z j (z j) = 1 := by
  apply Finset.prod_eq_one
  intro k hk
  exact div_self (sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hk).1 (hz h).symm))

lemma cardinal_other (z : Fin n → ℂ) {i j : Fin n} (hij : i ≠ j) :
    cardinal z j (z i) = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
  simp

lemma lebesgueFunction_at_node (z : Fin n → ℂ) (hz : Function.Injective z) (i : Fin n) :
    lebesgueFunction z (z i) = 1 := by
  unfold lebesgueFunction
  rw [Finset.sum_eq_single i]
  · rw [cardinal_self z hz i, norm_one]
  · intro j hj hji
    rw [cardinal_other z (Ne.symm hji), norm_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

lemma lebesgueFunction_nonneg (z : Fin n → ℂ) (w : ℂ) :
    0 ≤ lebesgueFunction z w :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

lemma continuous_cardinal (z : Fin n → ℂ) (j : Fin n) :
    Continuous (cardinal z j) := by
  apply continuous_finsetProd
  intro k hk
  exact (continuous_id.sub continuous_const).div_const _

lemma continuous_lebesgueFunction (z : Fin n → ℂ) :
    Continuous (lebesgueFunction z) := by
  apply continuous_finsetSum
  intro j hj
  exact (continuous_cardinal z j).norm

lemma continuous_circle_lebesgueFunction (nodes : NodeFamily n) :
    Continuous (fun w : Circle => lebesgueFunction nodes.coordinates (w : ℂ)) :=
  (continuous_lebesgueFunction nodes.coordinates).comp continuous_subtype_val

lemma exists_circle_maximum (nodes : NodeFamily n) :
    ∃ w : Circle, ∀ v : Circle,
      lebesgueFunction nodes.coordinates (v : ℂ) ≤
        lebesgueFunction nodes.coordinates (w : ℂ) := by
  obtain ⟨w, _, hw⟩ := isCompact_univ.exists_isMaxOn
    (show (Set.univ : Set Circle).Nonempty from ⟨1, Set.mem_univ 1⟩)
    (continuous_circle_lebesgueFunction nodes).continuousOn
  exact ⟨w, fun v => hw (Set.mem_univ v)⟩

lemma bddAbove_circle_lebesgueFunction (nodes : NodeFamily n) :
    BddAbove (Set.range (fun w : Circle => lebesgueFunction nodes.coordinates (w : ℂ))) := by
  obtain ⟨w, hw⟩ := exists_circle_maximum nodes
  refine ⟨lebesgueFunction nodes.coordinates (w : ℂ), ?_⟩
  rintro y ⟨v, rfl⟩
  exact hw v

lemma le_amplification (nodes : NodeFamily n) (w : Circle) :
    lebesgueFunction nodes.coordinates (w : ℂ) ≤ amplification nodes :=
  le_csSup (bddAbove_circle_lebesgueFunction nodes) ⟨w, rfl⟩

lemma amplification_le_iff (nodes : NodeFamily n) (b : ℝ) :
    amplification nodes ≤ b ↔
      ∀ w : Circle, lebesgueFunction nodes.coordinates (w : ℂ) ≤ b := by
  constructor
  · intro h w
    exact (le_amplification nodes w).trans h
  · intro h
    apply csSup_le (Set.range_nonempty _)
    rintro y ⟨w, rfl⟩
    exact h w

lemma amplification_attained (nodes : NodeFamily n) :
    ∃ w : Circle, amplification nodes = lebesgueFunction nodes.coordinates (w : ℂ) := by
  obtain ⟨w, hw⟩ := exists_circle_maximum nodes
  exact ⟨w, le_antisymm ((amplification_le_iff nodes _).mpr hw)
    (le_amplification nodes w)⟩

lemma one_le_amplification (nodes : NodeFamily n) (hn : 0 < n) :
    1 ≤ amplification nodes := by
  let i : Fin n := ⟨0, hn⟩
  have h := le_amplification nodes (nodes.point i)
  change lebesgueFunction nodes.coordinates (nodes.coordinates i) ≤ amplification nodes at h
  rw [lebesgueFunction_at_node nodes.coordinates nodes.coordinates_injective i] at h
  exact h

end

end UnitCircleInterpolation
