/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.Basic

/-!
# Rotation and enumeration invariance

The literal complex cardinal is unchanged when both its nodes and evaluation point
are multiplied by a nonzero scalar. Reindexing the nodes simply reindexes the
cardinals. These identities imply the corresponding invariance of the actual
Lebesgue sum and its supremum over the entire unit circle.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ}

/-- Rotate an admissible family by a unit complex number. -/
def NodeFamily.rotate (nodes : NodeFamily n) (rotation : Circle) : NodeFamily n where
  point i := rotation * nodes.point i
  injective := fun _ _ h => nodes.injective (mul_left_cancel h)

/-- Change the enumeration of an admissible family. -/
def NodeFamily.reindex (nodes : NodeFamily n) (permutation : Equiv.Perm (Fin n)) :
    NodeFamily n where
  point i := nodes.point (permutation i)
  injective := nodes.injective.comp permutation.injective

@[simp] lemma NodeFamily.coordinates_rotate (nodes : NodeFamily n) (rotation : Circle)
    (i : Fin n) :
    (nodes.rotate rotation).coordinates i = (rotation : ℂ) * nodes.coordinates i := by
  simp only [NodeFamily.coordinates, NodeFamily.rotate, Circle.coe_mul]

@[simp] lemma NodeFamily.coordinates_reindex (nodes : NodeFamily n)
    (permutation : Equiv.Perm (Fin n)) (i : Fin n) :
    (nodes.reindex permutation).coordinates i = nodes.coordinates (permutation i) :=
  rfl

/-- The cancellation identity uses only the nonzero multiplier; the nodes may be arbitrary. -/
lemma cardinal_mul (z : Fin n → ℂ) {a : ℂ} (ha : a ≠ 0) (j : Fin n) (w : ℂ) :
    cardinal (fun i => a * z i) j (a * w) = cardinal z j w := by
  unfold cardinal
  apply Finset.prod_congr rfl
  intro k hk
  rw [← mul_sub a w (z k), ← mul_sub a (z j) (z k)]
  exact mul_div_mul_left _ _ ha

lemma norm_cardinal_mul (z : Fin n → ℂ) {a : ℂ} (ha : a ≠ 0)
    (j : Fin n) (w : ℂ) :
    ‖cardinal (fun i => a * z i) j (a * w)‖ = ‖cardinal z j w‖ := by
  rw [cardinal_mul z ha]

lemma lebesgueFunction_mul (z : Fin n → ℂ) {a : ℂ} (ha : a ≠ 0) (w : ℂ) :
    lebesgueFunction (fun i => a * z i) (a * w) = lebesgueFunction z w := by
  unfold lebesgueFunction
  apply Finset.sum_congr rfl
  intro j hj
  exact norm_cardinal_mul z ha j w

lemma cardinal_rotate (nodes : NodeFamily n) (rotation : Circle) (j : Fin n)
    (w : Circle) :
    cardinal (nodes.rotate rotation).coordinates j ((rotation * w : Circle) : ℂ) =
      cardinal nodes.coordinates j (w : ℂ) := by
  simp only [Circle.coe_mul]
  change cardinal (fun i => (rotation : ℂ) * nodes.coordinates i) j
    ((rotation : ℂ) * (w : ℂ)) = _
  exact cardinal_mul nodes.coordinates (Circle.coe_ne_zero rotation) j (w : ℂ)

lemma norm_cardinal_rotate (nodes : NodeFamily n) (rotation : Circle) (j : Fin n)
    (w : Circle) :
    ‖cardinal (nodes.rotate rotation).coordinates j ((rotation * w : Circle) : ℂ)‖ =
      ‖cardinal nodes.coordinates j (w : ℂ)‖ := by
  rw [cardinal_rotate]

lemma lebesgueFunction_rotate (nodes : NodeFamily n) (rotation : Circle) (w : Circle) :
    lebesgueFunction (nodes.rotate rotation).coordinates ((rotation * w : Circle) : ℂ) =
      lebesgueFunction nodes.coordinates (w : ℂ) := by
  unfold lebesgueFunction
  apply Finset.sum_congr rfl
  intro j hj
  exact norm_cardinal_rotate nodes rotation j w

lemma amplification_rotate (nodes : NodeFamily n) (rotation : Circle) :
    amplification (nodes.rotate rotation) = amplification nodes := by
  apply le_antisymm
  · apply (amplification_le_iff _ _).mpr
    intro w
    calc
      lebesgueFunction (nodes.rotate rotation).coordinates (w : ℂ) =
          lebesgueFunction (nodes.rotate rotation).coordinates
            ((rotation * (rotation⁻¹ * w) : Circle) : ℂ) := by simp
      _ = lebesgueFunction nodes.coordinates ((rotation⁻¹ * w : Circle) : ℂ) :=
        lebesgueFunction_rotate nodes rotation (rotation⁻¹ * w)
      _ ≤ amplification nodes := le_amplification nodes (rotation⁻¹ * w)
  · apply (amplification_le_iff _ _).mpr
    intro w
    calc
      lebesgueFunction nodes.coordinates (w : ℂ) =
          lebesgueFunction (nodes.rotate rotation).coordinates
            ((rotation * w : Circle) : ℂ) :=
        (lebesgueFunction_rotate nodes rotation w).symm
      _ ≤ amplification (nodes.rotate rotation) :=
        le_amplification (nodes.rotate rotation) (rotation * w)

/-- Reindexing a family transports the cardinal indexed by the same permutation. -/
lemma cardinal_reindex (z : Fin n → ℂ) (permutation : Equiv.Perm (Fin n))
    (j : Fin n) (w : ℂ) :
    cardinal (fun i => z (permutation i)) j w = cardinal z (permutation j) w := by
  unfold cardinal
  apply Finset.prod_equiv permutation
  · intro i
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact (not_congr permutation.injective.eq_iff).symm
  · intro i hi
    rfl

lemma norm_cardinal_reindex (z : Fin n → ℂ) (permutation : Equiv.Perm (Fin n))
    (j : Fin n) (w : ℂ) :
    ‖cardinal (fun i => z (permutation i)) j w‖ =
      ‖cardinal z (permutation j) w‖ := by
  rw [cardinal_reindex]

lemma lebesgueFunction_reindex (nodes : NodeFamily n)
    (permutation : Equiv.Perm (Fin n)) (w : ℂ) :
    lebesgueFunction (nodes.reindex permutation).coordinates w =
      lebesgueFunction nodes.coordinates w := by
  unfold lebesgueFunction
  apply Fintype.sum_equiv permutation
  intro j
  change ‖cardinal (fun i => nodes.coordinates (permutation i)) j w‖ = _
  exact norm_cardinal_reindex nodes.coordinates permutation j w

lemma amplification_reindex (nodes : NodeFamily n)
    (permutation : Equiv.Perm (Fin n)) :
    amplification (nodes.reindex permutation) = amplification nodes := by
  unfold amplification
  simp only [lebesgueFunction_reindex]

lemma isMinimizer_rotate_iff (nodes : NodeFamily n) (rotation : Circle) :
    IsMinimizer (nodes.rotate rotation) ↔ IsMinimizer nodes := by
  simp only [IsMinimizer, amplification_rotate]

lemma isMinimizer_reindex_iff (nodes : NodeFamily n)
    (permutation : Equiv.Perm (Fin n)) :
    IsMinimizer (nodes.reindex permutation) ↔ IsMinimizer nodes := by
  simp only [IsMinimizer, amplification_reindex]

lemma isRegularRotation_rotate_iff (nodes : NodeFamily n) (rotation : Circle) :
    IsRegularRotation (nodes.rotate rotation) ↔ IsRegularRotation nodes := by
  constructor
  · rintro ⟨r, permutation, h⟩
    refine ⟨rotation⁻¹ * r, permutation, ?_⟩
    intro i
    have hi := congrArg (fun z : Circle => rotation⁻¹ * z) (h i)
    change rotation⁻¹ * (rotation * nodes.point i) =
      rotation⁻¹ * (r * regularPoint n (permutation i)) at hi
    simpa only [inv_mul_cancel_left, mul_assoc] using hi
  · rintro ⟨r, permutation, h⟩
    refine ⟨rotation * r, permutation, ?_⟩
    intro i
    change rotation * nodes.point i = (rotation * r) * regularPoint n (permutation i)
    rw [h i, mul_assoc]

lemma isRegularRotation_reindex_iff (nodes : NodeFamily n)
    (permutation : Equiv.Perm (Fin n)) :
    IsRegularRotation (nodes.reindex permutation) ↔ IsRegularRotation nodes := by
  constructor
  · rintro ⟨rotation, p, h⟩
    refine ⟨rotation, permutation.symm.trans p, ?_⟩
    intro i
    have hi := h (permutation.symm i)
    change nodes.point (permutation (permutation.symm i)) =
      rotation * regularPoint n (p (permutation.symm i)) at hi
    simpa only [Equiv.apply_symm_apply, Equiv.trans_apply] using hi
  · rintro ⟨rotation, p, h⟩
    refine ⟨rotation, permutation.trans p, ?_⟩
    intro i
    exact h (permutation i)

end

end UnitCircleInterpolation
