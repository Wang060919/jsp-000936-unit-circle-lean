/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.Basic

/-!
# Literal complex nodes and the circle-valued representation

The adapters below prove that the representation does not restrict the admissible nodes,
the evaluation domain, the objective, or the meaning of global minimization and regularity.
They do not prove the full minimizer classification.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ}

/-- Construct a circle-valued family from any distinct complex unit-modulus nodes. -/
def NodeFamily.ofCoordinates (z : Fin n → ℂ) (hunit : ∀ i, ‖z i‖ = 1)
    (hinj : Function.Injective z) : NodeFamily n where
  point i := ⟨z i, mem_sphere_zero_iff_norm.mpr (hunit i)⟩
  injective := fun _ _ h => hinj (congrArg (fun w : Circle => (w : ℂ)) h)

@[simp] lemma NodeFamily.coordinates_ofCoordinates (z : Fin n → ℂ)
    (hunit : ∀ i, ‖z i‖ = 1) (hinj : Function.Injective z) :
    (NodeFamily.ofCoordinates z hunit hinj).coordinates = z :=
  rfl

@[simp] lemma NodeFamily.ofCoordinates_coordinates (nodes : NodeFamily n) :
    NodeFamily.ofCoordinates nodes.coordinates nodes.norm_coordinates
      nodes.coordinates_injective = nodes := by
  cases nodes
  rfl

/-- The same literal supremum, before packaging the nodes as a `NodeFamily`. -/
def complexAmplification (z : Fin n → ℂ) : ℝ :=
  sSup (Set.range (fun w : Circle => lebesgueFunction z (w : ℂ)))

lemma complexAmplification_eq_sSup_image (z : Fin n → ℂ) :
    complexAmplification z = sSup (lebesgueFunction z '' {w : ℂ | ‖w‖ = 1}) := by
  unfold complexAmplification
  congr 1
  ext b
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨(w : ℂ), Circle.norm_coe w, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨(⟨w, mem_sphere_zero_iff_norm.mpr hw⟩ : Circle), rfl⟩

lemma complexAmplification_coordinates (nodes : NodeFamily n) :
    complexAmplification nodes.coordinates = amplification nodes :=
  rfl

lemma amplification_ofCoordinates (z : Fin n → ℂ) (hunit : ∀ i, ‖z i‖ = 1)
    (hinj : Function.Injective z) :
    amplification (NodeFamily.ofCoordinates z hunit hinj) = complexAmplification z :=
  rfl

/-- Minimization against every injective complex family with unit-modulus nodes. -/
def IsComplexMinimizer (z : Fin n → ℂ) : Prop :=
  ∀ other : Fin n → ℂ, (∀ i, ‖other i‖ = 1) → Function.Injective other →
    complexAmplification z ≤ complexAmplification other

lemma isComplexMinimizer_coordinates_iff (nodes : NodeFamily n) :
    IsComplexMinimizer nodes.coordinates ↔ IsMinimizer nodes := by
  constructor
  · intro h other
    exact h other.coordinates other.norm_coordinates other.coordinates_injective
  · intro h other hunit hinj
    exact h (NodeFamily.ofCoordinates other hunit hinj)

lemma isComplexMinimizer_ofCoordinates_iff (z : Fin n → ℂ)
    (hunit : ∀ i, ‖z i‖ = 1) (hinj : Function.Injective z) :
    IsComplexMinimizer z ↔ IsMinimizer (NodeFamily.ofCoordinates z hunit hinj) :=
  by simpa only [NodeFamily.coordinates_ofCoordinates] using
    isComplexMinimizer_coordinates_iff (NodeFamily.ofCoordinates z hunit hinj)

/-- The exact complex regular-polygon statement, with scalar rotation and arbitrary enumeration. -/
def IsComplexRegularRotation (z : Fin n → ℂ) : Prop :=
  ∃ rotation : ℂ, ‖rotation‖ = 1 ∧ ∃ permutation : Equiv.Perm (Fin n),
    ∀ i, z i = rotation * (Circle.exp
      (2 * Real.pi * (((permutation i).val : ℝ) / (n : ℝ))) : ℂ)

lemma isComplexRegularRotation_coordinates_iff (nodes : NodeFamily n) :
    IsComplexRegularRotation nodes.coordinates ↔ IsRegularRotation nodes := by
  constructor
  · rintro ⟨rotation, hunit, permutation, h⟩
    let r : Circle := ⟨rotation, mem_sphere_zero_iff_norm.mpr hunit⟩
    refine ⟨r, permutation, ?_⟩
    intro i
    apply Circle.coe_injective
    exact h i
  · rintro ⟨rotation, permutation, h⟩
    refine ⟨(rotation : ℂ), Circle.norm_coe rotation, permutation, ?_⟩
    intro i
    exact congrArg (fun w : Circle => (w : ℂ)) (h i)

lemma isComplexRegularRotation_ofCoordinates_iff (z : Fin n → ℂ)
    (hunit : ∀ i, ‖z i‖ = 1) (hinj : Function.Injective z) :
    IsComplexRegularRotation z ↔ IsRegularRotation (NodeFamily.ofCoordinates z hunit hinj) :=
  by simpa only [NodeFamily.coordinates_ofCoordinates] using
    isComplexRegularRotation_coordinates_iff (NodeFamily.ofCoordinates z hunit hinj)

end

end UnitCircleInterpolation
