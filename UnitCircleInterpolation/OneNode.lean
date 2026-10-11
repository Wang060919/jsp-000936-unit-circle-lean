/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.Basic
import UnitCircleInterpolation.RegularNodes

/-! # The complete one-node case -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

lemma cardinal_one (z : Fin 1 → ℂ) (j : Fin 1) (w : ℂ) : cardinal z j w = 1 := by
  have hj : j = 0 := Subsingleton.elim _ _
  simp [cardinal, hj]

lemma lebesgueFunction_one (z : Fin 1 → ℂ) (w : ℂ) : lebesgueFunction z w = 1 := by
  simp [lebesgueFunction, cardinal_one]

lemma amplification_one (nodes : NodeFamily 1) : amplification nodes = 1 := by
  obtain ⟨w, hw⟩ := amplification_attained nodes
  rw [hw, lebesgueFunction_one]

lemma isMinimizer_one (nodes : NodeFamily 1) : IsMinimizer nodes := by
  intro other
  simp [amplification_one]

lemma isRegularRotation_one (nodes : NodeFamily 1) : IsRegularRotation nodes := by
  refine ⟨nodes.point 0, Equiv.refl _, ?_⟩
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  simp [hi, regularPoint]

lemma minimizer_iff_regular_one (nodes : NodeFamily 1) :
    IsMinimizer nodes ↔ IsRegularRotation nodes :=
  ⟨fun _ => isRegularRotation_one nodes, fun _ => isMinimizer_one nodes⟩

lemma target_one :
    (∃ nodes : NodeFamily 1, IsMinimizer nodes) ∧
      ∀ nodes : NodeFamily 1, IsMinimizer nodes ↔ IsRegularRotation nodes :=
  ⟨⟨regularNodes 1 (by decide), isMinimizer_one _⟩, minimizer_iff_regular_one⟩

end

end UnitCircleInterpolation
