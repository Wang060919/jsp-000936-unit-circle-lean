/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Mathlib.Analysis.Complex.Circle
import Mathlib.Algebra.BigOperators.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace UnitCircleInterpolation

noncomputable section

/-- Distinct nodes on the genuine complex unit circle, with arbitrary enumeration. -/
structure NodeFamily (n : ℕ) where
  point : Fin n → Circle
  injective : Function.Injective point

/-- The complex coordinates of an admissible node family. -/
def NodeFamily.coordinates {n : ℕ} (nodes : NodeFamily n) : Fin n → ℂ :=
  fun i => (nodes.point i : ℂ)

/-- The literal Lagrange cardinal polynomial, evaluated at a complex point. -/
def cardinal {n : ℕ} (z : Fin n → ℂ) (j : Fin n) (w : ℂ) : ℂ :=
  ∏ k ∈ Finset.univ.erase j, (w - z k) / (z j - z k)

/-- The actual sum of the absolute values of all cardinal functions. -/
def lebesgueFunction {n : ℕ} (z : Fin n → ℂ) (w : ℂ) : ℝ :=
  ∑ j, ‖cardinal z j w‖

/-- The supremum over the entire unit circle. Attainment and boundedness are proved separately. -/
def amplification {n : ℕ} (nodes : NodeFamily n) : ℝ :=
  sSup (Set.range (fun w : Circle => lebesgueFunction nodes.coordinates (w : ℂ)))

/-- Global minimization among every admissible node family of the same size. -/
def IsMinimizer {n : ℕ} (nodes : NodeFamily n) : Prop :=
  ∀ other : NodeFamily n, amplification nodes ≤ amplification other

/-- The indexed regular N-gon point. Only positive N appears in the final target. -/
def regularPoint (n : ℕ) (i : Fin n) : Circle :=
  Circle.exp (2 * Real.pi * ((i.val : ℝ) / (n : ℝ)))

/-- A regular polygon, allowing every rotation and every enumeration. -/
def IsRegularRotation {n : ℕ} (nodes : NodeFamily n) : Prop :=
  ∃ rotation : Circle, ∃ permutation : Equiv.Perm (Fin n),
    ∀ i, nodes.point i = rotation * regularPoint n (permutation i)

/-- The complete target: existence and classification for all positive node counts.
This declaration is a proposition, not a proof of the final mathematical theorem. -/
def Target : Prop :=
  ∀ n : ℕ, 0 < n →
    (∃ nodes : NodeFamily n, IsMinimizer nodes) ∧
    ∀ nodes : NodeFamily n, IsMinimizer nodes ↔ IsRegularRotation nodes

end

end UnitCircleInterpolation
