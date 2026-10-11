/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.AngularDomainTopology
import UnitCircleInterpolation.GapPeaks

/-! # Exact transport between original nodes and normalized angular configurations -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {n d : ℕ}

lemma NodeFamily.eq_of_points_eq (nodes other : NodeFamily n)
    (h : ∀ i, nodes.point i = other.point i) : nodes = other := by
  have hp : nodes.point = other.point := funext h
  cases nodes
  cases other
  cases hp
  rfl

lemma orderedAngles_toNodeFamily_eq (nodes : NodeFamily n) (hn : 0 < n) :
    (orderedAngles nodes hn).toNodeFamily =
      (anchoredNodes nodes hn).reindex (anchoredNodes nodes hn).sortedPermutation := by
  apply NodeFamily.eq_of_points_eq
  intro i
  exact (anchoredNodes nodes hn).exp_sortedPhase i

lemma angularAmplification_orderedAngles (nodes : NodeFamily n) (hn : 0 < n) :
    angularAmplification (orderedAngles nodes hn) = amplification nodes := by
  unfold angularAmplification
  rw [orderedAngles_toNodeFamily_eq, amplification_reindex]
  exact amplification_rotate nodes _

lemma isMinimizer_orderedAngles_iff (nodes : NodeFamily n) (hn : 0 < n) :
    IsMinimizer (orderedAngles nodes hn).toNodeFamily ↔ IsMinimizer nodes := by
  rw [orderedAngles_toNodeFamily_eq, isMinimizer_reindex_iff]
  exact isMinimizer_rotate_iff nodes _

lemma isRegularRotation_orderedAngles_iff (nodes : NodeFamily n) (hn : 0 < n) :
    IsRegularRotation (orderedAngles nodes hn).toNodeFamily ↔ IsRegularRotation nodes := by
  rw [orderedAngles_toNodeFamily_eq, isRegularRotation_reindex_iff]
  exact isRegularRotation_rotate_iff nodes _

lemma regularAngularParameters_toNodeFamily (d : ℕ) :
    (cyclicAnglesOfParameters (regularAngularParameters d)
      (regularAngularParameters_mem_domain d)).toNodeFamily =
        regularNodes (d + 1) (Nat.succ_pos d) := by
  apply NodeFamily.eq_of_points_eq
  intro i
  change Circle.exp (angularParameterAngles (regularAngularParameters d) i) = regularPoint _ i
  rw [angularParameterAngles_regular]
  rfl

lemma CyclicAngles.isRegularRotation_of_parameters_eq_regular
    (angles : CyclicAngles (d + 1) (Nat.succ_pos d))
    (h : angles.interiorParameters = regularAngularParameters d) :
    IsRegularRotation angles.toNodeFamily := by
  have hpoints : ∀ i, angles.toNodeFamily.point i = (regularNodes (d + 1) (Nat.succ_pos d)).point i := by
    intro i
    change Circle.exp (angles.angle i) = regularPoint _ i
    rw [← angularParameterAngles_interiorParameters angles, h, angularParameterAngles_regular]
    rfl
  rw [NodeFamily.eq_of_points_eq _ _ hpoints]
  exact regularNodes_isRegularRotation _ _

end

end UnitCircleInterpolation
