/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.AngularParameters
import UnitCircleInterpolation.RegularNodes
import Mathlib.Analysis.Convex.PathConnected

/-! # Convexity and an explicit regular point in the actual angular domain -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {d : ℕ}

lemma angularParameterAngles_smul_add (u v : Fin d → ℝ) (a b : ℝ) :
    angularParameterAngles (a • u + b • v) =
      a • angularParameterAngles u + b • angularParameterAngles v := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp only [angularParameterAngles_zero, angularParameterAngles_succ,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_zero, add_zero]

theorem convex_angularParameterDomain (d : ℕ) : Convex ℝ (angularParameterDomain d) := by
  intro u hu v hv a b ha hb hab
  constructor
  · intro i j hij
    rw [angularParameterAngles_smul_add]
    change a * angularParameterAngles u i + b * angularParameterAngles v i <
      a * angularParameterAngles u j + b * angularParameterAngles v j
    by_cases ha' : 0 < a
    · exact add_lt_add_of_lt_of_le
        (mul_lt_mul_of_pos_left (hu.1 hij) ha')
        (mul_le_mul_of_nonneg_left (hv.1 hij).le hb)
    · have hb' : 0 < b := by linarith
      exact add_lt_add_of_le_of_lt
        (mul_le_mul_of_nonneg_left (hu.1 hij).le ha)
        (mul_lt_mul_of_pos_left (hv.1 hij) hb')
  · intro i
    exact (convex_Iio (2 * Real.pi)) (hu.2 i) (hv.2 i) ha hb hab

theorem isPreconnected_angularParameterDomain (d : ℕ) :
    IsPreconnected (angularParameterDomain d) :=
  (convex_angularParameterDomain d).isPreconnected

/-- The free angles of the literal regular polygon, without normalization choices. -/
def regularAngularParameters (d : ℕ) : Fin d → ℝ :=
  fun i => 2 * Real.pi * ((i.succ.val : ℝ) / ((d + 1 : ℕ) : ℝ))

lemma angularParameterAngles_regular (d : ℕ) (i : Fin (d + 1)) :
    angularParameterAngles (regularAngularParameters d) i =
      2 * Real.pi * ((i.val : ℝ) / ((d + 1 : ℕ) : ℝ)) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [angularParameterAngles_zero, Fin.val_zero, Nat.cast_zero, zero_div, mul_zero]
  · rfl

theorem regularAngularParameters_mem_domain (d : ℕ) :
    regularAngularParameters d ∈ angularParameterDomain d := by
  constructor
  · intro i j hij
    rw [angularParameterAngles_regular, angularParameterAngles_regular]
    apply mul_lt_mul_of_pos_left _ (by positivity : 0 < 2 * Real.pi)
    exact div_lt_div_of_pos_right (Nat.cast_lt.mpr hij)
      (Nat.cast_pos.mpr (Nat.succ_pos d))
  · intro i
    exact (regular_angle_mem_Ico (d + 1) (Nat.succ_pos d) i.succ).2

theorem angularParameterDomain_nonempty (d : ℕ) : (angularParameterDomain d).Nonempty :=
  ⟨regularAngularParameters d, regularAngularParameters_mem_domain d⟩

theorem isConnected_angularParameterDomain (d : ℕ) : IsConnected (angularParameterDomain d) :=
  (convex_angularParameterDomain d).isConnected (angularParameterDomain_nonempty d)

end

end UnitCircleInterpolation
