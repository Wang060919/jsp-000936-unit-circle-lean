/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.PeakSensitivityMatrix
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# The actual positive left kernel of the peak-sensitivity matrix

At the peak in physical gap `i`, exactly the `d-i` later nodes give negative
sine factors. The resulting row-factor sign cancels the quotient relation's
checkerboard phase. Thus every nonzero left relation of the literal sensitivity
matrix has either all strictly positive or all strictly negative coefficients.
No minimizer, cofactor orientation, or extra sign hypothesis is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Matrix

namespace UnitCircleInterpolation

noncomputable section

variable {d : ℕ} {hn : 0 < d + 1}

private lemma negOnePow_mul_self (k : ℕ) :
    (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
  rcases neg_one_pow_eq_or ℝ k with h | h <;> rw [h] <;> norm_num

private lemma negOnePow_complement (i : Fin (d + 1)) :
    (-1 : ℝ) ^ d * (-1 : ℝ) ^ i.val = (-1 : ℝ) ^ (d - i.val) := by
  have hle : i.val ≤ d := Nat.le_of_lt_succ i.isLt
  have hp : (-1 : ℝ) ^ d = (-1 : ℝ) ^ (d - i.val) * (-1 : ℝ) ^ i.val := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [hp, mul_assoc, negOnePow_mul_self, mul_one]

/-- Each node at or before the gap's left node gives a strictly positive sine factor. -/
lemma sin_orderedPeak_sub_node_pos_of_le (angles : CyclicAngles (d + 1) hn)
    (hsize : 2 ≤ d + 1) (i k : Fin (d + 1)) (hki : k ≤ i) :
    0 < Real.sin ((orderedPeak angles hsize i - angles.angle k) / 2) := by
  have hleft := (orderedPeak_mem_node_gap angles hsize i).1
  have hnode := angles.strictMono.monotone hki
  have hpeak := orderedPeak_mem_Ioo angles hsize i
  have hnonneg := angles.nonneg k
  apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [hpeak.1, hpeak.2]

/-- Every later node gives a strictly negative sine factor at the physical gap peak. -/
lemma sin_orderedPeak_sub_node_neg_of_lt (angles : CyclicAngles (d + 1) hn)
    (hsize : 2 ≤ d + 1) (i k : Fin (d + 1)) (hik : i < k) :
    Real.sin ((orderedPeak angles hsize i - angles.angle k) / 2) < 0 := by
  have hright := (orderedPeak_mem_node_gap angles hsize i).2
  have hnode := cyclicGapRight_le_angle_of_lt angles hik
  have hpeak := orderedPeak_mem_Ioo angles hsize i
  have hupper := angles.lt_two_pi k
  apply Real.sin_neg_of_neg_of_neg_pi_lt <;> linarith [hpeak.1, hpeak.2]

/-- The literal sine-product row factor has the sign of its `d-i` negative factors. -/
theorem peakSensitivityRowFactor_phase_pos (angles : CyclicAngles (d + 1) hn)
    (hsize : 2 ≤ d + 1) (i : Fin (d + 1)) :
    0 < (-1 : ℝ) ^ (d - i.val) * peakSensitivityRowFactor angles hsize i := by
  classical
  have hprod : 0 < ∏ k : Fin (d + 1),
      (if i < k then (-1 : ℝ) else 1) *
        Real.sin ((orderedPeak angles hsize i - angles.angle k) / 2) := by
    apply Finset.prod_pos
    intro k _
    by_cases hik : i < k
    · rw [if_pos hik, neg_one_mul]
      exact neg_pos.mpr (sin_orderedPeak_sub_node_neg_of_lt angles hsize i k hik)
    · rw [if_neg hik, one_mul]
      exact sin_orderedPeak_sub_node_pos_of_le angles hsize i k (le_of_not_gt hik)
  have hfilter : (Finset.univ.filter (fun k : Fin (d + 1) => i < k)) = Finset.Ioi i := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioi]
  have hphase : (∏ k : Fin (d + 1), if i < k then (-1 : ℝ) else 1) =
      (-1 : ℝ) ^ (d - i.val) := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, one_pow, mul_one, hfilter, Fin.card_Ioi,
      Nat.add_sub_cancel]
  rw [Finset.prod_mul_distrib, hphase] at hprod
  exact hprod

/-- The same row-factor sign, written in the phase used by the actual quotient relation. -/
lemma peakSensitivityRowFactor_checkerboard_pos (angles : CyclicAngles (d + 1) hn)
    (hsize : 2 ≤ d + 1) (i : Fin (d + 1)) :
    0 < ((-1 : ℝ) ^ d * (-1 : ℝ) ^ i.val) *
      peakSensitivityRowFactor angles hsize i := by
  rw [negOnePow_complement]
  exact peakSensitivityRowFactor_phase_pos angles hsize i

/-- A left sensitivity relation already vanishes as a quotient combination on the whole circle.
The `d` actual moving nodes supply more roots than the degree `d-1` root bound. -/
theorem peakSensitivity_left_relation_quotient_relation
    (angles : CyclicAngles (d + 1) hn) (hsize : 2 ≤ d + 1)
    (a : Fin (d + 1) → ℝ)
    (hrel : a ᵥ* peakSensitivityMatrix angles hsize = 0) :
    ∀ t, (∑ i, (a i * peakSensitivityRowFactor angles hsize i) *
      orderedPeakQuotient angles hsize i t) = 0 := by
  classical
  let b : Fin (d + 1) → ℝ := fun i => a i * peakSensitivityRowFactor angles hsize i
  have hbnode (j : Fin d) :
      (∑ i, b i * orderedPeakQuotient angles hsize i (angles.angle j.succ)) = 0 := by
    have hj := congrFun hrel j
    simp only [Matrix.vecMul_apply_eq_sum, Pi.zero_apply,
      peakSensitivityMatrix_apply_factorization, peakQuotientNodeMatrix] at hj
    have heq :
        (∑ i, a i * (peakSensitivityRowFactor angles hsize i *
          orderedPeakQuotient angles hsize i (angles.angle j.succ) *
          peakSensitivityColumnFactor angles j)) =
        (∑ i, b i * orderedPeakQuotient angles hsize i (angles.angle j.succ)) *
          peakSensitivityColumnFactor angles j := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [b]
      ring
    rw [heq] at hj
    exact (mul_eq_zero.mp hj).resolve_right (peakSensitivityColumnFactor_ne_zero angles j)
  let f : ℝ → ℝ := ∑ i, b i • orderedPeakQuotient angles hsize i
  have hfmem : f ∈ homogeneousTrigSpace (d + 1 - 2) :=
    (homogeneousTrigSpace (d + 1 - 2)).sum_mem (fun i _ =>
      (homogeneousTrigSpace (d + 1 - 2)).smul_mem _ (orderedPeakQuotient_mem_space angles hsize i))
  have hfzero : f = 0 := by
    by_contra hne
    have hfroot (j : Fin d) : f (angles.angle j.succ) = 0 := by
      simpa only [f, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hbnode j
    have hcount := actualPeakQuotientSpace_hasCyclicRootBound d f hfmem hne
      (fun j : Fin d => angles.angle j.succ)
      (angles.strictMono.injective.comp (Fin.succ_injective d))
      (fun j => ⟨angles.nonneg j.succ, angles.lt_two_pi j.succ⟩) hfroot
    omega
  intro t
  have ht := congrFun hfzero t
  simpa only [f, b, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using ht

/-- Every nonzero left relation of the actual sensitivity matrix has one strict sign. -/
theorem peakSensitivity_left_relation_coherent_sign
    (angles : CyclicAngles (d + 1) hn) (hsize : 2 ≤ d + 1)
    (a : Fin (d + 1) → ℝ)
    (hrel : a ᵥ* peakSensitivityMatrix angles hsize = 0) (ha : a ≠ 0) :
    (∀ i, 0 < a i) ∨ (∀ i, a i < 0) := by
  let b : Fin (d + 1) → ℝ := fun i => a i * peakSensitivityRowFactor angles hsize i
  have hbrel : ∀ t, (∑ i, b i * orderedPeakQuotient angles hsize i t) = 0 :=
    peakSensitivity_left_relation_quotient_relation angles hsize a hrel
  have hbne : b ≠ 0 := by
    intro hbzero
    apply ha
    funext i
    have hi : a i * peakSensitivityRowFactor angles hsize i = 0 := congrFun hbzero i
    exact (mul_eq_zero.mp hi).resolve_right (peakSensitivityRowFactor_ne_zero angles hsize i)
  have hphase (i : Fin (d + 1)) :
      (-1 : ℝ) ^ i.val * b i = ((-1 : ℝ) ^ d * a i) *
        (((-1 : ℝ) ^ d * (-1 : ℝ) ^ i.val) * peakSensitivityRowFactor angles hsize i) := by
    dsimp only [b]
    calc
      _ = ((-1 : ℝ) ^ d * (-1 : ℝ) ^ d) *
          ((-1 : ℝ) ^ i.val * (a i * peakSensitivityRowFactor angles hsize i)) := by
            rw [negOnePow_mul_self, one_mul]
      _ = _ := by ring
  have hcommon : (∀ i, 0 < (-1 : ℝ) ^ d * a i) ∨
      (∀ i, (-1 : ℝ) ^ d * a i < 0) := by
    rcases actualPeakQuotient_relation_coherent_sign angles hsize b hbrel hbne with h | h
    · left
      intro i
      have hi := h i
      rw [hphase] at hi
      exact (mul_pos_iff_of_pos_right (peakSensitivityRowFactor_checkerboard_pos angles hsize i)).mp hi
    · right
      intro i
      have hi := h i
      rw [hphase] at hi
      by_contra hnot
      exact (not_le_of_gt hi) (mul_nonneg (le_of_not_gt hnot)
        (peakSensitivityRowFactor_checkerboard_pos angles hsize i).le)
  rcases neg_one_pow_eq_or ℝ d with hd | hd
  · simpa only [hd, one_mul] using hcommon
  · rcases hcommon with h | h
    · right
      intro i
      have hi := h i
      simpa only [hd, neg_one_mul, neg_pos] using hi
    · left
      intro i
      have hi := h i
      simpa only [hd, neg_one_mul, neg_neg_iff_pos] using hi

end

end UnitCircleInterpolation
