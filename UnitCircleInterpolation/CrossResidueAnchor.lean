/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.CrossGapRoots
import UnitCircleInterpolation.RootSigns

/-!
# A positive residue anchor for the actual cross-gap interpolants

At a positive cut the anchor is its predecessor node. At cut zero the anchor
is the last node, with the right sample at `2π`. The sample and sum values
agree in both cases. Exhaustion and the proved root locations supply the
zero-free interval, so the residue sign follows from the derivative theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ} {hn : 0 < n}

/-- No difference root location enters the right interval after the predecessor of a cut. -/
lemma crossDifferenceRootLocation_not_mem_anchor_interval (angles : CyclicAngles n hn)
    (i j k : Fin n) (hki : k ≠ i) {t : ℝ}
    (ht : crossDifferenceRootLocation angles i j k t) :
    t ∉ Set.Ioc (angles.angle (gapPredecessor i)) (angles.angle i) := by
  intro hmem
  unfold crossDifferenceRootLocation at ht
  split_ifs at ht with hmiddle
  · have hipred : i ≤ gapPredecessor k := Nat.le_sub_one_of_lt hmiddle.1
    have hile : angles.angle i ≤ angles.angle (gapPredecessor k) :=
      angles.strictMono.monotone hipred
    exact (not_lt_of_ge hmem.2) (hile.trans_lt ht.1)
  · have hkval : k.val ≠ i.val := fun h => hki (Fin.ext h)
    by_cases hki' : k < i
    · have hkpred : k ≤ gapPredecessor i := Nat.le_sub_one_of_lt hki'
      have hupper : t ≤ angles.angle (gapPredecessor i) := by
        rw [ht]
        exact angles.strictMono.monotone hkpred
      exact (not_lt_of_ge hupper) hmem.1
    · have hik : i < k := by change i.val < k.val; change ¬k.val < i.val at hki'; omega
      have hgreater : angles.angle i < t := by rw [ht]; exact angles.strictMono hik
      exact (not_lt_of_ge hmem.2) hgreater

/-- At a positive cut, both the actual sum at the anchor and difference at its sample are `2`. -/
lemma crossResidueAnchor_positive_cut_values (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) (hi : 0 < i.val) :
    sineInterpolant angles.angle (crossDifferenceCoefficient i j)
        (angles.angle (gapPredecessor i)) = 0 ∧
      sineInterpolant angles.angle (crossSumCoefficient i j)
        (angles.angle (gapPredecessor i)) = 2 ∧
      sineInterpolant angles.angle (crossDifferenceCoefficient i j) (angles.angle i) = 2 := by
  have hpred : gapPredecessor i < i := by change i.val - 1 < i.val; omega
  constructor
  · exact crossDifferenceInterpolant_at_node_outside angles i j (gapPredecessor i)
      hij.le (Or.inl hpred)
  constructor
  · rw [crossSumInterpolant_at_node_outside angles i j (gapPredecessor i)
      hij.le (Or.inl hpred), gapCoefficient_at_predecessor i hi]
    norm_num
  · rw [crossDifferenceInterpolant_at_node_inside angles i j i hij.le le_rfl hij,
      gapCoefficient_at_cut]
    norm_num

/-- The positive-cut residue orientation follows from an actual right sample. -/
theorem crossResidueAnchor_positive_cut (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) (hi : 0 < i.val) :
    0 < sineInterpolant angles.angle (crossSumCoefficient i j)
        (angles.angle (gapPredecessor i)) *
      deriv (sineInterpolant angles.angle (crossDifferenceCoefficient i j))
        (angles.angle (gapPredecessor i)) := by
  obtain ⟨root, hmono, hloc, hbound, hroot⟩ :=
    exists_crossDifference_ordered_roots_with_locations angles i j hij
  have hP := crossDifferencePolynomial_ne_zero angles i j hij
  obtain ⟨hz, hsum, hsample⟩ := crossResidueAnchor_positive_cut_values angles i j hij hi
  have hpredbound : angles.angle (gapPredecessor i) ∈ Set.Ico 0 (2 * Real.pi) :=
    ⟨angles.nonneg _, angles.lt_two_pi _⟩
  obtain ⟨r, hr⟩ := cayley_chart_root_mem_of_saturated_roots (n - 1)
    (sineInterpolant angles.angle (crossDifferenceCoefficient i j))
    (interpolantPolynomial angles.angle (crossDifferenceCoefficient i j)) hP
    (interpolantPolynomial_natDegree_le _ _)
    (cos_pow_mul_interpolantPolynomial_eval_tan _ _)
    (interpolantPolynomial_coeff_top _ _) root hmono.injective hbound hroot
    _ hpredbound hz
  have hpred : gapPredecessor i < i := by change i.val - 1 < i.val; omega
  have hsign := sineInterpolant_deriv_mul_pos_of_next_sample angles.angle
    (crossDifferenceCoefficient i j) hP root hmono.injective hbound hroot r
    (angles.angle i) ⟨angles.nonneg i, angles.lt_two_pi i⟩
    (by rw [hr]; exact angles.strictMono hpred) (by
      intro k
      rw [hr]
      exact crossDifferenceRootLocation_not_mem_anchor_interval angles i j
        (crossDifferenceRootIndex i k) (crossDifferenceRootIndex_ne_cut i k) (hloc k))
  rw [hr, hsample] at hsign
  rw [hsum, mul_comm]
  exact hsign

/-- The literal zero-cut coefficient at the last node includes the full-turn phase. -/
lemma gapCoefficient_zero_cut_at_last (hn : 0 < n) :
    gapCoefficient (⟨0, hn⟩ : Fin n) (lastNodeIndex hn) = (-1 : ℝ) ^ (n - 1) := by
  have h := wrapCoefficient_eq_phaseSign_mul_gapCoefficient hn (lastNodeIndex hn)
  rw [wrapCoefficient_at_last] at h
  have hsq : (-1 : ℝ) ^ (n - 1) * (-1 : ℝ) ^ (n - 1) = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    gapCoefficient (⟨0, hn⟩ : Fin n) (lastNodeIndex hn) =
      ((-1 : ℝ) ^ (n - 1) * (-1 : ℝ) ^ (n - 1)) *
        gapCoefficient (⟨0, hn⟩ : Fin n) (lastNodeIndex hn) := by rw [hsq, one_mul]
    _ = (-1 : ℝ) ^ (n - 1) *
        ((-1 : ℝ) ^ (n - 1) * gapCoefficient (⟨0, hn⟩ : Fin n) (lastNodeIndex hn)) := by
      ring
    _ = (-1 : ℝ) ^ (n - 1) := by rw [← h, mul_one]

/-- At cut zero, the sum at the last node equals the difference at the `2π` sample. -/
lemma crossResidueAnchor_zero_cut_values (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) (hi : i.val = 0) :
    sineInterpolant angles.angle (crossDifferenceCoefficient i j)
        (angles.angle (lastNodeIndex hn)) = 0 ∧
      sineInterpolant angles.angle (crossSumCoefficient i j)
        (angles.angle (lastNodeIndex hn)) = 2 * (-1 : ℝ) ^ (n - 1) ∧
      sineInterpolant angles.angle (crossDifferenceCoefficient i j) (2 * Real.pi) =
        2 * (-1 : ℝ) ^ (n - 1) := by
  have hieq : i = (⟨0, hn⟩ : Fin n) := Fin.ext hi
  have hjlast : j ≤ lastNodeIndex hn := Nat.le_sub_one_of_lt j.isLt
  constructor
  · exact crossDifferenceInterpolant_at_node_outside angles i j (lastNodeIndex hn)
      hij.le (Or.inr hjlast)
  constructor
  · rw [crossSumInterpolant_at_node_outside angles i j (lastNodeIndex hn)
      hij.le (Or.inr hjlast), hieq, gapCoefficient_zero_cut_at_last]
  · have hfirst : sineInterpolant angles.angle (crossDifferenceCoefficient i j) 0 = 2 := by
      rw [← angles.first_eq_zero, ← hieq,
        crossDifferenceInterpolant_at_node_inside angles i j i hij.le le_rfl hij,
        gapCoefficient_at_cut]
      norm_num
    have h := sineInterpolant_add_two_pi angles.angle (crossDifferenceCoefficient i j) 0
    rw [zero_add, hfirst] at h
    rw [h, mul_comm]

/-- Every difference root location lies at or before the last node. -/
lemma crossDifferenceRootLocation_le_last (angles : CyclicAngles n hn)
    (i j k : Fin n) {t : ℝ} (ht : crossDifferenceRootLocation angles i j k t) :
    t ≤ angles.angle (lastNodeIndex hn) :=
  (crossDifferenceRootLocation_le_angle angles i j k ht).trans
    (angles.strictMono.monotone (Nat.le_sub_one_of_lt k.isLt))

/-- The wrap anchor also has positive residue, including the even-node phase sign. -/
theorem crossResidueAnchor_zero_cut (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) (hi : i.val = 0) :
    0 < sineInterpolant angles.angle (crossSumCoefficient i j)
        (angles.angle (lastNodeIndex hn)) *
      deriv (sineInterpolant angles.angle (crossDifferenceCoefficient i j))
        (angles.angle (lastNodeIndex hn)) := by
  obtain ⟨root, hmono, hloc, hbound, hroot⟩ :=
    exists_crossDifference_ordered_roots_with_locations angles i j hij
  have hP := crossDifferencePolynomial_ne_zero angles i j hij
  obtain ⟨hz, hsum, hsample⟩ := crossResidueAnchor_zero_cut_values angles i j hij hi
  have hlastbound : angles.angle (lastNodeIndex hn) ∈ Set.Ico 0 (2 * Real.pi) :=
    ⟨angles.nonneg _, angles.lt_two_pi _⟩
  obtain ⟨r, hr⟩ := cayley_chart_root_mem_of_saturated_roots (n - 1)
    (sineInterpolant angles.angle (crossDifferenceCoefficient i j))
    (interpolantPolynomial angles.angle (crossDifferenceCoefficient i j)) hP
    (interpolantPolynomial_natDegree_le _ _)
    (cos_pow_mul_interpolantPolynomial_eval_tan _ _)
    (interpolantPolynomial_coeff_top _ _) root hmono.injective hbound hroot
    _ hlastbound hz
  have hdne : deriv (sineInterpolant angles.angle (crossDifferenceCoefficient i j))
      (angles.angle (lastNodeIndex hn)) ≠ 0 := by
    rw [← hr]
    exact deriv_sineInterpolant_ne_zero_of_saturated_roots angles.angle
      (crossDifferenceCoefficient i j) hP root hmono.injective hbound hroot r
  have hsample_ne : sineInterpolant angles.angle (crossDifferenceCoefficient i j)
      (2 * Real.pi) ≠ 0 := by
    rw [hsample]
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  have hnozero : ∀ t ∈ Set.Ioc (angles.angle (lastNodeIndex hn)) (2 * Real.pi),
      sineInterpolant angles.angle (crossDifferenceCoefficient i j) t ≠ 0 := by
    intro t ht hzero
    by_cases hlt : t < 2 * Real.pi
    · have htbound : t ∈ Set.Ico 0 (2 * Real.pi) :=
        ⟨(angles.nonneg _).trans ht.1.le, hlt⟩
      obtain ⟨k, hk⟩ := cayley_chart_root_mem_of_saturated_roots (n - 1)
        (sineInterpolant angles.angle (crossDifferenceCoefficient i j))
        (interpolantPolynomial angles.angle (crossDifferenceCoefficient i j)) hP
        (interpolantPolynomial_natDegree_le _ _)
        (cos_pow_mul_interpolantPolynomial_eval_tan _ _)
        (interpolantPolynomial_coeff_top _ _) root hmono.injective hbound hroot t htbound hzero
      have hupper := crossDifferenceRootLocation_le_last angles i j
        (crossDifferenceRootIndex i k) (hloc k)
      rw [hk] at hupper
      exact (not_lt_of_ge hupper) ht.1
    · have heq : t = 2 * Real.pi := le_antisymm ht.2 (le_of_not_gt hlt)
      rw [heq] at hzero
      exact hsample_ne hzero
  have hsign := hasDerivAt_mul_sample_pos_of_zero_free_right
    (sineInterpolant angles.angle (crossDifferenceCoefficient i j))
    (angles.lt_two_pi (lastNodeIndex hn))
    (continuous_sineInterpolant angles.angle (crossDifferenceCoefficient i j)).continuousOn
    hz ((differentiable_sineInterpolant angles.angle (crossDifferenceCoefficient i j)
      (angles.angle (lastNodeIndex hn))).hasDerivAt) hdne hnozero
  rw [hsample] at hsign
  rw [hsum, mul_comm]
  exact hsign

/-- The anchor index is always a genuine original node; cut zero uses the last one. -/
def crossResidueAnchorIndex (hn : 0 < n) (i : Fin n) : Fin n :=
  if i.val = 0 then lastNodeIndex hn else gapPredecessor i

theorem crossResidueAnchor_is_root (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) :
    sineInterpolant angles.angle (crossDifferenceCoefficient i j)
      (angles.angle (crossResidueAnchorIndex hn i)) = 0 := by
  by_cases hi : i.val = 0
  · rw [crossResidueAnchorIndex, if_pos hi]
    exact (crossResidueAnchor_zero_cut_values angles i j hij hi).1
  · rw [crossResidueAnchorIndex, if_neg hi]
    exact (crossResidueAnchor_positive_cut_values angles i j hij (by omega)).1

/-- A positive actual sum/derivative product exists for every pair of distinct ordered cuts. -/
theorem crossResidueAnchor_pos (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) :
    0 < sineInterpolant angles.angle (crossSumCoefficient i j)
        (angles.angle (crossResidueAnchorIndex hn i)) *
      deriv (sineInterpolant angles.angle (crossDifferenceCoefficient i j))
        (angles.angle (crossResidueAnchorIndex hn i)) := by
  by_cases hi : i.val = 0
  · rw [crossResidueAnchorIndex, if_pos hi]
    exact crossResidueAnchor_zero_cut angles i j hij hi
  · rw [crossResidueAnchorIndex, if_neg hi]
    exact crossResidueAnchor_positive_cut angles i j hij (by omega)

lemma crossResidueAnchor_sum_ne_zero (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) :
    sineInterpolant angles.angle (crossSumCoefficient i j)
      (angles.angle (crossResidueAnchorIndex hn i)) ≠ 0 := by
  intro hzero
  have h := crossResidueAnchor_pos angles i j hij
  rw [hzero, zero_mul] at h
  exact (lt_irrefl 0) h

/-- Any saturated actual difference-root list contains the proved positive residue anchor. -/
theorem crossResidueAnchor_in_root_list (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) (root : Fin (n - 1) → ℝ)
    (hinj : Function.Injective root) (hbound : ∀ k, root k ∈ Set.Ico 0 (2 * Real.pi))
    (hroot : ∀ k, sineInterpolant angles.angle (crossDifferenceCoefficient i j) (root k) = 0) :
    ∃ k, root k = angles.angle (crossResidueAnchorIndex hn i) ∧
      0 < sineInterpolant angles.angle (crossSumCoefficient i j) (root k) *
        deriv (sineInterpolant angles.angle (crossDifferenceCoefficient i j)) (root k) := by
  have hP := crossDifferencePolynomial_ne_zero angles i j hij
  obtain ⟨k, hk⟩ := cayley_chart_root_mem_of_saturated_roots (n - 1)
    (sineInterpolant angles.angle (crossDifferenceCoefficient i j))
    (interpolantPolynomial angles.angle (crossDifferenceCoefficient i j)) hP
    (interpolantPolynomial_natDegree_le _ _)
    (cos_pow_mul_interpolantPolynomial_eval_tan _ _)
    (interpolantPolynomial_coeff_top _ _) root hinj hbound hroot
    _ ⟨angles.nonneg _, angles.lt_two_pi _⟩ (crossResidueAnchor_is_root angles i j hij)
  refine ⟨k, hk, ?_⟩
  rw [hk]
  exact crossResidueAnchor_pos angles i j hij

end

end UnitCircleInterpolation
