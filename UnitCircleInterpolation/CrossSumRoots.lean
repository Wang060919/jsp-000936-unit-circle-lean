/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.CrossGapCoefficients
import UnitCircleInterpolation.CircularSimpleRoots
import Mathlib.Topology.Order.IntermediateValue

/-!
# Saturated roots of the actual cross-gap sum

The sum has a nodal zero between the cuts and an IVT zero in every gap whose
two endpoints belong to one complementary nonzero block. When the first cut
is positive, the zero indexed by node zero is in the final wrap gap. Erasing
the second cut gives exactly `n - 1` pairwise distinct, canonical cyclic roots.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ} {hn : 0 < n}

private lemma crossSum_exists_zero_between_opposite_values (f : ℝ → ℝ)
    (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (hopposite : f b = -f a) (hne : f a ≠ 0) :
    ∃ t, t ∈ Set.Ioo a b ∧ f t = 0 := by
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hright : 0 < f b := by rw [hopposite]; linarith
    exact intermediate_value_Ioo hab.le hf.continuousOn ⟨hneg, hright⟩
  · have hright : f b < 0 := by rw [hopposite]; linarith
    exact intermediate_value_Ioo' hab.le hf.continuousOn ⟨hright, hpos⟩

/-- Exact location of the sum zero assigned to a nodal index other than `j`. -/
def crossSumRootLocation (angles : CyclicAngles n hn) (i j k : Fin n) (t : ℝ) : Prop :=
  if i ≤ k ∧ k < j then t = angles.angle k
  else if k.val = 0 then t ∈ wrapGap angles
  else t ∈ Set.Ioo (angles.angle (gapPredecessor k)) (angles.angle k)

/-- Alternating actual endpoint values construct a sum zero in an exterior ordinary gap. -/
theorem exists_crossSum_root_on_gap (angles : CyclicAngles n hn)
    (i j k : Fin n) (hij : i < j) (hkpos : 0 < k.val) (hk : k < i ∨ j < k) :
    ∃ t, t ∈ Set.Ioo (angles.angle (gapPredecessor k)) (angles.angle k) ∧
      sineInterpolant angles.angle (crossSumCoefficient i j) t = 0 := by
  have hpred : (gapPredecessor k).val + 1 = k.val := by
    change k.val - 1 + 1 = k.val
    omega
  have hpk : gapPredecessor k < k := by change k.val - 1 < k.val; omega
  have hpredoutside : gapPredecessor k < i ∨ j ≤ gapPredecessor k := by
    rcases hk with hki | hjk
    · exact Or.inl (hpk.trans hki)
    · exact Or.inr (Nat.le_sub_one_of_lt hjk)
  have hkoutside : k < i ∨ j ≤ k := hk.imp id le_of_lt
  apply crossSum_exists_zero_between_opposite_values
    (sineInterpolant angles.angle (crossSumCoefficient i j))
    (continuous_sineInterpolant angles.angle (crossSumCoefficient i j))
    (angles.strictMono hpk)
  · exact crossSumInterpolant_consecutive_flip angles i j (gapPredecessor k) k
      hij hpred hpredoutside hkoutside
  · exact (crossSumInterpolant_at_node_ne_zero_iff angles i j
      (gapPredecessor k) hij.le).mpr hpredoutside

/-- For a positive first cut, the final gap has opposite nonzero actual endpoint values. -/
theorem crossSumInterpolant_wrap_opposite (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) (hi : 0 < i.val) :
    sineInterpolant angles.angle (crossSumCoefficient i j) (2 * Real.pi) =
      -sineInterpolant angles.angle (crossSumCoefficient i j)
        (angles.angle (lastNodeIndex hn)) := by
  have hzlt : (⟨0, hn⟩ : Fin n) < i := hi
  have hlast : j ≤ lastNodeIndex hn := Nat.le_sub_one_of_lt j.isLt
  have hzero : sineInterpolant angles.angle (crossSumCoefficient i j) 0 =
      2 * gapCoefficient i (⟨0, hn⟩ : Fin n) := by
    rw [← angles.first_eq_zero]
    exact crossSumInterpolant_at_node_outside angles i j _ hij.le (Or.inl hzlt)
  have hlastvalue := crossSumInterpolant_at_node_outside angles i j
    (lastNodeIndex hn) hij.le (Or.inr hlast)
  have hperiod := sineInterpolant_add_two_pi angles.angle (crossSumCoefficient i j) 0
  rw [zero_add, hzero] at hperiod
  calc
    sineInterpolant angles.angle (crossSumCoefficient i j) (2 * Real.pi) =
        (-1 : ℝ) ^ (n - 1) * (2 * gapCoefficient i ⟨0, hn⟩) := hperiod
    _ = 2 * ((-1 : ℝ) ^ (n - 1) * gapCoefficient i ⟨0, hn⟩) := by ring
    _ = -(2 * gapCoefficient i (lastNodeIndex hn)) := by
      rw [gapCoefficient_wrap_flip hn i hi]
      ring
    _ = -sineInterpolant angles.angle (crossSumCoefficient i j)
        (angles.angle (lastNodeIndex hn)) := by rw [hlastvalue]

theorem exists_crossSum_root_on_wrapGap (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) (hi : 0 < i.val) :
    ∃ t, t ∈ wrapGap angles ∧
      sineInterpolant angles.angle (crossSumCoefficient i j) t = 0 := by
  apply crossSum_exists_zero_between_opposite_values
    (sineInterpolant angles.angle (crossSumCoefficient i j))
    (continuous_sineInterpolant angles.angle (crossSumCoefficient i j))
    (angles.lt_two_pi (lastNodeIndex hn))
  · exact crossSumInterpolant_wrap_opposite angles i j hij hi
  · exact (crossSumInterpolant_at_node_ne_zero_iff angles i j
      (lastNodeIndex hn) hij.le).mpr (Or.inr (Nat.le_sub_one_of_lt j.isLt))

/-- Every nodal index except the second cut supplies an actual zero. -/
theorem exists_crossSum_root_at_index (angles : CyclicAngles n hn)
    (i j k : Fin n) (hij : i < j) (hkj : k ≠ j) :
    ∃ t, crossSumRootLocation angles i j k t ∧
      sineInterpolant angles.angle (crossSumCoefficient i j) t = 0 := by
  by_cases hmiddle : i ≤ k ∧ k < j
  · exact ⟨angles.angle k, by simp [crossSumRootLocation, hmiddle],
      crossSumInterpolant_at_node_inside angles i j k hij.le hmiddle.1 hmiddle.2⟩
  · have houtside : k < i ∨ j < k := by
      have hneq : k.val ≠ j.val := fun h => hkj (Fin.ext h)
      by_cases hki : k < i
      · exact Or.inl hki
      · right
        have hik : i ≤ k := le_of_not_gt hki
        have hjk : j ≤ k := le_of_not_gt (fun h => hmiddle ⟨hik, h⟩)
        change j.val < k.val
        have hjkval : j.val ≤ k.val := hjk
        omega
    by_cases hkzero : k.val = 0
    · have hipos : 0 < i.val := by
        rcases houtside with hki | hjk
        · have hval : k.val < i.val := hki; omega
        · have hval : j.val < k.val := hjk; omega
      obtain ⟨t, ht, hz⟩ := exists_crossSum_root_on_wrapGap angles i j hij hipos
      exact ⟨t, by simpa [crossSumRootLocation, hmiddle, hkzero] using ht, hz⟩
    · have hkpos : 0 < k.val := Nat.pos_of_ne_zero hkzero
      obtain ⟨t, ht, hz⟩ := exists_crossSum_root_on_gap angles i j k hij hkpos houtside
      exact ⟨t, by simpa [crossSumRootLocation, hmiddle, hkzero] using ht, hz⟩

/-- Except for a wrap-gap zero, the assigned zero is at or before its nodal index. -/
lemma crossSumRootLocation_le_angle (angles : CyclicAngles n hn)
    (i j k : Fin n) {t : ℝ} (ht : crossSumRootLocation angles i j k t)
    (hregular : k.val ≠ 0 ∨ i ≤ k ∧ k < j) : t ≤ angles.angle k := by
  unfold crossSumRootLocation at ht
  split_ifs at ht with hmiddle hkzero
  · exact ht.le
  · rcases hregular with hk | hmiddle'
    · exact (hk hkzero).elim
    · exact (hmiddle hmiddle').elim
  · exact ht.2.le

/-- A larger regular index places its assigned zero strictly after every smaller node. -/
lemma angle_lt_of_crossSumRootLocation_of_lt (angles : CyclicAngles n hn)
    (i j k l : Fin n) (hkl : k < l) {u : ℝ}
    (hu : crossSumRootLocation angles i j l u) : angles.angle k < u := by
  have hlpos : 0 < l.val := by have hval : k.val < l.val := hkl; omega
  unfold crossSumRootLocation at hu
  split_ifs at hu with hmiddle hlzero
  · rw [hu]
    exact angles.strictMono hkl
  · omega
  · exact (angles.strictMono.monotone (Nat.le_sub_one_of_lt hkl)).trans_lt hu.1

lemma crossSumRootLocation_distinct_of_lt (angles : CyclicAngles n hn)
    (i j k l : Fin n) (hkl : k < l) {t u : ℝ}
    (ht : crossSumRootLocation angles i j k t)
    (hu : crossSumRootLocation angles i j l u) : t ≠ u := by
  by_cases hregular : k.val ≠ 0 ∨ i ≤ k ∧ k < j
  · exact ne_of_lt ((crossSumRootLocation_le_angle angles i j k ht hregular).trans_lt
      (angle_lt_of_crossSumRootLocation_of_lt angles i j k l hkl hu))
  · have hkzero : k.val = 0 := by tauto
    have hmiddle : ¬(i ≤ k ∧ k < j) := by tauto
    have hwrap : t ∈ wrapGap angles := by
      simpa [crossSumRootLocation, hmiddle, hkzero] using ht
    have hlzero : l.val ≠ 0 := by have hval : k.val < l.val := hkl; omega
    have huless := crossSumRootLocation_le_angle angles i j l hu (Or.inl hlzero)
    exact ne_of_gt (huless.trans_lt (angle_lt_of_mem_wrapGap angles hwrap l))

lemma crossSumRootLocation_mem_Ico (angles : CyclicAngles n hn)
    (i j k : Fin n) {t : ℝ} (ht : crossSumRootLocation angles i j k t) :
    t ∈ Set.Ico 0 (2 * Real.pi) := by
  unfold crossSumRootLocation at ht
  split_ifs at ht with hmiddle hkzero
  · rw [ht]
    exact ⟨angles.nonneg k, angles.lt_two_pi k⟩
  · exact ⟨(wrapGap_mem_Ioo angles ht).1.le, ht.2⟩
  · exact ⟨(angles.nonneg _).trans ht.1.le, ht.2.trans (angles.lt_two_pi k)⟩

/-- The actual zero selected at every erased nodal index is distinct from all the others. -/
theorem exists_crossSum_roots_on_erase (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) :
    ∃ root : ↥(Finset.univ.erase j : Finset (Fin n)) → ℝ, Function.Injective root ∧
      (∀ k, crossSumRootLocation angles i j k.val (root k)) ∧
      (∀ k, root k ∈ Set.Ico 0 (2 * Real.pi)) ∧
      (∀ k, sineInterpolant angles.angle (crossSumCoefficient i j) (root k) = 0) := by
  classical
  let s := (Finset.univ.erase j : Finset (Fin n))
  have hz (k : s) : ∃ t, crossSumRootLocation angles i j k.val t ∧
      sineInterpolant angles.angle (crossSumCoefficient i j) t = 0 :=
    exists_crossSum_root_at_index angles i j k.val hij (Finset.mem_erase.mp k.property).1
  let root : s → ℝ := fun k => Classical.choose (hz k)
  have hloc (k : s) : crossSumRootLocation angles i j k.val (root k) :=
    (Classical.choose_spec (hz k)).1
  refine ⟨root, ?_, hloc, fun k => crossSumRootLocation_mem_Ico angles i j k.val
    (hloc k), fun k => (Classical.choose_spec (hz k)).2⟩
  intro k l heq
  apply Subtype.ext
  rcases lt_trichotomy k.val l.val with hkl | hkl | hlk
  · exact False.elim ((crossSumRootLocation_distinct_of_lt angles i j k.val l.val hkl
      (hloc k) (hloc l)) heq)
  · exact hkl
  · exact False.elim ((crossSumRootLocation_distinct_of_lt angles i j l.val k.val hlk
      (hloc l) (hloc k)) heq.symm)

/-- Increasing enumeration of the erased nodal labels; the wrap zero retains label zero. -/
def crossSumRootIndex (j : Fin n) (k : Fin (n - 1)) : Fin n :=
  ((Finset.univ.erase j : Finset (Fin n)).orderIsoOfFin (by simp) k).val

lemma crossSumRootIndex_ne_cut (j : Fin n) (k : Fin (n - 1)) :
    crossSumRootIndex j k ≠ j :=
  (Finset.mem_erase.mp
    (((Finset.univ.erase j : Finset (Fin n)).orderIsoOfFin (by simp) k).property)).1

/-- The actual sum has `n - 1` distinct roots with retained exact locations. -/
theorem exists_crossSum_roots_with_locations (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) :
    ∃ root : Fin (n - 1) → ℝ, Function.Injective root ∧
      (∀ k, crossSumRootLocation angles i j (crossSumRootIndex j k) (root k)) ∧
      (∀ k, root k ∈ Set.Ico 0 (2 * Real.pi)) ∧
      (∀ k, sineInterpolant angles.angle (crossSumCoefficient i j) (root k) = 0) := by
  classical
  obtain ⟨root, hinj, hloc, hbound, hroot⟩ := exists_crossSum_roots_on_erase angles i j hij
  let e := (Finset.univ.erase j : Finset (Fin n)).orderIsoOfFin (by simp :
    (Finset.univ.erase j : Finset (Fin n)).card = n - 1)
  exact ⟨fun k => root (e k), hinj.comp e.injective, fun k => hloc (e k),
    fun k => hbound (e k), fun k => hroot (e k)⟩

lemma crossSumPolynomial_ne_zero (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) :
    interpolantPolynomial angles.angle (crossSumCoefficient i j) ≠ 0 := by
  apply interpolantPolynomial_ne_zero_of_node angles.angle angles.phaseNodes_injective
    (fun k => ⟨angles.nonneg k, angles.lt_two_pi k⟩) (crossSumCoefficient i j) j
  exact (crossSumCoefficient_ne_zero_iff i j j hij.le).mpr (Or.inr le_rfl)

/-- The constructed actual roots are simple and exhaust all zeros in the complete turn. -/
theorem exists_crossSum_saturated_roots_with_locations (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) :
    ∃ root : Fin (n - 1) → ℝ, Function.Injective root ∧
      (∀ k, crossSumRootLocation angles i j (crossSumRootIndex j k) (root k)) ∧
      (∀ k, root k ∈ Set.Ico 0 (2 * Real.pi)) ∧
      (∀ k, sineInterpolant angles.angle (crossSumCoefficient i j) (root k) = 0) ∧
      (∀ k, deriv (sineInterpolant angles.angle (crossSumCoefficient i j)) (root k) ≠ 0) ∧
      (∀ t ∈ Set.Ico 0 (2 * Real.pi),
        sineInterpolant angles.angle (crossSumCoefficient i j) t = 0 ↔
          ∃ k, root k = t) := by
  obtain ⟨root, hinj, hloc, hbound, hroot⟩ := exists_crossSum_roots_with_locations angles i j hij
  have hP := crossSumPolynomial_ne_zero angles i j hij
  refine ⟨root, hinj, hloc, hbound, hroot, ?_, ?_⟩
  · exact deriv_sineInterpolant_ne_zero_of_saturated_roots angles.angle
      (crossSumCoefficient i j) hP root hinj hbound hroot
  · intro t ht
    constructor
    · intro hz
      exact cayley_chart_root_mem_of_saturated_roots (n - 1)
        (sineInterpolant angles.angle (crossSumCoefficient i j))
        (interpolantPolynomial angles.angle (crossSumCoefficient i j)) hP
        (interpolantPolynomial_natDegree_le _ _) (cos_pow_mul_interpolantPolynomial_eval_tan _ _)
        (interpolantPolynomial_coeff_top _ _) root hinj hbound hroot t ht hz
    · rintro ⟨k, rfl⟩
      exact hroot k

end

end UnitCircleInterpolation
