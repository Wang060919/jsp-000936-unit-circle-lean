/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.CrossGapCoefficients
import UnitCircleInterpolation.CircularSimpleRoots
import Mathlib.Topology.Order.IntermediateValue

/-!
# Saturated roots of the actual cross-gap difference

The difference coefficients vanish at every node outside the cut interval.
Inside it their alternating nonzero values give an IVT root in each intervening
open node gap. Erasing the first cut leaves exactly `n - 1` ordered locations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ} {hn : 0 < n}

private lemma cross_exists_zero_between_opposite_values (f : ℝ → ℝ)
    (hf : Continuous f) {a b : ℝ} (hab : a < b)
    (hopposite : f b = -f a) (hne : f a ≠ 0) :
    ∃ t, t ∈ Set.Ioo a b ∧ f t = 0 := by
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hright : 0 < f b := by rw [hopposite]; linarith
    exact intermediate_value_Ioo hab.le hf.continuousOn ⟨hneg, hright⟩
  · have hright : f b < 0 := by rw [hopposite]; linarith
    exact intermediate_value_Ioo' hab.le hf.continuousOn ⟨hright, hpos⟩

/-- The root indexed by `k` lies before that node inside the cuts, or at it outside. -/
def crossDifferenceRootLocation (angles : CyclicAngles n hn) (i j k : Fin n) (t : ℝ) :
    Prop :=
  if i < k ∧ k < j then
    t ∈ Set.Ioo (angles.angle (gapPredecessor k)) (angles.angle k)
  else t = angles.angle k

/-- Actual opposite nodal values construct a root in every interior difference gap. -/
theorem exists_crossDifference_root_on_gap (angles : CyclicAngles n hn)
    (i j k : Fin n) (hik : i < k) (hkj : k < j) :
    ∃ t, t ∈ Set.Ioo (angles.angle (gapPredecessor k)) (angles.angle k) ∧
      sineInterpolant angles.angle (crossDifferenceCoefficient i j) t = 0 := by
  have hkpos : 0 < k.val := by have hval : i.val < k.val := hik; omega
  have hpred : (gapPredecessor k).val + 1 = k.val := by
    change k.val - 1 + 1 = k.val
    omega
  have hpk : gapPredecessor k < k := by
    change k.val - 1 < k.val
    omega
  have hip : i ≤ gapPredecessor k := Nat.le_sub_one_of_lt hik
  apply cross_exists_zero_between_opposite_values
    (sineInterpolant angles.angle (crossDifferenceCoefficient i j))
    (continuous_sineInterpolant angles.angle (crossDifferenceCoefficient i j))
    (angles.strictMono hpk)
  · exact crossDifferenceInterpolant_consecutive_flip angles i j (gapPredecessor k) k
      (hik.trans hkj).le hpred hip hkj
  · exact (crossDifferenceInterpolant_at_node_ne_zero_iff angles i j
      (gapPredecessor k) (hik.trans hkj).le).mpr ⟨hip, hpk.trans hkj⟩

/-- Every index except `i` determines one proved root location. -/
theorem exists_crossDifference_root_at_index (angles : CyclicAngles n hn)
    (i j k : Fin n) (hij : i < j) (hki : k ≠ i) :
    ∃ t, crossDifferenceRootLocation angles i j k t ∧
      sineInterpolant angles.angle (crossDifferenceCoefficient i j) t = 0 := by
  by_cases hk : i < k ∧ k < j
  · obtain ⟨t, ht, hz⟩ := exists_crossDifference_root_on_gap angles i j k hk.1 hk.2
    exact ⟨t, by simpa [crossDifferenceRootLocation, hk] using ht, hz⟩
  · have houtside : k < i ∨ j ≤ k := by
      have hval : k.val ≠ i.val := fun h => hki (Fin.ext h)
      by_cases hki' : k < i
      · exact Or.inl hki'
      · right
        have hik : i < k := by change i.val < k.val; change ¬k.val < i.val at hki'; omega
        exact le_of_not_gt (fun hkj => hk ⟨hik, hkj⟩)
    exact ⟨angles.angle k, by simp [crossDifferenceRootLocation, hk],
      crossDifferenceInterpolant_at_node_outside angles i j k hij.le houtside⟩

lemma crossDifferenceRootLocation_le_angle (angles : CyclicAngles n hn)
    (i j k : Fin n) {t : ℝ} (ht : crossDifferenceRootLocation angles i j k t) :
    t ≤ angles.angle k := by
  unfold crossDifferenceRootLocation at ht
  split_ifs at ht with hk
  · exact ht.2.le
  · exact ht.le

lemma crossDifferenceRootLocation_mem_Ico (angles : CyclicAngles n hn)
    (i j k : Fin n) {t : ℝ} (ht : crossDifferenceRootLocation angles i j k t) :
    t ∈ Set.Ico 0 (2 * Real.pi) := by
  unfold crossDifferenceRootLocation at ht
  split_ifs at ht with hk
  · exact ⟨(angles.nonneg _).trans ht.1.le, ht.2.trans (angles.lt_two_pi k)⟩
  · rw [ht]
    exact ⟨angles.nonneg k, angles.lt_two_pi k⟩

/-- The chosen roots on the erased index set are strictly ordered, including the nodal roots. -/
theorem exists_crossDifference_roots_on_erase (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) :
    ∃ root : {k : Fin n // k ∈ (Finset.univ.erase i : Finset (Fin n))} → ℝ,
      StrictMono root ∧
      (∀ k, crossDifferenceRootLocation angles i j k.val (root k)) ∧
      (∀ k, root k ∈ Set.Ico 0 (2 * Real.pi)) ∧
      (∀ k, sineInterpolant angles.angle (crossDifferenceCoefficient i j) (root k) = 0) := by
  classical
  let s := (Finset.univ.erase i : Finset (Fin n))
  have hz (k : s) : ∃ t, crossDifferenceRootLocation angles i j k.val t ∧
      sineInterpolant angles.angle (crossDifferenceCoefficient i j) t = 0 :=
    exists_crossDifference_root_at_index angles i j k.val hij (Finset.mem_erase.mp k.property).1
  let root : s → ℝ := fun k => Classical.choose (hz k)
  have hloc (k : s) : crossDifferenceRootLocation angles i j k.val (root k) :=
    (Classical.choose_spec (hz k)).1
  refine ⟨root, ?_, hloc, fun k => crossDifferenceRootLocation_mem_Ico angles i j k.val
    (hloc k), fun k => (Classical.choose_spec (hz k)).2⟩
  intro k l hkl
  have hkle : root k ≤ angles.angle k.val :=
    crossDifferenceRootLocation_le_angle angles i j k.val (hloc k)
  have hkl' : k.val < l.val := hkl
  have hl := hloc l
  unfold crossDifferenceRootLocation at hl
  split_ifs at hl with hlmiddle
  · have hkpred : k.val ≤ gapPredecessor l.val := Nat.le_sub_one_of_lt hkl'
    exact (hkle.trans (angles.strictMono.monotone hkpred)).trans_lt hl.1
  · rw [hl]
    exact hkle.trans_lt (angles.strictMono hkl')

/-- The increasing enumeration of all nodal indices except the first cut. -/
def crossDifferenceRootIndex (i : Fin n) (k : Fin (n - 1)) : Fin n :=
  ((Finset.univ.erase i : Finset (Fin n)).orderIsoOfFin (by simp) k).val

lemma crossDifferenceRootIndex_strictMono (i : Fin n) :
    StrictMono (crossDifferenceRootIndex i) := by
  intro k l hkl
  exact ((Finset.univ.erase i : Finset (Fin n)).orderIsoOfFin (by simp)).strictMono hkl

lemma crossDifferenceRootIndex_ne_cut (i : Fin n) (k : Fin (n - 1)) :
    crossDifferenceRootIndex i k ≠ i :=
  (Finset.mem_erase.mp
    (((Finset.univ.erase i : Finset (Fin n)).orderIsoOfFin (by simp) k).property)).1

/-- The difference has exactly `n - 1` explicitly located, ordered, full-turn zeros. -/
theorem exists_crossDifference_ordered_roots_with_locations (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) :
    ∃ root : Fin (n - 1) → ℝ, StrictMono root ∧
      (∀ k, crossDifferenceRootLocation angles i j (crossDifferenceRootIndex i k) (root k)) ∧
      (∀ k, root k ∈ Set.Ico 0 (2 * Real.pi)) ∧
      (∀ k, sineInterpolant angles.angle (crossDifferenceCoefficient i j) (root k) = 0) := by
  classical
  obtain ⟨root, hmono, hloc, hbound, hroot⟩ :=
    exists_crossDifference_roots_on_erase angles i j hij
  let e := (Finset.univ.erase i : Finset (Fin n)).orderIsoOfFin (by simp :
    (Finset.univ.erase i : Finset (Fin n)).card = n - 1)
  refine ⟨fun k => root (e k), hmono.comp e.strictMono, ?_, fun k => hbound (e k),
    fun k => hroot (e k)⟩
  intro k
  exact hloc (e k)

lemma crossDifferencePolynomial_ne_zero (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) :
    interpolantPolynomial angles.angle (crossDifferenceCoefficient i j) ≠ 0 := by
  apply interpolantPolynomial_ne_zero_of_node angles.angle angles.phaseNodes_injective
    (fun k => ⟨angles.nonneg k, angles.lt_two_pi k⟩) (crossDifferenceCoefficient i j) i
  exact (crossDifferenceCoefficient_ne_zero_iff i j i hij.le).mpr ⟨le_rfl, hij⟩

/-- These actual roots saturate the circle bound, so all are simple and all zeros are listed. -/
theorem exists_crossDifference_saturated_roots_with_locations (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) :
    ∃ root : Fin (n - 1) → ℝ, StrictMono root ∧
      (∀ k, crossDifferenceRootLocation angles i j (crossDifferenceRootIndex i k) (root k)) ∧
      (∀ k, root k ∈ Set.Ico 0 (2 * Real.pi)) ∧
      (∀ k, sineInterpolant angles.angle (crossDifferenceCoefficient i j) (root k) = 0) ∧
      (∀ k, deriv (sineInterpolant angles.angle (crossDifferenceCoefficient i j))
        (root k) ≠ 0) ∧
      (∀ t ∈ Set.Ico 0 (2 * Real.pi),
        sineInterpolant angles.angle (crossDifferenceCoefficient i j) t = 0 ↔
          ∃ k, root k = t) := by
  obtain ⟨root, hmono, hloc, hbound, hroot⟩ :=
    exists_crossDifference_ordered_roots_with_locations angles i j hij
  have hP := crossDifferencePolynomial_ne_zero angles i j hij
  refine ⟨root, hmono, hloc, hbound, hroot, ?_, ?_⟩
  · exact deriv_sineInterpolant_ne_zero_of_saturated_roots angles.angle
      (crossDifferenceCoefficient i j) hP root hmono.injective hbound hroot
  · intro t ht
    constructor
    · intro hz
      exact cayley_chart_root_mem_of_saturated_roots (n - 1)
        (sineInterpolant angles.angle (crossDifferenceCoefficient i j))
        (interpolantPolynomial angles.angle (crossDifferenceCoefficient i j)) hP
        (interpolantPolynomial_natDegree_le _ _)
        (cos_pow_mul_interpolantPolynomial_eval_tan _ _)
        (interpolantPolynomial_coeff_top _ _) root hmono.injective hbound hroot t ht hz
    · rintro ⟨k, rfl⟩
      exact hroot k

end

end UnitCircleInterpolation
