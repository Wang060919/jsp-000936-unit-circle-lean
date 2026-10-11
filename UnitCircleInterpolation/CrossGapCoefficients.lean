/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.GapSigns

/-!
# Coefficients of differences and sums across two gap cuts

These results use `gapCoefficient` literally, including its translated-wrap
interpretation at cut zero. They do not use `cyclicGapCoefficient`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ} {hn : 0 < n}

private lemma gapIndexSign_consecutive_cuts {i j k : Fin n}
    (hij : i.val + 1 = j.val) (hki : k ≠ i) :
    gapIndexSign j k = gapIndexSign i k := by
  have hkval : k.val ≠ i.val := fun h => hki (Fin.ext h)
  have hside : k < j ↔ k < i := by
    change k.val < j.val ↔ k.val < i.val
    omega
  simp only [gapIndexSign, hside]

/-- Moving the cut one step flips every coefficient except at the crossed node. -/
theorem gapCoefficient_consecutive_cuts (i j k : Fin n)
    (hij : i.val + 1 = j.val) :
    gapCoefficient j k = if k = i then gapCoefficient i k else -gapCoefficient i k := by
  by_cases hki : k = i
  · rw [if_pos hki]
    unfold gapCoefficient
    apply Finset.prod_congr rfl
    intro l hl
    rw [gapIndexSign_consecutive_cuts hij]
    simpa [hki] using (Finset.mem_erase.mp hl).1
  · rw [if_neg hki]
    let P : ℝ := ∏ l ∈ (Finset.univ.erase k).erase i,
      gapIndexSign i l * nodeIndexSign k l
    have hprod : (∏ l ∈ (Finset.univ.erase k).erase i,
        gapIndexSign j l * nodeIndexSign k l) = P := by
      apply Finset.prod_congr rfl
      intro l hl
      rw [gapIndexSign_consecutive_cuts hij (Finset.mem_erase.mp hl).1]
    have hmem : i ∈ (Finset.univ.erase k : Finset (Fin n)) :=
      Finset.mem_erase.mpr ⟨Ne.symm hki, Finset.mem_univ i⟩
    have hi : gapCoefficient i k = -nodeIndexSign k i * P := by
      unfold gapCoefficient
      rw [← Finset.mul_prod_erase (Finset.univ.erase k)
        (fun l => gapIndexSign i l * nodeIndexSign k l) hmem]
      simp only [gapIndexSign, lt_self_iff_false, if_false]
      change (-1 * nodeIndexSign k i) * P = -nodeIndexSign k i * P
      ring
    have hj : gapCoefficient j k = nodeIndexSign k i * P := by
      unfold gapCoefficient
      rw [← Finset.mul_prod_erase (Finset.univ.erase k)
        (fun l => gapIndexSign j l * nodeIndexSign k l) hmem, hprod]
      have hlt : i < j := by change i.val < j.val; omega
      simp [gapIndexSign, hlt]
    rw [hi, hj]
    ring

/-- Including the sign of the omitted factor makes cut transport uniformly alternating. -/
theorem gapCoefficient_signed_consecutive_cuts (i j k : Fin n)
    (hij : i.val + 1 = j.val) :
    gapIndexSign j k * gapCoefficient j k =
      -(gapIndexSign i k * gapCoefficient i k) := by
  rw [gapCoefficient_consecutive_cuts i j k hij]
  by_cases hki : k = i
  · rw [if_pos hki]
    have hlt : i < j := by change i.val < j.val; omega
    simp [hki, gapIndexSign, hlt]
  · rw [if_neg hki, gapIndexSign_consecutive_cuts hij hki]
    ring

/-- The phase associated with the number of cut steps from `i` to `j`. -/
def crossGapPhase (i j : Fin n) : ℝ := (-1 : ℝ) ^ (j.val - i.val)

lemma crossGapPhase_mul_self (i j : Fin n) :
    crossGapPhase i j * crossGapPhase i j = 1 := by
  unfold crossGapPhase
  rw [← mul_pow]
  norm_num

lemma crossGapPhase_ne_zero (i j : Fin n) : crossGapPhase i j ≠ 0 := by
  unfold crossGapPhase
  exact pow_ne_zero _ (by norm_num)

/-- Exact transport of the signed coefficient between arbitrary ordered cuts. -/
theorem gapCoefficient_signed_between_cuts (i j k : Fin n) (hij : i ≤ j) :
    gapIndexSign j k * gapCoefficient j k =
      crossGapPhase i j * (gapIndexSign i k * gapCoefficient i k) := by
  have haux : ∀ d : ℕ, ∀ j : Fin n, j.val = i.val + d →
      gapIndexSign j k * gapCoefficient j k =
        (-1 : ℝ) ^ d * (gapIndexSign i k * gapCoefficient i k) := by
    intro d
    induction d with
    | zero =>
      intro j hj
      have hji : j = i := Fin.ext (by omega)
      simp [hji]
    | succ d ih =>
      intro j hj
      let l : Fin n := ⟨j.val - 1, (Nat.sub_le _ _).trans_lt j.isLt⟩
      have hl : l.val = i.val + d := by dsimp [l]; omega
      have hlj : l.val + 1 = j.val := by dsimp [l]; omega
      rw [gapCoefficient_signed_consecutive_cuts l j k hlj, ih l hl, pow_succ]
      ring
  simpa only [crossGapPhase] using haux (j.val - i.val) j (by
    have hval : i.val ≤ j.val := hij
    omega)

/-- Outside the half-open interval of cuts, both coefficients differ by the phase alone. -/
theorem gapCoefficient_between_cuts_outside (i j k : Fin n) (hij : i ≤ j)
    (hk : k < i ∨ j ≤ k) :
    gapCoefficient j k = crossGapPhase i j * gapCoefficient i k := by
  have h := gapCoefficient_signed_between_cuts i j k hij
  rcases hk with hki | hjk
  · have hkj : k < j := hki.trans_le hij
    simpa [gapIndexSign, hki, hkj] using h
  · have hki : ¬k < i := not_lt.mpr (hij.trans hjk)
    have hkj : ¬k < j := not_lt.mpr hjk
    simp only [gapIndexSign, if_neg hki, if_neg hkj, neg_one_mul, mul_neg] at h
    exact neg_injective h

/-- Between the two cuts, omitting a crossed factor supplies one additional minus sign. -/
theorem gapCoefficient_between_cuts_inside (i j k : Fin n) (hij : i ≤ j)
    (hik : i ≤ k) (hkj : k < j) :
    gapCoefficient j k = -crossGapPhase i j * gapCoefficient i k := by
  have h := gapCoefficient_signed_between_cuts i j k hij
  have hki : ¬k < i := not_lt.mpr hik
  simpa [gapIndexSign, hki, hkj, neg_mul, mul_neg] using h

/-- A single piecewise form of the literal two-cut coefficient identity. -/
theorem gapCoefficient_between_cuts (i j k : Fin n) (hij : i ≤ j) :
    gapCoefficient j k =
      if i ≤ k ∧ k < j then -crossGapPhase i j * gapCoefficient i k
      else crossGapPhase i j * gapCoefficient i k := by
  by_cases hk : i ≤ k ∧ k < j
  · rw [if_pos hk]
    exact gapCoefficient_between_cuts_inside i j k hij hk.1 hk.2
  · rw [if_neg hk]
    apply gapCoefficient_between_cuts_outside i j k hij
    by_cases hki : k < i
    · exact Or.inl hki
    · exact Or.inr (le_of_not_gt (fun hkj => hk ⟨le_of_not_gt hki, hkj⟩))

/-- Literal coefficients of the difference of the two phase-aligned interpolants. -/
def crossDifferenceCoefficient (i j k : Fin n) : ℝ :=
  gapCoefficient i k - crossGapPhase i j * gapCoefficient j k

/-- Literal coefficients of the sum of the two phase-aligned interpolants. -/
def crossSumCoefficient (i j k : Fin n) : ℝ :=
  gapCoefficient i k + crossGapPhase i j * gapCoefficient j k

theorem crossDifferenceCoefficient_inside (i j k : Fin n) (hij : i ≤ j)
    (hik : i ≤ k) (hkj : k < j) :
    crossDifferenceCoefficient i j k = 2 * gapCoefficient i k := by
  unfold crossDifferenceCoefficient
  rw [gapCoefficient_between_cuts_inside i j k hij hik hkj]
  calc
    gapCoefficient i k - crossGapPhase i j *
        (-crossGapPhase i j * gapCoefficient i k) =
      gapCoefficient i k +
        (crossGapPhase i j * crossGapPhase i j) * gapCoefficient i k := by ring
    _ = 2 * gapCoefficient i k := by rw [crossGapPhase_mul_self]; ring

theorem crossDifferenceCoefficient_outside (i j k : Fin n) (hij : i ≤ j)
    (hk : k < i ∨ j ≤ k) : crossDifferenceCoefficient i j k = 0 := by
  unfold crossDifferenceCoefficient
  rw [gapCoefficient_between_cuts_outside i j k hij hk, ← mul_assoc,
    crossGapPhase_mul_self, one_mul, sub_self]

theorem crossSumCoefficient_inside (i j k : Fin n) (hij : i ≤ j)
    (hik : i ≤ k) (hkj : k < j) : crossSumCoefficient i j k = 0 := by
  unfold crossSumCoefficient
  rw [gapCoefficient_between_cuts_inside i j k hij hik hkj]
  calc
    gapCoefficient i k + crossGapPhase i j *
        (-crossGapPhase i j * gapCoefficient i k) =
      gapCoefficient i k -
        (crossGapPhase i j * crossGapPhase i j) * gapCoefficient i k := by ring
    _ = 0 := by rw [crossGapPhase_mul_self, one_mul, sub_self]

theorem crossSumCoefficient_outside (i j k : Fin n) (hij : i ≤ j)
    (hk : k < i ∨ j ≤ k) :
    crossSumCoefficient i j k = 2 * gapCoefficient i k := by
  unfold crossSumCoefficient
  rw [gapCoefficient_between_cuts_outside i j k hij hk, ← mul_assoc,
    crossGapPhase_mul_self, one_mul]
  ring

/-- Every original gap coefficient is nonzero, with no condition on its cut. -/
lemma gapCoefficient_ne_zero (cut k : Fin n) : gapCoefficient cut k ≠ 0 := by
  intro hzero
  have h := abs_gapCoefficient cut k
  rw [hzero, abs_zero] at h
  norm_num at h

theorem crossDifferenceCoefficient_eq (i j k : Fin n) (hij : i ≤ j) :
    crossDifferenceCoefficient i j k =
      if i ≤ k ∧ k < j then 2 * gapCoefficient i k else 0 := by
  by_cases hk : i ≤ k ∧ k < j
  · rw [if_pos hk]
    exact crossDifferenceCoefficient_inside i j k hij hk.1 hk.2
  · rw [if_neg hk]
    apply crossDifferenceCoefficient_outside i j k hij
    by_cases hki : k < i
    · exact Or.inl hki
    · exact Or.inr (le_of_not_gt (fun hkj => hk ⟨le_of_not_gt hki, hkj⟩))

theorem crossSumCoefficient_eq (i j k : Fin n) (hij : i ≤ j) :
    crossSumCoefficient i j k =
      if i ≤ k ∧ k < j then 0 else 2 * gapCoefficient i k := by
  by_cases hk : i ≤ k ∧ k < j
  · rw [if_pos hk]
    exact crossSumCoefficient_inside i j k hij hk.1 hk.2
  · rw [if_neg hk]
    apply crossSumCoefficient_outside i j k hij
    by_cases hki : k < i
    · exact Or.inl hki
    · exact Or.inr (le_of_not_gt (fun hkj => hk ⟨le_of_not_gt hki, hkj⟩))

/-- The difference is supported exactly on the half-open block between the cuts. -/
theorem crossDifferenceCoefficient_ne_zero_iff (i j k : Fin n) (hij : i ≤ j) :
    crossDifferenceCoefficient i j k ≠ 0 ↔ i ≤ k ∧ k < j := by
  rw [crossDifferenceCoefficient_eq i j k hij]
  by_cases hk : i ≤ k ∧ k < j
  · simp [hk, gapCoefficient_ne_zero]
  · simp [hk]

/-- The sum is supported exactly on the complementary two nodal blocks. -/
theorem crossSumCoefficient_ne_zero_iff (i j k : Fin n) (hij : i ≤ j) :
    crossSumCoefficient i j k ≠ 0 ↔ k < i ∨ j ≤ k := by
  rw [crossSumCoefficient_eq i j k hij]
  by_cases hk : i ≤ k ∧ k < j
  · have houtside : ¬(k < i ∨ j ≤ k) := by
      change ¬(k.val < i.val ∨ j.val ≤ k.val)
      have hik : i.val ≤ k.val := hk.1
      have hkj : k.val < j.val := hk.2
      omega
    simp [hk, houtside]
  · have houtside : k < i ∨ j ≤ k := by
      by_cases hki : k < i
      · exact Or.inl hki
      · exact Or.inr (le_of_not_gt (fun hkj => hk ⟨le_of_not_gt hki, hkj⟩))
    simp [hk, houtside, gapCoefficient_ne_zero]

theorem abs_crossDifferenceCoefficient_inside (i j k : Fin n) (hij : i ≤ j)
    (hik : i ≤ k) (hkj : k < j) : |crossDifferenceCoefficient i j k| = 2 := by
  rw [crossDifferenceCoefficient_inside i j k hij hik hkj, abs_mul,
    abs_gapCoefficient, mul_one]
  norm_num

theorem abs_crossSumCoefficient_outside (i j k : Fin n) (hij : i ≤ j)
    (hk : k < i ∨ j ≤ k) : |crossSumCoefficient i j k| = 2 := by
  rw [crossSumCoefficient_outside i j k hij hk, abs_mul,
    abs_gapCoefficient, mul_one]
  norm_num

/-- The interpolant here is the literal difference, without replacing its cardinal sum. -/
theorem crossDifferenceInterpolant_identity (θ : Fin n → ℝ) (i j : Fin n) (t : ℝ) :
    sineInterpolant θ (crossDifferenceCoefficient i j) t =
      sineInterpolant θ (gapCoefficient i) t -
        crossGapPhase i j * sineInterpolant θ (gapCoefficient j) t := by
  unfold sineInterpolant crossDifferenceCoefficient
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The interpolant here is the literal sum of the phase-aligned gap interpolants. -/
theorem crossSumInterpolant_identity (θ : Fin n → ℝ) (i j : Fin n) (t : ℝ) :
    sineInterpolant θ (crossSumCoefficient i j) t =
      sineInterpolant θ (gapCoefficient i) t +
        crossGapPhase i j * sineInterpolant θ (gapCoefficient j) t := by
  unfold sineInterpolant crossSumCoefficient
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma crossDifferenceInterpolant_at_node (angles : CyclicAngles n hn) (i j k : Fin n) :
    sineInterpolant angles.angle (crossDifferenceCoefficient i j) (angles.angle k) =
      crossDifferenceCoefficient i j k :=
  sineInterpolant_at_node angles.angle angles.phaseNodes_injective
    (crossDifferenceCoefficient i j) k

lemma crossSumInterpolant_at_node (angles : CyclicAngles n hn) (i j k : Fin n) :
    sineInterpolant angles.angle (crossSumCoefficient i j) (angles.angle k) =
      crossSumCoefficient i j k :=
  sineInterpolant_at_node angles.angle angles.phaseNodes_injective
    (crossSumCoefficient i j) k

theorem crossDifferenceInterpolant_at_node_inside (angles : CyclicAngles n hn)
    (i j k : Fin n) (hij : i ≤ j) (hik : i ≤ k) (hkj : k < j) :
    sineInterpolant angles.angle (crossDifferenceCoefficient i j) (angles.angle k) =
      2 * gapCoefficient i k := by
  rw [crossDifferenceInterpolant_at_node,
    crossDifferenceCoefficient_inside i j k hij hik hkj]

theorem crossDifferenceInterpolant_at_node_outside (angles : CyclicAngles n hn)
    (i j k : Fin n) (hij : i ≤ j) (hk : k < i ∨ j ≤ k) :
    sineInterpolant angles.angle (crossDifferenceCoefficient i j) (angles.angle k) = 0 := by
  rw [crossDifferenceInterpolant_at_node,
    crossDifferenceCoefficient_outside i j k hij hk]

theorem crossSumInterpolant_at_node_inside (angles : CyclicAngles n hn)
    (i j k : Fin n) (hij : i ≤ j) (hik : i ≤ k) (hkj : k < j) :
    sineInterpolant angles.angle (crossSumCoefficient i j) (angles.angle k) = 0 := by
  rw [crossSumInterpolant_at_node, crossSumCoefficient_inside i j k hij hik hkj]

theorem crossSumInterpolant_at_node_outside (angles : CyclicAngles n hn)
    (i j k : Fin n) (hij : i ≤ j) (hk : k < i ∨ j ≤ k) :
    sineInterpolant angles.angle (crossSumCoefficient i j) (angles.angle k) =
      2 * gapCoefficient i k := by
  rw [crossSumInterpolant_at_node, crossSumCoefficient_outside i j k hij hk]

theorem crossDifferenceInterpolant_at_node_ne_zero_iff (angles : CyclicAngles n hn)
    (i j k : Fin n) (hij : i ≤ j) :
    sineInterpolant angles.angle (crossDifferenceCoefficient i j) (angles.angle k) ≠ 0 ↔
      i ≤ k ∧ k < j := by
  rw [crossDifferenceInterpolant_at_node]
  exact crossDifferenceCoefficient_ne_zero_iff i j k hij

theorem crossSumInterpolant_at_node_ne_zero_iff (angles : CyclicAngles n hn)
    (i j k : Fin n) (hij : i ≤ j) :
    sineInterpolant angles.angle (crossSumCoefficient i j) (angles.angle k) ≠ 0 ↔
      k < i ∨ j ≤ k := by
  rw [crossSumInterpolant_at_node]
  exact crossSumCoefficient_ne_zero_iff i j k hij

/-- Consecutive indices in the nonzero difference block have opposite coefficients. -/
theorem crossDifferenceCoefficient_consecutive_flip (i j k l : Fin n)
    (hij : i ≤ j) (hkl : k.val + 1 = l.val) (hik : i ≤ k) (hlj : l < j) :
    crossDifferenceCoefficient i j l = -crossDifferenceCoefficient i j k := by
  have hkl_lt : k < l := by change k.val < l.val; omega
  have hil : i ≤ l := hik.trans hkl_lt.le
  have hkj : k < j := hkl_lt.trans hlj
  have hli : l ≠ i := ne_of_gt (hik.trans_lt hkl_lt)
  rw [crossDifferenceCoefficient_inside i j l hij hil hlj,
    crossDifferenceCoefficient_inside i j k hij hik hkj,
    gapCoefficient_consecutive_flip i k l hkl hli]
  ring

/-- On either complementary block, consecutive nonzero sum coefficients alternate. -/
theorem crossSumCoefficient_consecutive_flip (i j k l : Fin n)
    (hij : i < j) (hkl : k.val + 1 = l.val)
    (hk : k < i ∨ j ≤ k) (hl : l < i ∨ j ≤ l) :
    crossSumCoefficient i j l = -crossSumCoefficient i j k := by
  have hli : l ≠ i := by
    intro hli
    rcases hl with hl | hl
    · exact (lt_irrefl i) (hli ▸ hl)
    · exact (not_le_of_gt hij) (hli ▸ hl)
  rw [crossSumCoefficient_outside i j l hij.le hl,
    crossSumCoefficient_outside i j k hij.le hk,
    gapCoefficient_consecutive_flip i k l hkl hli]
  ring

theorem crossDifferenceInterpolant_consecutive_flip (angles : CyclicAngles n hn)
    (i j k l : Fin n) (hij : i ≤ j) (hkl : k.val + 1 = l.val)
    (hik : i ≤ k) (hlj : l < j) :
    sineInterpolant angles.angle (crossDifferenceCoefficient i j) (angles.angle l) =
      -sineInterpolant angles.angle (crossDifferenceCoefficient i j) (angles.angle k) := by
  rw [crossDifferenceInterpolant_at_node, crossDifferenceInterpolant_at_node]
  exact crossDifferenceCoefficient_consecutive_flip i j k l hij hkl hik hlj

theorem crossSumInterpolant_consecutive_flip (angles : CyclicAngles n hn)
    (i j k l : Fin n) (hij : i < j) (hkl : k.val + 1 = l.val)
    (hk : k < i ∨ j ≤ k) (hl : l < i ∨ j ≤ l) :
    sineInterpolant angles.angle (crossSumCoefficient i j) (angles.angle l) =
      -sineInterpolant angles.angle (crossSumCoefficient i j) (angles.angle k) := by
  rw [crossSumInterpolant_at_node, crossSumInterpolant_at_node]
  exact crossSumCoefficient_consecutive_flip i j k l hij hkl hk hl

end

end UnitCircleInterpolation
