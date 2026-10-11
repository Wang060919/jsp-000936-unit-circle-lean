/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.CrossGapRoots
import UnitCircleInterpolation.CrossSumRoots
import UnitCircleInterpolation.RootSigns
import UnitCircleInterpolation.CrossResidueAnchor
import UnitCircleInterpolation.CyclicMarkov
import UnitCircleInterpolation.CrossWronskian

/-! # Strict interlacing of the actual cross-gap difference and sum -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace UnitCircleInterpolation

noncomputable section

variable {n : ℕ} {hn : 0 < n}

/-- Deleting one nodal label shifts exactly the labels at or above the cut. -/
lemma erasedNodeIndex_val (cut : Fin n) (q : Fin (n - 1)) :
    (((Finset.univ.erase cut : Finset (Fin n)).orderIsoOfFin (by simp) q).val).val =
      if q.val < cut.val then q.val else q.val + 1 := by
  cases n with
  | zero => exact Fin.elim0 cut
  | succ m =>
    change ((Finset.univ.erase cut : Finset (Fin (m + 1))).orderEmbOfFin
      (by simp) q).val = _
    have he : (Finset.univ.erase cut : Finset (Fin (m + 1))) = {cut}ᶜ := by
      ext x
      simp
    simp only [he, Finset.orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb]
    change (cut.succAbove q).val = _
    by_cases h : q.val < cut.val
    · rw [if_pos h, Fin.succAbove_of_castSucc_lt cut q h]
      rfl
    · rw [if_neg h, Fin.succAbove_of_le_castSucc cut q (le_of_not_gt h)]
      rfl

lemma crossDifferenceRootIndex_val (i : Fin n) (q : Fin (n - 1)) :
    (crossDifferenceRootIndex i q).val =
      if q.val < i.val then q.val else q.val + 1 :=
  erasedNodeIndex_val i q

lemma crossSumRootIndex_val (j : Fin n) (q : Fin (n - 1)) :
    (crossSumRootIndex j q).val =
      if q.val < j.val then q.val else q.val + 1 :=
  erasedNodeIndex_val j q

/-- A difference zero assigned to a larger label is strictly after the smaller node. -/
lemma angle_lt_of_crossDifferenceRootLocation_of_lt (angles : CyclicAngles n hn)
    (i j k l : Fin n) (hkl : k < l) {t : ℝ}
    (ht : crossDifferenceRootLocation angles i j l t) : angles.angle k < t := by
  unfold crossDifferenceRootLocation at ht
  split_ifs at ht with hmiddle
  · exact (angles.strictMono.monotone (Nat.le_sub_one_of_lt hkl)).trans_lt ht.1
  · rw [ht]
    exact angles.strictMono hkl

/-- Every ordinary difference-root arc contains the next erased-label sum root. -/
theorem cross_roots_strictly_interlace_adjacent (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) (Droot Troot : Fin (n - 1) → ℝ)
    (hDloc : ∀ q, crossDifferenceRootLocation angles i j
      (crossDifferenceRootIndex i q) (Droot q))
    (hTloc : ∀ q, crossSumRootLocation angles i j
      (crossSumRootIndex j q) (Troot q))
    (q : Fin (n - 1)) (hqnext : q.val + 1 < n - 1) :
    Droot q < Troot ⟨q.val + 1, hqnext⟩ ∧
      Troot ⟨q.val + 1, hqnext⟩ < Droot ⟨q.val + 1, hqnext⟩ := by
  let s : Fin (n - 1) := ⟨q.val + 1, hqnext⟩
  let a := crossDifferenceRootIndex i q
  let b := crossDifferenceRootIndex i s
  let r := crossSumRootIndex j s
  have ha := crossDifferenceRootIndex_val i q
  have hb := crossDifferenceRootIndex_val i s
  have hr := crossSumRootIndex_val j s
  change a.val = _ at ha
  change b.val = if q.val + 1 < i.val then q.val + 1 else q.val + 1 + 1 at hb
  change r.val = if q.val + 1 < j.val then q.val + 1 else q.val + 1 + 1 at hr
  have hDa := hDloc q
  have hDb := hDloc s
  have hTr := hTloc s
  change crossDifferenceRootLocation angles i j a (Droot q) at hDa
  change crossDifferenceRootLocation angles i j b (Droot s) at hDb
  change crossSumRootLocation angles i j r (Troot s) at hTr
  have hijval : i.val < j.val := hij
  change Droot q < Troot s ∧ Troot s < Droot s
  by_cases hqi : q.val < i.val
  · rw [if_pos hqi] at ha
    by_cases hsi : q.val + 1 < i.val
    · rw [if_pos hsi] at hb
      have hsj : q.val + 1 < j.val := by omega
      rw [if_pos hsj] at hr
      have hAmiddle : ¬(i < a ∧ a < j) := by
        change ¬(i.val < a.val ∧ a.val < j.val); omega
      have hBmiddle : ¬(i < b ∧ b < j) := by
        change ¬(i.val < b.val ∧ b.val < j.val); omega
      have hRmiddle : ¬(i ≤ r ∧ r < j) := by
        change ¬(i.val ≤ r.val ∧ r.val < j.val); omega
      have hRzero : r.val ≠ 0 := by omega
      simp only [crossDifferenceRootLocation, if_neg hAmiddle] at hDa
      simp only [crossDifferenceRootLocation, if_neg hBmiddle] at hDb
      simp only [crossSumRootLocation, if_neg hRmiddle, if_neg hRzero] at hTr
      have hpred : gapPredecessor r = a := by
        apply Fin.ext
        change r.val - 1 = a.val
        omega
      have hrb : r = b := Fin.ext (by omega)
      rw [hpred] at hTr
      constructor
      · rw [hDa]
        exact hTr.1
      · rw [hDb]
        simpa only [hrb] using hTr.2
    · rw [if_neg hsi] at hb
      have hsj : q.val + 1 < j.val := by omega
      rw [if_pos hsj] at hr
      have hAmiddle : ¬(i < a ∧ a < j) := by
        change ¬(i.val < a.val ∧ a.val < j.val); omega
      have hRmiddle : i ≤ r ∧ r < j := by
        change i.val ≤ r.val ∧ r.val < j.val; omega
      simp only [crossDifferenceRootLocation, if_neg hAmiddle] at hDa
      simp only [crossSumRootLocation, if_pos hRmiddle] at hTr
      constructor
      · rw [hDa, hTr]
        exact angles.strictMono (show a < r from by change a.val < r.val; omega)
      · rw [hTr]
        exact angle_lt_of_crossDifferenceRootLocation_of_lt angles i j r b
          (by change r.val < b.val; omega) hDb
  · rw [if_neg hqi] at ha
    have hsi : ¬q.val + 1 < i.val := by omega
    rw [if_neg hsi] at hb
    by_cases hsj : q.val + 1 < j.val
    · rw [if_pos hsj] at hr
      have hAmiddle : i < a ∧ a < j := by
        change i.val < a.val ∧ a.val < j.val; omega
      have hRmiddle : i ≤ r ∧ r < j := by
        change i.val ≤ r.val ∧ r.val < j.val; omega
      simp only [crossDifferenceRootLocation, if_pos hAmiddle] at hDa
      simp only [crossSumRootLocation, if_pos hRmiddle] at hTr
      have har : a = r := Fin.ext (by omega)
      constructor
      · rw [hTr]
        simpa only [har] using hDa.2
      · rw [hTr]
        exact angle_lt_of_crossDifferenceRootLocation_of_lt angles i j r b
          (by change r.val < b.val; omega) hDb
    · rw [if_neg hsj] at hr
      have hAmiddle : ¬(i < a ∧ a < j) := by
        change ¬(i.val < a.val ∧ a.val < j.val); omega
      have hBmiddle : ¬(i < b ∧ b < j) := by
        change ¬(i.val < b.val ∧ b.val < j.val); omega
      have hRmiddle : ¬(i ≤ r ∧ r < j) := by
        change ¬(i.val ≤ r.val ∧ r.val < j.val); omega
      have hRzero : r.val ≠ 0 := by omega
      simp only [crossDifferenceRootLocation, if_neg hAmiddle] at hDa
      simp only [crossDifferenceRootLocation, if_neg hBmiddle] at hDb
      simp only [crossSumRootLocation, if_neg hRmiddle, if_neg hRzero] at hTr
      have hpred : gapPredecessor r = a := by
        apply Fin.ext
        change r.val - 1 = a.val
        omega
      have hrb : r = b := Fin.ext (by omega)
      rw [hpred] at hTr
      constructor
      · rw [hDa]
        exact hTr.1
      · rw [hDb]
        simpa only [hrb] using hTr.2

/-- The first erased-label sum root lies on one side of the entire ordinary chain. -/
lemma crossSum_first_root_outside_difference_span (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) (hm : 0 < n - 1)
    (Droot Troot : Fin (n - 1) → ℝ)
    (hDloc : ∀ q, crossDifferenceRootLocation angles i j
      (crossDifferenceRootIndex i q) (Droot q))
    (hTloc : ∀ q, crossSumRootLocation angles i j
      (crossSumRootIndex j q) (Troot q)) :
    (∀ q, Troot ⟨0, hm⟩ < Droot q) ∨ (∀ q, Droot q < Troot ⟨0, hm⟩) := by
  let first : Fin (n - 1) := ⟨0, hm⟩
  let zero : Fin n := ⟨0, hn⟩
  have hjpos : 0 < j.val := by have h := hij; change i.val < j.val at h; omega
  have hindex : crossSumRootIndex j first = zero := by
    apply Fin.ext
    have h := crossSumRootIndex_val j first
    simpa only [first, zero, if_pos hjpos] using h
  have hT := hTloc first
  rw [hindex] at hT
  by_cases hi : i.val = 0
  · have hmiddle : i ≤ zero ∧ zero < j := by
      change i.val ≤ 0 ∧ 0 < j.val
      omega
    simp only [crossSumRootLocation, if_pos hmiddle] at hT
    left
    intro q
    have hDindex : zero < crossDifferenceRootIndex i q := by
      have h := crossDifferenceRootIndex_val i q
      have hnot : ¬q.val < i.val := by omega
      rw [if_neg hnot] at h
      change 0 < (crossDifferenceRootIndex i q).val
      omega
    rw [hT]
    exact angle_lt_of_crossDifferenceRootLocation_of_lt angles i j zero
      (crossDifferenceRootIndex i q) hDindex (hDloc q)
  · have hmiddle : ¬(i ≤ zero ∧ zero < j) := by
      change ¬(i.val ≤ 0 ∧ 0 < j.val)
      omega
    simp only [crossSumRootLocation, if_neg hmiddle, zero] at hT
    right
    intro q
    have hupper := crossDifferenceRootLocation_le_angle angles i j
      (crossDifferenceRootIndex i q) (hDloc q)
    have hlast : crossDifferenceRootIndex i q ≤ lastNodeIndex hn :=
      Nat.le_sub_one_of_lt (crossDifferenceRootIndex i q).isLt
    exact (hupper.trans (angles.strictMono.monotone hlast)).trans_lt hT.1

/-- Ordinary adjacent interlacing excludes every other sum root, including the wrap root. -/
lemma interlacing_root_index_of_mem_adjacent_closed {m : ℕ} (hm : 0 < m)
    (Droot Troot : Fin m → ℝ) (hmono : StrictMono Droot)
    (hfirst : (∀ q, Troot ⟨0, hm⟩ < Droot q) ∨
      (∀ q, Droot q < Troot ⟨0, hm⟩))
    (hinter : ∀ q (hq : q.val + 1 < m), Droot q < Troot ⟨q.val + 1, hq⟩ ∧
      Troot ⟨q.val + 1, hq⟩ < Droot ⟨q.val + 1, hq⟩)
    (q : Fin m) (hq : q.val + 1 < m) (l : Fin m)
    (hl : Troot l ∈ Set.Icc (Droot q) (Droot ⟨q.val + 1, hq⟩)) :
    l = ⟨q.val + 1, hq⟩ := by
  by_cases hlzero : l.val = 0
  · have heq : l = ⟨0, hm⟩ := Fin.ext hlzero
    rw [heq] at hl
    rcases hfirst with hfirst | hfirst
    · exact False.elim ((not_lt_of_ge hl.1) (hfirst q))
    · exact False.elim ((not_lt_of_ge hl.2) (hfirst ⟨q.val + 1, hq⟩))
  · let p : Fin m := ⟨l.val - 1, by omega⟩
    have hpnext : p.val + 1 < m := by dsimp [p]; omega
    have hpl : (⟨p.val + 1, hpnext⟩ : Fin m) = l := by
      apply Fin.ext
      dsimp [p]
      omega
    have hinterl := hinter p hpnext
    rw [hpl] at hinterl
    by_cases hlq : l ≤ q
    · have hupper := hinterl.2.trans_le (hmono.monotone hlq)
      exact False.elim ((not_lt_of_ge hl.1) hupper)
    · by_contra hne
      have hqp : (⟨q.val + 1, hq⟩ : Fin m) ≤ p := by
        have hneval : l.val ≠ q.val + 1 := fun h => hne (Fin.ext h)
        change q.val + 1 ≤ l.val - 1
        change ¬l.val ≤ q.val at hlq
        omega
      have hlower := (hmono.monotone hqp).trans_lt hinterl.1
      exact (not_lt_of_ge hl.2) hlower

/-- Exhaustion and ordering remove every difference zero from an ordinary root arc. -/
lemma difference_no_zero_on_adjacent_arc (angles : CyclicAngles n hn)
    (i j : Fin n) (Droot : Fin (n - 1) → ℝ) (hmono : StrictMono Droot)
    (hbound : ∀ q, Droot q ∈ Set.Ico 0 (2 * Real.pi))
    (hexhaust : ∀ t ∈ Set.Ico 0 (2 * Real.pi),
      sineInterpolant angles.angle (crossDifferenceCoefficient i j) t = 0 ↔
        ∃ q, Droot q = t)
    (q : Fin (n - 1)) (hq : q.val + 1 < n - 1) :
    ∀ t ∈ Set.Ioo (Droot q) (Droot ⟨q.val + 1, hq⟩),
      sineInterpolant angles.angle (crossDifferenceCoefficient i j) t ≠ 0 := by
  intro t ht hz
  have htbound : t ∈ Set.Ico 0 (2 * Real.pi) :=
    ⟨(hbound q).1.trans ht.1.le, ht.2.trans (hbound ⟨q.val + 1, hq⟩).2⟩
  obtain ⟨l, hl⟩ := (hexhaust t htbound).mp hz
  by_cases hlq : l ≤ q
  · have hupper := hmono.monotone hlq
    rw [hl] at hupper
    exact (not_lt_of_ge hupper) ht.1
  · have hql : (⟨q.val + 1, hq⟩ : Fin (n - 1)) ≤ l := by
      change q.val + 1 ≤ l.val
      change ¬l.val ≤ q.val at hlq
      omega
    have hlower := hmono.monotone hql
    rw [hl] at hlower
    exact (not_lt_of_ge hlower) ht.2

/-- The actual sum has no other zeros on the closed interval around its interlacing root. -/
lemma crossSum_no_other_zero_on_adjacent_arc (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) (hm : 0 < n - 1)
    (Droot Troot : Fin (n - 1) → ℝ) (hmono : StrictMono Droot)
    (hDloc : ∀ q, crossDifferenceRootLocation angles i j
      (crossDifferenceRootIndex i q) (Droot q))
    (hTloc : ∀ q, crossSumRootLocation angles i j
      (crossSumRootIndex j q) (Troot q))
    (hDbound : ∀ q, Droot q ∈ Set.Ico 0 (2 * Real.pi))
    (hTexhaust : ∀ t ∈ Set.Ico 0 (2 * Real.pi),
      sineInterpolant angles.angle (crossSumCoefficient i j) t = 0 ↔
        ∃ q, Troot q = t)
    (q : Fin (n - 1)) (hq : q.val + 1 < n - 1) :
    ∀ t ∈ Set.Icc (Droot q) (Droot ⟨q.val + 1, hq⟩),
      t ≠ Troot ⟨q.val + 1, hq⟩ →
        sineInterpolant angles.angle (crossSumCoefficient i j) t ≠ 0 := by
  intro t ht hne hz
  have htbound : t ∈ Set.Ico 0 (2 * Real.pi) :=
    ⟨(hDbound q).1.trans ht.1, ht.2.trans_lt (hDbound ⟨q.val + 1, hq⟩).2⟩
  obtain ⟨l, hl⟩ := (hTexhaust t htbound).mp hz
  have hlmem : Troot l ∈ Set.Icc (Droot q) (Droot ⟨q.val + 1, hq⟩) := by
    rwa [hl]
  have hleq := interlacing_root_index_of_mem_adjacent_closed hm Droot Troot hmono
    (crossSum_first_root_outside_difference_span angles i j hij hm Droot Troot hDloc hTloc)
    (cross_roots_strictly_interlace_adjacent angles i j hij Droot Troot hDloc hTloc)
    q hq l hlmem
  exact hne (hl.symm.trans (congrArg Troot hleq))

/-- Actual strict interlacing transports the proved anchor to every saturated difference root. -/
theorem exists_crossDifference_positive_root_residues (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) :
    ∃ root : Fin (n - 1) → ℝ, Function.Injective root ∧
      (∀ q, root q ∈ Set.Ico 0 (2 * Real.pi)) ∧
      (∀ q, sineInterpolant angles.angle (crossDifferenceCoefficient i j) (root q) = 0) ∧
      (∀ q, 0 < sineInterpolant angles.angle (crossSumCoefficient i j) (root q) *
        deriv (sineInterpolant angles.angle (crossDifferenceCoefficient i j)) (root q)) := by
  obtain ⟨Droot, hmono, hDloc, hDbound, hDroot, hDsimple, hDexhaust⟩ :=
    exists_crossDifference_saturated_roots_with_locations angles i j hij
  obtain ⟨Troot, _hTinj, hTloc, _hTbound, hTroot, hTsimple, hTexhaust⟩ :=
    exists_crossSum_saturated_roots_with_locations angles i j hij
  have hm : 0 < n - 1 := by
    have h := hij
    change i.val < j.val at h
    have hj := j.isLt
    omega
  obtain ⟨anchor, _hanchoreq, hanchor⟩ := crossResidueAnchor_in_root_list angles i j hij
    Droot hmono.injective hDbound hDroot
  refine ⟨Droot, hmono.injective, hDbound, hDroot, ?_⟩
  apply finite_chain_positive_of_adjacent_iff
    (fun q => sineInterpolant angles.angle (crossSumCoefficient i j) (Droot q) *
      deriv (sineInterpolant angles.angle (crossDifferenceCoefficient i j)) (Droot q))
    ?_ anchor hanchor
  intro q l hsucc
  have hqnext : q.val + 1 < n - 1 := by rw [hsucc]; exact l.isLt
  have hleq : l = ⟨q.val + 1, hqnext⟩ := Fin.ext hsucc.symm
  rw [hleq]
  obtain ⟨har, hrb⟩ := cross_roots_strictly_interlace_adjacent angles i j hij
    Droot Troot hDloc hTloc q hqnext
  have hTnoother := crossSum_no_other_zero_on_adjacent_arc angles i j hij hm
    Droot Troot hmono hDloc hTloc hDbound hTexhaust q hqnext
  apply positive_residue_iff_across_interlacing
    (sineInterpolant angles.angle (crossDifferenceCoefficient i j))
    (sineInterpolant angles.angle (crossSumCoefficient i j)) har hrb
    (continuous_sineInterpolant _ _) (continuous_sineInterpolant _ _)
    (hDroot q) (hDroot ⟨q.val + 1, hqnext⟩)
    ((differentiable_sineInterpolant _ _ (Droot q)).hasDerivAt)
    ((differentiable_sineInterpolant _ _ (Droot ⟨q.val + 1, hqnext⟩)).hasDerivAt)
    (hDsimple q) (hDsimple ⟨q.val + 1, hqnext⟩)
    (difference_no_zero_on_adjacent_arc angles i j Droot hmono hDbound hDexhaust q hqnext)
    (hTroot ⟨q.val + 1, hqnext⟩)
    ((differentiable_sineInterpolant _ _ (Troot ⟨q.val + 1, hqnext⟩)).hasDerivAt)
    (hTsimple ⟨q.val + 1, hqnext⟩)
  · intro t ht
    exact hTnoother t ⟨ht.1, ht.2.le.trans hrb.le⟩ (ne_of_lt ht.2)
  · intro t ht
    exact hTnoother t ⟨har.le.trans ht.1.le, ht.2⟩ (ne_of_gt ht.1)

/-- The literal cross-gap difference/sum Wronskian is strictly negative at every real angle. -/
theorem crossGap_sineWronskian_neg (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) (t : ℝ) :
    sineWronskian angles.angle (crossDifferenceCoefficient i j)
      (crossSumCoefficient i j) t < 0 := by
  have hsize : 2 ≤ n := by
    have h := hij
    change i.val < j.val at h
    have hj := j.isLt
    omega
  obtain ⟨root, hinj, hbound, hroot, hresidue⟩ :=
    exists_crossDifference_positive_root_residues angles i j hij
  exact sineWronskian_neg_of_cyclic_root_residues hsize angles.angle
    (crossDifferenceCoefficient i j) (crossSumCoefficient i j)
    root hinj hbound hroot hresidue t

/-- The phase-oriented Wronskian for the literal gap coefficients is globally negative. -/
theorem crossGap_phase_sineWronskian_neg (angles : CyclicAngles n hn)
    (i j : Fin n) (hij : i < j) (t : ℝ) :
    crossGapPhase i j * sineWronskian angles.angle (gapCoefficient i) (gapCoefficient j) t < 0 :=
  (crossWronskian_neg_iff angles.angle i j t).mp
    (crossGap_sineWronskian_neg angles i j hij t)

end

end UnitCircleInterpolation
