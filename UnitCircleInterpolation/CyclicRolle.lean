/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith

/-!
# Rolle points on a full half-open turn

The last arc joins the last root to the first root plus one turn. Its Rolle
point is reduced by one turn only when necessary. The construction includes
the one-root case, whose only arc has length one full turn.

The zero-shift hypotheses below are generic properties to be proved by the
actual periodic or antiperiodic function supplied by a caller.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {p : ℕ}

/-- The next lifted root, including the root beyond the last arc. -/
def cyclicRolleNext (hp : 0 < p) (root : Fin p → ℝ) (T : ℝ) (i : Fin p) : ℝ :=
  if h : i.val + 1 < p then root ⟨i.val + 1, h⟩ else root ⟨0, hp⟩ + T

/-- A Rolle point in the lifted turn needs at most one subtraction. -/
def cyclicRolleReduce (T t : ℝ) : ℝ := if t < T then t else t - T

lemma cyclicRolleNext_gt (hp : 0 < p) (root : Fin p → ℝ) (T : ℝ)
    (hmono : StrictMono root) (hbound : ∀ i, root i ∈ Set.Ico 0 T) (i : Fin p) :
    root i < cyclicRolleNext hp root T i := by
  unfold cyclicRolleNext
  split_ifs with h
  · exact hmono (show i < (⟨i.val + 1, h⟩ : Fin p) from Nat.lt_succ_self i.val)
  · have hfirst := (hbound ⟨0, hp⟩).1
    have hi := (hbound i).2
    linarith

lemma cyclicRolleNext_le_first_add (hp : 0 < p) (root : Fin p → ℝ) (T : ℝ)
    (hbound : ∀ i, root i ∈ Set.Ico 0 T) (i : Fin p) :
    cyclicRolleNext hp root T i ≤ root ⟨0, hp⟩ + T := by
  unfold cyclicRolleNext
  split_ifs with h
  · have hn := (hbound ⟨i.val + 1, h⟩).2
    have hfirst := (hbound ⟨0, hp⟩).1
    linarith
  · exact le_rfl

lemma cyclicRolleReduce_mem_Ico (hp : 0 < p) (root : Fin p → ℝ) (T : ℝ)
    (hbound : ∀ i, root i ∈ Set.Ico 0 T) (point : Fin p → ℝ)
    (hpoint : ∀ i, point i ∈ Set.Ioo (root i) (cyclicRolleNext hp root T i))
    (i : Fin p) : cyclicRolleReduce T (point i) ∈ Set.Ico 0 T := by
  have hl := (hpoint i).1
  have hu := (hpoint i).2.trans_le (cyclicRolleNext_le_first_add hp root T hbound i)
  have hroot := hbound i
  have hfirst := hbound ⟨0, hp⟩
  unfold cyclicRolleReduce
  split_ifs with h
  · exact ⟨hroot.1.trans hl.le, h⟩
  · constructor
    · linarith
    · linarith [hfirst.2]

lemma cyclicRolleReduce_injective (hp : 0 < p) (root : Fin p → ℝ) (T : ℝ)
    (hmono : StrictMono root) (hbound : ∀ i, root i ∈ Set.Ico 0 T)
    (point : Fin p → ℝ)
    (hpoint : ∀ i, point i ∈ Set.Ioo (root i) (cyclicRolleNext hp root T i)) :
    Function.Injective (fun i => cyclicRolleReduce T (point i)) := by
  have hne {i j : Fin p} (hij : i < j) :
      cyclicRolleReduce T (point i) ≠ cyclicRolleReduce T (point j) := by
    have hnext : i.val + 1 < p := (Nat.succ_le_of_lt hij).trans_lt j.isLt
    have hnextj : (⟨i.val + 1, hnext⟩ : Fin p) ≤ j := Nat.succ_le_of_lt hij
    have hi_upper : point i < root j := by
      have h := (hpoint i).2
      rw [cyclicRolleNext, dif_pos hnext] at h
      exact h.trans_le (hmono.monotone hnextj)
    have hiT : point i < T := hi_upper.trans (hbound j).2
    rw [cyclicRolleReduce, if_pos hiT]
    by_cases hjT : point j < T
    · rw [cyclicRolleReduce, if_pos hjT]
      exact ne_of_lt (hi_upper.trans (hpoint j).1)
    · rw [cyclicRolleReduce, if_neg hjT]
      have hj_upper := (hpoint j).2.trans_le
        (cyclicRolleNext_le_first_add hp root T hbound j)
      have hfirst_le : root ⟨0, hp⟩ ≤ root i :=
        hmono.monotone (show (⟨0, hp⟩ : Fin p) ≤ i from Nat.zero_le i.val)
      have hi_lower := (hpoint i).1
      exact ne_of_gt (by linarith)
  intro i j hij
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact False.elim (hne hlt hij)
  · exact heq
  · exact False.elim (hne hgt hij.symm)

/-- One Rolle point in each lifted root arc, with distinct derivative-zero
representatives in the original half-open turn. -/
theorem exists_cyclic_rolle_points (hp : 0 < p) (T : ℝ) (_hT : 0 < T)
    (root : Fin p → ℝ) (hmono : StrictMono root)
    (hbound : ∀ i, root i ∈ Set.Ico 0 T) (f : ℝ → ℝ)
    (hf : Differentiable ℝ f) (hroot : ∀ i, f (root i) = 0)
    (hshift : ∀ t, f t = 0 → f (t + T) = 0)
    (hdshift : ∀ t, deriv f (t + T) = 0 → deriv f t = 0) :
    ∃ point : Fin p → ℝ,
      (∀ i, point i ∈ Set.Ioo (root i) (cyclicRolleNext hp root T i)) ∧
      (∀ i, deriv f (point i) = 0) ∧
      Function.Injective (fun i => cyclicRolleReduce T (point i)) ∧
      (∀ i, cyclicRolleReduce T (point i) ∈ Set.Ico 0 T) ∧
      (∀ i, deriv f (cyclicRolleReduce T (point i)) = 0) := by
  have hnext_zero (i : Fin p) : f (cyclicRolleNext hp root T i) = 0 := by
    unfold cyclicRolleNext
    split_ifs with h
    · exact hroot _
    · exact hshift _ (hroot _)
  have hex (i : Fin p) :
      ∃ t ∈ Set.Ioo (root i) (cyclicRolleNext hp root T i), deriv f t = 0 := by
    exact exists_hasDerivAt_eq_zero (cyclicRolleNext_gt hp root T hmono hbound i)
      hf.continuous.continuousOn ((hroot i).trans (hnext_zero i).symm)
      (fun t _ => (hf t).hasDerivAt)
  choose point hpoint hzero using hex
  refine ⟨point, hpoint, hzero,
    cyclicRolleReduce_injective hp root T hmono hbound point hpoint,
    cyclicRolleReduce_mem_Ico hp root T hbound point hpoint, ?_⟩
  intro i
  unfold cyclicRolleReduce
  split_ifs with h
  · exact hzero i
  · apply hdshift (point i - T)
    simpa only [sub_add_cancel] using hzero i

/-- The finite family needed by a full-turn derivative root-count theorem. -/
theorem exists_cyclic_deriv_roots (hp : 0 < p) (T : ℝ) (hT : 0 < T)
    (root : Fin p → ℝ) (hmono : StrictMono root)
    (hbound : ∀ i, root i ∈ Set.Ico 0 T) (f : ℝ → ℝ)
    (hf : Differentiable ℝ f) (hroot : ∀ i, f (root i) = 0)
    (hshift : ∀ t, f t = 0 → f (t + T) = 0)
    (hdshift : ∀ t, deriv f (t + T) = 0 → deriv f t = 0) :
    ∃ point : Fin p → ℝ, Function.Injective point ∧
      (∀ i, point i ∈ Set.Ico 0 T) ∧ (∀ i, deriv f (point i) = 0) := by
  obtain ⟨point, _, _, hinj, hbound', hzero⟩ :=
    exists_cyclic_rolle_points hp T hT root hmono hbound f hf hroot hshift hdshift
  exact ⟨fun i => cyclicRolleReduce T (point i), hinj, hbound', hzero⟩

/-- A local maximum with nonzero second derivative has strictly negative second
derivative. Continuity of the original function is the only extra regularity
needed beyond the stated derivative values. -/
lemma second_deriv_neg_of_localMax {f : ℝ → ℝ} {t : ℝ}
    (hmax : IsLocalMax f t) (hcont : ContinuousAt f t) (hzero : deriv f t = 0)
    (hne : deriv (deriv f) t ≠ 0) : deriv (deriv f) t < 0 := by
  rcases hne.lt_or_gt with hneg | hpos
  · exact hneg
  · have hmin := isLocalMin_of_deriv_deriv_pos hpos hzero hcont
    have heq : f =ᶠ[nhds t] (fun _ => f t) := by
      filter_upwards [hmax, hmin] with x hxmax hxmin
      exact le_antisymm hxmax hxmin
    have hz : deriv (deriv f) t = 0 := by
      simpa only [deriv_const', deriv_const] using heq.deriv.deriv_eq
    exact False.elim (hne hz)

/-- An ordinary open root arc, or its last arc folded into the half-open turn.
The folded last arc contains `0` when the first root is positive. -/
def cyclicRootArc (hp : 0 < p) (root : Fin p → ℝ) (T : ℝ) (i : Fin p) : Set ℝ :=
  if h : i.val + 1 < p then Set.Ioo (root i) (root ⟨i.val + 1, h⟩)
  else {t | t ∈ Set.Ico 0 T ∧ (root i < t ∨ t < root ⟨0, hp⟩)}

lemma cyclicRootArc_mem_Ico (hp : 0 < p) (root : Fin p → ℝ) (T : ℝ)
    (hbound : ∀ i, root i ∈ Set.Ico 0 T) {i : Fin p} {t : ℝ}
    (ht : t ∈ cyclicRootArc hp root T i) : t ∈ Set.Ico 0 T := by
  unfold cyclicRootArc at ht
  split_ifs at ht with h
  · exact ⟨(hbound i).1.trans ht.1.le, ht.2.trans (hbound ⟨i.val + 1, h⟩).2⟩
  · exact ht.1

lemma cyclicRootArc_disjoint_of_lt (hp : 0 < p) (root : Fin p → ℝ) (T : ℝ)
    (hmono : StrictMono root) {i j : Fin p} (hij : i < j) :
    Disjoint (cyclicRootArc hp root T i) (cyclicRootArc hp root T j) := by
  have hnext : i.val + 1 < p := (Nat.succ_le_of_lt hij).trans_lt j.isLt
  have hnextj : (⟨i.val + 1, hnext⟩ : Fin p) ≤ j := Nat.succ_le_of_lt hij
  have hroot_next_le : root ⟨i.val + 1, hnext⟩ ≤ root j := hmono.monotone hnextj
  have hfirst_le : root ⟨0, hp⟩ ≤ root i :=
    hmono.monotone (show (⟨0, hp⟩ : Fin p) ≤ i from Nat.zero_le i.val)
  apply Set.disjoint_left.mpr
  intro t hti htj
  rw [cyclicRootArc, dif_pos hnext] at hti
  unfold cyclicRootArc at htj
  split_ifs at htj with hjnext
  · have hi_upper := hti.2
    have hj_lower := htj.1
    linarith
  · rcases htj.2 with hj_lower | hj_upper
    · have hi_upper := hti.2
      linarith
    · have hi_lower := hti.1
      linarith

/-- All cyclic root arcs are pairwise disjoint, including the one-root case. -/
lemma cyclicRootArc_pairwise_disjoint (hp : 0 < p) (root : Fin p → ℝ) (T : ℝ)
    (hmono : StrictMono root) :
    Pairwise (fun i j => Disjoint (cyclicRootArc hp root T i) (cyclicRootArc hp root T j)) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact cyclicRootArc_disjoint_of_lt hp root T hmono hlt
  · exact (cyclicRootArc_disjoint_of_lt hp root T hmono hgt).symm

/-- Every reduced lifted Rolle point belongs to its own cyclic root arc. -/
lemma cyclicRolleReduce_mem_arc (hp : 0 < p) (root : Fin p → ℝ) (T : ℝ)
    (hbound : ∀ i, root i ∈ Set.Ico 0 T) (point : Fin p → ℝ)
    (hpoint : ∀ i, point i ∈ Set.Ioo (root i) (cyclicRolleNext hp root T i))
    (i : Fin p) : cyclicRolleReduce T (point i) ∈ cyclicRootArc hp root T i := by
  unfold cyclicRootArc
  split_ifs with hnext
  · have hi : point i ∈ Set.Ioo (root i) (root ⟨i.val + 1, hnext⟩) := by
      simpa only [cyclicRolleNext, dif_pos hnext] using hpoint i
    have hiT := hi.2.trans (hbound ⟨i.val + 1, hnext⟩).2
    simpa only [cyclicRolleReduce, if_pos hiT] using hi
  · refine ⟨cyclicRolleReduce_mem_Ico hp root T hbound point hpoint i, ?_⟩
    unfold cyclicRolleReduce
    split_ifs with hiT
    · exact Or.inl (hpoint i).1
    · apply Or.inr
      have hi_upper := (hpoint i).2
      rw [cyclicRolleNext, dif_neg hnext] at hi_upper
      linarith

/-- Membership of a reduced Rolle point in a cyclic root arc determines its index. -/
lemma cyclicRolleReduce_index_eq_of_mem_arc (hp : 0 < p) (root : Fin p → ℝ) (T : ℝ)
    (hmono : StrictMono root) (hbound : ∀ i, root i ∈ Set.Ico 0 T)
    (point : Fin p → ℝ)
    (hpoint : ∀ i, point i ∈ Set.Ioo (root i) (cyclicRolleNext hp root T i))
    {i j : Fin p} (hmem : cyclicRolleReduce T (point j) ∈ cyclicRootArc hp root T i) :
    j = i := by
  by_contra hne
  have hd := cyclicRootArc_pairwise_disjoint hp root T hmono (Ne.symm hne)
  exact Set.disjoint_left.mp hd hmem (cyclicRolleReduce_mem_arc hp root T hbound point hpoint j)

end

end UnitCircleInterpolation
