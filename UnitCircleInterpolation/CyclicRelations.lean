/-
Unit-circle project integration and adaptations: wang060919.
Developed with Codex assistance. Original authors and MIT notices are retained below.
-/

/-
Copyright (c) 2026 Ethan Yang
Copyright (c) 2026 randyxian08 (free-node extension and repairs)

Adapted from randyxian08/jsp000936-lean, commit
0ced15a2630c5c68b23de896d7e6ad1e7cfeda01,
Erdos1153/DeBoorPinkus/Minors.lean, alternating-root and relation kernels:
https://github.com/randyxian08/jsp000936-lean/blob/0ced15a2630c5c68b23de896d7e6ad1e7cfeda01/Erdos1153/DeBoorPinkus/Minors.lean
Original file SHA256: df1a894ff71edc5c6947800468ae48fe5711e5f79d933231412a5c5d87c974b0
Original Git blob: 77bc503ee163b89beaf270e32c29d82f8e811103
The local file and pinned tree manifest were checked against these hashes.

MIT License

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

import UnitCircleInterpolation.HomogeneousLinear
import Mathlib.Topology.Order.IntermediateValue

/-!
# Relations in a continuous function space with a circular root bound

The source's original header was:

# Maximal quotient-evaluation minors

This file formalizes the last, genuinely linear-algebraic step in Lemma 2 of
de Boor--Pinkus.  The checkerboard signs of the critical quotients are not by
themselves a nonsingularity theorem.  The additional input used here is that
all quotient polynomials have degree at most `d - 1`: the source's alternating
sign construction would otherwise produce `d` distinct real zeros.

Here the generic hypotheses concern a literal subspace of continuous functions
with a bound on distinct canonical circular roots. They are proved for the
homogeneous trigonometric space below. No actual critical quotient sign table
or Jacobian/minor assertion is assumed or claimed to have been established.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace UnitCircleInterpolation

noncomputable section

open Polynomial

/-- Every nonzero member has at most `p` distinct roots in one canonical turn. -/
def HasCyclicRootBound (p : ℕ) (V : Submodule ℝ (ℝ → ℝ)) : Prop :=
  ∀ (m : ℕ) (f : ℝ → ℝ), f ∈ V → f ≠ 0 →
    ∀ root : Fin m → ℝ, Function.Injective root →
      (∀ i, root i ∈ Set.Ico 0 (2 * Real.pi)) → (∀ i, f (root i) = 0) → m ≤ p

lemma homogeneousTrigSpace_hasCyclicRootBound (p : ℕ) :
    HasCyclicRootBound p (homogeneousTrigSpace p) := by
  intro m f hf hne root hinj hbound hroot
  exact distinct_root_count_of_mem_homogeneousTrigSpace p f hf hne root hinj hbound hroot

/-- Alternating at `d+1` ordered canonical angles contradicts a `d-1` root bound. -/
theorem eq_zero_of_cyclic_alternation {d : ℕ} (hd : 0 < d)
    (V : Submodule ℝ (ℝ → ℝ))
    (hcontinuous : ∀ f ∈ V, Continuous f)
    (hrootBound : HasCyclicRootBound (d - 1) V)
    (f : ℝ → ℝ) (hf : f ∈ V) (τ : Fin (d + 1) → ℝ)
    (hτ : StrictMono τ) (hbound : ∀ i, τ i ∈ Set.Ico 0 (2 * Real.pi))
    (hsign : ∀ j : Fin d, f (τ j.castSucc) * f (τ j.succ) < 0) : f = 0 := by
  classical
  have hexists (j : Fin d) :
      ∃ x ∈ Set.Ioo (τ j.castSucc) (τ j.succ), f x = 0 := by
    have hab : τ j.castSucc ≤ τ j.succ := (hτ Fin.castSucc_lt_succ).le
    have hcont : ContinuousOn f (Set.Icc (τ j.castSucc) (τ j.succ)) :=
      (hcontinuous f hf).continuousOn
    rcases mul_neg_iff.mp (hsign j) with hj | hj
    · exact intermediate_value_Ioo' hab hcont ⟨hj.2, hj.1⟩
    · exact intermediate_value_Ioo hab hcont hj
  let r : Fin d → ℝ := fun j => Classical.choose (hexists j)
  have hr_mem (j : Fin d) : r j ∈ Set.Ioo (τ j.castSucc) (τ j.succ) :=
    (Classical.choose_spec (hexists j)).1
  have hr_eval (j : Fin d) : f (r j) = 0 := (Classical.choose_spec (hexists j)).2
  have hr_strictMono : StrictMono r := by
    intro i j hij
    have hij' : i.val + 1 ≤ j.val := by omega
    have hmiddle : τ i.succ ≤ τ j.castSucc := by
      apply hτ.monotone
      exact Fin.le_iff_val_le_val.mpr (by simpa using hij')
    exact ((hr_mem i).2.trans_le hmiddle).trans (hr_mem j).1
  have hr_bound (j : Fin d) : r j ∈ Set.Ico 0 (2 * Real.pi) :=
    ⟨(hbound j.castSucc).1.trans (hr_mem j).1.le,
      (hr_mem j).2.trans (hbound j.succ).2⟩
  by_contra hne
  have hcount := hrootBound d f hf hne r hr_strictMono.injective hr_bound hr_eval
  omega

private lemma sq_negOnePow (k : ℕ) : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
  rcases neg_one_pow_eq_or ℝ k with h | h <;> rw [h] <;> norm_num

private def negativeLaterIndices {d : ℕ} (a : Fin (d + 1) → ℝ) :
    Finset (Fin (d + 1)) :=
  (Finset.univ.erase 0).filter fun i => a i < 0

private def positiveLaterIndices {d : ℕ} (a : Fin (d + 1) → ℝ) :
    Finset (Fin (d + 1)) :=
  (Finset.univ.erase 0).filter fun i => 0 < a i

private lemma sum_eq_first_add_negative_add_positive {d : ℕ}
    (a v : Fin (d + 1) → ℝ) :
    (∑ i, a i * v i) =
      a 0 * v 0 +
        ∑ i ∈ negativeLaterIndices a, a i * v i +
          ∑ i ∈ positiveLaterIndices a, a i * v i := by
  classical
  let I : Finset (Fin (d + 1)) := Finset.univ.erase 0
  let N := negativeLaterIndices a
  let P := positiveLaterIndices a
  have hNsub : N ⊆ I := Finset.filter_subset _ _
  have hPsub : P ⊆ I := Finset.filter_subset _ _
  have hdis : Disjoint N P := by
    refine Finset.disjoint_left.mpr ?_
    intro i hiN hiP
    have hneg : a i < 0 := (Finset.mem_filter.mp hiN).2
    have hpos : 0 < a i := (Finset.mem_filter.mp hiP).2
    linarith
  have hcover :
      (∑ i ∈ N ∪ P, a i * v i) = ∑ i ∈ I, a i * v i := by
    apply Finset.sum_subset (Finset.union_subset hNsub hPsub)
    intro i hiI hiNP
    have hiN : i ∉ N := fun h => hiNP (Finset.mem_union_left P h)
    have hiP : i ∉ P := fun h => hiNP (Finset.mem_union_right N h)
    have hnneg : ¬a i < 0 := by
      intro h
      exact hiN (Finset.mem_filter.mpr ⟨hiI, h⟩)
    have hnpos : ¬0 < a i := by
      intro h
      exact hiP (Finset.mem_filter.mpr ⟨hiI, h⟩)
    have hai : a i = 0 := le_antisymm (le_of_not_gt hnpos) (le_of_not_gt hnneg)
    simp [hai]
  rw [Finset.sum_union hdis] at hcover
  have herase := Finset.sum_erase_add Finset.univ (fun i => a i * v i)
    (Finset.mem_univ (0 : Fin (d + 1)))
  change (∑ i ∈ I, a i * v i) + a 0 * v 0 = ∑ i, a i * v i at herase
  rw [← herase, ← hcover]
  dsimp only [N, P]
  ring

/-- The source-normalized relation pattern follows from continuity and the literal
circular root bound. This theorem assumes no determinant or minor property. -/
theorem cyclic_relation_normalized_sign_pattern {d : ℕ} (hd : 0 < d)
    (V : Submodule ℝ (ℝ → ℝ))
    (hcontinuous : ∀ f ∈ V, Continuous f)
    (hrootBound : HasCyclicRootBound (d - 1) V)
    (q : Fin (d + 1) → ℝ → ℝ) (hq : ∀ i, q i ∈ V)
    (τ : Fin (d + 1) → ℝ) (hτ : StrictMono τ)
    (hbound : ∀ i, τ i ∈ Set.Ico 0 (2 * Real.pi))
    (hfirst : ∀ i, 0 < q i (τ 0))
    (hfirstLater : ∀ j, j ≠ 0 → 0 < (-1 : ℝ) ^ (j.val + 1) * q 0 (τ j))
    (hoff : ∀ i j, i ≠ 0 → i ≠ j → 0 < (-1 : ℝ) ^ j.val * q i (τ j))
    (a : Fin (d + 1) → ℝ) (hrel : ∀ x, (∑ i, a i * q i x) = 0)
    (ha : a ≠ 0) :
    (0 < a 0 ∧ ∀ i, i ≠ 0 → a i < 0) ∨
      (a 0 < 0 ∧ ∀ i, i ≠ 0 → 0 < a i) := by
  classical
  let orient : ℝ := if 0 ≤ a 0 then 1 else -1
  let b : Fin (d + 1) → ℝ := fun i => orient * a i
  have horient : orient = 1 ∨ orient = -1 := by
    dsimp [orient]
    split <;> simp
  have horient_ne : orient ≠ 0 := by
    rcases horient with h | h <;> rw [h] <;> norm_num
  have hbfirst : 0 ≤ b 0 := by
    dsimp [b, orient]
    split_ifs with h
    · simpa using h
    · have hlt : a 0 < 0 := lt_of_not_ge h
      simp only [neg_one_mul]
      exact neg_nonneg.mpr hlt.le
  have hbne : b ≠ 0 := by
    intro hb
    apply ha
    funext i
    have hi := congrFun hb i
    dsimp [b] at hi
    exact (mul_eq_zero.mp hi).resolve_left horient_ne
  have hbrel_eval (x : ℝ) : (∑ i, b i * q i x) = 0 := by
    calc
      (∑ i, b i * q i x) = orient * (∑ i, a i * q i x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [b]
        ring
      _ = 0 := by rw [hrel, mul_zero]
  let N := negativeLaterIndices b
  let P := positiveLaterIndices b
  have hN : N.Nonempty := by
    by_contra hNempty
    rw [Finset.not_nonempty_iff_eq_empty] at hNempty
    have hbnonneg (i : Fin (d + 1)) : 0 ≤ b i := by
      by_cases hi : i = 0
      · simpa [hi] using hbfirst
      · apply le_of_not_gt
        intro hneg
        have hiN : i ∈ N := by
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩, hneg⟩
        rw [hNempty] at hiN
        simp at hiN
    obtain ⟨i, hbi⟩ := Function.ne_iff.mp hbne
    have hbipos : 0 < b i := lt_of_le_of_ne (hbnonneg i) (Ne.symm hbi)
    have hterm_nonneg (k : Fin (d + 1)) :
        0 ≤ b k * q k
          (τ 0) :=
      mul_nonneg (hbnonneg k)
        (hfirst k).le
    have hterm_pos :
        0 < b i * q i
          (τ 0) :=
      mul_pos hbipos
        (hfirst i)
    have hsumpos : 0 <
        ∑ k, b k * q k
          (τ 0) := by
      rw [Finset.sum_pos_iff_of_nonneg (fun k _hk => hterm_nonneg k)]
      exact ⟨i, Finset.mem_univ i, hterm_pos⟩
    rw [hbrel_eval] at hsumpos
    exact (lt_irrefl 0) hsumpos
  -- The source's auxiliary polynomial: first row plus all negatively
  -- weighted later rows.
  let f : ℝ → ℝ := b 0 • q 0 + ∑ i ∈ N, b i • q i
  have hfmem : f ∈ V := by
    exact V.add_mem (V.smul_mem _ (hq 0))
      (V.sum_mem (fun i hi => V.smul_mem _ (hq i)))
  have hf_eval (x : ℝ) : f x = b 0 * q 0 x + ∑ i ∈ N, b i * q i x := by
    simp only [f, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hf_eval_eq_neg_pos (x : ℝ) : f x =
      -∑ i ∈ P, b i * q i x := by
    have hsplit := sum_eq_first_add_negative_add_positive b
      (fun i => q i x)
    have hzero := hbrel_eval x
    change (∑ i, b i * q i x) =
      b 0 * q 0 x +
        ∑ i ∈ N, b i * q i x +
          ∑ i ∈ P, b i * q i x at hsplit
    rw [hf_eval]
    linarith
  have hNmem {i : Fin (d + 1)} (hi : i ∈ N) : i ≠ 0 ∧ b i < 0 := by
    exact ⟨(Finset.mem_erase.mp (Finset.mem_filter.mp hi).1).1,
      (Finset.mem_filter.mp hi).2⟩
  have hPmem {i : Fin (d + 1)} (hi : i ∈ P) : i ≠ 0 ∧ 0 < b i := by
    exact ⟨(Finset.mem_erase.mp (Finset.mem_filter.mp hi).1).1,
      (Finset.mem_filter.mp hi).2⟩
  have hfzero : f = 0 := by
    by_cases hP : P.Nonempty
    · have hf_sign (j : Fin (d + 1)) :
          0 < (-1 : ℝ) ^ (j.val + 1) * f
            (τ j) := by
        by_cases hj0 : j = 0
        · subst j
          have hsumpos : 0 < ∑ i ∈ P,
              b i * q i
                (τ 0) := by
            apply Finset.sum_pos
            · intro i hi
              exact mul_pos (hPmem hi).2
                (hfirst i)
            · exact hP
          rw [hf_eval_eq_neg_pos]
          simpa using hsumpos
        · by_cases hjP : j ∈ P
          · have hfirst : 0 ≤
                b 0 * ((-1 : ℝ) ^ (j.val + 1) *
                  q 0
                    (τ j)) :=
              mul_nonneg hbfirst
                (hfirstLater j hj0).le
            have hNsum : 0 < ∑ i ∈ N,
                (-1 : ℝ) ^ (j.val + 1) *
                  (b i * q i
                    (τ j)) := by
              apply Finset.sum_pos
              · intro i hi
                have hine := (hNmem hi).1
                have hibneg := (hNmem hi).2
                have hij : i ≠ j := by
                  intro hij
                  subst i
                  linarith [hibneg, (hPmem hjP).2]
                have hq := hoff i j hine hij
                calc
                  0 < (-b i) * ((-1 : ℝ) ^ j.val *
                      q i
                        (τ j)) :=
                    mul_pos (neg_pos.mpr hibneg) hq
                  _ = (-1 : ℝ) ^ (j.val + 1) *
                      (b i * q i
                        (τ j)) := by
                    rw [pow_succ]
                    ring
              · exact hN
            rw [hf_eval]
            calc
              0 < b 0 * ((-1 : ℝ) ^ (j.val + 1) *
                    q 0
                      (τ j)) +
                  ∑ i ∈ N, (-1 : ℝ) ^ (j.val + 1) *
                    (b i * q i
                      (τ j)) :=
                add_pos_of_nonneg_of_pos hfirst hNsum
              _ = (-1 : ℝ) ^ (j.val + 1) *
                  (b 0 * q 0
                      (τ j) +
                    ∑ i ∈ N, b i *
                      q i
                        (τ j)) := by
                rw [← Finset.mul_sum]
                ring
          · have hjnotpos : ¬0 < b j := by
              intro hjpos
              exact hjP (Finset.mem_filter.mpr
                ⟨Finset.mem_erase.mpr ⟨hj0, Finset.mem_univ j⟩, hjpos⟩)
            have hPsum : 0 < ∑ i ∈ P,
                (-1 : ℝ) ^ (j.val + 1) *
                  (-(b i * q i
                    (τ j))) := by
              apply Finset.sum_pos
              · intro i hi
                have hine := (hPmem hi).1
                have hibpos := (hPmem hi).2
                have hij : i ≠ j := by
                  intro hij
                  subst i
                  exact hjnotpos hibpos
                have hq := hoff i j hine hij
                calc
                  0 < b i * ((-1 : ℝ) ^ j.val *
                      q i
                        (τ j)) := mul_pos hibpos hq
                  _ = (-1 : ℝ) ^ (j.val + 1) *
                      (-(b i * q i
                        (τ j))) := by
                    rw [pow_succ]
                    ring
              · exact hP
            rw [hf_eval_eq_neg_pos]
            calc
              0 < ∑ i ∈ P, (-1 : ℝ) ^ (j.val + 1) *
                  (-(b i * q i
                    (τ j))) := hPsum
              _ = (-1 : ℝ) ^ (j.val + 1) *
                  (-∑ i ∈ P, b i *
                    q i
                      (τ j)) := by
                rw [← Finset.mul_sum]
                congr 1
                rw [← Finset.sum_neg_distrib]
      apply eq_zero_of_cyclic_alternation hd V hcontinuous hrootBound f hfmem τ hτ hbound
      intro j
      have hleft := hf_sign j.castSucc
      have hright := hf_sign j.succ
      simp only [Fin.val_castSucc, Fin.val_succ] at hleft hright
      rw [show j.val + 1 + 1 = (j.val + 1) + 1 by omega, pow_succ] at hright
      nlinarith [sq_negOnePow (j.val + 1)]
    · funext x
      have heval : ∀ x : ℝ, f x = 0 := by
        intro x
        rw [hf_eval_eq_neg_pos]
        rw [Finset.not_nonempty_iff_eq_empty.mp hP]
        simp
      exact heval x
  have hPempty : P = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hP
    have hsumpos : 0 < ∑ i ∈ P,
        b i * q i
          (τ 0) := by
      apply Finset.sum_pos
      · intro i hi
        exact mul_pos (hPmem hi).2
          (hfirst i)
      · exact hP
    have hf0 := congrArg
      (fun g : ℝ → ℝ => g (τ 0)) hfzero
    have hf0' : f (τ 0) = 0 := by
      simpa only [Pi.zero_apply] using hf0
    rw [hf_eval_eq_neg_pos] at hf0'
    linarith
  have hblater (i : Fin (d + 1)) (hi0 : i ≠ 0) : b i ≠ 0 := by
    intro hbi
    have hiP : i ∉ P := by rw [hPempty]; simp
    have hibnonpos : b i ≤ 0 := by
      apply le_of_not_gt
      intro hpos
      exact hiP (Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hi0, Finset.mem_univ i⟩, hpos⟩)
    have hiN : i ∉ N := by
      intro hiN
      exact (hNmem hiN).2.ne hbi
    have hfirst : 0 ≤ b 0 * ((-1 : ℝ) ^ (i.val + 1) *
        q 0
          (τ i)) :=
      mul_nonneg hbfirst
        (hfirstLater i hi0).le
    have hNsum : 0 < ∑ k ∈ N, (-1 : ℝ) ^ (i.val + 1) *
        (b k * q k
          (τ i)) := by
      apply Finset.sum_pos
      · intro k hk
        have hk0 := (hNmem hk).1
        have hkbneg := (hNmem hk).2
        have hki : k ≠ i := by
          intro hki
          subst k
          exact hiN hk
        have hq := hoff k i hk0 hki
        calc
          0 < (-b k) * ((-1 : ℝ) ^ i.val *
              q k
                (τ i)) :=
            mul_pos (neg_pos.mpr hkbneg) hq
          _ = (-1 : ℝ) ^ (i.val + 1) *
              (b k * q k
                (τ i)) := by
            rw [pow_succ]
            ring
      · exact hN
    have hfpos : 0 < (-1 : ℝ) ^ (i.val + 1) *
        f (τ i) := by
      rw [hf_eval]
      calc
        0 < b 0 * ((-1 : ℝ) ^ (i.val + 1) *
              q 0
                (τ i)) +
            ∑ k ∈ N, (-1 : ℝ) ^ (i.val + 1) *
              (b k * q k
                (τ i)) :=
          add_pos_of_nonneg_of_pos hfirst hNsum
        _ = (-1 : ℝ) ^ (i.val + 1) *
            (b 0 * q 0
                (τ i) +
              ∑ k ∈ N, b k * q k
                (τ i)) := by
          rw [← Finset.mul_sum]
          ring
    rw [hfzero] at hfpos
    simp at hfpos
  have hbzero : b 0 ≠ 0 := by
    intro hb0
    have hNsumneg :
        ∑ i ∈ N, b i * q i
          (τ 0) < 0 := by
      apply Finset.sum_neg
      · intro i hi
        exact mul_neg_of_neg_of_pos (hNmem hi).2
          (hfirst i)
      · exact hN
    have hsplit := sum_eq_first_add_negative_add_positive b
      (fun i => q i
        (τ 0))
    change (∑ i, b i * q i
        (τ 0)) =
      b 0 * q 0
          (τ 0) +
        ∑ i ∈ N, b i * q i
          (τ 0) +
        ∑ i ∈ P, b i * q i
          (τ 0) at hsplit
    rw [hbrel_eval, hb0, hPempty] at hsplit
    simp at hsplit
    exact (ne_of_lt hNsumneg) hsplit.symm
  have hbfirstpos : 0 < b 0 := lt_of_le_of_ne hbfirst (Ne.symm hbzero)
  have hblaterneg (i : Fin (d + 1)) (hi : i ≠ 0) : b i < 0 := by
    have hnonpos : b i ≤ 0 := by
      apply le_of_not_gt
      intro hpos
      have hiP : i ∈ P := Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩, hpos⟩
      rw [hPempty] at hiP
      simp at hiP
    exact lt_of_le_of_ne hnonpos (hblater i hi)
  rcases horient with horient | horient
  · left
    constructor
    · simpa [b, horient] using hbfirstpos
    · intro i hi
      simpa [b, horient] using hblaterneg i hi
  · right
    constructor
    · have := hbfirstpos
      simp only [b, horient, neg_one_mul] at this
      linarith
    · intro i hi
      have := hblaterneg i hi
      simp only [b, horient, neg_one_mul] at this
      linarith


/-- The row scaling that aligns the full-circle checkerboard table with the
source-normalized first-row sign table. -/
def cyclicRelationNormalizer {d : ℕ} (i : Fin (d + 1)) : ℝ :=
  if i = 0 then -1 else (-1 : ℝ) ^ i.val

private lemma cyclicRelationNormalizer_sq {d : ℕ} (i : Fin (d + 1)) :
    cyclicRelationNormalizer i * cyclicRelationNormalizer i = 1 := by
  unfold cyclicRelationNormalizer
  split_ifs
  · norm_num
  · nlinarith [sq_negOnePow i.val]

/-- In a nonzero relation among a full-circle checkerboard family, the adjusted
coefficients `(-1)^i aᵢ` are all strictly positive or all strictly negative. -/
theorem cyclic_relation_coherent_sign {d : ℕ} (hd : 0 < d)
    (V : Submodule ℝ (ℝ → ℝ))
    (hcontinuous : ∀ f ∈ V, Continuous f)
    (hrootBound : HasCyclicRootBound (d - 1) V)
    (q : Fin (d + 1) → ℝ → ℝ) (hq : ∀ i, q i ∈ V)
    (τ : Fin (d + 1) → ℝ) (hτ : StrictMono τ)
    (hbound : ∀ i, τ i ∈ Set.Ico 0 (2 * Real.pi))
    (hdiag : ∀ i, q i (τ i) < 0)
    (hoff : ∀ i j, i ≠ j → 0 < (-1 : ℝ) ^ (i.val + j.val) * q i (τ j))
    (a : Fin (d + 1) → ℝ) (hrel : ∀ x, (∑ i, a i * q i x) = 0)
    (ha : a ≠ 0) :
    (∀ i, 0 < (-1 : ℝ) ^ i.val * a i) ∨
      (∀ i, (-1 : ℝ) ^ i.val * a i < 0) := by
  classical
  let r : Fin (d + 1) → ℝ → ℝ := fun i => cyclicRelationNormalizer i • q i
  let c : Fin (d + 1) → ℝ := fun i => cyclicRelationNormalizer i * a i
  have hrmem (i : Fin (d + 1)) : r i ∈ V := V.smul_mem _ (hq i)
  have hfirst (i : Fin (d + 1)) : 0 < r i (τ 0) := by
    by_cases hi : i = 0
    · subst i
      simpa [r, cyclicRelationNormalizer] using neg_pos.mpr (hdiag 0)
    · have h := hoff i 0 hi
      simpa [r, cyclicRelationNormalizer, hi] using h
  have hfirstLater (j : Fin (d + 1)) (hj : j ≠ 0) :
      0 < (-1 : ℝ) ^ (j.val + 1) * r 0 (τ j) := by
    have h := hoff 0 j hj.symm
    simpa [r, cyclicRelationNormalizer, pow_succ] using h
  have hroff (i j : Fin (d + 1)) (hi : i ≠ 0) (hij : i ≠ j) :
      0 < (-1 : ℝ) ^ j.val * r i (τ j) := by
    have h := hoff i j hij
    simpa [r, cyclicRelationNormalizer, hi, pow_add, mul_assoc,
      mul_left_comm, mul_comm] using h
  have hcrel (x : ℝ) : (∑ i, c i * r i x) = 0 := by
    convert hrel x using 1
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [c, r]
    calc
      cyclicRelationNormalizer i * a i * (cyclicRelationNormalizer i * q i x) =
          (cyclicRelationNormalizer i * cyclicRelationNormalizer i) * (a i * q i x) := by ring
      _ = a i * q i x := by rw [cyclicRelationNormalizer_sq, one_mul]
  have hcne : c ≠ 0 := by
    intro hc
    apply ha
    funext i
    have hci := congrFun hc i
    have hs := cyclicRelationNormalizer_sq i
    dsimp [c] at hci
    change cyclicRelationNormalizer i * a i = 0 at hci
    change a i = 0
    have hsne : cyclicRelationNormalizer i ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hs
      norm_num at hs
    exact (mul_eq_zero.mp hci).resolve_left hsne
  rcases cyclic_relation_normalized_sign_pattern hd V hcontinuous hrootBound r hrmem
      τ hτ hbound hfirst hfirstLater hroff c hcrel hcne with h | h
  · right
    intro i
    by_cases hi : i = 0
    · subst i
      have h0 := h.1
      simp [c, cyclicRelationNormalizer] at h0
      simpa using h0
    · simpa only [c, cyclicRelationNormalizer, if_neg hi] using h.2 i hi
  · left
    intro i
    by_cases hi : i = 0
    · subst i
      have h0 := h.1
      simp [c, cyclicRelationNormalizer] at h0
      simpa using h0
    · simpa only [c, cyclicRelationNormalizer, if_neg hi] using h.2 i hi

/-- The explicit homogeneous-degree instance of the generic full-circle relation theorem.
The literal peak sign table remains an input to be proved for actual quotients. -/
theorem homogeneousTrig_relation_coherent_sign {d : ℕ} (hd : 0 < d)
    (P : Fin (d + 1) → ℝ[X]) (hdegree : ∀ i, (P i).natDegree ≤ d - 1)
    (τ : Fin (d + 1) → ℝ) (hτ : StrictMono τ)
    (hbound : ∀ i, τ i ∈ Set.Ico 0 (2 * Real.pi))
    (hdiag : ∀ i, homogeneousTrig (d - 1) (P i) (τ i) < 0)
    (hoff : ∀ i j, i ≠ j → 0 < (-1 : ℝ) ^ (i.val + j.val) *
      homogeneousTrig (d - 1) (P i) (τ j))
    (a : Fin (d + 1) → ℝ)
    (hrel : ∀ x, (∑ i, a i * homogeneousTrig (d - 1) (P i) x) = 0)
    (ha : a ≠ 0) :
    (∀ i, 0 < (-1 : ℝ) ^ i.val * a i) ∨
      (∀ i, (-1 : ℝ) ^ i.val * a i < 0) := by
  exact cyclic_relation_coherent_sign hd (homogeneousTrigSpace (d - 1))
    (continuous_of_mem_homogeneousTrigSpace (d - 1))
    (homogeneousTrigSpace_hasCyclicRootBound (d - 1))
    (fun i => homogeneousTrig (d - 1) (P i))
    (fun i => homogeneousTrig_mem_space (d - 1) (P i) (hdegree i))
    τ hτ hbound hdiag hoff a hrel ha

/-- Every coefficient of a nonzero homogeneous circular relation is nonzero. -/
theorem homogeneousTrig_relation_coeff_ne_zero {d : ℕ} (hd : 0 < d)
    (P : Fin (d + 1) → ℝ[X]) (hdegree : ∀ i, (P i).natDegree ≤ d - 1)
    (τ : Fin (d + 1) → ℝ) (hτ : StrictMono τ)
    (hbound : ∀ i, τ i ∈ Set.Ico 0 (2 * Real.pi))
    (hdiag : ∀ i, homogeneousTrig (d - 1) (P i) (τ i) < 0)
    (hoff : ∀ i j, i ≠ j → 0 < (-1 : ℝ) ^ (i.val + j.val) *
      homogeneousTrig (d - 1) (P i) (τ j))
    (a : Fin (d + 1) → ℝ)
    (hrel : ∀ x, (∑ i, a i * homogeneousTrig (d - 1) (P i) x) = 0)
    (ha : a ≠ 0) : ∀ i, a i ≠ 0 := by
  rcases homogeneousTrig_relation_coherent_sign hd P hdegree τ hτ hbound hdiag hoff
      a hrel ha with h | h
  · intro i hi
    have := h i
    simp [hi] at this
  · intro i hi
    have := h i
    simp [hi] at this

/-- A relation omitting even one member is trivial; equivalently every row-deleted
homogeneous circular family is linearly independent as functions. -/
theorem homogeneousTrig_relation_eq_zero_of_missing_coeff {d : ℕ} (hd : 0 < d)
    (P : Fin (d + 1) → ℝ[X]) (hdegree : ∀ i, (P i).natDegree ≤ d - 1)
    (τ : Fin (d + 1) → ℝ) (hτ : StrictMono τ)
    (hbound : ∀ i, τ i ∈ Set.Ico 0 (2 * Real.pi))
    (hdiag : ∀ i, homogeneousTrig (d - 1) (P i) (τ i) < 0)
    (hoff : ∀ i j, i ≠ j → 0 < (-1 : ℝ) ^ (i.val + j.val) *
      homogeneousTrig (d - 1) (P i) (τ j))
    (a : Fin (d + 1) → ℝ)
    (hrel : ∀ x, (∑ i, a i * homogeneousTrig (d - 1) (P i) x) = 0)
    (missing : Fin (d + 1)) (hmissing : a missing = 0) : a = 0 := by
  by_contra ha
  exact (homogeneousTrig_relation_coeff_ne_zero hd P hdegree τ hτ hbound hdiag hoff
    a hrel ha missing) hmissing

end

end UnitCircleInterpolation
