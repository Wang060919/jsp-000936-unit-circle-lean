/-
Unit-circle project integration and adaptations: wang060919.
Developed with Codex assistance. Original authors and MIT notices are retained below.
-/

/-
Copyright (c) 2026 Ethan Yang
Copyright (c) 2026 randyxian08 (free-node extension and repairs)

Adapted from randyxian08/jsp000936-lean, commit
0ced15a2630c5c68b23de896d7e6ad1e7cfeda01,
Erdos1153/DeBoorPinkus/DerivativeInterlacing.lean, lines 156–436:
https://github.com/randyxian08/jsp000936-lean/blob/0ced15a2630c5c68b23de896d7e6ad1e7cfeda01/Erdos1153/DeBoorPinkus/DerivativeInterlacing.lean

The finite real-polynomial kernel below is reused proof infrastructure.
The unit-circle formalization and its eventual classification are separate work.
Original file SHA256: 8ac28122f151b6033b5e4914b5cfc7333e0b50214648083335617e0ec12bbafe

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

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A finite real-polynomial Markov kernel

For a nonempty list of distinct real roots `d`, put
`D = finiteRootProduct d * C scale`. If `S.natDegree ≤ m` and
`S.eval (d k) * D.derivative.eval (d k)` is positive at every root,
then `D S' - D' S` is strictly negative at every real point.

The proof interpolates `S` at the roots, removes its constant multiple of the
root product, and writes the Wronskian as a sum of negative squares.
Its hypotheses contain no interval interpolation nodes or gap-polynomial data.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

open Polynomial
open scoped BigOperators

noncomputable section

def finiteRootProduct {m : ℕ} (d : Fin m → ℝ) : ℝ[X] :=
  ∏ k : Fin m, (X - C (d k))

def finiteRootComplement {m : ℕ} (d : Fin m → ℝ)
    (k : Fin m) : ℝ[X] :=
  ∏ l ∈ (Finset.univ.erase k : Finset (Fin m)), (X - C (d l))

lemma finiteRootProduct_eq_mul_complement {m : ℕ}
    (d : Fin m → ℝ) (k : Fin m) :
    finiteRootProduct d = (X - C (d k)) * finiteRootComplement d k := by
  classical
  rw [finiteRootProduct, Fintype.prod_eq_mul_prod_compl k]
  simp only [finiteRootComplement, Finset.compl_singleton]

lemma finiteRootComplement_eval_self_ne_zero {m : ℕ}
    {d : Fin m → ℝ} (hd : Function.Injective d) (k : Fin m) :
    (finiteRootComplement d k).eval (d k) ≠ 0 := by
  classical
  simp only [finiteRootComplement, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro l hl
  have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
  exact sub_ne_zero.mpr (hd.ne hlk.symm)

lemma finiteRootProduct_derivative_eval_root {m : ℕ}
    (d : Fin m → ℝ) (k : Fin m) :
    (finiteRootProduct d).derivative.eval (d k) =
      (finiteRootComplement d k).eval (d k) := by
  rw [finiteRootProduct_eq_mul_complement d k, Polynomial.derivative_mul]
  simp

/-- Cardinal basis attached to a finite list of distinct real roots, written
in the unnormalized complement-product form needed by the Wronskian
calculation. -/
def finiteRootBasis {m : ℕ} (d : Fin m → ℝ)
    (k : Fin m) : ℝ[X] :=
  C ((finiteRootComplement d k).eval (d k))⁻¹ *
    finiteRootComplement d k

lemma finiteRootBasis_eval_self {m : ℕ} {d : Fin m → ℝ}
    (hd : Function.Injective d) (k : Fin m) :
    (finiteRootBasis d k).eval (d k) = 1 := by
  rw [finiteRootBasis, Polynomial.eval_mul, Polynomial.eval_C]
  exact inv_mul_cancel₀ (finiteRootComplement_eval_self_ne_zero hd k)

lemma finiteRootBasis_eval_of_ne {m : ℕ} {d : Fin m → ℝ}
    (k l : Fin m) (hlk : l ≠ k) :
    (finiteRootBasis d k).eval (d l) = 0 := by
  classical
  rw [finiteRootBasis, Polynomial.eval_mul, Polynomial.eval_C]
  suffices (finiteRootComplement d k).eval (d l) = 0 by rw [this, mul_zero]
  simp only [finiteRootComplement, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hlk, Finset.mem_univ l⟩)
  simp

lemma finiteRootBasis_eq_lagrangeBasis {m : ℕ}
    {d : Fin m → ℝ} (hd : Function.Injective d) (k : Fin m) :
    finiteRootBasis d k = Lagrange.basis Finset.univ d k := by
  classical
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ hd.injOn
  · have hEvalNe := finiteRootComplement_eval_self_ne_zero hd k
    have hComplementNe : finiteRootComplement d k ≠ 0 := by
      intro hzero
      rw [hzero, Polynomial.eval_zero] at hEvalNe
      exact hEvalNe rfl
    rw [finiteRootBasis, Polynomial.degree_mul,
      Polynomial.degree_C (inv_ne_zero hEvalNe), zero_add,
      Polynomial.degree_eq_natDegree hComplementNe,
      finiteRootComplement, natDegree_finset_prod_X_sub_C_eq_card,
      Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
      Fintype.card_fin]
    exact_mod_cast Nat.sub_lt (Nat.zero_lt_of_lt k.isLt) Nat.zero_lt_one
  · have hdegree := Lagrange.degree_basis hd.injOn (Finset.mem_univ k)
    rw [hdegree, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast Nat.sub_lt (Nat.zero_lt_of_lt k.isLt) Nat.zero_lt_one
  · intro l _hl
    by_cases hlk : l = k
    · subst l
      rw [finiteRootBasis_eval_self hd]
      exact (Lagrange.eval_basis_self hd.injOn (Finset.mem_univ k)).symm
    · rw [finiteRootBasis_eval_of_ne k l hlk]
      exact (Lagrange.eval_basis_of_ne (Ne.symm hlk) (Finset.mem_univ l)).symm

lemma finiteRootBasis_wronskian {m : ℕ} (d : Fin m → ℝ)
    (scale : ℝ) (k : Fin m) (x : ℝ) :
    ((finiteRootProduct d * C scale).eval x *
        (finiteRootBasis d k).derivative.eval x -
      (finiteRootProduct d * C scale).derivative.eval x *
        (finiteRootBasis d k).eval x) =
      -(scale * ((finiteRootComplement d k).eval (d k))⁻¹) *
        ((finiteRootComplement d k).eval x) ^ 2 := by
  rw [finiteRootProduct_eq_mul_complement d k]
  simp only [finiteRootBasis, Polynomial.derivative_mul,
    Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
    sub_zero, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_zero,
    Polynomial.eval_one]
  ring

lemma finiteRootScaledBasis_wronskian {m : ℕ}
    (d : Fin m → ℝ) (scale value : ℝ) (k : Fin m) (x : ℝ) :
    ((finiteRootProduct d * C scale).eval x *
        (C value * finiteRootBasis d k).derivative.eval x -
      (finiteRootProduct d * C scale).derivative.eval x *
        (C value * finiteRootBasis d k).eval x) =
      -(value * scale *
          ((finiteRootComplement d k).eval (d k))⁻¹) *
        ((finiteRootComplement d k).eval x) ^ 2 := by
  have hbase := finiteRootBasis_wronskian d scale k x
  calc
    (finiteRootProduct d * C scale).eval x *
          (C value * finiteRootBasis d k).derivative.eval x -
        (finiteRootProduct d * C scale).derivative.eval x *
          (C value * finiteRootBasis d k).eval x =
        value * ((finiteRootProduct d * C scale).eval x *
          (finiteRootBasis d k).derivative.eval x -
        (finiteRootProduct d * C scale).derivative.eval x *
          (finiteRootBasis d k).eval x) := by
            simp only [Polynomial.derivative_mul, Polynomial.derivative_C,
              zero_mul, zero_add, Polynomial.eval_mul, Polynomial.eval_C]
            ring
    _ = value * (-(scale *
          ((finiteRootComplement d k).eval (d k))⁻¹) *
        ((finiteRootComplement d k).eval x) ^ 2) := by rw [hbase]
    _ = -(value * scale *
          ((finiteRootComplement d k).eval (d k))⁻¹) *
        ((finiteRootComplement d k).eval x) ^ 2 := by ring

def finiteRootInterpolant {m : ℕ} (d : Fin m → ℝ)
    (S : ℝ[X]) : ℝ[X] :=
  ∑ k : Fin m, C (S.eval (d k)) * finiteRootBasis d k

lemma finiteRootInterpolant_eq_lagrange {m : ℕ}
    {d : Fin m → ℝ} (hd : Function.Injective d) (S : ℝ[X]) :
    finiteRootInterpolant d S =
      Lagrange.interpolate Finset.univ d (fun k => S.eval (d k)) := by
  classical
  rw [finiteRootInterpolant, Lagrange.interpolate_apply]
  simp only [finiteRootBasis_eq_lagrangeBasis hd]

lemma finiteRootInterpolant_degree_lt {m : ℕ}
    {d : Fin m → ℝ} (hd : Function.Injective d) (S : ℝ[X]) :
    (finiteRootInterpolant d S).degree < m := by
  rw [finiteRootInterpolant_eq_lagrange hd]
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Lagrange.degree_interpolate_lt (s := Finset.univ) (v := d)
      (fun k => S.eval (d k)) hd.injOn

lemma finiteRootInterpolant_eval_root {m : ℕ}
    {d : Fin m → ℝ} (hd : Function.Injective d) (S : ℝ[X])
    (k : Fin m) :
    (finiteRootInterpolant d S).eval (d k) = S.eval (d k) := by
  rw [finiteRootInterpolant_eq_lagrange hd]
  exact Lagrange.eval_interpolate_at_node _ hd.injOn (Finset.mem_univ k)

lemma exists_finiteRootComplement_eval_ne_zero {m : ℕ}
    (hm : 0 < m) {d : Fin m → ℝ} (hd : Function.Injective d) (x : ℝ) :
    ∃ k : Fin m, (finiteRootComplement d k).eval x ≠ 0 := by
  classical
  by_cases hx : ∃ k : Fin m, x = d k
  · obtain ⟨k, rfl⟩ := hx
    exact ⟨k, finiteRootComplement_eval_self_ne_zero hd k⟩
  · let k : Fin m := ⟨0, hm⟩
    refine ⟨k, ?_⟩
    simp only [finiteRootComplement, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro l _hl
    exact sub_ne_zero.mpr (fun heq => hx ⟨l, heq⟩)

/-- Finite V. A. Markov specialization in the form actually consumed below.
The proof is Lagrange interpolation modulo the exhaustive root product.
Every residue contributes a negative square, and at least one complementary
root product is nonzero at each real point. -/
theorem finite_markov_wronskian_neg {m : ℕ} (hm : 0 < m)
    (d : Fin m → ℝ) (hd : Function.Injective d) (scale : ℝ)
    (hscale : scale ≠ 0) (S : ℝ[X]) (hSdegree : S.natDegree ≤ m)
    (hresidue : ∀ k : Fin m,
      0 < S.eval (d k) *
        (finiteRootProduct d * C scale).derivative.eval (d k))
    (x : ℝ) :
    (finiteRootProduct d * C scale).eval x * S.derivative.eval x -
      (finiteRootProduct d * C scale).derivative.eval x * S.eval x < 0 := by
  classical
  let M : ℝ[X] := finiteRootProduct d
  let D : ℝ[X] := M * C scale
  let R : ℝ[X] := finiteRootInterpolant d S
  have hMmonic : M.Monic := by
    change (∏ k ∈ (Finset.univ : Finset (Fin m)), (X - C (d k))).Monic
    exact monic_prod_of_monic _ _ fun k _hk => monic_X_sub_C (d k)
  have hMne : M ≠ 0 := hMmonic.ne_zero
  have hMdegree : M.natDegree = m := by
    change (∏ k ∈ (Finset.univ : Finset (Fin m)),
      (X - C (d k))).natDegree = m
    rw [natDegree_finset_prod_X_sub_C_eq_card, Finset.card_univ,
      Fintype.card_fin]
  have hRdegree : R.degree < m := by
    simpa only [R] using finiteRootInterpolant_degree_lt hd S
  have hRnatDegree : R.natDegree ≤ m := by
    rw [Polynomial.natDegree_le_iff_degree_le]
    exact hRdegree.le
  have hMdvd : M ∣ S - R := by
    change (∏ k : Fin m, (X - C (d k))) ∣ S - R
    apply Fintype.prod_dvd_of_coprime
    · exact pairwise_coprime_X_sub_C hd
    · intro k
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot,
        Polynomial.eval_sub]
      change S.eval (d k) - (finiteRootInterpolant d S).eval (d k) = 0
      rw [finiteRootInterpolant_eval_root hd S k, sub_self]
  obtain ⟨Q, hQ⟩ := hMdvd
  have hSRdegree : (S - R).natDegree ≤ m :=
    (Polynomial.natDegree_sub_le S R).trans (max_le hSdegree hRnatDegree)
  have hQdegree : Q.natDegree = 0 := by
    by_cases hQzero : Q = 0
    · simp [hQzero]
    · have hproduct : (M * Q).natDegree ≤ m := by
        rw [← hQ]
        exact hSRdegree
      rw [Polynomial.natDegree_mul hMne hQzero, hMdegree] at hproduct
      omega
  obtain ⟨q, hq⟩ := Polynomial.natDegree_eq_zero.mp hQdegree
  have hSfactor : S = R + M * C q := by
    rw [← hq] at hQ
    calc
      S = (S - R) + R := by ring
      _ = M * C q + R := by rw [hQ]
      _ = R + M * C q := by ring
  have hWinvariant :
      D.eval x * S.derivative.eval x - D.derivative.eval x * S.eval x =
        D.eval x * R.derivative.eval x - D.derivative.eval x * R.eval x := by
    rw [hSfactor]
    dsimp only [D]
    simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
      Polynomial.derivative_C, mul_zero, add_zero,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    ring
  let coefficient : Fin m → ℝ := fun k =>
    S.eval (d k) * scale *
      ((finiteRootComplement d k).eval (d k))⁻¹
  have hcoefficient : ∀ k : Fin m, 0 < coefficient k := by
    intro k
    let e : ℝ := (finiteRootComplement d k).eval (d k)
    have he : e ≠ 0 := finiteRootComplement_eval_self_ne_zero hd k
    have hderivative : D.derivative.eval (d k) = e * scale := by
      simp only [D, M, Polynomial.derivative_mul, Polynomial.derivative_C,
        mul_zero, add_zero, Polynomial.eval_mul, Polynomial.eval_C]
      rw [finiteRootProduct_derivative_eval_root]
    have hpositive : 0 < S.eval (d k) * (e * scale) := by
      rw [← hderivative]
      simpa only [D, M] using hresidue k
    have he2 : 0 < e ^ 2 := sq_pos_of_ne_zero he
    have heq : coefficient k * e ^ 2 = S.eval (d k) * (e * scale) := by
      dsimp only [coefficient, e]
      field_simp
    nlinarith
  have hWsum :
      D.eval x * R.derivative.eval x - D.derivative.eval x * R.eval x =
        -∑ k : Fin m, coefficient k *
          ((finiteRootComplement d k).eval x) ^ 2 := by
    simp only [R, finiteRootInterpolant, Polynomial.derivative_sum,
      Polynomial.eval_finset_sum]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    rw [finiteRootScaledBasis_wronskian]
    simp only [coefficient]
    ring
  have hsumPos : 0 < ∑ k : Fin m, coefficient k *
      ((finiteRootComplement d k).eval x) ^ 2 := by
    apply Finset.sum_pos'
    · intro k _hk
      exact mul_nonneg (hcoefficient k).le (sq_nonneg _)
    · obtain ⟨k, hk⟩ := exists_finiteRootComplement_eval_ne_zero hm hd x
      exact ⟨k, Finset.mem_univ k,
        mul_pos (hcoefficient k) (sq_pos_of_ne_zero hk)⟩
  rw [hWinvariant, hWsum]
  exact neg_neg_of_pos hsumPos

end

end UnitCircleInterpolation
