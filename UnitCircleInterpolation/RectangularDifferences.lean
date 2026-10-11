/-
Unit-circle project integration and adaptations: wang060919.
Developed with Codex assistance. Original authors and MIT notices are retained below.
-/

/-
Copyright (c) 2026 Ethan Yang
Copyright (c) 2026 randyxian08 (free-node extension and repairs)

Adapted from randyxian08/jsp000936-lean, commit
0ced15a2630c5c68b23de896d7e6ad1e7cfeda01,
Erdos1153/DeBoorPinkus/Minors.lean, cofactor and adjacent-difference kernels (lines 970–1008 and 1216–1308):
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


import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Cofactors and adjacent differences of a rectangular real matrix

These are finite linear-algebra statements. The final application must prove
that the actual cofactor vector has a common strict sign; bare nonzero deleted
minors alone do not imply invertibility of adjacent row differences.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Matrix

namespace UnitCircleInterpolation

noncomputable section

variable {d : ℕ}

def rectangularCofactor (M : Matrix (Fin (d + 1)) (Fin d) ℝ) (i : Fin (d + 1)) : ℝ :=
  (-1 : ℝ) ^ i.val * (M.submatrix i.succAbove id).det

/-- The signed deleted determinants form a literal left relation of every
rectangular matrix, by expansion of a duplicated-column square matrix. -/
lemma rectangularCofactor_left_relation (M : Matrix (Fin (d + 1)) (Fin d) ℝ) :
    rectangularCofactor M ᵥ* M = 0 := by
  classical
  funext j
  let A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
    fun i k => Fin.cases (M i j) (fun k' => M i k') k
  have hcols : ∀ i, A i 0 = A i j.succ := by simp [A]
  have hne : (0 : Fin (d + 1)) ≠ j.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_succ] at hv
    omega
  have hdet : A.det = 0 := Matrix.det_zero_of_column_eq hne hcols
  have hexpand := Matrix.det_succ_column A (0 : Fin (d + 1))
  rw [hdet] at hexpand
  have hminor (i : Fin (d + 1)) :
      (A.submatrix i.succAbove (0 : Fin (d + 1)).succAbove).det =
        (M.submatrix i.succAbove id).det := by
    congr 1
  simp only [Fin.val_zero, Nat.add_zero, A, Fin.cases_zero, hminor] at hexpand
  simpa [rectangularCofactor, Matrix.vecMul, dotProduct, mul_assoc,
    mul_left_comm, mul_comm] using hexpand.symm

lemma rectangularCofactor_ne_zero_of_first_minor
    (M : Matrix (Fin (d + 1)) (Fin d) ℝ)
    (hminor : (M.submatrix (0 : Fin (d + 1)).succAbove id).det ≠ 0) :
    rectangularCofactor M ≠ 0 := by
  intro hz
  have h := congrFun hz (0 : Fin (d + 1))
  simp only [rectangularCofactor, Fin.val_zero, pow_zero, one_mul, Pi.zero_apply] at h
  exact hminor h

def augmentedOnesMatrix (M : Matrix (Fin (d + 1)) (Fin d) ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i k => Fin.cases 1 (fun j => M i j) k

lemma augmentedOnesMatrix_det_eq_sum_cofactors
    (M : Matrix (Fin (d + 1)) (Fin d) ℝ) :
    (augmentedOnesMatrix M).det = ∑ i, rectangularCofactor M i := by
  have hexpand := Matrix.det_succ_column_zero (augmentedOnesMatrix M)
  have hminor (i : Fin (d + 1)) :
      ((augmentedOnesMatrix M).submatrix i.succAbove
        Fin.succ).det = (M.submatrix i.succAbove id).det := by
    congr 1
  simpa only [augmentedOnesMatrix, Fin.cases_zero, mul_one, hminor,
    rectangularCofactor] using hexpand

lemma augmentedOnesMatrix_det_ne_zero_of_coherent_cofactors
    (M : Matrix (Fin (d + 1)) (Fin d) ℝ)
    (hcoherent : (∀ i, 0 < rectangularCofactor M i) ∨
      (∀ i, rectangularCofactor M i < 0)) : (augmentedOnesMatrix M).det ≠ 0 := by
  rw [augmentedOnesMatrix_det_eq_sum_cofactors]
  rcases hcoherent with h | h
  · exact (Finset.sum_pos (fun i _ => h i) Finset.univ_nonempty).ne'
  · exact (Finset.sum_neg (fun i _ => h i) Finset.univ_nonempty).ne

def adjacentRowDifferenceMatrix (M : Matrix (Fin (d + 1)) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => M i.succ j - M i.castSucc j

/-- Consecutive differences are nonsingular when the augmented square matrix is. -/
theorem adjacentRowDifferenceMatrix_det_ne_zero_of_augmented
    (M : Matrix (Fin (d + 1)) (Fin d) ℝ)
    (haug : (augmentedOnesMatrix M).det ≠ 0) :
    (adjacentRowDifferenceMatrix M).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hvne, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let rowValue : Fin (d + 1) → ℝ := fun i => ∑ j, M i j * v j
  have hadj (i : Fin d) : rowValue i.succ = rowValue i.castSucc := by
    have hi := congrFun hv i
    simp only [adjacentRowDifferenceMatrix, Matrix.mulVec, dotProduct,
      Pi.zero_apply, rowValue] at hi ⊢
    simp_rw [sub_mul] at hi
    rw [Finset.sum_sub_distrib] at hi
    linarith
  have hconst (i : Fin (d + 1)) : rowValue i = rowValue 0 := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih => exact (hadj i).trans ih
  let w : Fin (d + 1) → ℝ := Fin.cases (-(rowValue 0)) v
  have hwne : w ≠ 0 := by
    intro hw
    apply hvne
    funext j
    have hj := congrFun hw j.succ
    simpa [w] using hj
  have hAw : (augmentedOnesMatrix M).mulVec w = 0 := by
    funext i
    rw [show (augmentedOnesMatrix M).mulVec w i = -(rowValue 0) + rowValue i by
      simp [Matrix.mulVec, dotProduct, augmentedOnesMatrix, w, Fin.sum_univ_succ, rowValue]]
    rw [hconst i]
    simp
  exact haug (Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hwne, hAw⟩)

/-- Common strict cofactor signs imply an invertible adjacent-difference matrix. -/
theorem adjacentRowDifferenceMatrix_det_ne_zero_of_coherent_cofactors
    (M : Matrix (Fin (d + 1)) (Fin d) ℝ)
    (hcoherent : (∀ i, 0 < rectangularCofactor M i) ∨
      (∀ i, rectangularCofactor M i < 0)) :
    (adjacentRowDifferenceMatrix M).det ≠ 0 :=
  adjacentRowDifferenceMatrix_det_ne_zero_of_augmented M
    (augmentedOnesMatrix_det_ne_zero_of_coherent_cofactors M hcoherent)

end

end UnitCircleInterpolation
