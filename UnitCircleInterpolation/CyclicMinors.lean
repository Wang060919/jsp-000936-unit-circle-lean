/-
Unit-circle project integration and adaptations: wang060919.
Developed with Codex assistance. Original authors and MIT notices are retained below.
-/

/-
Copyright (c) 2026 Ethan Yang
Copyright (c) 2026 randyxian08 (free-node extension and repairs)

Adapted from randyxian08/jsp000936-lean, commit
0ced15a2630c5c68b23de896d7e6ad1e7cfeda01,
Erdos1153/DeBoorPinkus/Minors.lean, row-deleted evaluation-matrix kernel (lines 838–912):
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

import UnitCircleInterpolation.CyclicRelations
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Row-deleted circular families and their evaluation determinants

There are `d+1` full-circle functions with root bound `d-1`. Deleting any one
leaves `d` linearly independent functions. Evaluating that family at any `d`
distinct canonical circular angles gives a square matrix with nonzero determinant.

The peak checkerboard signs are literal hypotheses; no actual quotient sign
instance, Jacobian, or final minimizer assertion is claimed by this generic layer.
The homogeneous-space corollaries use the root bound already proved on the entire
circle, including the tangent-chart pole.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace UnitCircleInterpolation

noncomputable section

open Polynomial

variable {d : ℕ}

/-- In the generic circular space, a relation missing one coefficient is zero. -/
theorem cyclic_relation_eq_zero_of_missing_coeff (hd : 0 < d)
    (V : Submodule ℝ (ℝ → ℝ))
    (hcontinuous : ∀ f ∈ V, Continuous f)
    (hrootBound : HasCyclicRootBound (d - 1) V)
    (q : Fin (d + 1) → ℝ → ℝ) (hq : ∀ i, q i ∈ V)
    (τ : Fin (d + 1) → ℝ) (hτ : StrictMono τ)
    (hbound : ∀ i, τ i ∈ Set.Ico 0 (2 * Real.pi))
    (hdiag : ∀ i, q i (τ i) < 0)
    (hoff : ∀ i j, i ≠ j → 0 < (-1 : ℝ) ^ (i.val + j.val) * q i (τ j))
    (a : Fin (d + 1) → ℝ) (hrel : ∀ x, (∑ i, a i * q i x) = 0)
    (missing : Fin (d + 1)) (hmissing : a missing = 0) : a = 0 := by
  by_contra ha
  rcases cyclic_relation_coherent_sign hd V hcontinuous hrootBound q hq
      τ hτ hbound hdiag hoff a hrel ha with h | h
  · have := h missing
    simp [hmissing] at this
  · have := h missing
    simp [hmissing] at this

/-- Extending a deleted-family relation by zero in the missing slot makes every
coefficient zero. This is the finite-sum interface used by independence and minors. -/
theorem cyclic_deleted_relation_eq_zero (hd : 0 < d)
    (V : Submodule ℝ (ℝ → ℝ))
    (hcontinuous : ∀ f ∈ V, Continuous f)
    (hrootBound : HasCyclicRootBound (d - 1) V)
    (q : Fin (d + 1) → ℝ → ℝ) (hq : ∀ i, q i ∈ V)
    (τ : Fin (d + 1) → ℝ) (hτ : StrictMono τ)
    (hbound : ∀ i, τ i ∈ Set.Ico 0 (2 * Real.pi))
    (hdiag : ∀ i, q i (τ i) < 0)
    (hoff : ∀ i j, i ≠ j → 0 < (-1 : ℝ) ^ (i.val + j.val) * q i (τ j))
    (omitted : Fin (d + 1)) (c : Fin d → ℝ)
    (hrel : ∀ x, (∑ i, c i * q (omitted.succAbove i) x) = 0) : c = 0 := by
  classical
  let a : Fin (d + 1) → ℝ := Fin.succAboveCases (α := fun _ => ℝ) omitted 0 c
  have harel (x : ℝ) : (∑ i, a i * q i x) = 0 := by
    rw [Fin.sum_univ_succAbove (fun i => a i * q i x) omitted]
    simpa [a] using hrel x
  have hazero := cyclic_relation_eq_zero_of_missing_coeff hd V hcontinuous hrootBound
    q hq τ hτ hbound hdiag hoff a harel omitted (by simp [a])
  funext i
  have hi := congrFun hazero (omitted.succAbove i)
  simpa [a] using hi

/-- The `d` retained functions are linearly independent as functions on all angles. -/
theorem cyclic_deleted_linearIndependent (hd : 0 < d)
    (V : Submodule ℝ (ℝ → ℝ))
    (hcontinuous : ∀ f ∈ V, Continuous f)
    (hrootBound : HasCyclicRootBound (d - 1) V)
    (q : Fin (d + 1) → ℝ → ℝ) (hq : ∀ i, q i ∈ V)
    (τ : Fin (d + 1) → ℝ) (hτ : StrictMono τ)
    (hbound : ∀ i, τ i ∈ Set.Ico 0 (2 * Real.pi))
    (hdiag : ∀ i, q i (τ i) < 0)
    (hoff : ∀ i j, i ≠ j → 0 < (-1 : ℝ) ^ (i.val + j.val) * q i (τ j))
    (omitted : Fin (d + 1)) :
    LinearIndependent ℝ (fun i : Fin d => q (omitted.succAbove i)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hrel (x : ℝ) : (∑ k, c k * q (omitted.succAbove k) x) = 0 := by
    have hx := congrFun hc x
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hx
  exact congrFun (cyclic_deleted_relation_eq_zero hd V hcontinuous hrootBound q hq
    τ hτ hbound hdiag hoff omitted c hrel) i

/-- `d` distinct canonical evaluation zeros already force a deleted relation to be zero. -/
theorem cyclic_deleted_evaluation_relation_eq_zero (hd : 0 < d)
    (V : Submodule ℝ (ℝ → ℝ))
    (hcontinuous : ∀ f ∈ V, Continuous f)
    (hrootBound : HasCyclicRootBound (d - 1) V)
    (q : Fin (d + 1) → ℝ → ℝ) (hq : ∀ i, q i ∈ V)
    (τ : Fin (d + 1) → ℝ) (hτ : StrictMono τ)
    (hbound : ∀ i, τ i ∈ Set.Ico 0 (2 * Real.pi))
    (hdiag : ∀ i, q i (τ i) < 0)
    (hoff : ∀ i j, i ≠ j → 0 < (-1 : ℝ) ^ (i.val + j.val) * q i (τ j))
    (omitted : Fin (d + 1)) (x : Fin d → ℝ) (hxinj : Function.Injective x)
    (hxbound : ∀ j, x j ∈ Set.Ico 0 (2 * Real.pi)) (c : Fin d → ℝ)
    (hrel : ∀ j, (∑ i, c i * q (omitted.succAbove i) (x j)) = 0) : c = 0 := by
  classical
  let f : ℝ → ℝ := ∑ i, c i • q (omitted.succAbove i)
  have hfmem : f ∈ V := V.sum_mem (fun i hi => V.smul_mem _ (hq _))
  have hfzero : f = 0 := by
    by_contra hne
    have hfroot (j : Fin d) : f (x j) = 0 := by
      simpa only [f, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hrel j
    have hcount := hrootBound d f hfmem hne x hxinj hxbound hfroot
    omega
  have hfullrel (t : ℝ) : (∑ i, c i * q (omitted.succAbove i) t) = 0 := by
    have ht := congrFun hfzero t
    simpa only [f, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using ht
  exact cyclic_deleted_relation_eq_zero hd V hcontinuous hrootBound q hq
    τ hτ hbound hdiag hoff omitted c hfullrel

/-- Transpose-oriented evaluation: rows are `d` evaluation angles and columns are
`d` retained members of a family of `d+1` functions. -/
def cyclicDeletedEvaluationMatrix (q : Fin (d + 1) → ℝ → ℝ)
    (omitted : Fin (d + 1)) (x : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun j i => q (omitted.succAbove i) (x j)

/-- Any distinct `d` canonical angles yield a nonsingular square evaluation matrix. -/
theorem cyclicDeletedEvaluationMatrix_det_ne_zero (hd : 0 < d)
    (V : Submodule ℝ (ℝ → ℝ))
    (hcontinuous : ∀ f ∈ V, Continuous f)
    (hrootBound : HasCyclicRootBound (d - 1) V)
    (q : Fin (d + 1) → ℝ → ℝ) (hq : ∀ i, q i ∈ V)
    (τ : Fin (d + 1) → ℝ) (hτ : StrictMono τ)
    (hbound : ∀ i, τ i ∈ Set.Ico 0 (2 * Real.pi))
    (hdiag : ∀ i, q i (τ i) < 0)
    (hoff : ∀ i j, i ≠ j → 0 < (-1 : ℝ) ^ (i.val + j.val) * q i (τ j))
    (omitted : Fin (d + 1)) (x : Fin d → ℝ) (hxinj : Function.Injective x)
    (hxbound : ∀ j, x j ∈ Set.Ico 0 (2 * Real.pi)) :
    (cyclicDeletedEvaluationMatrix q omitted x).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨c, hcne, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hrel (j : Fin d) : (∑ i, c i * q (omitted.succAbove i) (x j)) = 0 := by
    have hj := congrFun hc j
    simp only [cyclicDeletedEvaluationMatrix, Matrix.mulVec, dotProduct, Pi.zero_apply] at hj
    simpa only [mul_comm] using hj
  exact hcne (cyclic_deleted_evaluation_relation_eq_zero hd V hcontinuous hrootBound
    q hq τ hτ hbound hdiag hoff omitted x hxinj hxbound c hrel)

/-- The `(d+1)×d` matrix in physical row convention. -/
def cyclicEvaluationMatrix (q : Fin (d + 1) → ℝ → ℝ) (x : Fin d → ℝ) :
    Matrix (Fin (d + 1)) (Fin d) ℝ := fun i j => q i (x j)

lemma cyclicDeletedEvaluationMatrix_transpose (q : Fin (d + 1) → ℝ → ℝ)
    (omitted : Fin (d + 1)) (x : Fin d → ℝ) :
    (cyclicDeletedEvaluationMatrix q omitted x).transpose =
      (cyclicEvaluationMatrix q x).submatrix omitted.succAbove id := by
  rfl

/-- The determinant conclusion also holds in physical row convention. -/
theorem cyclicEvaluationMatrix_deleted_row_det_ne_zero (hd : 0 < d)
    (V : Submodule ℝ (ℝ → ℝ))
    (hcontinuous : ∀ f ∈ V, Continuous f)
    (hrootBound : HasCyclicRootBound (d - 1) V)
    (q : Fin (d + 1) → ℝ → ℝ) (hq : ∀ i, q i ∈ V)
    (τ : Fin (d + 1) → ℝ) (hτ : StrictMono τ)
    (hbound : ∀ i, τ i ∈ Set.Ico 0 (2 * Real.pi))
    (hdiag : ∀ i, q i (τ i) < 0)
    (hoff : ∀ i j, i ≠ j → 0 < (-1 : ℝ) ^ (i.val + j.val) * q i (τ j))
    (omitted : Fin (d + 1)) (x : Fin d → ℝ) (hxinj : Function.Injective x)
    (hxbound : ∀ j, x j ∈ Set.Ico 0 (2 * Real.pi)) :
    ((cyclicEvaluationMatrix q x).submatrix omitted.succAbove id).det ≠ 0 := by
  rw [← cyclicDeletedEvaluationMatrix_transpose, Matrix.det_transpose]
  exact cyclicDeletedEvaluationMatrix_det_ne_zero hd V hcontinuous hrootBound
    q hq τ hτ hbound hdiag hoff omitted x hxinj hxbound

/-- The actual homogeneous-degree space gives row-deleted functional independence. -/
theorem homogeneousTrig_deleted_linearIndependent (hd : 0 < d)
    (P : Fin (d + 1) → ℝ[X]) (hdegree : ∀ i, (P i).natDegree ≤ d - 1)
    (τ : Fin (d + 1) → ℝ) (hτ : StrictMono τ)
    (hbound : ∀ i, τ i ∈ Set.Ico 0 (2 * Real.pi))
    (hdiag : ∀ i, homogeneousTrig (d - 1) (P i) (τ i) < 0)
    (hoff : ∀ i j, i ≠ j → 0 < (-1 : ℝ) ^ (i.val + j.val) *
      homogeneousTrig (d - 1) (P i) (τ j)) (omitted : Fin (d + 1)) :
    LinearIndependent ℝ (fun i : Fin d => homogeneousTrig (d - 1) (P (omitted.succAbove i))) := by
  exact cyclic_deleted_linearIndependent hd (homogeneousTrigSpace (d - 1))
    (continuous_of_mem_homogeneousTrigSpace (d - 1))
    (homogeneousTrigSpace_hasCyclicRootBound (d - 1))
    (fun i => homogeneousTrig (d - 1) (P i))
    (fun i => homogeneousTrig_mem_space (d - 1) (P i) (hdegree i))
    τ hτ hbound hdiag hoff omitted

/-- The actual homogeneous-degree instance has nonsingular deleted evaluation matrices. -/
theorem homogeneousTrig_deleted_evaluation_det_ne_zero (hd : 0 < d)
    (P : Fin (d + 1) → ℝ[X]) (hdegree : ∀ i, (P i).natDegree ≤ d - 1)
    (τ : Fin (d + 1) → ℝ) (hτ : StrictMono τ)
    (hbound : ∀ i, τ i ∈ Set.Ico 0 (2 * Real.pi))
    (hdiag : ∀ i, homogeneousTrig (d - 1) (P i) (τ i) < 0)
    (hoff : ∀ i j, i ≠ j → 0 < (-1 : ℝ) ^ (i.val + j.val) *
      homogeneousTrig (d - 1) (P i) (τ j)) (omitted : Fin (d + 1))
    (x : Fin d → ℝ) (hxinj : Function.Injective x)
    (hxbound : ∀ j, x j ∈ Set.Ico 0 (2 * Real.pi)) :
    (cyclicDeletedEvaluationMatrix (fun i => homogeneousTrig (d - 1) (P i)) omitted x).det ≠ 0 := by
  exact cyclicDeletedEvaluationMatrix_det_ne_zero hd (homogeneousTrigSpace (d - 1))
    (continuous_of_mem_homogeneousTrigSpace (d - 1))
    (homogeneousTrigSpace_hasCyclicRootBound (d - 1))
    (fun i => homogeneousTrig (d - 1) (P i))
    (fun i => homogeneousTrig_mem_space (d - 1) (P i) (hdegree i))
    τ hτ hbound hdiag hoff omitted x hxinj hxbound

end

end UnitCircleInterpolation
