/-
Unit-circle project integration and adaptations: wang060919.
Developed with Codex assistance. Original authors and MIT notices are retained below.
-/

/-
Copyright (c) 2026 Ethan Yang
Copyright (c) 2026 randyxian08 (free-node extension and repairs)

The diagonal determinant calculation is adapted from
randyxian08/jsp000936-lean, commit 0ced15a2630c5c68b23de896d7e6ad1e7cfeda01,
Erdos1153/DeBoorPinkus/Jacobian.lean, lines 297–315:
https://github.com/randyxian08/jsp000936-lean/blob/0ced15a2630c5c68b23de896d7e6ad1e7cfeda01/Erdos1153/DeBoorPinkus/Jacobian.lean
Original file SHA256: 081a8a26cf99643afa728c2cd560b1bee6cd9b1b912c0534376a0b00deceff08
Original Git blob: 85d4db52973b3b3e6a7c49ad60c70cc4ea3a4c05

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

import UnitCircleInterpolation.ActualCyclicKernel

/-!
# Nonzero minors of the actual node-sensitivity matrix at the gap peaks

The matrix entries are the literal expressions `-F_i′(θ_j) S_j(τ_i)` with
the anchored node held fixed. A sine-product identity factors them into the
already-proved actual quotient evaluation matrix and nonzero diagonal factors.
This file does not yet identify this matrix with the derivative of the height
map: that identification also requires smoothness of the actual moving peak.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace UnitCircleInterpolation

noncomputable section

variable {d : ℕ} {hn : 0 < d + 1}

def peakSensitivityRowFactor (angles : CyclicAngles (d + 1) hn)
    (hsize : 2 ≤ d + 1) (i : Fin (d + 1)) : ℝ :=
  ∏ k, Real.sin ((orderedPeak angles hsize i - angles.angle k) / 2)

def peakSensitivityColumnFactor (angles : CyclicAngles (d + 1) hn) (j : Fin d) : ℝ :=
  (∏ k ∈ Finset.univ.erase j.succ, Real.sin ((angles.angle j.succ - angles.angle k) / 2))⁻¹

def peakQuotientNodeMatrix (angles : CyclicAngles (d + 1) hn)
    (hsize : 2 ≤ d + 1) : Matrix (Fin (d + 1)) (Fin d) ℝ :=
  fun i j => orderedPeakQuotient angles hsize i (angles.angle j.succ)

def peakSensitivityMatrix (angles : CyclicAngles (d + 1) hn)
    (hsize : 2 ≤ d + 1) : Matrix (Fin (d + 1)) (Fin d) ℝ :=
  fun i j => -deriv (orderedGapInterpolant angles i) (angles.angle j.succ) *
    sineCardinal angles.angle j.succ (orderedPeak angles hsize i)

lemma sin_orderedPeak_sub_node_ne_zero (angles : CyclicAngles (d + 1) hn)
    (hsize : 2 ≤ d + 1) (i k : Fin (d + 1)) :
    Real.sin ((orderedPeak angles hsize i - angles.angle k) / 2) ≠ 0 := by
  have hpeak := gapPeak_mem_Ioo angles hsize (physicalGapCut hn i)
  by_cases hcut : (physicalGapCut hn i).val = 0
  · have hwrap : orderedPeak angles hsize i ∈ wrapGap angles := by
      exact (gapInterval_of_zero angles _ hcut) ▸ hpeak
    exact (sin_numerator_pos_on_wrapGap angles hwrap k).ne'
  · have hc : 0 < (physicalGapCut hn i).val := Nat.pos_of_ne_zero hcut
    have hord : orderedPeak angles hsize i ∈ ordinaryGap angles (physicalGapCut hn i) hc := by
      exact (gapInterval_of_pos angles _ hc) ▸ hpeak
    exact sin_numerator_ne_zero_on_gap angles _ hc hord k

lemma peakSensitivityRowFactor_ne_zero (angles : CyclicAngles (d + 1) hn)
    (hsize : 2 ≤ d + 1) (i : Fin (d + 1)) :
    peakSensitivityRowFactor angles hsize i ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun k _ => sin_orderedPeak_sub_node_ne_zero angles hsize i k)

lemma peakSensitivityColumnFactor_ne_zero (angles : CyclicAngles (d + 1) hn) (j : Fin d) :
    peakSensitivityColumnFactor angles j ≠ 0 := by
  apply inv_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact sine_denominator_ne_zero angles.angle angles.phaseNodes_injective
    (Finset.mem_erase.mp hk).1.symm

lemma peakSensitivityMatrix_apply_factorization (angles : CyclicAngles (d + 1) hn)
    (hsize : 2 ≤ d + 1) (i : Fin (d + 1)) (j : Fin d) :
    peakSensitivityMatrix angles hsize i j = peakSensitivityRowFactor angles hsize i *
      peakQuotientNodeMatrix angles hsize i j * peakSensitivityColumnFactor angles j := by
  classical
  unfold peakSensitivityMatrix peakQuotientNodeMatrix peakSensitivityColumnFactor
  rw [deriv_orderedGapInterpolant_sine_factor angles hsize i]
  rw [show (angles.angle j.succ - orderedPeak angles hsize i) / 2 =
    -((orderedPeak angles hsize i - angles.angle j.succ) / 2) by ring, Real.sin_neg]
  unfold sineCardinal
  rw [Finset.prod_div_distrib]
  unfold peakSensitivityRowFactor
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin (d + 1)))
    (fun k => Real.sin ((orderedPeak angles hsize i - angles.angle k) / 2))
    (Finset.mem_univ j.succ)]
  ring

lemma peakSensitivityMatrix_factorization (angles : CyclicAngles (d + 1) hn)
    (hsize : 2 ≤ d + 1) :
    peakSensitivityMatrix angles hsize = Matrix.diagonal (peakSensitivityRowFactor angles hsize) *
      peakQuotientNodeMatrix angles hsize * Matrix.diagonal (peakSensitivityColumnFactor angles) := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  exact peakSensitivityMatrix_apply_factorization angles hsize i j

theorem peakQuotientNodeMatrix_deleted_det_ne_zero (angles : CyclicAngles (d + 1) hn)
    (hsize : 2 ≤ d + 1) (omitted : Fin (d + 1)) :
    ((peakQuotientNodeMatrix angles hsize).submatrix omitted.succAbove id).det ≠ 0 := by
  exact actualPeakQuotient_deleted_evaluation_det_ne_zero angles hsize omitted
    (fun j => angles.angle j.succ)
    (angles.strictMono.injective.comp (Fin.succ_injective d))
    (fun j => ⟨angles.nonneg j.succ, angles.lt_two_pi j.succ⟩)

/-- Each actual sensitivity minor is its actual quotient minor times nonzero factors. -/
theorem peakSensitivityMatrix_deleted_det_factorization (angles : CyclicAngles (d + 1) hn)
    (hsize : 2 ≤ d + 1) (omitted : Fin (d + 1)) :
    ((peakSensitivityMatrix angles hsize).submatrix omitted.succAbove id).det =
      (∏ i : Fin d, peakSensitivityRowFactor angles hsize (omitted.succAbove i)) *
        ((peakQuotientNodeMatrix angles hsize).submatrix omitted.succAbove id).det *
          ∏ j : Fin d, peakSensitivityColumnFactor angles j := by
  let R : Matrix (Fin d) (Fin d) ℝ :=
    Matrix.diagonal (fun i => peakSensitivityRowFactor angles hsize (omitted.succAbove i))
  let Q : Matrix (Fin d) (Fin d) ℝ :=
    (peakQuotientNodeMatrix angles hsize).submatrix omitted.succAbove id
  let C : Matrix (Fin d) (Fin d) ℝ := Matrix.diagonal (peakSensitivityColumnFactor angles)
  have hmatrix : (peakSensitivityMatrix angles hsize).submatrix omitted.succAbove id =
      R * Q * C := by
    ext i j
    simp only [R, Q, C, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.submatrix_apply,
      id_eq]
    exact peakSensitivityMatrix_apply_factorization angles hsize _ _
  rw [hmatrix, Matrix.det_mul, Matrix.det_mul]
  simp only [R, Q, C, Matrix.det_diagonal]

/-- All maximal minors of the literal actual node-sensitivity matrix are nonzero. -/
theorem peakSensitivityMatrix_deleted_det_ne_zero (angles : CyclicAngles (d + 1) hn)
    (hsize : 2 ≤ d + 1) (omitted : Fin (d + 1)) :
    ((peakSensitivityMatrix angles hsize).submatrix omitted.succAbove id).det ≠ 0 := by
  rw [peakSensitivityMatrix_deleted_det_factorization]
  apply mul_ne_zero
  · exact mul_ne_zero
      (Finset.prod_ne_zero_iff.mpr (fun i _ => peakSensitivityRowFactor_ne_zero angles hsize _))
      (peakQuotientNodeMatrix_deleted_det_ne_zero angles hsize omitted)
  · exact Finset.prod_ne_zero_iff.mpr (fun j _ => peakSensitivityColumnFactor_ne_zero angles j)

end

end UnitCircleInterpolation
