/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.CyclicRootCount
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Saturated finite root lists

The distinct-root bound alone does not assert simplicity. A list reaching the
degree bound exhausts the polynomial's roots with multiplicity; its roots are
therefore simple. This is the algebraic step needed by cyclic Rolle arguments.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Polynomial

namespace UnitCircleInterpolation

noncomputable section

lemma polynomial_roots_eq_of_saturated_roots {ι : Type*} [Fintype ι]
    (P : ℝ[X]) (hP : P ≠ 0) (root : ι → ℝ) (hinj : Function.Injective root)
    (hdegree : P.natDegree ≤ Fintype.card ι) (hroot : ∀ i, P.eval (root i) = 0) :
    P.roots = (Finset.univ.image root).val := by
  classical
  apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hroot i
  · simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ] using hdegree
  · exact hP

lemma polynomial_derivative_ne_zero_of_saturated_roots {ι : Type*} [Fintype ι]
    (P : ℝ[X]) (hP : P ≠ 0) (root : ι → ℝ) (hinj : Function.Injective root)
    (hdegree : P.natDegree ≤ Fintype.card ι) (hroot : ∀ i, P.eval (root i) = 0)
    (i : ι) : P.derivative.eval (root i) ≠ 0 := by
  classical
  intro hd
  have hmult : 1 < P.rootMultiplicity (root i) :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hP).mpr ⟨hroot i, hd⟩
  have hcount : P.roots.count (root i) ≤ 1 := by
    rw [polynomial_roots_eq_of_saturated_roots P hP root hinj hdegree hroot]
    exact Multiset.nodup_iff_count_le_one.mp (Finset.univ.image root).nodup (root i)
  rw [Polynomial.count_roots] at hcount
  omega

lemma polynomial_root_mem_of_saturated_roots {ι : Type*} [Fintype ι]
    (P : ℝ[X]) (hP : P ≠ 0) (root : ι → ℝ) (hinj : Function.Injective root)
    (hdegree : P.natDegree ≤ Fintype.card ι) (hroot : ∀ i, P.eval (root i) = 0)
    (x : ℝ) (hx : P.eval x = 0) : ∃ i, root i = x := by
  classical
  have hmem := (Polynomial.mem_roots hP).mpr hx
  rw [polynomial_roots_eq_of_saturated_roots P hP root hinj hdegree hroot] at hmem
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
  exact ⟨i, hi⟩

/-- A saturated circle-root list leaves no additional zero anywhere in the complete turn. -/
lemma cayley_chart_root_mem_of_saturated_roots (p : ℕ) (f : ℝ → ℝ) (P : ℝ[X])
    (hP : P ≠ 0) (hdegree : P.natDegree ≤ p)
    (hchart : ∀ t, Real.cos (t / 2) ≠ 0 →
      Real.cos (t / 2) ^ p * P.eval (Real.tan (t / 2)) = f t)
    (hpoleValue : P.coeff p = f Real.pi) (root : Fin p → ℝ)
    (hinj : Function.Injective root) (hbound : ∀ i, root i ∈ Set.Ico 0 (2 * Real.pi))
    (hroot : ∀ i, f (root i) = 0) (x : ℝ) (hx : x ∈ Set.Ico 0 (2 * Real.pi))
    (hz : f x = 0) : ∃ i, root i = x := by
  classical
  by_contra hmissing
  have hnot : x ∉ Set.range root := by
    rintro ⟨i, hi⟩
    exact hmissing ⟨i, hi⟩
  have hinj' := Fin.cons_injective_of_injective hnot hinj
  have hbound' : ∀ i : Fin (p + 1),
      Fin.cons (α := fun _ => ℝ) x root i ∈ Set.Ico 0 (2 * Real.pi) := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa only [Fin.cons_zero] using hx
    · intro j
      simpa only [Fin.cons_succ] using hbound j
  have hroot' : ∀ i : Fin (p + 1),
      f (Fin.cons (α := fun _ => ℝ) x root i) = 0 := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa only [Fin.cons_zero] using hz
    · intro j
      simpa only [Fin.cons_succ] using hroot j
  have hc := cayley_chart_distinct_root_count p f P hP hdegree hchart hpoleValue
    (Fin.cons x root) hinj' hbound' hroot'
  omega

end

end UnitCircleInterpolation
