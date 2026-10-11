/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.CircularSimpleRoots
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue

/-!
# Derivative signs from actual samples between simple roots

A zero-free interval propagates the sign of a sample back to a simple endpoint
root. The derivative sign follows from the one-sided slope limit, rather than
from an assumed orientation. The final lemma applies this to the already proved
exhaustion and simplicity of saturated sine-interpolant roots.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped Topology

namespace UnitCircleInterpolation

noncomputable section

lemma positive_on_right_of_zero_free (f : ℝ → ℝ) {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hnozero : ∀ t ∈ Set.Ioo a b, f t ≠ 0) (hb : 0 < f b)
    {t : ℝ} (ht : t ∈ Set.Ioo a b) : 0 < f t := by
  by_contra hpos
  have hnonpos : f t ≤ 0 := le_of_not_gt hpos
  obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc ht.2.le
    (hf.mono (by intro x hx; exact ⟨ht.1.le.trans hx.1, hx.2⟩))
    (show (0 : ℝ) ∈ Set.Icc (f t) (f b) from ⟨hnonpos, hb.le⟩)
  have hub : u < b := lt_of_le_of_ne hu.2 (by
    intro heq
    rw [heq] at hfu
    exact hb.ne' hfu)
  exact hnozero u ⟨ht.1.trans_le hu.1, hub⟩ hfu

lemma hasDerivAt_pos_of_zero_free_right (f : ℝ → ℝ) {a b d : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
    (ha : f a = 0) (hd : HasDerivAt f d a) (hdne : d ≠ 0)
    (hnozero : ∀ t ∈ Set.Ioo a b, f t ≠ 0) (hb : 0 < f b) : 0 < d := by
  have hnear : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0), h < b - a :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by linarith : (0 : ℝ) < b - a))
  have hdnonneg : 0 ≤ d := by
    apply ge_of_tendsto hd.tendsto_slope_zero_right
    filter_upwards [self_mem_nhdsWithin, hnear] with h hh hsmall
    change 0 < h at hh
    have hsample : 0 < f (a + h) :=
      positive_on_right_of_zero_free f hf hnozero hb ⟨by linarith, by linarith⟩
    simp only [ha, sub_zero, smul_eq_mul]
    exact (mul_pos (inv_pos.mpr hh) hsample).le
  exact lt_of_le_of_ne hdnonneg hdne.symm

/-- The sign at a zero-free right sample determines the simple root's orientation. -/
lemma hasDerivAt_mul_sample_pos_of_zero_free_right (f : ℝ → ℝ) {a b d : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
    (ha : f a = 0) (hd : HasDerivAt f d a) (hdne : d ≠ 0)
    (hnozero : ∀ t ∈ Set.Ioc a b, f t ≠ 0) : 0 < d * f b := by
  have hbnz := hnozero b ⟨hab, le_rfl⟩
  rcases lt_or_gt_of_ne hbnz with hbneg | hbpos
  · have hderivneg : 0 < -d :=
      hasDerivAt_pos_of_zero_free_right (fun t => -f t) hab hf.neg
        (by simp [ha]) hd.neg (neg_ne_zero.mpr hdne)
        (fun t ht => neg_ne_zero.mpr (hnozero t ⟨ht.1, ht.2.le⟩)) (by linarith)
    have hprod := mul_pos hderivneg (neg_pos.mpr hbneg)
    simpa using hprod
  · exact mul_pos (hasDerivAt_pos_of_zero_free_right f hab hf ha hd hdne
      (fun t ht => hnozero t ⟨ht.1, ht.2.le⟩) hbpos) hbpos

/-- A left sample gives the opposite orientation at a simple right endpoint root. -/
lemma hasDerivAt_mul_sample_neg_of_zero_free_left (f : ℝ → ℝ) {a b d : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
    (hb : f b = 0) (hd : HasDerivAt f d b) (hdne : d ≠ 0)
    (hnozero : ∀ t ∈ Set.Ico a b, f t ≠ 0) : d * f a < 0 := by
  have hcomp : HasDerivAt (fun t => f (-t)) (-d) (-b) := by
    have hd' : HasDerivAt f d (-(-b)) := by simpa only [neg_neg] using hd
    have h := hd'.comp (-b) (hasDerivAt_neg (-b))
    simpa only [neg_neg, Function.comp_def, mul_neg_one] using h
  have hcontinuous : ContinuousOn (fun t => f (-t)) (Set.Icc (-b) (-a)) :=
    hf.comp continuous_neg.continuousOn (by
      intro t ht
      constructor <;> linarith [ht.1, ht.2])
  have hp := hasDerivAt_mul_sample_pos_of_zero_free_right (fun t => f (-t))
    (show -b < -a by linarith) hcontinuous (by simpa using hb) hcomp
    (neg_ne_zero.mpr hdne) (by
      intro t ht
      apply hnozero (-t)
      constructor <;> linarith [ht.1, ht.2])
  simp only [neg_neg, neg_mul] at hp
  linarith

/-- With no zero between two simple endpoint roots, their derivatives have
opposite signs. This follows from one actual midpoint sample. -/
lemma endpoint_derivatives_mul_neg_of_zero_free (f : ℝ → ℝ) {a b da db : ℝ}
    (hab : a < b) (hf : Continuous f) (ha : f a = 0) (hb : f b = 0)
    (hda : HasDerivAt f da a) (hdb : HasDerivAt f db b)
    (hdane : da ≠ 0) (hdbne : db ≠ 0)
    (hnozero : ∀ t ∈ Set.Ioo a b, f t ≠ 0) : da * db < 0 := by
  let m : ℝ := (a + b) / 2
  have ham : a < m := by dsimp [m]; linarith
  have hmb : m < b := by dsimp [m]; linarith
  have hmne : f m ≠ 0 := hnozero m ⟨ham, hmb⟩
  have hleft := hasDerivAt_mul_sample_pos_of_zero_free_right f ham hf.continuousOn
    ha hda hdane (fun t ht => hnozero t ⟨ht.1, ht.2.trans_lt hmb⟩)
  have hright := hasDerivAt_mul_sample_neg_of_zero_free_left f hmb hf.continuousOn
    hb hdb hdbne (fun t ht => hnozero t ⟨ham.trans_le ht.1, ht.2⟩)
  have hprod : (da * f m) * (db * f m) < 0 :=
    mul_neg_of_pos_of_neg hleft hright
  have heq : (da * f m) * (db * f m) = (f m) ^ 2 * (da * db) := by ring
  rw [heq] at hprod
  have hsquare : 0 < (f m) ^ 2 := sq_pos_of_ne_zero hmne
  by_contra hneg
  exact (not_le_of_gt hprod) (mul_nonneg hsquare.le (le_of_not_gt hneg))

/-- Crossing exactly one simple interior root reverses the signs at two samples. -/
lemma sample_values_mul_neg_of_single_simple_root (f : ℝ → ℝ) {a r b d : ℝ}
    (har : a < r) (hrb : r < b) (hf : Continuous f) (hr : f r = 0)
    (hd : HasDerivAt f d r) (hdne : d ≠ 0)
    (hleft : ∀ t ∈ Set.Ico a r, f t ≠ 0)
    (hright : ∀ t ∈ Set.Ioc r b, f t ≠ 0) : f a * f b < 0 := by
  have hl := hasDerivAt_mul_sample_neg_of_zero_free_left f har hf.continuousOn
    hr hd hdne hleft
  have hr' := hasDerivAt_mul_sample_pos_of_zero_free_right f hrb hf.continuousOn
    hr hd hdne hright
  have hprod : (d * f a) * (d * f b) < 0 := mul_neg_of_neg_of_pos hl hr'
  have heq : (d * f a) * (d * f b) = d ^ 2 * (f a * f b) := by ring
  rw [heq] at hprod
  by_contra hneg
  exact (not_le_of_gt hprod) (mul_nonneg (sq_nonneg d) (le_of_not_gt hneg))

/-- Positive residues propagate across interlacing simple roots: both the first
function's endpoint derivatives and the second function's samples reverse sign. -/
lemma positive_residue_propagates_across_interlacing (D T : ℝ → ℝ)
    {a r b da dr db : ℝ} (har : a < r) (hrb : r < b)
    (hD : Continuous D) (hT : Continuous T) (hDa : D a = 0) (hDb : D b = 0)
    (hda : HasDerivAt D da a) (hdb : HasDerivAt D db b)
    (hdane : da ≠ 0) (hdbne : db ≠ 0)
    (hDnozero : ∀ t ∈ Set.Ioo a b, D t ≠ 0)
    (hTr : T r = 0) (hdr : HasDerivAt T dr r) (hdrne : dr ≠ 0)
    (hTleft : ∀ t ∈ Set.Ico a r, T t ≠ 0)
    (hTright : ∀ t ∈ Set.Ioc r b, T t ≠ 0)
    (hresidue : 0 < T a * da) : 0 < T b * db := by
  have hderiv := endpoint_derivatives_mul_neg_of_zero_free D (har.trans hrb) hD
    hDa hDb hda hdb hdane hdbne hDnozero
  have hsample := sample_values_mul_neg_of_single_simple_root T har hrb hT
    hTr hdr hdrne hTleft hTright
  have hp : 0 < (T a * T b) * (da * db) := mul_pos_of_neg_of_neg hsample hderiv
  have heq : (T a * T b) * (da * db) = (T a * da) * (T b * db) := by ring
  rw [heq] at hp
  by_contra hpos
  exact (not_le_of_gt hp)
    (mul_nonpos_of_nonneg_of_nonpos hresidue.le (le_of_not_gt hpos))

/-- The same sign propagation works in both directions along the linear root list. -/
lemma positive_residue_iff_across_interlacing (D T : ℝ → ℝ)
    {a r b da dr db : ℝ} (har : a < r) (hrb : r < b)
    (hD : Continuous D) (hT : Continuous T) (hDa : D a = 0) (hDb : D b = 0)
    (hda : HasDerivAt D da a) (hdb : HasDerivAt D db b)
    (hdane : da ≠ 0) (hdbne : db ≠ 0)
    (hDnozero : ∀ t ∈ Set.Ioo a b, D t ≠ 0)
    (hTr : T r = 0) (hdr : HasDerivAt T dr r) (hdrne : dr ≠ 0)
    (hTleft : ∀ t ∈ Set.Ico a r, T t ≠ 0)
    (hTright : ∀ t ∈ Set.Ioc r b, T t ≠ 0) :
    (0 < T a * da ↔ 0 < T b * db) := by
  have hderiv := endpoint_derivatives_mul_neg_of_zero_free D (har.trans hrb) hD
    hDa hDb hda hdb hdane hdbne hDnozero
  have hsample := sample_values_mul_neg_of_single_simple_root T har hrb hT
    hTr hdr hdrne hTleft hTright
  have hp : 0 < (T a * da) * (T b * db) := by
    have heq : (T a * T b) * (da * db) = (T a * da) * (T b * db) := by ring
    rw [← heq]
    exact mul_pos_of_neg_of_neg hsample hderiv
  constructor
  · intro hpos
    by_contra hnot
    exact (not_le_of_gt hp)
      (mul_nonpos_of_nonneg_of_nonpos hpos.le (le_of_not_gt hnot))
  · intro hpos
    by_contra hnot
    exact (not_le_of_gt hp)
      (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot) hpos.le)

/-- Adjacent sign equivalences propagate one proved positive anchor to every
member of a finite linear chain, including the singleton case. -/
lemma finite_chain_positive_of_adjacent_iff {m : ℕ} (f : Fin m → ℝ)
    (hstep : ∀ k l : Fin m, k.val + 1 = l.val → (0 < f k ↔ 0 < f l))
    (anchor : Fin m) (hanchor : 0 < f anchor) : ∀ k, 0 < f k := by
  have hm : 0 < m := Nat.zero_lt_of_lt anchor.isLt
  let first : Fin m := ⟨0, hm⟩
  have hconst : ∀ v (hv : v < m), (0 < f ⟨v, hv⟩ ↔ 0 < f first) := by
    intro v
    induction v with
    | zero => intro hv; rfl
    | succ v ih =>
      intro hv
      have hv' : v < m := by omega
      exact (hstep ⟨v, hv'⟩ ⟨v + 1, hv⟩ rfl).symm.trans (ih hv')
  have hfirst : 0 < f first := (hconst anchor.val anchor.isLt).mp hanchor
  intro k
  exact (hconst k.val k.isLt).mpr hfirst

variable {n : ℕ}

/-- Exhaustion removes all unlisted zeros, and saturation supplies simplicity.
No derivative orientation is assumed for the actual interpolant. -/
lemma sineInterpolant_deriv_mul_pos_of_next_sample (θ : Fin n → ℝ) (c : Fin n → ℝ)
    (hP : interpolantPolynomial θ c ≠ 0) (root : Fin (n - 1) → ℝ)
    (hinj : Function.Injective root) (hbound : ∀ i, root i ∈ Set.Ico 0 (2 * Real.pi))
    (hroot : ∀ i, sineInterpolant θ c (root i) = 0) (i : Fin (n - 1))
    (b : ℝ) (hb : b ∈ Set.Ico 0 (2 * Real.pi)) (hib : root i < b)
    (hnoother : ∀ j, root j ∉ Set.Ioc (root i) b) :
    0 < deriv (sineInterpolant θ c) (root i) * sineInterpolant θ c b := by
  apply hasDerivAt_mul_sample_pos_of_zero_free_right (sineInterpolant θ c) hib
    (continuous_sineInterpolant θ c).continuousOn (hroot i)
    ((differentiable_sineInterpolant θ c (root i)).hasDerivAt)
    (deriv_sineInterpolant_ne_zero_of_saturated_roots θ c hP root hinj hbound hroot i)
  intro t ht hzero
  have htbound : t ∈ Set.Ico 0 (2 * Real.pi) :=
    ⟨(hbound i).1.trans ht.1.le, ht.2.trans_lt hb.2⟩
  obtain ⟨j, hj⟩ := cayley_chart_root_mem_of_saturated_roots (n - 1)
    (sineInterpolant θ c) (interpolantPolynomial θ c) hP
    (interpolantPolynomial_natDegree_le θ c)
    (cos_pow_mul_interpolantPolynomial_eval_tan θ c)
    (interpolantPolynomial_coeff_top θ c) root hinj hbound hroot t htbound hzero
  exact hnoother j (by rwa [hj])

end

end UnitCircleInterpolation
