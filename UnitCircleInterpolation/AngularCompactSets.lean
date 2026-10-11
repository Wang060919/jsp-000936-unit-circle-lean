/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import UnitCircleInterpolation.GapWidths
import Mathlib.Order.Fin.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Compact subsets of the actual normalized angular simplex

Requiring every literal cyclic gap width to be at least a fixed positive
number gives a closed set inside the open node domain. Its free coordinates
lie in the explicit compact box `[ε, 2π - ε]`. This is purely the geometry of
the actual chart; no properness statement for the height map is asserted.
The empty set and the chart with no free coordinates are both included.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {d : ℕ}

/-- The width of an ordinary gap is the literal successive angle difference. -/
lemma parameterGapWidth_succ (u : Fin d → ℝ) (i : Fin d) :
    parameterGapWidth i.succ u = angularParameterAngles u i.succ -
      angularParameterAngles u i.castSucc := by
  have hpred : gapLeftNodeIndex (Nat.succ_pos d) i.succ = i.castSucc := by
    apply Fin.ext
    simp [gapLeftNodeIndex, gapPredecessor]
  simp only [parameterGapWidth, Fin.val_succ, Nat.succ_ne_zero, if_false, hpred]

/-- The final width uses the lifted first angle at `2π`. -/
lemma parameterGapWidth_zero (u : Fin d → ℝ) :
    parameterGapWidth (0 : Fin (d + 1)) u =
      2 * Real.pi - angularParameterAngles u (lastNodeIndex (Nat.succ_pos d)) := by
  simp [parameterGapWidth, gapLeftNodeIndex]

/-- Every actual cyclic gap is separated by at least `ε`. -/
def shrunkenAngularSimplex (d : ℕ) (ε : ℝ) : Set (Fin d → ℝ) :=
  {u | ∀ cut : Fin (d + 1), ε ≤ parameterGapWidth cut u}

lemma mem_shrunkenAngularSimplex (u : Fin d → ℝ) (ε : ℝ) :
    u ∈ shrunkenAngularSimplex d ε ↔ ∀ cut, ε ≤ parameterGapWidth cut u :=
  Iff.rfl

lemma isClosed_shrunkenAngularSimplex (d : ℕ) (ε : ℝ) :
    IsClosed (shrunkenAngularSimplex d ε) := by
  have heq : shrunkenAngularSimplex d ε =
      ⋂ cut : Fin (d + 1), {u : Fin d → ℝ | ε ≤ parameterGapWidth cut u} := by
    ext u
    simp only [shrunkenAngularSimplex, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [heq]
  exact isClosed_iInter (fun cut => isClosed_le continuous_const (continuous_parameterGapWidth cut))

/-- Positive literal width at every cut forces strictly increasing full angles. -/
lemma shrunkenAngularSimplex_strictMono {ε : ℝ} (hε : 0 < ε)
    {u : Fin d → ℝ} (hu : u ∈ shrunkenAngularSimplex d ε) :
    StrictMono (angularParameterAngles u) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have hwidth := hu i.succ
  rw [parameterGapWidth_succ] at hwidth
  exact sub_pos.mp (hε.trans_le hwidth)

lemma shrunkenAngularSimplex_last_le {ε : ℝ} {u : Fin d → ℝ}
    (hu : u ∈ shrunkenAngularSimplex d ε) :
    angularParameterAngles u (lastNodeIndex (Nat.succ_pos d)) ≤ 2 * Real.pi - ε := by
  have hlast := hu 0
  rw [parameterGapWidth_zero] at hlast
  linarith

/-- The closed shrunken simplex lies inside the actual open chart. -/
lemma shrunkenAngularSimplex_subset_domain {ε : ℝ} (hε : 0 < ε) :
    shrunkenAngularSimplex d ε ⊆ angularParameterDomain d := by
  intro u hu
  have hmono := shrunkenAngularSimplex_strictMono hε hu
  refine ⟨hmono, ?_⟩
  intro i
  have hlast := shrunkenAngularSimplex_last_le hu
  have hi : angularParameterAngles u i.succ ≤
      angularParameterAngles u (lastNodeIndex (Nat.succ_pos d)) :=
    hmono.monotone (show i.succ ≤ lastNodeIndex (Nat.succ_pos d) from Fin.le_last _)
  change u i < 2 * Real.pi
  change u i ≤ angularParameterAngles u (lastNodeIndex (Nat.succ_pos d)) at hi
  linarith

/-- The free coordinates lie in a closed box with a literal `ε` margin at both ends. -/
lemma shrunkenAngularSimplex_coordinate_bounds {ε : ℝ} (hε : 0 < ε)
    {u : Fin d → ℝ} (hu : u ∈ shrunkenAngularSimplex d ε) (i : Fin d) :
    ε ≤ u i ∧ u i ≤ 2 * Real.pi - ε := by
  have hmono := shrunkenAngularSimplex_strictMono hε hu
  have hwidth := hu i.succ
  rw [parameterGapWidth_succ, angularParameterAngles_succ] at hwidth
  have hnonneg : 0 ≤ angularParameterAngles u i.castSucc := by
    have h := hmono.monotone (show (0 : Fin (d + 1)) ≤ i.castSucc from Fin.zero_le _)
    simpa only [angularParameterAngles_zero] using h
  have hi : angularParameterAngles u i.succ ≤
      angularParameterAngles u (lastNodeIndex (Nat.succ_pos d)) :=
    hmono.monotone (show i.succ ≤ lastNodeIndex (Nat.succ_pos d) from Fin.le_last _)
  exact ⟨by linarith, hi.trans (shrunkenAngularSimplex_last_le hu)⟩

lemma shrunkenAngularSimplex_subset_box {ε : ℝ} (hε : 0 < ε) :
    shrunkenAngularSimplex d ε ⊆ Set.Icc (fun _ : Fin d => ε) (fun _ => 2 * Real.pi - ε) := by
  intro u hu
  exact ⟨fun i => (shrunkenAngularSimplex_coordinate_bounds hε hu i).1,
    fun i => (shrunkenAngularSimplex_coordinate_bounds hε hu i).2⟩

/-- Uniformly positive literal circular gap widths define a compact actual parameter set. -/
theorem isCompact_shrunkenAngularSimplex {ε : ℝ} (hε : 0 < ε) :
    IsCompact (shrunkenAngularSimplex d ε) :=
  (isCompact_Icc : IsCompact
    (Set.Icc (fun _ : Fin d => ε) (fun _ => 2 * Real.pi - ε))).of_isClosed_subset
    (isClosed_shrunkenAngularSimplex d ε) (shrunkenAngularSimplex_subset_box hε)

lemma isBounded_shrunkenAngularSimplex {ε : ℝ} (hε : 0 < ε) :
    Bornology.IsBounded (shrunkenAngularSimplex d ε) :=
  (isCompact_shrunkenAngularSimplex hε).isBounded

/-- Inside the actual chart the shrunken condition is precisely a bound on its actual minimum. -/
lemma mem_shrunkenAngularSimplex_iff_minimumGapWidth (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (ε : ℝ) :
    u ∈ shrunkenAngularSimplex d ε ↔ ε ≤ minimumGapWidth (cyclicAnglesOfParameters u hu) := by
  constructor
  · intro h
    obtain ⟨cut, heq⟩ := exists_gapWidth_eq_minimum (cyclicAnglesOfParameters u hu)
    rw [← heq, ← parameterGapWidth_of_mem_domain u hu]
    exact h cut
  · intro h cut
    rw [parameterGapWidth_of_mem_domain u hu]
    exact h.trans (minimumGapWidth_le (cyclicAnglesOfParameters u hu) cut)

end

end UnitCircleInterpolation
