/-
Unit-circle project integration and adaptations: wang060919.
Developed with Codex assistance. Original authors and MIT notices are retained below.
-/

/-
Copyright (c) 2026 Ethan Yang
Copyright (c) 2026 randyxian08 (free-node extension and repairs)

The generic covering kernels below are adapted from
randyxian08/jsp000936-lean, commit 0ced15a2630c5c68b23de896d7e6ad1e7cfeda01,
Erdos1153/DeBoorPinkus/GlobalHomeomorph.lean, lines 30–87.
The final open-and-closed range argument is adapted from lines 110–120,
with an arbitrary nonempty preconnected source instead of a Euclidean source.
https://github.com/randyxian08/jsp000936-lean/blob/0ced15a2630c5c68b23de896d7e6ad1e7cfeda01/Erdos1153/DeBoorPinkus/GlobalHomeomorph.lean
Original file SHA256: 356ea83a88920eb701e7f1b397875628f64bb41c8ead4816495daee182e2d1d6
Original Git blob: 9b2973cfafd6faabf07310932e72c4547fa01e3f
The local source and pinned tree manifest were checked against these hashes.

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

import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Generic global inversion over a Euclidean target

A proper local homeomorphism is a covering map. A surjective covering of a
simply connected target, with preconnected source, is a homeomorphism.
For a Euclidean target, surjectivity follows from a nonempty open-and-closed range.
These are generic topology kernels: no actual angular-domain properness or
connectedness, and no global circular minimizer result, is asserted here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

open Function Topology

noncomputable section

/-- Properness and local charts give the compact discrete fibers of a covering map. -/
theorem isCoveringMap_of_localHomeomorph_of_proper
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [T2Space E] [T2Space X] {f : E → X}
    (hloc : IsLocalHomeomorph f) (hproper : IsProperMap f) :
    IsCoveringMap f := by
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  apply hproper.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
  · intro x _
    have hdisc : IsDiscrete (f ⁻¹' {x}) :=
      IsDiscrete.of_openPartialHomeomorph f Set.Subset.rfl fun e _ ↦ by
        obtain ⟨φ, heφ, hφ⟩ := hloc e
        exact ⟨φ, heφ, hφ.symm⟩
    exact (hproper.isCompact_preimage isCompact_singleton).finite hdisc
  · intro e _
    obtain ⟨φ, heφ, hφ⟩ := hloc e
    exact ⟨φ, heφ, hφ⟩

/-- Lifting the target identity gives the inverse of a connected one-sheeted covering. -/
theorem isHomeomorph_of_surjective_covering
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [PreconnectedSpace E] [Nonempty X]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    {f : E → X} (hcover : IsCoveringMap f) (hsurj : Surjective f) :
    IsHomeomorph f := by
  let x₀ : X := Classical.arbitrary X
  obtain ⟨e₀, he₀⟩ := hsurj x₀
  let fid : C(X, X) := ContinuousMap.id X
  obtain ⟨s, hs, _⟩ :=
    hcover.existsUnique_continuousMap_lifts fid x₀ e₀ (by simpa [fid] using he₀)
  obtain ⟨hs₀, hfs⟩ := hs
  have hsf : (s : X → E) ∘ f = id := by
    refine hcover.eq_of_comp_eq
      (s.continuous.comp hcover.continuous) continuous_id ?_ e₀ ?_
    · funext e
      have hright := congrFun hfs (f e)
      simpa [fid, Function.comp_def] using hright
    · simpa [he₀] using hs₀
  rw [isHomeomorph_iff_exists_inverse]
  refine ⟨hcover.continuous, s, ?_, ?_, s.continuous⟩
  · intro e
    exact congrFun hsf e
  · intro x
    have hright := congrFun hfs x
    simpa [fid, Function.comp_def] using hright

/-- A proper local homeomorphism from any nonempty preconnected Hausdorff space
to a finite-dimensional real coordinate space is a global homeomorphism. -/
theorem euclideanTarget_isHomeomorph_of_localHomeomorph_of_proper
    {E : Type*} [TopologicalSpace E] [T2Space E]
    [PreconnectedSpace E] [Nonempty E] {d : ℕ} {f : E → Fin d → ℝ}
    (hloc : IsLocalHomeomorph f) (hproper : IsProperMap f) :
    IsHomeomorph f := by
  have hcover : IsCoveringMap f := isCoveringMap_of_localHomeomorph_of_proper hloc hproper
  have hrangeOpen : IsOpen (Set.range f) := by
    simpa only [Set.image_univ] using hloc.isOpenMap Set.univ isOpen_univ
  have hrangeClosed : IsClosed (Set.range f) := hproper.isClosed_range
  have hrangeNonempty : (Set.range f).Nonempty :=
    ⟨f (Classical.arbitrary E), Classical.arbitrary E, rfl⟩
  have hrange : Set.range f = Set.univ :=
    IsClopen.eq_univ ⟨hrangeClosed, hrangeOpen⟩ hrangeNonempty
  exact isHomeomorph_of_surjective_covering hcover (Set.range_eq_univ.mp hrange)

end

end UnitCircleInterpolation
