# Unit-circle proof submission material

Public formalization author and maintainer: **wang060919**.
Original repository: [wang060919/jsp-000936-unit-circle-lean](https://github.com/wang060919/jsp-000936-unit-circle-lean).
Branch: `main`. Select the full 40-character proof commit and its matching
successful GitHub Actions run when submitting the contribution.

Project contributions use MIT; third-party licenses and authors remain intact.
See `AUTHORS.md` and `PROVENANCE.md` for the accurate AI-assisted development
record, original mathematics, and reused generic formalization sources.

This material describes a complete formalization of the **unit-circle variant**
associated with JSP-000936 / Erdős problem 1129. It does not claim a new
mathematical solution or that the organizers have accepted a separate award
claim for this variant.

## Mathematical result and evidence

For each positive number of distinct complex unit-modulus nodes, take the
literal Lagrange cardinal products and the maximum on the entire unit circle of
the sum of their norms. A configuration minimizes this quantity if and only if
it is a regular polygon, allowing arbitrary rotation and enumeration.

The mathematical solution is due to L. Brutman and A. Pinkus, *On the Erdös
Conjecture Concerning Minimal Norm Interpolation on the Unit Circle*, SIAM
Journal on Numerical Analysis 17(3) (1980), 373–375,
[DOI 10.1137/0717031](https://doi.org/10.1137/0717031). Theorem 1 on page 373
states the unique regular configuration up to rotation. The paper completes the
even-node case and cites Brutman's preceding odd-node result. The trigonometric
and global proof framework is due to de Boor–Pinkus and Kilgore; the complete
references are in the project README.

## Formalized statements

| Requirement | Declaration / source |
| --- | --- |
| Original complex cardinal products | `cardinal`, `lebesgueFunction` in `Definitions.lean` |
| Maximum on all circle points, with boundedness and attainment | `amplification`, `amplification_attained` in `Definitions.lean` / `Basic.lean` |
| Arbitrary injective complex coordinates of norm one | `NodeFamily.ofCoordinates` and its exact adapters in `ComplexNodes.lean` |
| Every positive node count, including one | `unitCircleInterpolation_target` in `FinalClassification.lean` |
| Existence and both directions of the regular-polygon classification | `minimizer_iff_regular` in `FinalClassification.lean` |
| Literal complex-coordinate classification | `complex_minimizer_iff_regular` in `FinalClassification.lean` |
| Original literal lower bound | `complexAmplification_regular_le` in `FinalClassification.lean` |
| Independently written products, full complex circle, and complex exponential regular points | `original_classification`, `original_lower_bound` in `verification/OriginalStatement.lean` |

The final complex declarations assume only positive size, unit-modulus nodes,
and injectivity. They have no ordering, parity, special-node, local-minimum,
or additional mathematical hypotheses.

## Attribution

The project supplies the unit-circle formalization. Existing real-interval
formalizations remain prior contributions. Seven generic source modules adapt
MIT-licensed code from `randyxian08/jsp000936-lean` at commit
`0ced15a2630c5c68b23de896d7e6ad1e7cfeda01`; their source headers retain full
copyright notices, the MIT permission text, and exact provenance:

- `MarkovKernel.lean`
- `CyclicRelations.lean`
- `CyclicMinors.lean`
- `RectangularDifferences.lean`
- `PeakSensitivityMatrix.lean`
- `PeakImplicit.lean`
- `GenericGlobalInverse.lean`

The actual complex/sine bridges, circular root and sign arguments, actual
Jacobian instances, collision estimates, properness, and final unit-circle
assembly are proved here. Reused generic kernels are not claimed as original
code or as a new mathematical solution.

## Reproduction

The project fixes Lean `4.33.0` and Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`. The Lake manifest is included.

With the exact toolchain configured through Elan, run from the project root:

```sh
lake exe cache get
python3 scripts/audit.py
lake env lean verification/OriginalStatement.lean
lake env leanchecker --fresh -v UnitCircleInterpolation.FinalClassification
```

The project wrapper prefers the official local Linux toolchain at
`.tools/lean-4.33.0-linux/` and otherwise uses Elan/PATH, requiring the exact
Lean 4.33.0 version. The local toolchain is excluded from the archive. The
comprehensive public-proof and original-statement axiom check is:

```sh
python3 scripts/audit.py
```

The audit checks the full `Target` explicitly, all 771 public proofs, and all
five original-statement challenge proofs. Its only permitted axioms are
`propext`, `Classical.choice`, and `Quot.sound`. The statement challenge is a
Lean elaboration check; `leanchecker` is Lean's own kernel replay, not an
independently implemented external checker.

The final checks, exact source hashes, clean-project reproduction results, and
raw logs are described in `verification/REPORT.md`. The isolated reproduction
recompiled all 77 project modules and the umbrella without copying this
project's compiled artifacts; it reused the pinned external dependency cache.

## Publication fields

The original proof repository is public. The [official contribution PR #5009](https://github.com/TheJustinSunPrize/awards/pull/5009) submits
commit `e99c4a7fb868a264e08e79355c44adf73e4fc332`, contained in `main`, with
[successful CI run 38158599411](https://github.com/wang060919/jsp-000936-unit-circle-lean/actions/runs/38158599411)
and the reproduction evidence for that exact version. Scope and proof review
remain pending; no award claim has been submitted. Public version and CI
references are in `verification/PUBLICATION.md`.
The public author identity is `wang060919`, with the accurate contribution
record in `AUTHORS.md`; repository ownership alone does not determine award
attribution. The selected commit must be contained in `main`. A local SHA256 source manifest does not replace those publication
fields.

Submit references and catalog text to the awards repository, with the Lean
source and build files retained in the external proof repository. Preserve the
distinction between the historical mathematical solution and this formalization.
Award scope, acceptance, priority, and entitlement remain organizer decisions.

The live scope snapshot dated 2026-10-11 (Asia/Shanghai) is included as
`verification/evidence/award-scope-final-2026-10-11.json`. It records the actual
catalog, participation rules, related PRs and pinned external source scopes;
it does not establish that this variant is accepted as a separate contribution.
The pending scope question is [official Feedback #5007](https://github.com/TheJustinSunPrize/awards/issues/5007).
