# Provenance and mathematical sources

## Project scope and identity

Public project identity: **[wang060919](https://github.com/wang060919)**.
Original repository: [wang060919/jsp-000936-unit-circle-lean](https://github.com/wang060919/jsp-000936-unit-circle-lean).
The AI-assisted development workflow and attribution
roles are described in [AUTHORS.md](AUTHORS.md).

This project formalizes the unit-circle variant associated with JSP-000936 /
Erdős problem 1129. For every positive node count, it uses the literal complex
Lagrange cardinal products, takes the maximum of the sum of their norms on the
entire unit circle, and proves that minimizers are exactly the regular polygons
up to rotation and permutation. The final statement assumes only positive size,
injectivity, and unit-modulus nodes.

The mathematical solution is historical. This contribution is its Lean
formalization; it does not assert a new mathematical solution or accepted
award status.

## Reused MIT-licensed source

All seven adaptations below come from **`randyxian08/jsp000936-lean`**, pinned to
the full commit **`0ced15a2630c5c68b23de896d7e6ad1e7cfeda01`**. Each local module
retains the original notices:

> Copyright (c) 2026 Ethan Yang  
> Copyright (c) 2026 randyxian08 (free-node extension and repairs)

Each also retains the full MIT permission text and warranty disclaimer. The
project's MIT License for new code does not replace these notices or change
third-party attribution.

The SHA256 values below identify the **entire original upstream files at the
pinned commit**, not the modified local modules. They are transcribed from the
existing source provenance headers. `PeakImplicit.lean` shares its original
`Jacobian.lean` file with `PeakSensitivityMatrix.lean`; its original-file digest
is the same digest recorded for that pinned file in the latter header.

| Local file in `UnitCircleInterpolation/` | Original path | Adapted portion | Original file SHA256 |
| --- | --- | --- | --- |
| `MarkovKernel.lean` | `Erdos1153/DeBoorPinkus/DerivativeInterlacing.lean` | Finite real-polynomial Markov kernel, lines 156–436 | `8ac28122f151b6033b5e4914b5cfc7333e0b50214648083335617e0ec12bbafe` |
| `CyclicRelations.lean` | `Erdos1153/DeBoorPinkus/Minors.lean` | Alternating-root and relation kernels, adapted to circular families | `df1a894ff71edc5c6947800468ae48fe5711e5f79d933231412a5c5d87c974b0` |
| `CyclicMinors.lean` | `Erdos1153/DeBoorPinkus/Minors.lean` | Row-deleted evaluation-matrix kernel, lines 838–912 | `df1a894ff71edc5c6947800468ae48fe5711e5f79d933231412a5c5d87c974b0` |
| `RectangularDifferences.lean` | `Erdos1153/DeBoorPinkus/Minors.lean` | Cofactor and adjacent-difference kernels, lines 970–1008 and 1216–1308 | `df1a894ff71edc5c6947800468ae48fe5711e5f79d933231412a5c5d87c974b0` |
| `PeakSensitivityMatrix.lean` | `Erdos1153/DeBoorPinkus/Jacobian.lean` | Diagonal determinant calculation, lines 297–315 | `081a8a26cf99643afa728c2cd560b1bee6cd9b1b912c0534376a0b00deceff08` |
| `PeakImplicit.lean` | `Erdos1153/DeBoorPinkus/Jacobian.lean` | Scalar vertical-derivative helper `fderiv_comp_inr_eq_of_hasDeriv` | `081a8a26cf99643afa728c2cd560b1bee6cd9b1b912c0534376a0b00deceff08` |
| `GenericGlobalInverse.lean` | `Erdos1153/DeBoorPinkus/GlobalHomeomorph.lean` | Generic covering kernels, lines 30–87; open-and-closed range argument, lines 110–120, generalized to a nonempty preconnected source | `356ea83a88920eb701e7f1b397875628f64bb41c8ead4816495daee182e2d1d6` |

Pinned original files:

- [DerivativeInterlacing.lean](https://github.com/randyxian08/jsp000936-lean/blob/0ced15a2630c5c68b23de896d7e6ad1e7cfeda01/Erdos1153/DeBoorPinkus/DerivativeInterlacing.lean)
- [Minors.lean](https://github.com/randyxian08/jsp000936-lean/blob/0ced15a2630c5c68b23de896d7e6ad1e7cfeda01/Erdos1153/DeBoorPinkus/Minors.lean)
- [Jacobian.lean](https://github.com/randyxian08/jsp000936-lean/blob/0ced15a2630c5c68b23de896d7e6ad1e7cfeda01/Erdos1153/DeBoorPinkus/Jacobian.lean)
- [GlobalHomeomorph.lean](https://github.com/randyxian08/jsp000936-lean/blob/0ced15a2630c5c68b23de896d7e6ad1e7cfeda01/Erdos1153/DeBoorPinkus/GlobalHomeomorph.lean)

These are explicitly attributed generic adaptations, not claims to original
code. The source headers specify their local extent. The prior real-interval
formalization remains a separate prior contribution.

## Unit-circle development in this project

The actual complex-to-sine identities, rotation and permutation transport,
circular root and sign arguments for both parities, moving gap maxima, actual
Jacobian instances, collision estimates, angular properness and global
inversion, regular-node heights, existence and equioscillation of minima, and
the final all-positive-node-count classification are developed for the
unit-circle statement in this project. They use Mathlib and the attributed
generic kernels above.

This distinguishes the project's formalization work from historical
mathematical authorship. It does not claim that each mathematical technique is
new. The public formalization identity is `wang060919`; Codex's substantial
implementation and verification role is disclosed in [AUTHORS.md](AUTHORS.md).

## Mathematical bibliography

- L. Brutman and A. Pinkus, *On the Erdös Conjecture Concerning Minimal Norm
  Interpolation on the Unit Circle*, SIAM Journal on Numerical Analysis 17(3)
  (1980), 373–375, [DOI 10.1137/0717031](https://doi.org/10.1137/0717031).
  Theorem 1 on page 373 states the unique regular configuration up to rotation.
  This paper completes the even-node case and cites Brutman's odd-node result.
- L. Brutman, *On the polynomial and rational projections in the complex plane*,
  SIAM Journal on Numerical Analysis 17(3) (1980), 366–372.
- C. de Boor and A. Pinkus, *Proof of the conjectures of Bernstein and Erdős
  concerning the optimal nodes for polynomial interpolation*, Journal of
  Approximation Theory 24 (1978), 289–303.
- T. A. Kilgore, *A characterization of the Lagrange interpolating projection
  with minimal Tchebycheff norm*, Journal of Approximation Theory 24 (1978),
  273–288.

## Dependencies and verification

Lean is pinned to `4.33.0`; Mathlib is pinned to
`db584cd6d46c92f209a44c0f1c829460d327499d`. `lake-manifest.json` fixes the
resolved external dependency revisions. Dependencies retain their own
licenses and attribution; they are not relicensed by this project's MIT
License.

The build, original-statement elaboration, axiom audit, and kernel-replay
evidence are recorded in [verification/REPORT.md](verification/REPORT.md).
Those checks establish local formal verification, not external authorship
recognition or award acceptance. A local source SHA256 manifest does not
replace the public repository, branch, and full Git commit SHA required for
formalization review. Public version and workflow references are in
[verification/PUBLICATION.md](verification/PUBLICATION.md). No official awards
contribution PR or claim has been submitted.
