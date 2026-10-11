# Unit-circle Lagrange interpolation

Public project author and maintainer: **wang060919**. Project contributions are
released under the [MIT license](LICENSE). Third-party notices and original
attribution remain in the reused source files; see [AUTHORS.md](AUTHORS.md) and
[PROVENANCE.md](PROVENANCE.md). Development used Codex assistance as described
in the authorship record.

Repository: [wang060919/jsp-000936-unit-circle-lean](https://github.com/wang060919/jsp-000936-unit-circle-lean).
[GitHub Actions](https://github.com/wang060919/jsp-000936-unit-circle-lean/actions/workflows/verify.yml) checks the published
version. The [scope inquiry](https://github.com/TheJustinSunPrize/awards/issues/5007)
is pending. The [official contribution PR #5009](https://github.com/TheJustinSunPrize/awards/pull/5009) is open for scope and proof review; no award claim has been submitted.

An independent Lean 4 project for the unit-circle variant of Erdős problem 1129,
associated with JSP-000936. The mathematical result is due to Brutman and
Brutman–Pinkus, with the trigonometric/global framework of de Boor–Pinkus.

For every positive node count and every injectively enumerated family of
unit-modulus complex nodes, the maximum on the unit circle of the sum of the
absolute Lagrange cardinal functions is minimized exactly by a regular polygon,
up to rotation and permutation.

**Status: the complete all-positive-N unit-circle minimizer classification is proved.**
The existing real-interval formalizations are prior contributions and are not
claimed as new work here. Award eligibility of this unit-circle variant remains
an organizer decision.

## Versions and verification

- Lean: `leanprover/lean4:v4.33.0`
- Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`
- The local toolchain and build/download logs live in ignored `.tools/` and `.work/`.
- For a clean checkout, install Elan from https://github.com/leanprover/elan,
  enter this repository, and run `lake exe cache get` followed by
  `python3 scripts/audit.py`. Elan selects the fixed `lean-toolchain` version.
  The wrapper uses the local toolchain if present and otherwise the exact
  Lean 4.33.0 available through Elan/PATH; it checks the observed version.
- GitHub Actions configuration is in `.github/workflows/verify.yml`. It builds,
  checks the target and all public axioms, checks the literal specification,
  replays the final module with `leanchecker --fresh`, and verifies both hashes and file coverage in `SHA256SUMS`.
  See [the workflow runs](https://github.com/wang060919/jsp-000936-unit-circle-lean/actions/workflows/verify.yml) for the actual
  result and exact commit checked.
- Run `python3 scripts/verify_manifest.py` to verify release hashes and complete
  file coverage. After intended publication-file changes, regenerate the
  manifest with `python3 scripts/verify_manifest.py --write`.
- Run `scripts/lake build` using the local toolchain, or ordinary `lake build`
  with the exact toolchain configured through Elan.
- Run `python3 scripts/audit.py` for the complete build, an explicit
  `example : Target := unitCircleInterpolation_target`, and every public proof's
  axiom inventory. The resulting `.work/logs/development-audit.json` records
  the exact source hashes and theorem count. The full target and all 771 public
  proofs in 77 modules have passed with only `propext`, `Classical.choice`, and
  `Quot.sound`.

## Reproduction from the public repository

Replace `COMMIT_SHA` below with the full 40-character commit SHA selected from
the `main` branch, and inspect the workflow result for that exact commit.
Install [Elan](https://github.com/leanprover/elan) first so the included
`lean-toolchain` selects the exact release.

```sh
git clone https://github.com/wang060919/jsp-000936-unit-circle-lean.git
cd jsp-000936-unit-circle-lean
git checkout --detach COMMIT_SHA
lake exe cache get
python3 scripts/audit.py
lake env leanchecker --fresh -v UnitCircleInterpolation.FinalClassification
python3 scripts/verify_manifest.py
```

The audit records the observed Lean release and Mathlib Git revision and
rejects a mismatch. The wrapper also rejects an inconsistent Lake version.
No project-local `.tools` directory is needed with the correct Elan/PATH setup.

## Final statements

All final declarations are in `UnitCircleInterpolation/FinalClassification.lean`.

| Declaration | Scope |
| --- | --- |
| `unitCircleInterpolation_target` | Existence and complete classification for every positive node count. |
| `minimizer_iff_regular` | Arbitrary circle nodes, with every rotation and enumeration. |
| `complex_minimizer_iff_regular` | The same classification for any injective complex node family of unit norm. |
| `complexAmplification_regular_le` | The literal complex cardinal-product supremum on the whole circle is minimized by regular nodes. |

`verification/OriginalStatement.lean` independently writes out the literal
complex products, the supremum over all complex points of norm one, and complex
exponential regular coordinates. It checks the classification and lower bound
against those definitions. Its verification level is a Lean statement check;
it is not a separate implementation of a proof checker.

## Proof structure

The literal complex-cardinal/real-sine bridge, compact attained maximum,
rotation and permutation invariance, arbitrary-node cyclic ordering, and the
complete one-node classification have been compiled. The finite Cayley root
bound includes its omitted circle point, and the division-free homogeneous
representation has a global derivative formula at that point as well.

Both ordinary and wrap gaps have proved sign coefficients and actual
`n - 1` ordered zeros constructed by intermediate values. Cyclic Rolle,
polynomial root multiplicities, and the complete-circle derivative bound prove
that every critical point of these actual signed gap interpolants is
nondegenerate for `n >= 2`. Every ordinary and wrap gap has a unique strict
interior peak above one with strictly negative second derivative. The uniform
peak/height interface is connected to the literal complex Lebesgue function.
The supremum over the entire unit circle equals the finite maximum of these
actual heights, including for arbitrary original node rotations and enumerations.

The cross-gap difference and sum have complete simple root lists constructed
from their actual complementary nodal coefficients. Their root locations and
a proved residue anchor imply positive residues at every difference root.
For each evaluation point, a translated Cayley chart avoids all roots and that
point; the finite Markov kernel then gives a strict global Wronskian sign.
The actual wrap-gap phase is carried through explicitly, giving strict signs
for another gap function's derivative at each positive peak, for both parities.

The derivatives of the actual positive-gap interpolants have global continuous
critical quotients of homogeneous degree `n - 2`. Their diagonal values are
twice the negative second derivative; their off-diagonal values have proved
checkerboard signs in physical peak order. Every nonzero quotient relation has
one alternating sign, so every row-deleted family is linearly independent and
its distinct-angle evaluation matrix is nonsingular. The literal node-sensitivity formula is
proved, including its full parameter and joint Fréchet differentials.

The normalized free-angle domain is open. The actual nondegenerate peaks give
smooth implicit branches; critical-point uniqueness identifies these branches
with the actual peaks. Envelope cancellation proves the differential of the
actual height map. Every maximal height-Jacobian minor is nonzero. The proved
sine-product row signs cancel the quotient relation phases, so the actual left
kernel and signed cofactors have one strict sign. Consequently the actual
adjacent-height difference map has a nonsingular Jacobian everywhere in the
admissible angular chart, for every `n >= 2`.

The collision estimates use literal complex cardinal products. A wide empty
gap's midpoint is uniformly separated from all nodes, including for gaps wider
than a half-circle. Comparing it with a small-gap peak yields an explicit
reciprocal-width lower bound for the difference of their actual heights.
The widths sum to `2π`, and a largest gap has at least the mean width. The
resulting fixed reciprocal bound proves that the actual adjacent-height
difference norm diverges when the minimum gap width tends to zero. Conversely,
a bounded difference norm gives an explicit positive lower bound on every gap.
The corresponding closed angular simplex is compact, including its wrap gap.

These actual estimates prove that the actual difference map on the angular
domain is proper. The smooth inverse function theorem supplies local inverse
charts. The domain is convex and nonempty, so the covering-space argument makes
the actual difference map a global homeomorphism onto `ℝ^(n - 1)`. In particular,
exactly one normalized node configuration has all actual gap heights equal.

The full-circle objective has compact sublevels, hence a global minimum.
Deleting any one height row gives a nonsingular differential. If that omitted
height were below the maximum, an admissible direction could lower all other
heights while keeping the omitted one below the old maximum. Thus every minimum
has equal heights. Rotation symmetry proves that the regular polygon has equal
heights as well; global injectivity identifies the minimum with it. Exact node
transport removes normalization and ordering, and the complete one-node proof
closes the all-positive-N classification.

The generic finite polynomial Markov kernel reuses MIT-licensed code from
`randyxian08/jsp000936-lean` at commit
`0ced15a2630c5c68b23de896d7e6ad1e7cfeda01`; its full license and attribution are
retained in `UnitCircleInterpolation/MarkovKernel.lean`. The generic relation,
deleted-evaluation, cofactor, and determinant kernels also adapt that pinned
repository; their complete MIT notices and precise attribution are retained in
`CyclicRelations.lean`, `CyclicMinors.lean`, `RectangularDifferences.lean`,
`PeakSensitivityMatrix.lean`, `PeakImplicit.lean`, and `GenericGlobalInverse.lean`. The actual circle
instances and their analytic hypotheses are proved in this project.

## Award scope

A live check on 2026-10-11 (Asia/Shanghai) found that the
[official JSP-000936 entry](https://github.com/TheJustinSunPrize/awards/blob/16877004910734cecca83cc5af0fec2f5a4125b3/problems/catalog-0901-1000.md#JSP-000936)
still says `Eligible to claim: No`. The
[participation rules](https://www.hejustinsun.com/prize/participation)
explain that this flag describes the current verification status and does not
prevent participation. Complete proofs of the original problem are required.
The catalog bibliography includes the original unit-circle problem and solution,
while the existing
[real-interval submission](https://github.com/randyxian08/jsp000936-lean/blob/2535658804b579cbcaeae11a205648ab88eef572/README.md#L25-L27)
explicitly excludes the circle variant. The latest related
[PR #4987](https://github.com/TheJustinSunPrize/awards/pull/4987) points to a source
whose [challenge](https://github.com/Drag0ndddd1118/jsp-000936-formalization/blob/a9afe1737bb9b786f0f42d0851a3c249ddfcb64b/Challenge.lean#L15)
still states a three-node real-interval result. A bounded public PR and code
search did not identify another checkable complete unit-circle proof; it does
not establish exclusivity or priority.
These scope checks do not establish that the organizers accept a separate
unit-circle contribution for this catalog entry. That decision remains unknown,
independently of the progress of this formalization.

## Mathematical sources

- L. Brutman and A. Pinkus, *On the Erdös Conjecture Concerning Minimal Norm
  Interpolation on the Unit Circle*, SIAM Journal on Numerical Analysis 17(3)
  (1980), 373–375, [DOI: 10.1137/0717031](https://doi.org/10.1137/0717031).
- L. Brutman, *On the polynomial and rational projections in the complex plane*,
  SIAM Journal on Numerical Analysis 17(3) (1980), 366–372.
- C. de Boor and A. Pinkus, *Proof of the conjectures of Bernstein and Erdős
  concerning the optimal nodes for polynomial interpolation*, Journal of
  Approximation Theory 24 (1978), 289–303.
- T. A. Kilgore, *A characterization of the Lagrange interpolating projection
  with minimal Tchebycheff norm*, Journal of Approximation Theory 24 (1978),
  273–288.

The mathematical solution is historical. The present contribution is its
unit-circle Lean formalization, with the generic source reuse identified above.

## Proof layers

1. Literal definitions, compact attained maximum, cardinal and phase identities.
2. Rotation/permutation invariance and regular-node construction.
3. Weighted Cayley polynomials and finite root counts, for both parities.
4. Cyclic interlacing and nondegenerate gap maxima.
5. Sensitivity, quotient relations and all maximal Jacobian minors.
6. Collision coercivity, coherent cofactors and the global inverse map.
7. Full minimizer classification, literal complex statement and axiom audit.

The mathematical route and prior-source audit are recorded in the adjacent
`selection-audit-2026-10-03` folder. Local build, statement, and axiom evidence
is in `.work/logs/`. The final verification report and packaged evidence are in
`verification/REPORT.md` and `verification/evidence/`. The publication-preparation
review is in `verification/RELEASE-REVIEW.md`. These are dated local snapshots;
public version and CI references are in `verification/PUBLICATION.md`. Submission preparation is
documented in `SUBMISSION.md`.
The [official contribution PR #5009](https://github.com/TheJustinSunPrize/awards/pull/5009) submits the unit-circle formalization for maintainer review. Scope acceptance remains pending.
