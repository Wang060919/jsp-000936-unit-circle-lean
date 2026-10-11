# Verification report for the publication preparation

> Historical snapshot of the local prepublication checks completed on
> 2026-10-11, before the public repository and scope inquiry were created.
> The proof inputs remain the versions identified below. Current public
> repository and CI references are in [PUBLICATION.md](PUBLICATION.md).

Public project author and maintainer: **wang060919**.
Planned repository: `wang060919/jsp-000936-unit-circle-lean`.
Verification date: **2026-10-11, Asia/Shanghai**.

The complete unit-circle minimizer classification is proved for every positive
node count. The final complex-coordinate theorem assumes only positive size,
unit-modulus nodes and injectivity. The supremum is over the entire unit circle,
and minimizers are exactly regular polygons up to rotation and permutation.

## Formal statement

The literal objective is:

```text
sup { ∑ⱼ |∏ₖ≠ⱼ (w − zₖ)/(zⱼ − zₖ)| : w ∈ ℂ, |w| = 1 }.
```

`UnitCircleInterpolation.unitCircleInterpolation_target : Target` supplies
existence and both classification directions. The final complex statements are
`complex_minimizer_iff_regular` and `complexAmplification_regular_le` in
`UnitCircleInterpolation/FinalClassification.lean`.

`verification/OriginalStatement.lean` separately writes out the complex
products, full norm-one domain and regular coordinates as complex exponentials.
Its classification and lower bound are checked against those definitions.
There are no ordering, parity, special-node, sampled-circle or local-minimum
hypotheses. The one-node case is included.

## Results for this version

| Check | Observed result | Evidence |
| --- | --- | --- |
| Complete build and public axiom audit | Exit 0; 771 public declarations in 77 modules | `evidence/development-audit.json`, `development-build.log`, `development-axioms.log` |
| Explicit inhabitant of the complete Target | Type-checked | `evidence/development-axioms.lean` |
| Literal original-statement audit | Five proof declarations checked | `evidence/original-statement.log` |
| Final-module fresh kernel replay | Exit 0; 265.32 seconds | `evidence/release-verification.json`, `release-kernel-fresh.log` |
| Isolated compilation without `.tools` or project build artifacts | Exit 0; 89.26 seconds; all 77 modules plus umbrella newly built | `evidence/release-clean-reproduction.json`, `release-clean-development-build.log` |
| Isolated public and literal axiom audit | All 771 public and five challenge declarations checked | `evidence/release-clean-development-axioms.log`, `release-clean-original-statement.log` |
| Lake/Lean version consistency guard | Inconsistent versions rejected | `evidence/release-guard-regressions.json` |
| Release-manifest checks | Changed contents and omitted files rejected, including new Git-tracked files | `evidence/release-guard-regressions.json`, `release-git-inventory-regression.json` |

The final Target depends on exactly `propext`, `Classical.choice` and
`Quot.sound`. Every inventoried public and challenge theorem uses only these
standard axioms. No `sorry`, `admit`, custom axioms, `native_decide` or unsafe
proof substitute is used. Three existing polynomial deprecation warnings in
the reused `MarkovKernel.lean` remain; they are not proof failures.

The actual Lean release is 4.33.0, commit
`d8b18978322de05a8f3dba51ef03cf5461676c17`. The observed Mathlib Git HEAD is
`db584cd6d46c92f209a44c0f1c829460d327499d`.
The Lake manifest (`lake-manifest.json`) SHA256 is
`a393079054790ace57094dc8ea247e63fbec005a9eff74fe869134f70988348f`.
The audit certificate hashes all **79** Lean inputs: 77 proof modules, the
umbrella and the literal statement challenge. The source-header change record
confirms every preceding Lean file body was retained byte for byte; changes to
mathematical source were added authorship/provenance comments.

The isolated reproduction reused the official fixed executable through PATH
and the pinned external dependency cache, without copying this project's
compiled artifacts. It is a clean project build, not a full external-dependency
rebuild or a clone from a newly published remote repository.

## Reproduction and CI

Install [Elan](https://github.com/leanprover/elan), then run from this project:

```sh
lake exe cache get
python3 scripts/audit.py
lake env leanchecker --fresh -v UnitCircleInterpolation.FinalClassification
python3 scripts/verify_manifest.py
```

The included toolchain and Lake manifest fix Lean and dependency versions.
The wrapper can use the exact Elan/PATH toolchain without `.tools`, and checks
both Lean and Lake. The audit records observed versions and rejects a mismatch.
`verify_manifest.py` verifies content hashes and complete release-file coverage;
in a Git checkout it checks the tracked inventory, and in an extracted archive
it checks regular release files while excluding local build directories.

`.github/workflows/verify.yml` uses fixed official Action SHAs, a read-only
contents permission, bounded execution and one Lean thread. It runs the build,
complete public/literal axiom audit, fresh kernel replay and manifest verifier.
The workflow and its pinned Action inputs were checked. **It has not run on
GitHub.** The Elan installer used by the pinned Action is obtained from its
upstream installer branch; no claim that every installer download is fixed is
made. The Action, Lean release and Mathlib revision are fixed.

Kernel replay uses Lean's own kernel and replays the final module and imported
constants into an empty environment. The literal challenge is a separate
specification/elaboration check. Neither is an independently implemented
external proof checker.

## Attribution and publication status

Public identity and MIT copyright for new contributions are **wang060919**.
`AUTHORS.md` records the substantial Codex proof-construction and verification
assistance. The seven reused modules preserve their original MIT permissions
and original author notices; `PROVENANCE.md` identifies the pinned sources and
historical mathematical authors. No historical result or reused generic code
is claimed as new mathematics or as solely authored by this project.

No project Git commit, repository publication, push or official awards PR was
performed. The planned owner/name and public identity are fixed, while the
verified publication commit SHA and actual GitHub CI/clean-clone links remain
pending. The source manifest cannot replace those future public-history fields.
Whether the unit-circle variant is accepted as a separate prize contribution,
formalization priority and award attribution remain organizer decisions.
