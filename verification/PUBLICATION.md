# Public version and verification references

Public project author and maintainer: **wang060919**.
Public repository created on **2026-10-12 (Asia/Shanghai)**:
[wang060919/jsp-000936-unit-circle-lean](https://github.com/wang060919/jsp-000936-unit-circle-lean).
Branch: `main`.

## Select the verified public version

Use a full 40-character SHA from the [main commit history](https://github.com/wang060919/jsp-000936-unit-circle-lean/commits/main/).
The [Lean verification workflow](https://github.com/wang060919/jsp-000936-unit-circle-lean/actions/workflows/verify.yml) identifies
the exact `head_sha` checked by each run. Use the successful run corresponding
to the selected proof commit; a workflow configuration or a different commit's
result does not establish that version's online verification.

The workflow installs the pinned Lean release, retrieves Mathlib's dependency
cache, builds the complete project, audits the full Target and all 771 public
and five literal-statement proof declarations, replays the final module and
its imports in a fresh Lean kernel environment, and verifies the complete
release manifest. Source code and local verification records are included.

For reproduction, use the selected SHA in the clean-clone commands in
[README.md](../README.md#reproduction-from-the-public-repository).
The 2026-10-11 [local verification report](REPORT.md) and
[prepublication review](RELEASE-REVIEW.md) are historical snapshots, with all
79 current Lean input hashes recorded in `evidence/development-audit.json`.

## Award submission status

The public [scope question #5007](https://github.com/TheJustinSunPrize/awards/issues/5007)
asks whether the complete unit-circle result can be reviewed separately or
jointly with a separately attributed real-interval proof. No official awards
contribution PR or claim has been submitted. Publishing this proof repository
and running CI do not determine scope acceptance, authorship eligibility,
formalization priority or an award.

See [AUTHORS.md](../AUTHORS.md) for the actual development workflow and
[PROVENANCE.md](../PROVENANCE.md) for third-party code and historical mathematics.
