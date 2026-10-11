# Unit-circle interpolation formalization

Scope: this project only. Preserve the official awards repository and the selection audit.

- Prove the original unit-circle problem for every positive node count, arbitrary distinct unit-modulus complex nodes, and the full classification of minimizers up to rotation and permutation.
- Lean is fixed to 4.33.0; Mathlib is fixed to db584cd6d46c92f209a44c0f1c829460d327499d. Preserve the resolved Lake manifest.
- Run the project-local `scripts/lake` wrapper while using the local toolchain. Keep builds bounded and limit Lean parallelism to suit available memory.
- Add no `sorry`, `admit`, custom axioms, `native_decide`, unsafe proof substitutes, skipped kernel checks, or assumptions standing in for missing mathematics. An unproved goal belongs in the plan, never in the proved theorem chain.
- Keep the literal cardinal, maximum, injectivity, unit-circle domain and positive-N requirements visible. Definitions of targets are not proofs of targets.
- Retain attribution and licenses for reused code. A previous real-interval proof is not our original circle formalization.
- Record actual compiler and axiom outputs. Do not describe static review, an uncompiled statement, or a partial layer as a complete proof.
- Coordinate file ownership between agents. Never commit, push, submit or contact others without the applicable user authorization.
