#!/usr/bin/env python3
# Copyright (c) 2026 wang060919. Released under the MIT license.
"""Build, check the complete target, and audit every public proof's axioms."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
LOGS = ROOT / ".work" / "logs"
LOGS.mkdir(parents=True, exist_ok=True)
lean_observed = subprocess.check_output(
    [str(ROOT / "scripts/lake"), "env", "lean", "--version"],
    cwd=ROOT, text=True, stderr=subprocess.STDOUT, timeout=60).strip()
if not lean_observed.startswith("Lean (version 4.33.0, ") or \
        "commit d8b18978322de05a8f3dba51ef03cf5461676c17, Release)" not in lean_observed:
    raise SystemExit(f"Unexpected Lean toolchain: {lean_observed}")
MODULE_RE = re.compile(r"^import UnitCircleInterpolation\.([A-Za-z0-9_]+)$", re.M)
DECL_RE = re.compile(r"^(?:@\[[^\]]+\]\s*)?(?:lemma|theorem)\s+([^\s{(:]+)", re.M)
modules = MODULE_RE.findall((ROOT / "UnitCircleInterpolation.lean").read_text())
declarations = []
hashes = {}
hashes["UnitCircleInterpolation.lean"] = hashlib.sha256(
    (ROOT / "UnitCircleInterpolation.lean").read_bytes()).hexdigest()
for module in modules:
    source = ROOT / "UnitCircleInterpolation" / f"{module}.lean"
    content = source.read_text()
    hashes[str(source.relative_to(ROOT))] = hashlib.sha256(source.read_bytes()).hexdigest()
    declarations.extend("UnitCircleInterpolation." + name for name in DECL_RE.findall(content))
if not declarations or len(declarations) != len(set(declarations)):
    raise SystemExit("Empty or duplicate public theorem inventory")
target = "UnitCircleInterpolation.unitCircleInterpolation_target"
if target not in declarations:
    raise SystemExit("The full target theorem is absent from the imported proof inventory")
challenge = ROOT / "verification" / "OriginalStatement.lean"
hashes[str(challenge.relative_to(ROOT))] = hashlib.sha256(challenge.read_bytes()).hexdigest()
challenge_declarations = ["OriginalUnitCircleStatement." + name for name in
    ("literalMaximum_eq", "literalMinimizer_iff", "literalRegular_iff",
     "original_classification", "original_lower_bound")]

probe = LOGS / "development-axioms.lean"
probe.write_text("import UnitCircleInterpolation\n\n"
    f"example : UnitCircleInterpolation.Target := {target}\n\n" + "\n".join(
    f"#check {name}\n#print axioms {name}" for name in declarations) + "\n")
commands = [([str(ROOT / "scripts/lake"), "build"], "development-build.log"),
            ([str(ROOT / "scripts/lake"), "env", "lean", str(probe)], "development-axioms.log"),
            ([str(ROOT / "scripts/lake"), "env", "lean", str(challenge)], "original-statement.log")]
for command, filename in commands:
    with (LOGS / filename).open("w") as stream:
        try:
            result = subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT,
                                    timeout=600)
        except subprocess.TimeoutExpired:
            raise SystemExit(f"Timed out: inspect {LOGS / filename}")
    if result.returncode != 0:
        raise SystemExit(f"Command failed ({result.returncode}): inspect {LOGS / filename}")

mathlib_observed = subprocess.check_output(
    ["git", "-C", str(ROOT / ".lake/packages/mathlib"), "rev-parse", "HEAD"],
    text=True, stderr=subprocess.STDOUT, timeout=60).strip()
if mathlib_observed != "db584cd6d46c92f209a44c0f1c829460d327499d":
    raise SystemExit(f"Unexpected Mathlib revision: {mathlib_observed}")

output = (LOGS / "development-axioms.log").read_text() + (LOGS / "original-statement.log").read_text()
observed = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output))
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name in declarations + challenge_declarations:
    if name not in observed:
        raise SystemExit(f"Missing axiom result: {name}")
    axioms = {item.strip() for item in observed[name].split(",") if item.strip()}
    if not axioms <= allowed:
        raise SystemExit(f"Unexpected axioms for {name}: {sorted(axioms - allowed)}")
for source, old_hash in hashes.items():
    if hashlib.sha256((ROOT / source).read_bytes()).hexdigest() != old_hash:
        raise SystemExit(f"Source changed during audit: {source}")

result = {"scope": "complete all-positive-N unit-circle minimizer target and imported public proofs",
          "target": target,
          "module_count": len(modules),
          "challenge_theorems": challenge_declarations,
          "theorem_count": len(declarations), "theorems": declarations,
          "source_sha256": hashes, "allowed_axioms": sorted(allowed),
          "lean": "4.33.0", "lean_version_output": lean_observed,
          "mathlib": mathlib_observed}
(LOGS / "development-audit.json").write_text(json.dumps(result, indent=2) + "\n")
print(f"Build passed; {len(declarations)} public theorems audited with only standard axioms.")
print(f"The complete all-positive-N Target was type-checked using {target}.")
