#!/usr/bin/env bash
set -euo pipefail

# Build from the checked-out source tree by default.  An explicitly supplied
# `LEANPHY_BUILD_ROOT` can still select a local mirror (for example when a
# mounted workspace is slow), but silently choosing a stale mirror would make
# the regression script validate different sources from the ones under review.
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BUILD_ROOT="${LEANPHY_BUILD_ROOT:-${PROJECT_ROOT}}"
if [[ ! -f "${BUILD_ROOT}/lakefile.toml" ]]; then
  echo "verification failed: build root has no lakefile.toml: ${BUILD_ROOT}" >&2
  exit 1
fi
export PATH="/root/.elan/bin:${PATH}"

cd "${BUILD_ROOT}"
lake build
# The lightweight public profiles are separate library modules and are not
# dependencies of the monolithic `LeanPhy` target.  Compile them explicitly so
# a change in the import surface cannot pass the main build unnoticed.
lake build LeanPhy.Minimal \
  LeanPhy.Entry.Quantum LeanPhy.Entry.Research \
  LeanPhy.Entry.FieldTheory LeanPhy.Entry.Condensed \
  LeanPhy.Entry.Gauge LeanPhy.Entry.HighEnergy \
  LeanPhy.Entry.Classical LeanPhy.Entry.Optics LeanPhy.Entry.Fluid LeanPhy.Entry.Relativity \
  LeanPhy.Entry.StatMech LeanPhy.Entry.FinitePDE LeanPhy.Entry.Analysis \
  LeanPhy.Mathematics.SpectralCalculus LeanPhy.Mathematics.SpectralGap \
  LeanPhy.Entry.Physics \
  LeanPhy.Mathematics.SymmetryReduction LeanPhy.Mathematics.ConstraintAlgebra \
  LeanPhy.Mathematics.ConstraintMap LeanPhy.Mathematics.BRST \
  LeanPhy.Mathematics.GradedBRST \
  LeanPhy.CLI LeanPhy.Examples.ClosedLoop \
  LeanPhy.Examples.PhysicsTactic \
  LeanPhy.Library \
  LeanPhy.Examples.ApproximateModel \
  LeanPhy.Examples.ResearchPackageTemplate LeanPhy.Examples.ClientProject \
  LeanPhy.Scaffold leanphy_client_regression leanphy_strict_client leanphy_init

# The project generator is part of the public workflow.  Exercise it without
# building the generated project (which would intentionally resolve the
# downstream dependency graph again); the generated source is then checked for
# the expected no-fake-claim starting point.
SCAFFOLD_DIR="/tmp/leanphy-scaffold.$$"
trap 'rm -rf "${SCAFFOLD_DIR}"' EXIT
lake exe leanphy_init "${SCAFFOLD_DIR}" --name verify_physics \
  --profile minimal --leanphy-path "${BUILD_ROOT}" >/dev/null
if ! rg -q 'name = "verify_physics"' "${SCAFFOLD_DIR}/lakefile.toml"; then
  echo "verification failed: scaffold omitted the project name" >&2
  exit 1
fi
if [[ "$(cat "${SCAFFOLD_DIR}/lean-toolchain")" != "leanprover/lean4:v4.34.0" ]]; then
  echo "verification failed: scaffold omitted the pinned Lean toolchain" >&2
  exit 1
fi
if ! rg -q '\|>\.addPackage package\)' "${SCAFFOLD_DIR}/Research.lean"; then
  echo "verification failed: scaffold inserted a fake checked claim" >&2
  exit 1
fi
if ! rg -q 'addBoundaryText' "${SCAFFOLD_DIR}/Research.lean"; then
  echo "verification failed: scaffold omitted the boundary ledger API" >&2
  exit 1
fi
if ! rg -q 'by physics' "${SCAFFOLD_DIR}/README.md"; then
  echo "verification failed: scaffold README omitted the public physics tactic" >&2
  exit 1
fi
if ! rg -q 'by physics_search' "${SCAFFOLD_DIR}/README.md"; then
  echo "verification failed: scaffold README omitted theorem search" >&2
  exit 1
fi
if ! rg -q 'lake build' "${SCAFFOLD_DIR}/scripts/verify-leanphy.sh"; then
  echo "verification failed: scaffold omitted the CI verification script" >&2
  exit 1
fi
if ! rg -q 'verify-leanphy\.sh' "${SCAFFOLD_DIR}/.github/workflows/leanphy.yml"; then
  echo "verification failed: scaffold omitted the GitHub Actions verification step" >&2
  exit 1
fi
# An existing empty destination directory is accepted (the common `mktemp -d`
# workflow).  A full generated-project build is available for release jobs;
# it is opt-in here because Lake may need to fetch mathlib again in a clean
# temporary directory.
if [[ "${LEANPHY_VERIFY_SCAFFOLD_BUILD:-0}" == "1" ]]; then
  (cd "${SCAFFOLD_DIR}" && lake build >/dev/null)
  if ! (cd "${SCAFFOLD_DIR}" && lake exe verify_physics_check --project-json >/dev/null); then
    echo "verification failed: generated downstream project could not run its CLI" >&2
    exit 1
  fi
fi
if lake exe leanphy_init "${SCAFFOLD_DIR}" --name verify_physics >/dev/null 2>&1; then
  echo "verification failed: scaffold overwrote an existing project without --force" >&2
  exit 1
fi

PROTOTYPE_LOG="$(mktemp /tmp/leanphy-prototype.XXXXXX.log)"
lake exe leanphy_prototype | tee "${PROTOTYPE_LOG}"
PROTOTYPE_COUNT="$(rg -c '^\[proved\]' "${PROTOTYPE_LOG}")"
if (( PROTOTYPE_COUNT < 6 )); then
  echo "verification failed: closed-loop prototype reported only ${PROTOTYPE_COUNT} proved obligations" >&2
  exit 1
fi

SMOKE_LOG="$(mktemp /tmp/leanphy-smoke.XXXXXX.log)"
lake exe leanphy_smoke | tee "${SMOKE_LOG}"
OK_COUNT="$(rg -c '^  \[ok\]' "${SMOKE_LOG}")"
if (( OK_COUNT < 450 )); then
  echo "verification failed: expected at least 450 smoke capabilities, got ${OK_COUNT}" >&2
  exit 1
fi

PACKAGE_LOG="$(mktemp /tmp/leanphy-packages.XXXXXX.log)"
lake exe leanphy_check | tee "${PACKAGE_LOG}"
PACKAGE_COUNT="$(rg -c '^Status: VERIFIED-CONDITIONAL$' "${PACKAGE_LOG}")"
if (( PACKAGE_COUNT < 8 )); then
  echo "verification failed: expected eight conditional theory packages, got ${PACKAGE_COUNT}" >&2
  exit 1
fi
if ! rg -q 'LeanPhy\.Quantum\.Pauli' "${PACKAGE_LOG}"; then
  echo "verification failed: package report omitted theorem provenance" >&2
  exit 1
fi

# The same compiled ledgers also expose a stable machine-readable projection.
# Parse it with Python so malformed quoting or a dropped package cannot pass
# merely because the human report still looks plausible.
PACKAGE_JSON_LOG="$(mktemp /tmp/leanphy-packages-json.XXXXXX.log)"
lake exe leanphy_check --json >"${PACKAGE_JSON_LOG}"
python3 - "${PACKAGE_JSON_LOG}" <<'PY'
import json
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
packages = json.loads(path.read_text(encoding="utf-8"))
if len(packages) != 8:
    raise SystemExit(f"verification failed: JSON report contains {len(packages)} packages")
if any(p.get("status") != "VERIFIED-CONDITIONAL" for p in packages):
    raise SystemExit("verification failed: JSON report has an unexpected package status")
if any(not p.get("id", "").startswith("leanphy.package:") for p in packages):
    raise SystemExit("verification failed: JSON report omitted stable package ids")
if not any(
    claim.get("source") == "LeanPhy.Quantum.Pauli"
    for package in packages
    for claim in package.get("claims", [])
):
    raise SystemExit("verification failed: JSON report omitted theorem provenance")
if any(
    not claim.get("id", "").startswith("leanphy.claim:")
    for package in packages
    for claim in package.get("claims", [])
):
    raise SystemExit("verification failed: JSON report omitted stable claim ids")
if not all(
    claim.get("requires")
    for package in packages
    for claim in package.get("claims", [])
):
    raise SystemExit("verification failed: JSON report omitted assumption links")
if any(package.get("unresolved_assumption_links") for package in packages):
    raise SystemExit("verification failed: package contains an unresolved assumption link")
if any(package.get("unresolved_claim_links") for package in packages):
    raise SystemExit("verification failed: package contains an unresolved claim link")
if not all(package.get("open_obligations") for package in packages):
    raise SystemExit("verification failed: package report omitted open-obligation ledger")
if any(package.get("diagnostics") for package in packages):
    raise SystemExit("verification failed: package report contains ledger diagnostics")
PY

CATALOG_LOG="$(mktemp /tmp/leanphy-catalog.XXXXXX.log)"
lake exe leanphy_check --catalog-json >"${CATALOG_LOG}"
python3 - "${CATALOG_LOG}" <<'PY'
import json
import pathlib
import sys

catalog = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if len(catalog) < 7:
    raise SystemExit("verification failed: reusable lemma catalogue is unexpectedly small")
if any(entry.get("status") != "kernel_checked" for entry in catalog):
    raise SystemExit("verification failed: lemma catalogue contains a non-checked entry")
if not any("commutator" in entry.get("tags", []) for entry in catalog):
    raise SystemExit("verification failed: lemma catalogue omitted a commutator entry")
if any(not entry.get("id", "").startswith("leanphy.lemma:") for entry in catalog):
    raise SystemExit("verification failed: lemma catalogue omitted stable ids")
PY

CLAIMS_LOG="$(mktemp /tmp/leanphy-claims.XXXXXX.log)"
lake exe leanphy_check --claims-json >"${CLAIMS_LOG}"
python3 - "${CLAIMS_LOG}" <<'PY'
import json
import pathlib
import sys

claims = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if len(claims) < 15:
    raise SystemExit("verification failed: flat claim index is unexpectedly small")
if any(claim.get("status") != "kernel_checked" for claim in claims):
    raise SystemExit("verification failed: flat claim index contains an unchecked claim")
if any(not claim.get("package") for claim in claims):
    raise SystemExit("verification failed: flat claim index omitted package provenance")
if not any("Pauli" in claim.get("name", "") for claim in claims):
    raise SystemExit("verification failed: flat claim index omitted a quantum claim")
PY

# The project-level projection is the boundary used when one paper combines
# several domain packages.  Keep its JSON contract tested separately from the
# legacy per-package array.
PROJECT_JSON_LOG="$(mktemp /tmp/leanphy-project-json.XXXXXX.log)"
lake exe leanphy_check --project-json >"${PROJECT_JSON_LOG}"
python3 - "${PROJECT_JSON_LOG}" <<'PY'
import json
import pathlib
import sys

project = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if project.get("schema_version") != "1":
    raise SystemExit("verification failed: project report has an unsupported schema")
if project.get("status") != "VERIFIED-CONDITIONAL":
    raise SystemExit("verification failed: project report has an unexpected status")
if project.get("invalid_packages"):
    raise SystemExit("verification failed: project report lists invalid packages")
if project.get("diagnostics"):
    raise SystemExit("verification failed: project report contains project diagnostics")
if len(project.get("packages", [])) != 8:
    raise SystemExit("verification failed: project report omitted a package")
if project.get("package_count") != 8:
    raise SystemExit("verification failed: project report has an incorrect package count")
if project.get("claim_count", 0) < 15:
    raise SystemExit("verification failed: project report has an unexpectedly small claim count")
if project.get("open_obligation_count", 0) == 0:
    raise SystemExit("verification failed: project report hid open obligations")
if any(package.get("diagnostics") for package in project["packages"]):
    raise SystemExit("verification failed: project report contains ledger diagnostics")
PY

# The extended profile exercises the same ledger with field-theory, high-energy
# and bounded-analysis adapters.  It is intentionally separate from the
# default eight-package compatibility report.
EXTENDED_JSON_LOG="$(mktemp /tmp/leanphy-extended-json.XXXXXX.log)"
lake exe leanphy_check --extended --project-json >"${EXTENDED_JSON_LOG}"
python3 - "${EXTENDED_JSON_LOG}" <<'PY'
import json
import pathlib
import sys

project = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if project.get("status") != "VERIFIED-CONDITIONAL":
    raise SystemExit("verification failed: extended project report has an unexpected status")
if len(project.get("packages", [])) != 11:
    raise SystemExit("verification failed: extended project omitted a domain package")
if project.get("package_count") != 11:
    raise SystemExit("verification failed: extended project has an incorrect package count")
expected = {
    "finite field-theory algebra",
    "finite high-energy algebra",
    "bounded analysis and numerical bridges",
}
names = {package.get("name") for package in project["packages"]}
if not expected.issubset(names):
    raise SystemExit("verification failed: extended project omitted one of the new packages")
if project.get("diagnostics"):
    raise SystemExit("verification failed: extended project contains diagnostics")
PY
if lake exe leanphy_check --extended --strict --project-json >/dev/null 2>/dev/null; then
  echo "verification failed: strict mode accepted open research obligations" >&2
  exit 1
fi

# The broad profile checks that adding optics/AMO and fluid/plasma adapters
# preserves the same conditional-verification contract.
BROAD_JSON_LOG="$(mktemp /tmp/leanphy-broad-json.XXXXXX.log)"
lake exe leanphy_check --broad --project-json >"${BROAD_JSON_LOG}"
python3 - "${BROAD_JSON_LOG}" <<'PY'
import json
import pathlib
import sys

project = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if project.get("status") != "VERIFIED-CONDITIONAL":
    raise SystemExit("verification failed: broad project report has an unexpected status")
if project.get("package_count") != 13 or len(project.get("packages", [])) != 13:
    raise SystemExit("verification failed: broad project does not contain 13 packages")
names = {package.get("name") for package in project["packages"]}
expected = {"finite optics and AMO", "finite fluid and plasma transport"}
if not expected.issubset(names):
    raise SystemExit("verification failed: broad project omitted optics or fluid package")
if project.get("claim_count", 0) < 24:
    raise SystemExit("verification failed: broad project claim count is unexpectedly small")
if project.get("open_obligation_count", 0) == 0:
    raise SystemExit("verification failed: broad project hid open research obligations")
if project.get("diagnostics"):
    raise SystemExit("verification failed: broad project contains diagnostics")
claims = [claim for package in project["packages"] for claim in package.get("claims", [])]
if not any("Optics" in claim.get("source", "") for claim in claims):
    raise SystemExit("verification failed: broad project omitted optics theorem provenance")
if not any("FiniteDivergence" in claim.get("source", "") for claim in claims):
    raise SystemExit("verification failed: broad project omitted fluid theorem provenance")
PY
BROAD_CLAIMS_LOG="$(mktemp /tmp/leanphy-broad-claims.XXXXXX.log)"
lake exe leanphy_check --broad --claims-json >"${BROAD_CLAIMS_LOG}"
python3 - "${BROAD_CLAIMS_LOG}" <<'PY'
import json
import pathlib
import sys

claims = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if len(claims) < 24:
    raise SystemExit("verification failed: broad flat claim index is unexpectedly small")
if any(claim.get("status") != "kernel_checked" for claim in claims):
    raise SystemExit("verification failed: broad flat claim index contains an unchecked claim")
PY
if lake exe leanphy_check --broad --strict --project-json >/dev/null 2>/dev/null; then
  echo "verification failed: broad strict mode accepted open research obligations" >&2
  exit 1
fi

MANIFEST_LOG="$(mktemp /tmp/leanphy-manifest.XXXXXX.log)"
lake exe leanphy_check --extended --manifest-json >"${MANIFEST_LOG}"
python3 - "${MANIFEST_LOG}" <<'PY'
import json
import pathlib
import sys

manifest = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if manifest.get("schema_version") != "1":
    raise SystemExit("verification failed: manifest report has an unsupported schema")
if manifest.get("status") != "VERIFIED-CONDITIONAL":
    raise SystemExit("verification failed: manifest status is not conditional-verified")
if manifest.get("toolchain", {}).get("lean") != "v4.34.0":
    raise SystemExit("verification failed: manifest omitted the Lean toolchain")
if "LeanPhy.Entry.FieldTheory" not in manifest.get("profiles", []):
    raise SystemExit("verification failed: manifest omitted the field-theory profile")
if manifest.get("claim_count", 0) < 20:
    raise SystemExit("verification failed: manifest claim count is unexpectedly small")
if manifest.get("open_obligation_count", 0) == 0:
    raise SystemExit("verification failed: manifest hid open research obligations")
PY

# Compile and execute a downstream-style client that imports only the public
# umbrella and CLI.  This guards the reusable integration surface separately
# from the built-in catalogue used by `leanphy_check`.
CLIENT_JSON_LOG="$(mktemp /tmp/leanphy-client-json.XXXXXX.log)"
lake exe leanphy_client_regression --project-json >"${CLIENT_JSON_LOG}"
python3 - "${CLIENT_JSON_LOG}" <<'PY'
import json
import pathlib
import sys

project = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if project.get("name") != "client project":
    raise SystemExit("verification failed: downstream client report used the wrong project")
if project.get("status") != "VERIFIED-CONDITIONAL":
    raise SystemExit("verification failed: downstream client report is not conditional-verified")
if project.get("package_count") != 2 or project.get("claim_count") != 2:
    raise SystemExit("verification failed: downstream client report lost its checked claim")
edges = project.get("dependency_edges", [])
if edges != [{"target": "client derived algebra::Pauli commutator derived from XY product",
              "dependency": "client Pauli model::Pauli XY product"}]:
    raise SystemExit("verification failed: downstream client report lost its dependency edge")
if project.get("dependency_edge_count") != 1:
    raise SystemExit("verification failed: downstream client report has a wrong edge count")
if project.get("schema_version") != "1":
    raise SystemExit("verification failed: downstream client report has an unsupported schema")
if project.get("diagnostics"):
    raise SystemExit("verification failed: downstream client report contains diagnostics")
PY
if lake exe leanphy_client_regression --json --project-json >/dev/null 2>/dev/null; then
  echo "verification failed: CLI accepted conflicting output modes" >&2
  exit 1
fi
if lake exe leanphy_client_regression --unknown-option >/dev/null 2>/dev/null; then
  echo "verification failed: CLI accepted an unknown option" >&2
  exit 1
fi
STRICT_JSON_LOG="$(mktemp /tmp/leanphy-strict-client.XXXXXX.log)"
lake exe leanphy_strict_client --strict --project-json >"${STRICT_JSON_LOG}"
python3 - "${STRICT_JSON_LOG}" <<'PY'
import json
import pathlib
import sys

project = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if project.get("status") != "VERIFIED-CONDITIONAL":
    raise SystemExit("verification failed: strict client report is not verified")
if project.get("claim_count") != 1:
    raise SystemExit("verification failed: strict client lost its theorem claim")
if project.get("open_obligation_count") != 0:
    raise SystemExit("verification failed: strict client unexpectedly has obligations")
PY
DOT_LOG="$(mktemp /tmp/leanphy-client-dot.XXXXXX.log)"
lake exe leanphy_client_regression --dot >"${DOT_LOG}"
if ! rg -q '^digraph LeanPhy \{$' "${DOT_LOG}"; then
  echo "verification failed: DOT report has no graph header" >&2
  exit 1
fi
if ! rg -q 'client derived algebra::Pauli commutator derived from XY product' "${DOT_LOG}"; then
  echo "verification failed: DOT report omitted the derived claim node" >&2
  exit 1
fi

# Strip nested Lean comments before checking; documentation may discuss these words.
python3 "${PROJECT_ROOT}/scripts/check_declarations.py"

AXIOM_LOG="$(mktemp /tmp/leanphy-axioms.XXXXXX.log)"
lake env lean "${PROJECT_ROOT}/scripts/axioms.lean" | tee "${AXIOM_LOG}"
if rg -n 'sorryAx|Lean\.ofReduceBool' "${AXIOM_LOG}"; then
  echo "verification failed: untrusted axiom dependency found" >&2
  exit 1
fi

# Scan every locally defined LeanPhy declaration, not only a representative list.
lake env lean "${PROJECT_ROOT}/scripts/audit_all.lean"

python3 "${PROJECT_ROOT}/scripts/test_negative_runner.py"
"${PROJECT_ROOT}/scripts/negative_tests.sh"

echo "LeanPhy verification passed: ${OK_COUNT} smoke capabilities; representative theorems have no sorryAx."
