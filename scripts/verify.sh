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
  LeanPhy.Mathematics.LieCohomology \
  LeanPhy.CLI LeanPhy.Examples.ClosedLoop \
  LeanPhy.Examples.PhysicsTactic \
  LeanPhy.Library \
  LeanPhy.Examples.ApproximateModel \
  LeanPhy.Examples.ResearchPackageTemplate LeanPhy.Examples.ClientProject \
  LeanPhy.Scaffold leanphy_client_regression leanphy_strict_client leanphy_init \
  leanphy_ghost_research leanphy_lie_research leanphy_structure_research leanphy_parameter_research \
  leanphy_automatic_parameters leanphy_symbolic_lie leanphy_model_domains leanphy_deformations leanphy_adjoint_deformations leanphy_second_order leanphy_deformation_gauge leanphy_third_cohomology leanphy_parameter_obstructions leanphy_third_order leanphy_third_search leanphy_lie_ghost

# New shared operations and independent research clients are release targets.
lake build LeanPhy.Workflow.Core LeanPhy.CLI.Core LeanPhy.Library.Core \
  LeanPhy.FieldTheory.Variational LeanPhy.FieldTheory.VariationalResidual \
  LeanPhy.Classical.VariationalBridge leanphy_obligation_client \
  leanphy_variational_client leanphy_source_client leanphy_effective_client \
  leanphy_fermion_client leanphy_dynamics_client leanphy_exploration_client leanphy_matrix_certificate_client leanphy_action_evaluation_client leanphy_fermion_word_client leanphy_self_consistency_client leanphy_field_redefinition_client leanphy_finite_lattice_client leanphy_index

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
if ! rg -q '#leanphy_audit_module' "${SCAFFOLD_DIR}/Research.lean" || \
   ! rg -q 'audit_project.py' "${SCAFFOLD_DIR}/scripts/verify-leanphy.sh"; then
  echo "verification failed: scaffold omitted declaration dependency auditing" >&2
  exit 1
fi
if ! cmp -s "${PROJECT_ROOT}/scripts/audit_project.py" "${SCAFFOLD_DIR}/scripts/audit_project.py"; then
  echo "verification failed: scaffold copied a stale or different project verifier" >&2
  exit 1
fi
if ! rg -q 'verify-leanphy\.sh' "${SCAFFOLD_DIR}/.github/workflows/leanphy.yml"; then
  echo "verification failed: scaffold omitted the GitHub Actions verification step" >&2
  exit 1
fi
# An existing empty destination directory is accepted (the common `mktemp -d`
# workflow).  A full generated-project build is available for release jobs;
# it is opt-in here because Lake may need to fetch mathlib again in a clean
# temporary directory. The project-audit regression below always checks a real
# generated project using the already installed, pinned dependency artifacts.
if [[ "${LEANPHY_VERIFY_SCAFFOLD_BUILD:-0}" == "1" ]]; then
  (cd "${SCAFFOLD_DIR}" && bash scripts/verify-leanphy.sh >/dev/null)
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
if (( OK_COUNT < 777 )); then
  echo "verification failed: expected at least 777 smoke capabilities, got ${OK_COUNT}" >&2
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
ghost_entries = {"ghost_koszul_nilpotency", "ghost_left_derivative_car",
                 "ghost_quadratic_nilpotency", "ghost_quadratic_nontriviality",
                 "ghost_finite_nilpotency_criterion", "lie_ghost_degree_one_bridge",
                 "lie_ghost_jacobi_nilpotency", "lie_ghost_degree_two_bridge",
                 "lie_ghost_integer_degree", "ghost_koszul_integer_degree",
                 "lie_ghost_homogeneous_primitive", "lie_ghost_scalar_boundary",
                 "lie_ghost_closed_reflection", "lie_ghost_exact_reflection",
                 "lie_ghost_h2_equivalence", "lie_ghost_complete_coordinates",
                 "lie_matter_nilpotent", "lie_matter_degree", "lie_matter_invariants", "lie_matter_cocycle"}
if not ghost_entries.issubset({entry.get("name") for entry in catalog}):
    raise SystemExit("verification failed: lemma catalogue omitted ghost derivative theorems")
lie_entries = {"lie_d2_d1", "lie_h2_zero_iff_boundary", "central_extension_classification",
               "cohomology_reduction_exactness", "heisenberg_h2_dimension",
               "finite_lie_cocycle_check", "generated_vector_h2_dimension",
               "diagonal_cohomology_exactness", "solvable_family_dimension",
               "generated_solvable_strata_dimension", "generated_determinant_strata_dimension",
               "symbolic_heisenberg_dimension", "symbolic_vector_exactness", "discovered_lie_model_domain",
               "adjoint_h2_deformation_classification", "second_order_deformation_obstruction", "intrinsic_h3_extension_criterion", "parameter_actual_h3", "parameter_intrinsic_extension", "intrinsic_obstruction_closed",
               "joint_third_search_criterion", "joint_third_search_all_models", "joint_third_search_nonexistence",
               "third_order_model_criterion", "third_order_intrinsic_obstruction", "third_order_computed_correction",
               "computed_adjoint_deformation_equivalence", "computed_deformation_representatives_unique"}
if not lie_entries.issubset({entry.get("name") for entry in catalog}):
    raise SystemExit("verification failed: lemma catalogue omitted degree-two Lie theorems")
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
if manifest.get("toolchain", {}).get("leanphy") != pathlib.Path("VERSION").read_text().strip():
    raise SystemExit("verification failed: manifest LeanPhy version does not match VERSION")
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

# A finite research calculation exports real proofs and retains its open obligations.
GHOST_JSON_LOG="$(mktemp /tmp/leanphy-ghost-project.XXXXXX.log)"
lake exe leanphy_ghost_research --project-json >"${GHOST_JSON_LOG}"
python3 - "${GHOST_JSON_LOG}" <<'PY'
import json
import pathlib
import sys

project = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if project.get("status") != "VERIFIED-CONDITIONAL" or project.get("diagnostics"):
    raise SystemExit("verification failed: finite ghost research report is malformed")
if (project.get("package_count"), project.get("claim_count"),
        project.get("open_obligation_count")) != (1, 11, 2):
    raise SystemExit("verification failed: finite ghost report lost claims or open obligations")
claims = project["packages"][0]["claims"]
if any(not claim.get("source", "").startswith("LeanPhy.Examples.GhostResearch.")
       or not claim.get("requires") for claim in claims):
    raise SystemExit("verification failed: finite ghost claim lost provenance or assumptions")
PY
if lake exe leanphy_ghost_research --strict --project-json >/dev/null 2>/dev/null; then
  echo "verification failed: strict mode accepted open ghost interpretation obligations" >&2
  exit 1
fi

# Degree-two research distinguishes nonzero cochains from nonzero quotient classes.
LIE_JSON_LOG="$(mktemp /tmp/leanphy-lie-project.XXXXXX.log)"
lake exe leanphy_lie_research --project-json >"${LIE_JSON_LOG}"
python3 - "${LIE_JSON_LOG}" <<'PY'
import json
import pathlib
import sys

project = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if project.get("status") != "VERIFIED-CONDITIONAL" or project.get("diagnostics"):
    raise SystemExit("verification failed: Lie cohomology research report is malformed")
if (project.get("package_count"), project.get("claim_count"),
        project.get("open_obligation_count")) != (1, 16, 2):
    raise SystemExit("verification failed: Lie cohomology report lost claims or obligations")
claims = project["packages"][0]["claims"]
if any(not claim.get("source", "").startswith("LeanPhy.Examples.LieCohomologyResearch.")
       or not claim.get("requires") for claim in claims):
    raise SystemExit("verification failed: Lie cohomology claim lost provenance or assumptions")
PY
if lake exe leanphy_lie_research --strict --project-json >/dev/null 2>/dev/null; then
  echo "verification failed: strict mode accepted open Lie cohomology interpretation obligations" >&2
  exit 1
fi

# Structure constants and coefficient actions produce an independent research ledger.
STRUCTURE_JSON_LOG="$(mktemp /tmp/leanphy-structure-project.XXXXXX.log)"
lake exe leanphy_structure_research --project-json >"${STRUCTURE_JSON_LOG}"
python3 - "${STRUCTURE_JSON_LOG}" <<'PYREPORT'
import json
import pathlib
import sys

project = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if project.get("status") != "VERIFIED-CONDITIONAL" or project.get("diagnostics"):
    raise SystemExit("verification failed: structure constant report is malformed")
if (project.get("package_count"), project.get("claim_count"),
        project.get("open_obligation_count")) != (1, 10, 1):
    raise SystemExit("verification failed: structure constant report lost claims or obligations")
if any(not c.get("source", "").startswith("LeanPhy.Examples.StructureConstantResearch.")
       or not c.get("requires") for c in project["packages"][0]["claims"]):
    raise SystemExit("verification failed: structure constant claim lost provenance or assumptions")
PYREPORT
if lake exe leanphy_structure_research --strict --project-json >/dev/null 2>/dev/null; then
  echo "verification failed: strict mode accepted open structure constant interpretation obligations" >&2
  exit 1
fi

# A symbolic family retains parameter conditions and physical interpretation obligations.
PARAMETER_JSON_LOG="$(mktemp /tmp/leanphy-parameter-project.XXXXXX.log)"
lake exe leanphy_parameter_research --project-json >"${PARAMETER_JSON_LOG}"
python3 - "${PARAMETER_JSON_LOG}" <<'PYREPORT'
import json
import pathlib
import sys

project = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if project.get("status") != "VERIFIED-CONDITIONAL" or project.get("diagnostics"):
    raise SystemExit("verification failed: parameter cohomology report is malformed")
if (project.get("package_count"), project.get("claim_count"),
        project.get("open_obligation_count")) != (1, 12, 1):
    raise SystemExit("verification failed: parameter cohomology report lost claims or obligations")
if any(not c.get("source", "").startswith("LeanPhy.Examples.ParameterCohomologyResearch.")
       or not c.get("requires") for c in project["packages"][0]["claims"]):
    raise SystemExit("verification failed: parameter cohomology claim lost provenance or assumptions")
PYREPORT
if lake exe leanphy_parameter_research --strict --project-json >/dev/null 2>/dev/null; then
  echo "verification failed: strict mode accepted open parameter interpretation obligations" >&2
  exit 1
fi

# Automatic branches must report their proof provenance and remaining interpretation task.
AUTOMATIC_JSON_LOG="$(mktemp /tmp/leanphy-automatic-project.XXXXXX.log)"
lake exe leanphy_automatic_parameters --project-json >"${AUTOMATIC_JSON_LOG}"
python3 - "${AUTOMATIC_JSON_LOG}" <<'PYREPORT'
import json
import pathlib
import sys

project = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if project.get("status") != "VERIFIED-CONDITIONAL" or project.get("diagnostics"):
    raise SystemExit("verification failed: automatic parameter report is malformed")
if (project.get("package_count"), project.get("claim_count"),
        project.get("open_obligation_count")) != (1, 13, 1):
    raise SystemExit("verification failed: automatic parameter report lost claims or obligations")
if any(not c.get("source", "").startswith("LeanPhy.Examples.AutomatedParameterResearch.")
       or not c.get("requires") for c in project["packages"][0]["claims"]):
    raise SystemExit("verification failed: automatic parameter report lost proof provenance")
PYREPORT
if lake exe leanphy_automatic_parameters --strict --project-json >/dev/null 2>/dev/null; then
  echo "verification failed: strict mode accepted open automatic parameter interpretation obligations" >&2
  exit 1
fi

# Symbolic Lie inputs retain model conditions and the physical interpretation task.
SYMBOLIC_JSON_LOG="$(mktemp /tmp/leanphy-symbolic-lie-project.XXXXXX.log)"
lake exe leanphy_symbolic_lie --project-json >"${SYMBOLIC_JSON_LOG}"
python3 - "${SYMBOLIC_JSON_LOG}" <<'PYREPORT'
import json
import pathlib
import sys

project = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if project.get("status") != "VERIFIED-CONDITIONAL" or project.get("diagnostics"):
    raise SystemExit("verification failed: symbolic Lie report is malformed")
if (project.get("package_count"), project.get("claim_count"),
        project.get("open_obligation_count")) != (1, 14, 1):
    raise SystemExit("verification failed: symbolic Lie report lost claims or obligations")
if any(not c.get("source", "").startswith("LeanPhy.Examples.SymbolicLieResearch.")
       or not c.get("requires") for c in project["packages"][0]["claims"]):
    raise SystemExit("verification failed: symbolic Lie report lost proof provenance")
PYREPORT
if lake exe leanphy_symbolic_lie --strict --project-json >/dev/null 2>/dev/null; then
  echo "verification failed: strict mode accepted open symbolic Lie interpretation obligations" >&2
  exit 1
fi

# Discovered model domains retain proof provenance and interpretation obligations.
DOMAIN_JSON_LOG="$(mktemp /tmp/leanphy-model-domain-project.XXXXXX.log)"
lake exe leanphy_model_domains --project-json >"${DOMAIN_JSON_LOG}"
python3 - "${DOMAIN_JSON_LOG}" <<'PYREPORT'
import json
import pathlib
import sys
project = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if project.get("status") != "VERIFIED-CONDITIONAL" or project.get("diagnostics"):
    raise SystemExit("verification failed: model domain report is malformed")
if (project.get("package_count"), project.get("claim_count"), project.get("open_obligation_count")) != (1, 12, 1):
    raise SystemExit("verification failed: model domain report lost claims or obligations")
if any(not c.get("source", "").startswith("LeanPhy.Examples.ModelDomainResearch.")
       or not c.get("requires") for c in project["packages"][0]["claims"]):
    raise SystemExit("verification failed: model domain report lost proof provenance")
PYREPORT
if lake exe leanphy_model_domains --strict --project-json >/dev/null 2>/dev/null; then
  echo "verification failed: strict mode accepted open model domain interpretation obligations" >&2
  exit 1
fi

# Deformation results retain algebraic premises and the physical interpretation boundary.
DEFORMATION_JSON_LOG="$(mktemp /tmp/leanphy-deformation-project.XXXXXX.log)"
lake exe leanphy_deformations --project-json >"${DEFORMATION_JSON_LOG}"
python3 - "${DEFORMATION_JSON_LOG}" <<'PYREPORT'
import json
import pathlib
import sys
project = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if project.get("status") != "VERIFIED-CONDITIONAL" or project.get("diagnostics"):
    raise SystemExit("verification failed: deformation report is malformed")
if (project.get("package_count"), project.get("claim_count"), project.get("open_obligation_count")) != (1, 14, 1):
    raise SystemExit("verification failed: deformation report lost claims or obligations")
for claim in project["packages"][0]["claims"]:
    if not claim.get("source", "").startswith(("LeanPhy.Examples.LieDeformationResearch.", "LeanPhy.Mathematics.LieDeformation.")) or not claim.get("requires"):
        raise SystemExit("verification failed: deformation report lost proof provenance")
PYREPORT
if lake exe leanphy_deformations --strict --project-json >/dev/null 2>/dev/null; then
  echo "verification failed: strict mode accepted open deformation interpretation obligations" >&2
  exit 1
fi

# Computed adjoint coordinates produce proof-bearing deformation reports.
ADJOINT_JSON_LOG="$(mktemp /tmp/leanphy-adjoint-project.XXXXXX.log)"
lake exe leanphy_adjoint_deformations --project-json >"${ADJOINT_JSON_LOG}"
python3 - "${ADJOINT_JSON_LOG}" <<'PYREPORT'
import json
import pathlib
import sys
project = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if project.get("status") != "VERIFIED-CONDITIONAL" or project.get("diagnostics"):
    raise SystemExit("verification failed: adjoint deformation report is malformed")
if (project.get("package_count"), project.get("claim_count"), project.get("open_obligation_count")) != (1, 12, 1):
    raise SystemExit("verification failed: adjoint deformation report lost claims or obligations")
if any(not c.get("source", "").startswith("LeanPhy.Examples.AdjointDeformationResearch.")
       or not c.get("requires") for c in project["packages"][0]["claims"]):
    raise SystemExit("verification failed: adjoint deformation report lost proof provenance")
PYREPORT
if lake exe leanphy_adjoint_deformations --strict --project-json >/dev/null 2>/dev/null; then
  echo "verification failed: strict mode accepted open adjoint interpretation obligations" >&2
  exit 1
fi

# Complete second-order solvers expose checked claims and retain interpretation obligations.
SECOND_ORDER_JSON_LOG="$(mktemp /tmp/leanphy-second-order-project.XXXXXX.log)"
lake exe leanphy_second_order --project-json >"${SECOND_ORDER_JSON_LOG}"
python3 - "${SECOND_ORDER_JSON_LOG}" <<'PYREPORT'
import json
import pathlib
import sys
project = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if project.get("status") != "VERIFIED-CONDITIONAL" or project.get("diagnostics"):
    raise SystemExit("verification failed: second-order report is malformed")
if (project.get("package_count"), project.get("claim_count"), project.get("open_obligation_count")) != (1, 13, 1):
    raise SystemExit("verification failed: second-order report lost claims or obligations")
if any(not c.get("source", "").startswith("LeanPhy.Examples.SecondOrderDeformationResearch.")
       or not c.get("requires") for c in project["packages"][0]["claims"]):
    raise SystemExit("verification failed: second-order report lost proof provenance")
PYREPORT
if lake exe leanphy_second_order --strict --project-json >/dev/null 2>/dev/null; then
  echo "verification failed: strict mode accepted open second-order interpretation obligations" >&2
  exit 1
fi

# Second-order generator changes retain typed provenance and physical obligations.
GAUGE_JSON_LOG="$(mktemp /tmp/leanphy-deformation-gauge-project.XXXXXX.log)"
lake exe leanphy_deformation_gauge --project-json >"${GAUGE_JSON_LOG}"
python3 - "${GAUGE_JSON_LOG}" <<'PYREPORT'
import json
import pathlib
import sys
project = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if project.get("status") != "VERIFIED-CONDITIONAL" or project.get("diagnostics"):
    raise SystemExit("verification failed: deformation gauge report is malformed")
if (project.get("package_count"), project.get("claim_count"), project.get("open_obligation_count")) != (1, 15, 1):
    raise SystemExit("verification failed: deformation gauge report lost claims or obligations")
if any(not c.get("source", "").startswith("LeanPhy.Examples.DeformationGaugeResearch.")
       or not c.get("requires") for c in project["packages"][0]["claims"]):
    raise SystemExit("verification failed: deformation gauge report lost proof provenance")
PYREPORT
if lake exe leanphy_deformation_gauge --strict --project-json >/dev/null 2>/dev/null; then
  echo "verification failed: strict mode accepted open generator interpretation obligations" >&2
  exit 1
fi

# Actual H3 calculations retain checked claims and physical interpretation obligations.
THIRD_JSON_LOG="$(mktemp /tmp/leanphy-third-cohomology-project.XXXXXX.log)"
lake exe leanphy_third_cohomology --project-json >"${THIRD_JSON_LOG}"
python3 - "${THIRD_JSON_LOG}" <<'PYREPORT'
import json
import pathlib
import sys
project = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if project.get("status") != "VERIFIED-CONDITIONAL" or project.get("diagnostics"):
    raise SystemExit("verification failed: third cohomology report is malformed")
if (project.get("package_count"), project.get("claim_count"), project.get("open_obligation_count")) != (1, 14, 1):
    raise SystemExit("verification failed: third cohomology report lost claims or obligations")
if any(not c.get("source", "").startswith("LeanPhy.Examples.ThirdCohomologyResearch.")
       or not c.get("requires") for c in project["packages"][0]["claims"]):
    raise SystemExit("verification failed: third cohomology report lost proof provenance")
PYREPORT
if lake exe leanphy_third_cohomology --strict --project-json >/dev/null 2>/dev/null; then
  echo "verification failed: strict mode accepted open H3 interpretation obligations" >&2
  exit 1
fi

# Parameter-dependent H3 calculations preserve complete strata and model conditions.
PARAM_OBSTRUCTION_LOG="$(mktemp /tmp/leanphy-parameter-obstructions-project.XXXXXX.log)"
lake exe leanphy_parameter_obstructions --project-json >"${PARAM_OBSTRUCTION_LOG}"
python3 - "${PARAM_OBSTRUCTION_LOG}" <<'PYREPORT'
import json
import pathlib
import sys
project = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if project.get("status") != "VERIFIED-CONDITIONAL" or project.get("diagnostics"):
    raise SystemExit("verification failed: parameter obstruction report is malformed")
if (project.get("package_count"), project.get("claim_count"), project.get("open_obligation_count")) != (1, 16, 1):
    raise SystemExit("verification failed: parameter obstruction report lost claims or obligations")
if any(not c.get("source", "").startswith("LeanPhy.Examples.ParameterizedObstructionResearch.")
       or not c.get("requires") for c in project["packages"][0]["claims"]):
    raise SystemExit("verification failed: parameter obstruction report lost proof provenance")
PYREPORT
if lake exe leanphy_parameter_obstructions --strict --project-json >/dev/null 2>/dev/null; then
  echo "verification failed: strict mode accepted open H3 interpretation obligations" >&2
  exit 1
fi

# Third-order models retain their specified lower corrections and interpretation obligation.
THIRD_ORDER_LOG="$(mktemp /tmp/leanphy-third-order-project.XXXXXX.log)"
lake exe leanphy_third_order --project-json >"${THIRD_ORDER_LOG}"
python3 - "${THIRD_ORDER_LOG}" <<'PYREPORT'
import json
import pathlib
import sys
project = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if project.get("status") != "VERIFIED-CONDITIONAL" or project.get("diagnostics"):
    raise SystemExit("verification failed: third-order report is malformed")
if (project.get("package_count"), project.get("claim_count"), project.get("open_obligation_count")) != (1, 13, 1):
    raise SystemExit("verification failed: third-order report lost claims or obligations")
if any(not c.get("source", "").startswith("LeanPhy.Examples.ThirdOrderDeformationResearch.")
       or not c.get("requires") for c in project["packages"][0]["claims"]):
    raise SystemExit("verification failed: third-order report lost proof provenance")
PYREPORT
if lake exe leanphy_third_order --strict --project-json >/dev/null 2>/dev/null; then
  echo "verification failed: strict mode accepted open third-order interpretation obligations" >&2
  exit 1
fi

# Joint correction search reports both successful repairs and true third-order obstructions.
THIRD_SEARCH_LOG="$(mktemp /tmp/leanphy-third-search-project.XXXXXX.log)"
lake exe leanphy_third_search --project-json >"${THIRD_SEARCH_LOG}"
python3 - "${THIRD_SEARCH_LOG}" <<'PYREPORT'
import json
import pathlib
import sys
project = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if project.get("status") != "VERIFIED-CONDITIONAL" or project.get("diagnostics"):
    raise SystemExit("verification failed: joint correction search report is malformed")
if (project.get("package_count"), project.get("claim_count"), project.get("open_obligation_count")) != (1, 14, 1):
    raise SystemExit("verification failed: joint correction report lost claims or obligations")
if any(not c.get("source", "").startswith("LeanPhy.Examples.ThirdOrderSearchResearch.")
       or not c.get("requires") for c in project["packages"][0]["claims"]):
    raise SystemExit("verification failed: joint correction report lost proof provenance")
PYREPORT
if lake exe leanphy_third_search --strict --project-json >/dev/null 2>/dev/null; then
  echo "verification failed: strict mode accepted open joint correction interpretation obligations" >&2
  exit 1
fi

# Generated pure-ghost calculations retain a separate physical interpretation obligation.
LIE_GHOST_LOG="$(mktemp /tmp/leanphy-lie-ghost-project.XXXXXX.log)"
lake exe leanphy_lie_ghost --project-json >"${LIE_GHOST_LOG}"
python3 - "${LIE_GHOST_LOG}" <<'PYREPORT'
import json
import pathlib
import sys
project = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if project.get("status") != "VERIFIED-CONDITIONAL" or project.get("diagnostics"):
    raise SystemExit("verification failed: Lie ghost report is malformed")
if (project.get("package_count"), project.get("claim_count"), project.get("open_obligation_count")) != (1, 54, 1):
    raise SystemExit("verification failed: Lie ghost report lost claims or obligations")
if any(not c.get("source", "").startswith(("LeanPhy.Examples.LieGhostResearch.", "LeanPhy.Examples.GhostCohomology.", "LeanPhy.Examples.GhostMatter."))
       for c in project["packages"][0]["claims"]):
    raise SystemExit("verification failed: Lie ghost report lost proof provenance")
PYREPORT
if lake exe leanphy_lie_ghost --strict --project-json >/dev/null 2>/dev/null; then
  echo "verification failed: strict mode accepted open Lie ghost interpretation obligations" >&2
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

# Enumerate, build and import every source module; audit imported and private
# declarations too. The driver verifies source/mirror hashes before and after.
python3 "${PROJECT_ROOT}/scripts/audit_library.py" \
  --source-root "${PROJECT_ROOT}" --build-root "${BUILD_ROOT}"
python3 "${PROJECT_ROOT}/scripts/test_axiom_audit.py" --build-root "${BUILD_ROOT}"
python3 "${PROJECT_ROOT}/scripts/test_project_audit.py" --build-root "${BUILD_ROOT}"

python3 "${PROJECT_ROOT}/scripts/test_negative_runner.py"
LEANPHY_BUILD_ROOT="${BUILD_ROOT}" python3 "${PROJECT_ROOT}/scripts/test_research_infrastructure.py"
python3 "${PROJECT_ROOT}/scripts/test_matrix_certificate.py" --build-root "${BUILD_ROOT}"
python3 "${PROJECT_ROOT}/scripts/test_fermion_words.py" --build-root "${BUILD_ROOT}"
python3 "${PROJECT_ROOT}/scripts/test_driven_response.py" --build-root "${BUILD_ROOT}"
python3 "${PROJECT_ROOT}/scripts/test_heavy_field_matching.py" --build-root "${BUILD_ROOT}"
python3 "${PROJECT_ROOT}/scripts/test_fermion_vacuum.py" --build-root "${BUILD_ROOT}"
python3 "${PROJECT_ROOT}/scripts/test_self_consistency.py" --build-root "${BUILD_ROOT}"
python3 "${PROJECT_ROOT}/scripts/test_gibbs_certificate.py" --build-root "${BUILD_ROOT}"
python3 "${PROJECT_ROOT}/scripts/test_field_redefinitions.py" --build-root "${BUILD_ROOT}"
"${PROJECT_ROOT}/scripts/negative_tests.sh"

echo "LeanPhy verification passed: ${OK_COUNT} smoke capabilities; representative theorems have no sorryAx."
