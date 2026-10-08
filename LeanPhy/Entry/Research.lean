import LeanPhy.Minimal
import LeanPhy.Workflow.Core
import LeanPhy.Workflow.Exploration
import LeanPhy.Verification

/-! Research-project entry point.

This profile adds the package ledger and certificate bridge to the minimal
surface.  Domain packages can be imported separately, so a paper need not
compile the entire catalogue merely to produce a reproducibility report.

Use one of the sibling `Entry.*` profiles (`Quantum`, `FieldTheory`,
`Condensed`, `Gauge`, `HighEnergy`, `Classical`, `Relativity`, `StatMech`,
`FinitePDE`, or `Analysis`) alongside this module when the project needs
domain objects.
-/
