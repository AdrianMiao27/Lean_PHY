import LeanPhy.Entry.Research
import LeanPhy.Entry.Quantum
import LeanPhy.Entry.FieldTheory
import LeanPhy.Entry.HighEnergy
import LeanPhy.Entry.Analysis
import LeanPhy.Entry.FinitePDE
import LeanPhy.Entry.StatMech
import LeanPhy.Entry.Gauge
import LeanPhy.Entry.Condensed
import LeanPhy.Entry.Classical
import LeanPhy.Entry.Relativity
import LeanPhy.Entry.Optics
import LeanPhy.Entry.Fluid

/-!
# Broad physics entry point

`LeanPhy.Entry.Physics` is the convenient umbrella import for a research
project that spans several subfields.  It deliberately reuses the same Lean
4 declarations and namespaces as the selective `Entry.*` profiles; it does
not introduce a second syntax or a second logic.  Projects that need faster
incremental builds should import only the profiles they use.
-/
