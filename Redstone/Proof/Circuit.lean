import Redstone.Proof.Axioms
import Redstone.Proof.Build
import Redstone.Proof.Checkpoint
import Redstone.Proof.Quiescent
import Redstone.Proof.Tactic

/-!
# Everything a theorem about a circuit needs

A file that proves a circuit starts with

```lean
import Redstone.Proof.Circuit

set_option Elab.async false
```

and has the builder (`Level.ofCells`, `blk%`), the observations, the checkpoint command
(`checkpoints`), the tactic (`circuit_decide`), the theorems about levels at rest and about
cycles, and the axioms guard (`assert_standard_axioms`). The how-to is
`Redstone/Proof/README.md`.
-/
