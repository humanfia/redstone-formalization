import Lean

/-!
# Checking the axioms of a theorem

`assert_standard_axioms t` fails the build unless the theorem `t` depends on nothing but the
three axioms every Mathlib proof may use: `propext`, `Classical.choice` and `Quot.sound`.

Theorems about circuits are proved by letting the kernel evaluate the model
(`decide +kernel`). That adds no axiom. A proof that trusted the compiler instead would depend
on `Lean.ofReduceBool` or `Lean.trustCompiler`, and an unfinished one on the axiom Lean puts in
place of a missing proof. This command catches all of them, and unlike `#print axioms` under
`#guard_msgs` it does not break when a proof stops needing one of the three.
-/

namespace Redstone.Proof

/-- The axioms a theorem of this project may depend on. -/
def standardAxioms : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]

open Lean Elab Command in
/-- `assert_standard_axioms t` fails unless `t` depends only on `propext`, `Classical.choice`
and `Quot.sound`. -/
elab "assert_standard_axioms " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axioms ← liftCoreM <| collectAxioms name
  let extra := axioms.toList.filter (!standardAxioms.contains ·)
  unless extra.isEmpty do
    throwError "{name} depends on axioms other than the standard ones: {extra}"

end Redstone.Proof
