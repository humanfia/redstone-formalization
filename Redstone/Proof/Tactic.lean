import Lean
import Redstone.Mechanics.Dispatch
import Redstone.Proof.Axioms
import Redstone.Proof.Checkpoint

/-!
# The tactic and the command that prove circuits

* `circuit_decide` closes a closed, decidable statement by letting the kernel evaluate it
  (`decide +kernel`). It refuses to run while Lean elaborates the theorems of the file on
  several threads, because kernel evaluations that run side by side are many times slower
  (`docs/proof-feasibility.md`): a file that uses it has to say `set_option Elab.async false`.
* `lit% e` evaluates the closed term `e` with compiled code and gives its value back written
  out as a term.
* `checkpoints name := schedule from level` plays a schedule on a level with compiled code,
  defines the level after every game tick as a literal (`name_1`, `name_2`, ...), and proves,
  by kernel evaluation, that each game tick takes one literal to the next (`name_step_k`),
  that the first `k` ticks of the schedule end in `name_k` (`name_run_k`), and that the whole
  schedule ends in the last literal (`name_run`).

Nothing here is trusted. Compiled code only proposes the literals; every `name_step_k` is
checked by the kernel, and the command fails unless `name_run` depends on the three standard
axioms only.

Left out: levels with entities (`Level.beqBlocks` rejects them, and so does the command).
-/

namespace Redstone.Proof

open Lean Elab Meta Term Command Tactic

/-- `circuit_decide` proves a closed decidable proposition by kernel evaluation
(`decide +kernel`). The file must set `set_option Elab.async false`, so that the evaluations of
a file run one after the other. -/
elab "circuit_decide" : tactic => do
  if Lean.Elab.async.get (← getOptions) then
    throwError "circuit_decide: put `set_option Elab.async false` at the top of this file. \
      Kernel evaluations that run side by side are many times slower \
      (docs/proof-feasibility.md)."
  evalTactic (← `(tactic| decide +kernel))

/-- Parses what `Repr` printed as a term. A proof field is printed as `_`: it is replaced by
`by decide` (the bounds of an `IntRange`, in a repeater's delay or the power of redstone
dust). -/
def parseRepr (str : String) : CoreM Term := do
  let str := [",", " }", "}", "\n"].foldl
    (fun s close => s.replace (":= _" ++ close) (":= by decide" ++ close)) str
  match Parser.runParserCategory (← getEnv) `term str with
  | .ok stx => return ⟨stx⟩
  | .error e => throwError "what `Repr` printed is not a term: {e}"

private unsafe def evalStringUnsafe (e : Expr) : MetaM String :=
  evalExpr String (mkConst ``String) e

/-- Runs compiled code for a closed term of type `String`. -/
@[implemented_by evalStringUnsafe]
private opaque evalString (e : Expr) : MetaM String

private unsafe def evalStringsUnsafe (e : Expr) : MetaM (List String) :=
  evalExpr (List String) (mkApp (mkConst ``List [Lean.Level.zero]) (mkConst ``String)) e

/-- Runs compiled code for a closed term of type `List String`. -/
@[implemented_by evalStringsUnsafe]
private opaque evalStrings (e : Expr) : MetaM (List String)

/-- `lit% e` evaluates the closed term `e` with compiled code and elaborates what `Repr` prints
for the value. The result is a term written out in constructors; that it equals `e` is not
known to Lean and has to be proved (for a level: `Level.eq_of_beqBlocks (by circuit_decide)`). -/
elab "lit% " e:term : term <= ty => do
  let e ← elabTermEnsuringType e ty
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let str ← evalString (← mkAppM ``reprStr #[e])
  elabTermEnsuringType (← parseRepr str) ty

/-- `blk% "minecraft:lever[face=floor,facing=north,powered=false]"` is the block state with
that name, as a term written in constructors. The name is parsed when the file is elaborated;
the kernel never sees the string. The name has to be the one the game prints: every property,
in alphabetical order, and nothing else. -/
elab "blk% " s:str : term => do
  let some b := Block.parse? s.getString
    | throwError "not a block state: {s.getString}"
  unless toString b == s.getString do
    throwError "write the block state in full, as the game prints it: {b}"
  elabTermEnsuringType (← parseRepr (reprStr b)) (mkConst ``Block)

/-- What `Repr` prints for the level after each game tick of the schedule `s` played from `l`.
A level with entities gives the empty string: it has no literal. -/
def reprTrace (r : Rules) : Schedule → Level → List String
  | [], _ => []
  | is :: s, l =>
    let l' := r.stepWith is l
    (if l'.entities.isEmpty then reprStr l' else "") :: reprTrace r s l'

/-- `checkpoints name := schedule from level`, where `schedule : Schedule` and `level : Level`
are the names of two definitions, plays the schedule on the level and adds, for every game tick
`k` from `1` to the length `n` of the schedule:

* `name_k : Level`, the level after `k` game ticks, written out as a term;
* `name_step_k : rules.stepWith (schedule.inputsAt (k - 1)) name_(k-1) = name_k`, where
  `name_0` is `level` itself: the inputs of tick `k` and then one game tick take the previous
  checkpoint to this one. Proved by kernel evaluation, one tick at a time;
* `name_run_k : rules.runSchedule (schedule.take k) level = name_k`;

and `name_run : rules.runSchedule schedule level = name_n`.

`checkpoints (timing) name := ...` also reports, for every game tick, how long the literal, the
step lemma (the kernel evaluation of the tick) and the joining lemma took.

The lemmas are checked one after the other whatever `Elab.async` says. The command fails when
a level along the run has an entity, and unless `name_run` depends only on the standard
axioms. -/
syntax (name := checkpointsCmd)
  "checkpoints " ("(" &"timing" ") ")? ident " := " ident " from " ident : command

@[command_elab checkpointsCmd] def elabCheckpoints : CommandElab := fun stx => do
  let timing := !stx[1].isNone
  let name : Ident := ⟨stx[2]⟩
  let sched : Ident := ⟨stx[4]⟩
  let init : Ident := ⟨stx[6]⟩
  let strs ← liftTermElabM do
    let ty := mkApp (mkConst ``List [Lean.Level.zero]) (mkConst ``String)
    let e ← elabTermEnsuringType (← `(Redstone.Proof.reprTrace Redstone.rules $sched $init)) ty
    synthesizeSyntheticMVarsNoPostponing
    evalStrings (← instantiateMVars e)
  if strs.isEmpty then throwErrorAt sched "the schedule has no game tick"
  let n := strs.length
  let ident (suffix : String) : Ident := mkIdentFrom name (name.getId.appendAfter suffix)
  let hadErrors := (← get).messages.hasErrors
  let mut times : Array (Nat × Nat × Nat × Nat) := #[]
  let mut prev := init
  let mut k := 0
  for str in strs do
    k := k + 1
    if str.isEmpty then
      throwErrorAt name "the level after game tick {k} has an entity: it cannot be a checkpoint"
    let lit ← liftCoreM <| parseRepr str
    let level := ident s!"_{k}"
    let step := ident s!"_step_{k}"
    let run := ident s!"_run_{k}"
    let prevRun := ident s!"_run_{k - 1}"
    let before := Syntax.mkNumLit (toString (k - 1))
    let this := Syntax.mkNumLit (toString k)
    let defCmd ← `(command| def $level : Redstone.Level := $lit)
    let stepCmd ← `(command|
      theorem $step : Redstone.Rules.stepWith Redstone.rules
          (Redstone.Schedule.inputsAt $sched $before) $prev = $level :=
        Redstone.Level.eq_of_beqBlocks (by decide +kernel))
    let runCmd ←
      if k = 1 then
        `(command|
          theorem $run : Redstone.Rules.runSchedule Redstone.rules
              (List.take $this $sched) $init = $level :=
            Redstone.Rules.runSchedule_take_one $step (by decide +kernel))
      else
        `(command|
          theorem $run : Redstone.Rules.runSchedule Redstone.rules
              (List.take $this $sched) $init = $level :=
            Redstone.Rules.runSchedule_take_succ (k := $before) $prevRun $step
              (by decide +kernel))
    let t₀ ← IO.monoMsNow
    let (t₁, t₂) ← withScope (fun sc => { sc with opts := Lean.Elab.async.set sc.opts false }) do
      elabCommand defCmd
      let t₁ ← IO.monoMsNow
      elabCommand stepCmd
      let t₂ ← IO.monoMsNow
      elabCommand runCmd
      return (t₁, t₂)
    times := times.push (t₁ - t₀, t₂ - t₁, (← IO.monoMsNow) - t₂, k)
    if !hadErrors && (← get).messages.hasErrors then
      throwErrorAt name "game tick {k} could not be checked"
    prev := level
  let total := ident "_run"
  let lastRun := ident s!"_run_{n}"
  let totalCmd ← `(command|
    theorem $total : Redstone.Rules.runSchedule Redstone.rules $sched $init = $prev :=
      Redstone.Rules.runSchedule_of_take $lastRun (by decide +kernel))
  withScope (fun sc => { sc with opts := Lean.Elab.async.set sc.opts false }) do
    elabCommand totalCmd
  if !hadErrors && (← get).messages.hasErrors then
    throwErrorAt name "the run could not be joined"
  elabCommand (← `(command| assert_standard_axioms $total))
  if timing then
    let lines := times.toList.map fun (lit, step, run, k) =>
      s!"tick {k}: literal {lit} ms, step {step} ms, joining {run} ms"
    let sum (f : Nat × Nat × Nat × Nat → Nat) := times.foldl (· + f ·) 0
    logInfoAt name s!"{n} checkpoints: literals {sum (·.1)} ms, steps {sum (·.2.1)} ms, \
      joining {sum (·.2.2.1)} ms\n{"\n".intercalate lines}"

end Redstone.Proof
