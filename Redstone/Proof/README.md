# How to prove a circuit

This directory is the proof foundation: what a file under `Redstone/Theorems` needs to state
and prove what a concrete circuit does, game tick by game tick, with nothing trusted but the
Lean kernel. `docs/proof-feasibility.md` has the measurements that led to the method; this
file is the how-to.

| File | What it has |
|---|---|
| `Circuit.lean` | The one import: everything below. |
| `Build.lean` | `Level.ofCells` (a level from a list of blocks) and the observations: `blocksAt`, `powered`, `signalTo`, `emits`, `dustPower`, `pending`, `itemCount`. |
| `Checkpoint.lean` | `Level.beqBlocks` with `Level.eq_of_beqBlocks` (the comparison of two levels, and its soundness), and the lemmas that join per-tick equations into a run. |
| `Tactic.lean` | `circuit_decide`, `lit%`, `blk%` and the command `checkpoints`. |
| `Quiescent.lean` | `Level.Quiescent` and "a level at rest stays as it is for ever"; `Level.shift`, `Rules.Cycle` and the conditional periodicity theorem. |
| `Axioms.lean` | `assert_standard_axioms`. |
| `Smoke.lean` | The regression guard of the model (one evaluation per theorem; not the method for new theorems). |

The eight files of `Redstone/Theorems/Basics` are complete examples: lever and lamp, torch
inverter, repeater delay, dust decay, RS latch, sticky piston, hopper pair, repeater clock.
`Redstone/Lemmas/Repeater.lean` is the example of generic lemmas about one component.

## The method in one paragraph

Compiled code plays the schedule and prints the level after every game tick; each printed
level becomes a definition (a *checkpoint*). The kernel then checks, one game tick at a time,
that a tick takes each checkpoint to the next (`decide +kernel` on `Level.beqBlocks`, turned
into an equation by `Level.eq_of_beqBlocks`). The per-tick equations are joined into equations
about the run by lemmas applied to the *names* of the checkpoints. A theorem about the circuit
rewrites the run to a checkpoint and lets the kernel read the fact off the literal. Compiled
code is never trusted: it only proposes the right-hand sides.

## A complete example

```lean
import Redstone.Proof.Circuit

set_option Elab.async false          -- required: `circuit_decide` refuses to run without it

namespace Redstone.Theorems.Basics.LeverLamp

def lever : Pos := ⟨0, 1, 0⟩
def lamp : Pos := ⟨1, 1, 0⟩

/-- A lever on a stone block, with a redstone lamp next to the lever. -/
def circuit : Level :=
  .ofCells [(⟨0, 0, 0⟩, .plain .stone), (lever, .lever ⟨.floor, .north, false⟩),
    (lamp, .redstoneLamp ⟨false⟩)]

/-- The lever is used before game tick 1 and again before game tick 3; seven game ticks. -/
def schedule : Schedule := .first [.use lever .up] 2 ++ .first [.use lever .up] 5

checkpoints state := schedule from circuit

theorem lamp_off_delay :
    (rules.runSchedule (schedule.take 5) circuit).blockAt lamp = .redstoneLamp ⟨true⟩ ∧
      (rules.runSchedule (schedule.take 6) circuit).blockAt lamp = .redstoneLamp ⟨false⟩ ∧
      (rules.runSchedule (schedule.take 6) circuit).overflow = false := by
  rw [state_run_5, state_run_6]
  circuit_decide

assert_standard_axioms lamp_off_delay

theorem lamp_stays_dark (n : ℕ) :
    (rules.steps n (rules.runSchedule schedule circuit)).blockAt lamp = .redstoneLamp ⟨false⟩ := by
  rw [state_run, rules.blockAt_steps_of_quiescent (by circuit_decide)]
  circuit_decide

assert_standard_axioms lamp_stays_dark

end Redstone.Theorems.Basics.LeverLamp
```

`checkpoints state := schedule from circuit` takes the *names* of a `Schedule` and a `Level`
and adds, for `k` from 1 to the length `n` of the schedule:

* `state_k : Level`: the level after `k` game ticks, as a literal;
* `state_step_k : rules.stepWith (schedule.inputsAt (k - 1)) state_(k-1) = state_k`, with the
  initial level in place of `state_0`: one game tick, checked by the kernel;
* `state_run_k : rules.runSchedule (schedule.take k) circuit = state_k`;
* `state_run : rules.runSchedule schedule circuit = state_n`.

It checks its lemmas one after the other, fails if a level along the run has an entity, and
fails unless `state_run` depends on the standard axioms only. `checkpoints (timing) state :=
...` also prints how long each tick took; use it while writing a file, and remove it before
committing.

## Writing the level

* `Level.ofCells cells blockEntities` is a **raw load**: blocks are put in place with no
  reaction, at game time zero. A block with a block entity gets a fresh one unless the second
  argument gives it; ticking block entities (hoppers) tick in the order of the list.
* Say what the raw load assumes. Prove `circuit.Quiescent` when it holds; when the level
  cannot be quiescent (a hopper), say so.
* A raw level must be a state the game can be in. Dust has a shape and a power, a torch is
  lit or not, a latch is in one of its states: if you write them by hand, check them. The
  safe way is to let the model build the circuit: place the blocks with `.set` inputs in a
  scratch file, let it settle, and print the world (`#eval IO.println (repr l.world)`);
  `Redstone/Theorems/Basics/RSLatch.lean` was written that way.
* Write block states with constructors (`.lever ⟨.floor, .north, false⟩`) or with
  `blk% "minecraft:redstone_wire[east=side,north=none,power=0,south=none,west=side]"`, which
  parses the string when the file is elaborated. `blk%` wants every property. Never use
  `Block.parse?` in a definition the kernel evaluates.
* A schedule is a list of input lists, one per game tick: `Schedule.first inputs n` (the
  inputs, then `n` game ticks), `Schedule.idle n`, and `++`. After `++` write `Schedule.idle`
  in full: `.idle` is resolved against `List`.

## Stating the theorem

* State facts about `rules.runSchedule (schedule.take k) circuit` (the level after `k` game
  ticks) or `rules.runSchedule schedule circuit`. Rewrite with `state_run_k`, then
  `circuit_decide`. Several `state_run_k` go into one `rw`.
* The statement left for `circuit_decide` must be **closed and decidable**: equalities of
  blocks, lists of blocks, numbers, block entities, Booleans, joined by `∧`. Observe block
  states (`blockAt`, `blocksAt`, `dustPower`) in preference to signals.
* **Always state `overflow = false`.** A level with `overflow` is not an image of the game.
* **For ever.** If the checkpoint is quiescent, use `rules.steps_of_quiescent`,
  `rules.blockAt_steps_of_quiescent`, `rules.overflow_steps_of_quiescent` with
  `(by circuit_decide)` for the hypothesis. After `rw [rules.steps_of_quiescent ...]` the goal
  mentions `l.advance n` with a free `n`, which `circuit_decide` cannot evaluate: remove it
  first with `simp only [Level.blockAt_advance, Level.blocksAt_advance,
  Level.dustPower_advance, Level.overflow_advance]` (and the name of your own observation).
* **Clocks.** A clock is never quiescent. State the observations over a bounded run and a
  cycle certificate, `rules.Cycle (level after k ticks) period dc`: after one period the level
  is itself, shifted in time (`Level.shift`). Prove it from two checkpoints with
  `Rules.steps_of_runs` and `Level.eq_of_beqBlocks (by circuit_decide)`, as in
  `RepeaterClock.lean`. `dc` is the number of ticks scheduled in one period: the difference
  of `subTickCount` between the two checkpoints. Take the first checkpoint a full period after
  the start: the first round may differ from the steady state in a field you do not look at
  (in the repeater clock, `lightWorld`). Say in the docstring that the certificate is not
  periodicity for ever; `Rules.periodic_of_shiftInvariant` is the conditional statement, and
  its hypothesis is not proved for any component.
* Every theorem is followed by `assert_standard_axioms name`.

## What it costs

Measured on a quiet compute node, each file on its own, lemmas one after the other. "Step" is
the kernel evaluation of one game tick; the times are per tick.

| What happens in the tick | Step | Peak memory of the file |
|---|---|---|
| nothing (a scheduled tick counts down, or the level is at rest) | 15 to 30 ms | 1.3 GB |
| a hopper on cooldown is ticked | 30 to 100 ms | 1.3 GB |
| a lever is used, a lamp or a torch switches | 70 to 160 ms | 1.3 GB |
| a repeater switches a lamp | 120 to 140 ms | 1.3 GB |
| a piston starts to move one block; the block arrives | 330 to 390 ms; 170 to 250 ms | 1.4 GB |
| a hopper moves an item | 100 to 170 ms | 1.3 GB |
| a comparator looks at a hopper with items in four slots; it then switches on | 1.0 s; 130 ms | 1.3 GB |
| a repeater of the clock switches (one corner of dust goes on, one off) | 0.53 to 0.60 s | 2.3 GB |
| a line of 5 dust goes on (RS latch) | 0.4 to 1.2 s | |
| a line of 5 dust goes off behind a torch (RS latch) | 7.8 s | 3.1 GB |
| a line of 15 dust goes on | 4.2 s | |
| a line of 15 dust goes off | 14 s | 4.5 GB |

The five rows with dust were measured again after the dust was profiled
(`docs/proof-feasibility.md`, "Redstone dust: where the kernel time went"); they were 1.2 to
1.7 s, 1.3 to 2.9 s, 17 s and 5.6 GB, 7.1 s, and 34 s and 9.0 GB. The other rows were not
measured again.

Besides the step: the literal of a checkpoint takes 10 to 60 ms to elaborate, and **joining
costs 2 to 5 ms per game tick, whatever the size of the level and the length of the run** (18
ticks of the clock: 64 ms in all). Joining applies `Rules.runSchedule_take_succ` to the names
of the checkpoints, so the kernel compares names and never unfolds a level. Reading a fact off
a checkpoint (`rw [state_run_k]; circuit_decide`) costs milliseconds.

The whole of `Redstone/Theorems/Basics` was 87 s of kernel time: 42 s for the dust line, 26 s
for the RS latch, 13.5 s for the clock, and under 2 s for each of the other five. The three
with dust are now 19 s, 13 s and 6 s.

**Dust is the expensive block, and switching it off is the expensive direction.** Budget a
file by its dust: about 0.2 s for every time a dust changes its power, and switching a line
off changes each dust several times (64 changes for 15 dust). Where the time went, what was
changed for it and what is left is in `docs/proof-feasibility.md`.

**Memory is per tick, and files build in parallel.** The kernel frees its cache between
declarations, so the peak of a file is the peak of its worst tick. Lake builds independent
files at once, as many as the machine has cores, and the CI runner has 4 cores and 16 GB. The
rule is for the whole repository, not for one directory:

* A file is *heavy* if one of its ticks needs more than about 4 GB (the peak resident
  memory of `lean` run on the file alone; a dust line that switches off is the usual cause). No file may need more than about 10 GB: split the run or shorten the circuit.
* **All heavy files of the repository form one chain of imports**, so that no two of them
  are ever checked at the same time. A heavy file imports the heavy file before it, on a line
  under the comment `-- Heavy chain:`, which is how the chain is found:
  `git grep -n -A4 'Heavy chain:' -- Redstone`. The chain today is `Redstone/Proof/Smoke.lean`
  (5.4 GB, for its line of 15 dust) ← `RepeaterClock.lean` ← `RSLatch.lean` ← `DustDecay.lean`
  (4.5 GB), the last three in `Redstone/Theorems/Basics`; its end is the heavy file that no
  other file imports under that comment. The clock and the latch are no longer heavy (2.3 and
  3.1 GB) and stay in the chain as they are.
* A new heavy file imports the end of the chain and becomes the end. Two branches written at
  the same time will both import the same end; whoever merges second moves its first heavy
  file behind the end that is then on `main`. This is part of merging a branch with proofs.
* The files that are not heavy (below 4 GB, almost all of them below 2 GB) need no care: three
  of them next to one heavy file fit.

On the cluster, give a build with heavy files `--mem 48G`.

## Do

* Start the file with `import Redstone.Proof.Circuit` and `set_option Elab.async false`.
* One circuit per file, one `checkpoints` per run. Split a long experiment into runs that
  start from a checkpoint (`checkpoints second := schedule2 from state_8`), and join them with
  `Rules.runSchedule_andThen` if needed.
* Look at the model first: `#eval` the observations along the schedule in a scratch file
  (compiled code is fast), then write the theorem.
* Keep statements about checkpoints, joined to the run by `rw`.
* Put generic facts about one component in `Redstone/Lemmas/<Component>.lean`: attribute
  lemmas (the block state alone) and single-reaction lemmas (one reaction on an arbitrary
  level, under hypotheses about what it reads). These files are `module`s and use ordinary
  tactics, not evaluation.

## Do not

* Do not prove a tick with `rfl`, `decide` without `+kernel`, `simp` or `exact` of a term
  whose type has to be *unfolded* to match. The elaborator then evaluates the model itself,
  symbolically, and runs out of heartbeats. This also happens by accident: `rfl` for
  `r.runSchedule (is :: s) l = r.runSchedule s (r.stepWith is l)` timed out, because the
  elaborator, comparing arguments, tried to compute `r.stepWith is l`. Use the lemmas of
  `Checkpoint.lean` (`runSchedule_cons`, `runSchedule_append`, `runSchedule_idle`,
  `steps_of_runs`, ...) and `rw`; never rely on a level being *definitionally* something.
* Do not evaluate many ticks in one `circuit_decide`: time and memory grow with the run, and
  the kernel gives up (`docs/proof-feasibility.md`). Three ticks of a small circuit is the
  limit of good taste.
* Do not leave a variable in a goal for `circuit_decide`.
* Do not bind a level with `let` in a statement; give it a `def`.
* Do not use entities. A level with an entity has no checkpoint: entity motion is `Float`,
  which the kernel cannot evaluate, and `Level.beqBlocks` rejects it. The command stops at the
  first such tick. Dropped items, minecarts, primed TNT and projectiles are out of reach of
  this method.
* Do not assume a path is cheap, or reduces at all, because compiled code runs it. A
  comparator that reads a container goes through `Container.redstoneSignal`, which was
  `Float32` and stuck in the kernel until it was made exact arithmetic; it costs a second now
  (the table above). Time the first tick of a new kind with `checkpoints (timing)` before
  building on it.
* Do not name a theorem with a Lean keyword (`extends`), and do not write the three words the
  CI check rejects, even in a comment.
* Do not claim more than was checked: a bounded run is a bounded run, a cycle certificate is
  one period.

## What is not here

* Levels with entities (above).
* Periodicity for ever: only the conditional theorem.
* `Level.shift` does not move the times kept inside block entities (the game time of a
  hopper's last tick), so a cycle certificate cannot hold for a hopper clock as it stands.
* A frame rule ("blocks outside this box do not matter") and lemmas about a whole delay of a
  component over an arbitrary level: every theorem is about a concrete, complete level.
