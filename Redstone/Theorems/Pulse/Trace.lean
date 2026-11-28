import Redstone.Proof.Circuit

/-!
# Pulse circuits: output traces

This directory has the theorems about pulse circuits, one circuit per file, and this file has
what they share. A pulse circuit is described by its *output trace*: what the output is after
each game tick of a run. `after` is that trace, as a list, for the game ticks one asks for; the
theorems state it for every game tick of a run, so a pulse length is read off as the number of
consecutive entries that are on.

## The circuits

* `ButtonPulse.lean`: a button and dust. A stone button gives 20 game ticks, a wooden one 30;
  a second press is ignored.
* `RepeaterStretch.lean`: lever, repeater, dust. A pulse of one game tick comes out
  `2 * delay` game ticks long, for the four delays.
* `ComparatorLimiter.lean`: a comparator in subtraction mode with a repeater at its side. One
  pulse of `2 * delay` game ticks for the delays 2 to 4, none for the delay 1, none on the
  falling edge.
* `Monostable.lean`: an inverting torch and a repeater into the block of the output torch (the
  rising-edge detector). One pulse of `2 * delay - 2` game ticks for the delays 3 and 4, none
  for 1 and 2, none on the falling edge.
* `FallingEdgeLock.lean`: a repeater locked by a second one and fed through a third. No pulse
  on the rising edge, one of 2 game ticks, 4 game ticks after the falling edge.
* `DualEdge.lean`: an observer watching dust. One pulse of 2 game ticks on each edge.
* `RepeaterExtender.lean`: the input OR the input delayed by two repeaters. The output is
  longer than the input by the delay of the chain; there is a gap when the input is shorter
  than the chain.
* `FadeOutExtender.lean`: two comparators and four pieces of dust in a loop. The powers lap by
  lap; the output outlasts the input by exactly 30 game ticks.

The generic lemmas that go with them are in `Redstone/Lemmas/Button.lean` and
`Redstone/Lemmas/RepeaterPulse.lean`.

Every pulse length is a statement about a concrete run: an input of a given length (or one
that stays on, with "for ever" through `Level.Quiescent`). No theorem here quantifies over the
length of the input.

## Not yet proved

* **A pulse limiter built on a locked repeater.** A lock freezes a repeater in the state it
  has, so locking can keep a pulse out (the falling-edge detector) but cannot end one; no such
  layout was found, and the two limiters proved are the comparator and the torch design.
* **Pulse limiters that cut the line with a piston** (dust-cut, moved block). The model can
  evaluate pistons; these layouts were not written.
* **A dual-edge detector without an observer** (rising-edge and falling-edge detector joined),
  and a **falling-edge detector made of torches only**. Not written.
* **The fade-out extender for other loops.** Only the loop of two comparators and four pieces
  of dust is proved; there is no theorem about the decay as a function of the loop.
* **A wooden button held down by an arrow.** The arrow is an entity; entity motion is `Float`,
  which the kernel cannot evaluate (`Redstone/Proof/README.md`).
* The dropper-and-hopper pulse extender, the T flip-flops and pulse dividers, and the observer
  chains that multiply a pulse belong to the units about item circuits, memory and observers.

**The clock used in the docstrings of this directory.** *Time `k`* is the level after game tick
`k`, that is `rules.runSchedule (schedule.take k) circuit`. An input that arrives before game
tick `k + 1` (entry `k` of the schedule) acts at time `k`: the level after game tick `k + 1` is
the first that shows it. A scheduled tick with delay `d`, scheduled at time `k`, runs in game
tick `k + d`. So a button pressed at time 0 and released in game tick 20 is on after the game
ticks 1 to 19 and off after game tick 20: a pulse of 20 game ticks, from time 0 to time 20.
One redstone tick is two game ticks.

The observations are block states: whether a lever, a button, a repeater, a comparator, a
torch or an observer is on, and the power of a piece of redstone dust (`Level.dustPower`).
They answer `false` (or 0) also when the block is not there, so a theorem whose output is off
throughout says in addition that the block is in its place: by the block itself, or by the
blocks of the whole level at the end of the run.

`rw_runs name a b` rewrites with the lemmas `name_run_a`, ..., `name_run_b` of the command
`checkpoints`, one after the other; it fails if one of them does not occur in the goal.
-/

namespace Redstone.Theorems.Pulse

/-- What `obs` sees after each of the game ticks `ks` of the schedule `s` played from `l`. -/
def after {α : Type} (obs : Level → α) (s : Schedule) (l : Level) (ks : List ℕ) : List α :=
  ks.map fun k => obs (rules.runSchedule (s.take k) l)

/-- Is the lever at `p` switched on? -/
def leverOn (l : Level) (p : Pos) : Bool :=
  match l.blockAt p with
  | .lever s => s.powered
  | _ => false

/-- Is the button at `p` pressed? -/
def buttonPressed (l : Level) (p : Pos) : Bool :=
  match l.blockAt p with
  | .button _ s => s.powered
  | _ => false

/-- Is the repeater at `p` powered? -/
def repeaterOn (l : Level) (p : Pos) : Bool :=
  match l.blockAt p with
  | .repeater s => s.powered
  | _ => false

/-- Is the repeater at `p` locked? -/
def repeaterLocked (l : Level) (p : Pos) : Bool :=
  match l.blockAt p with
  | .repeater s => s.locked
  | _ => false

/-- Is the comparator at `p` powered? -/
def comparatorOn (l : Level) (p : Pos) : Bool :=
  match l.blockAt p with
  | .comparator s => s.powered
  | _ => false

/-- Is the redstone torch at `p` lit? -/
def torchLit (l : Level) (p : Pos) : Bool :=
  match l.blockAt p with
  | .redstoneTorch s => s.lit
  | .redstoneWallTorch s => s.lit
  | _ => false

/-- Is the observer at `p` powered? -/
def observerOn (l : Level) (p : Pos) : Bool :=
  match l.blockAt p with
  | .observer s => s.powered
  | _ => false

open Lean Elab Tactic in
/-- `rw_runs name a b` rewrites with `name_run_a`, ..., `name_run_b`, the lemmas of
`checkpoints name := ...` about the levels after the game ticks `a` to `b`. Every one of them
has to occur in the goal. -/
elab "rw_runs " name:ident a:num b:num : tactic => do
  unless a.getNat ≤ b.getNat do
    throwError "rw_runs: the first game tick ({a.getNat}) is after the last ({b.getNat})"
  for k in [a.getNat : b.getNat + 1] do
    let run := mkIdentFrom name (name.getId.appendAfter s!"_run_{k}")
    evalTactic (← `(tactic| rw [$run:ident]))

end Redstone.Theorems.Pulse
