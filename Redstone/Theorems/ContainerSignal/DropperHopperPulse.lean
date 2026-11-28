import Redstone.Proof.Circuit

/-!
# The dropper and hopper pulse generator

A dropper that points up into a hopper, which points back down into the dropper, and one
item. A rising edge at the dropper sends the item up; the hopper, which was empty and is put
on its cooldown by the item, gives it back seven game ticks later. A comparator reads the
hopper: its output is one pulse of fixed length for every rising edge of the input, however
long the input stays on (a monostable circuit).

```
y = 2:       H   C   L      H: hopper pointing down;  C: comparator reading H;  L: lamp
y = 1:   i   D   S          D: dropper pointing up;  S: stone;  i: where the input is put
x:      -1   0   1   2
```

The input is a block of redstone put next to the dropper. It touches the dropper only: it
does not power the dropper strongly, so the hopper above is never locked. (A lever on the
dropper would lock the hopper for as long as it is on, and the item would come back only when
the lever is released.)

What is proved, for an input of two game ticks (`short_pulse`) and one of 30 game ticks
(`long_pulse`), with the same numbers:

* the dropper fires in game tick 4, four game ticks after the rising edge, and the item is in
  the hopper;
* the comparator gives 1 after game ticks 6 to 12, and the lamp is lit after game ticks 6 to
  16 (a lamp goes out four game ticks after it loses its signal);
* the item is back in the dropper after game tick 11, seven game ticks after it left;
* at the end of the run the circuit is as at the start: the item is in the dropper, the
  comparator gives 0 and the lamp is dark.

The hopper is a ticking block entity: no level here is quiescent, and the statements are
about bounded runs. The level is loaded raw.

## Not proved

More than one item in the dropper (the pulse extender, whose pulse grows with the number of
items): a dropper fires one item per rising edge, so that circuit needs a clock at the
dropper and is another layout.
-/

set_option Elab.async false

-- The theorems are conjunctions of many equations between tuples, and the instance that
-- decides such an equation is large.
set_option synthInstance.maxSize 100000

namespace Redstone.Theorems.ContainerSignal.DropperHopperPulse

/-- The dropper, which points up into the hopper. -/
def dropper : Pos := ⟨0, 1, 0⟩

/-- The hopper, which points down into the dropper. -/
def hopper : Pos := ⟨0, 2, 0⟩

/-- The comparator that reads the hopper. -/
def comparator : Pos := ⟨1, 2, 0⟩

/-- The lamp in front of the comparator: the output. -/
def lamp : Pos := ⟨2, 2, 0⟩

/-- The cell west of the dropper, where the block of redstone that is the input is put. -/
def input : Pos := ⟨-1, 1, 0⟩

/-- A dropper with one piece of redstone, a hopper on top of it that points back down, a
comparator on a stone block that reads the hopper, and a lamp. -/
def circuit : Level :=
  .ofCells [(dropper, .dropper ⟨.up, false⟩), (hopper, .hopper ⟨true, .down⟩),
      (⟨1, 1, 0⟩, .plain .stone), (comparator, .comparator ⟨.west, .compare, false⟩),
      (lamp, .redstoneLamp ⟨false⟩)]
    [(dropper, .dropper { items := (Inventory.empty 9).setItem 0 (.of "minecraft:redstone" 1) })]

/-- A short pulse: the block of redstone is there for two game ticks; 20 game ticks. -/
def shortPulse : Schedule :=
  .first [.set input (.plain .redstone_block)] 2 ++ .first [.set input .AIR] 18

/-- A long pulse: the block of redstone is there for 30 game ticks; 34 game ticks. -/
def longPulse : Schedule :=
  .first [.set input (.plain .redstone_block)] 30 ++ .first [.set input .AIR] 4

/-- The number of items in the dropper. -/
def dropperCount (l : Level) : ℕ :=
  match l.blockEntities dropper with
  | some (.dropper d) => (d.items.map (·.count)).sum
  | _ => 0

/-- The output the comparator has stored. -/
def output (l : Level) : ℕ :=
  match l.blockEntities comparator with
  | some (.comparator d) => d.output
  | _ => 0

/-- What is observed: the numbers of items in the dropper and in the hopper, the output of the
comparator, and whether the lamp is lit. -/
def observe (l : Level) : ℕ × ℕ × ℕ × Bool :=
  (dropperCount l, l.itemCount hopper, output l, l.blockAt lamp == .redstoneLamp ⟨true⟩)

checkpoints short := shortPulse from circuit
checkpoints long := longPulse from circuit

/-- At the start the item is in the dropper, the hopper is empty, the comparator gives 0 and
the lamp is dark; nothing is scheduled. -/
theorem start : observe circuit = (1, 0, 0, false) ∧ circuit.pending = [] := by
  circuit_decide

assert_standard_axioms start

/-- **A short input gives one pulse.** Each line is the state after one game tick: the items in
the dropper, the items in the hopper, the output of the comparator, and whether the lamp is
lit. The block of redstone is there for game ticks 1 and 2. The item is in the hopper after
game tick 4 and back in the dropper after game tick 11; the comparator gives 1 after game ticks
6 to 12; the lamp is lit after game ticks 6 to 16. -/
theorem short_pulse :
    observe (rules.runSchedule (shortPulse.take 1) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (shortPulse.take 2) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (shortPulse.take 3) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (shortPulse.take 4) circuit) = (0, 1, 0, false) ∧
      observe (rules.runSchedule (shortPulse.take 5) circuit) = (0, 1, 0, false) ∧
      observe (rules.runSchedule (shortPulse.take 6) circuit) = (0, 1, 1, true) ∧
      observe (rules.runSchedule (shortPulse.take 7) circuit) = (0, 1, 1, true) ∧
      observe (rules.runSchedule (shortPulse.take 8) circuit) = (0, 1, 1, true) ∧
      observe (rules.runSchedule (shortPulse.take 9) circuit) = (0, 1, 1, true) ∧
      observe (rules.runSchedule (shortPulse.take 10) circuit) = (0, 1, 1, true) ∧
      observe (rules.runSchedule (shortPulse.take 11) circuit) = (1, 0, 1, true) ∧
      observe (rules.runSchedule (shortPulse.take 12) circuit) = (1, 0, 1, true) ∧
      observe (rules.runSchedule (shortPulse.take 13) circuit) = (1, 0, 0, true) ∧
      observe (rules.runSchedule (shortPulse.take 14) circuit) = (1, 0, 0, true) ∧
      observe (rules.runSchedule (shortPulse.take 15) circuit) = (1, 0, 0, true) ∧
      observe (rules.runSchedule (shortPulse.take 16) circuit) = (1, 0, 0, true) ∧
      observe (rules.runSchedule (shortPulse.take 17) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (shortPulse.take 18) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (shortPulse.take 19) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (shortPulse.take 20) circuit) = (1, 0, 0, false) ∧
      (rules.runSchedule (shortPulse.take 20) circuit).overflow = false := by
  rw [short_run_1, short_run_2, short_run_3, short_run_4, short_run_5, short_run_6, short_run_7,
    short_run_8, short_run_9, short_run_10, short_run_11, short_run_12, short_run_13,
    short_run_14, short_run_15, short_run_16, short_run_17, short_run_18, short_run_19,
    short_run_20]
  circuit_decide

assert_standard_axioms short_pulse

/-- **A long input gives the same pulse.** The block of redstone is there for game ticks 1 to
30. The lines after game ticks 1 to 20 are those of the short input; nothing more happens while
the input stays on, nor when it is removed. -/
theorem long_pulse :
    observe (rules.runSchedule (longPulse.take 1) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (longPulse.take 2) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (longPulse.take 3) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (longPulse.take 4) circuit) = (0, 1, 0, false) ∧
      observe (rules.runSchedule (longPulse.take 5) circuit) = (0, 1, 0, false) ∧
      observe (rules.runSchedule (longPulse.take 6) circuit) = (0, 1, 1, true) ∧
      observe (rules.runSchedule (longPulse.take 7) circuit) = (0, 1, 1, true) ∧
      observe (rules.runSchedule (longPulse.take 8) circuit) = (0, 1, 1, true) ∧
      observe (rules.runSchedule (longPulse.take 9) circuit) = (0, 1, 1, true) ∧
      observe (rules.runSchedule (longPulse.take 10) circuit) = (0, 1, 1, true) ∧
      observe (rules.runSchedule (longPulse.take 11) circuit) = (1, 0, 1, true) ∧
      observe (rules.runSchedule (longPulse.take 12) circuit) = (1, 0, 1, true) ∧
      observe (rules.runSchedule (longPulse.take 13) circuit) = (1, 0, 0, true) ∧
      observe (rules.runSchedule (longPulse.take 14) circuit) = (1, 0, 0, true) ∧
      observe (rules.runSchedule (longPulse.take 15) circuit) = (1, 0, 0, true) ∧
      observe (rules.runSchedule (longPulse.take 16) circuit) = (1, 0, 0, true) ∧
      observe (rules.runSchedule (longPulse.take 17) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (longPulse.take 18) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (longPulse.take 19) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (longPulse.take 20) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (longPulse.take 21) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (longPulse.take 22) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (longPulse.take 23) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (longPulse.take 24) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (longPulse.take 25) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (longPulse.take 26) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (longPulse.take 27) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (longPulse.take 28) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (longPulse.take 29) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (longPulse.take 30) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (longPulse.take 31) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (longPulse.take 32) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (longPulse.take 33) circuit) = (1, 0, 0, false) ∧
      observe (rules.runSchedule (longPulse.take 34) circuit) = (1, 0, 0, false) ∧
      (rules.runSchedule (longPulse.take 34) circuit).overflow = false := by
  rw [long_run_1, long_run_2, long_run_3, long_run_4, long_run_5, long_run_6, long_run_7,
    long_run_8, long_run_9, long_run_10, long_run_11, long_run_12, long_run_13, long_run_14,
    long_run_15, long_run_16, long_run_17, long_run_18, long_run_19, long_run_20, long_run_21,
    long_run_22, long_run_23, long_run_24, long_run_25, long_run_26, long_run_27, long_run_28,
    long_run_29, long_run_30, long_run_31, long_run_32, long_run_33, long_run_34]
  circuit_decide

assert_standard_axioms long_pulse

end Redstone.Theorems.ContainerSignal.DropperHopperPulse
