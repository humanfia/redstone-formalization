import Redstone.Theorems.Dropper.Basic

/-!
# A dropper and a hopper that pass one item back and forth

```
y = 2    H          H  hopper pointing down
y = 1    D L        D  dropper facing up, one piece of redstone
         x = 0 1    L  lever on the east face of the dropper
```

The two containers face each other: the dropper pushes up into the hopper, the hopper pushes
down into the dropper. This pair is the core of the dropper and hopper pulse extenders and
toggles of the community. The lever on the dropper powers the dropper strongly, and through it
the hopper, which is thereby locked (`enabled=false`).

The schedule: two game ticks without input; the lever is switched on before game tick 3 and
off before game tick 17; 24 game ticks in all.

What the theorems say:

* with the lever off the item rests in the dropper: the hopper has nothing to push;
* the rising edge triggers the dropper and locks the hopper in the same game tick, and four
  game ticks later the item is in the hopper;
* **the locked hopper holds the item** for as long as the lever is on, also after its
  transfer cooldown of 8 game ticks has run out;
* **the item comes back in the game tick of the falling edge**: the hopper is unlocked, is
  ticked in that game tick, and pushes the item down into the dropper, which the same edge has
  cleared of `triggered`;
* the dropper and the hopper hold one item together at every game tick.

A hopper is a ticking block entity and records the game time of its last tick, so this level
is never quiescent (`Level.Quiescent`): the statements are about the bounded run of 24 game
ticks. A comparator that reads one of the two containers is not part of this circuit; the
circuits with a comparator readout belong to the hopper circuits.

The level is loaded raw, with the hopper off cooldown.
-/

set_option Elab.async false

namespace Redstone.Theorems.Dropper.HopperLoop

/-- The position of the dropper. -/
def dropper : Pos := ⟨0, 1, 0⟩

/-- The position of the hopper. -/
def hopper : Pos := ⟨0, 2, 0⟩

/-- The position of the lever. -/
def lever : Pos := ⟨1, 1, 0⟩

/-- A dropper facing up with a hopper on top that points down, and a lever on the side of the
dropper. The dropper holds one piece of redstone. -/
def circuit : Level :=
  .ofCells [(dropper, .dropper ⟨.up, false⟩), (hopper, .hopper ⟨true, .down⟩),
    (lever, .lever ⟨.wall, .east, false⟩)]
    [(dropper, .dropper { items := (Inventory.empty 9).setItem 0 (.of "minecraft:redstone" 1) })]

/-- Two game ticks without input, the lever switched on before game tick 3 and off before game
tick 17; 24 game ticks in all. -/
def schedule : Schedule :=
  .idle 2 ++ Schedule.first [.use lever .east] 14 ++ Schedule.first [.use lever .east] 8

checkpoints state := schedule from circuit

/-- The transfer cooldown of the hopper; zero if there is no hopper. -/
def cooldown (l : Level) : ℤ :=
  match l.blockEntities hopper with
  | some (.hopper d) => d.cooldownTime
  | _ => 0

/-- What the dropper and the hopper hold, in this order. -/
def pair (l : Level) : List (ℕ × String × ℕ) × List (ℕ × String × ℕ) :=
  (contents l dropper, contents l hopper)

/-- The item in the dropper, the hopper empty. -/
def inDropper : List (ℕ × String × ℕ) × List (ℕ × String × ℕ) :=
  ([(0, "minecraft:redstone", 1)], [])

/-- The item in the hopper, the dropper empty. -/
def inHopper : List (ℕ × String × ℕ) × List (ℕ × String × ℕ) :=
  ([], [(0, "minecraft:redstone", 1)])

/-- At the start the item is in the dropper, and the hopper is the one ticking block
entity. -/
theorem start : pair circuit = inDropper ∧ circuit.blockEntityTickers = [hopper] := by
  circuit_decide

assert_standard_axioms start

/-- **With the lever off the item rests in the dropper**: after the first two game ticks
nothing has changed. -/
theorem rest :
    pair (rules.runSchedule (schedule.take 1) circuit) = inDropper ∧
      pair (rules.runSchedule (schedule.take 2) circuit) = inDropper ∧
      (rules.runSchedule (schedule.take 2) circuit).blocksAt [lever, dropper, hopper] =
        [.lever ⟨.wall, .east, false⟩, .dropper ⟨.up, false⟩, .hopper ⟨true, .down⟩] ∧
      (rules.runSchedule (schedule.take 2) circuit).overflow = false := by
  rw [state_run_1, state_run_2]
  circuit_decide

assert_standard_axioms rest

/-- **The rising edge** triggers the dropper and locks the hopper in the same game tick, and
schedules the dropper's tick four game ticks after the lever was used. -/
theorem rising_edge :
    (rules.runSchedule (schedule.take 3) circuit).blocksAt [lever, dropper, hopper] =
        [.lever ⟨.wall, .east, true⟩, .dropper ⟨.up, true⟩, .hopper ⟨false, .down⟩] ∧
      (rules.runSchedule (schedule.take 3) circuit).pending = [(dropper, .dropper, 3, .normal)] ∧
      pair (rules.runSchedule (schedule.take 3) circuit) = inDropper ∧
      (rules.runSchedule (schedule.take 3) circuit).overflow = false := by
  rw [state_run_3]
  circuit_decide

assert_standard_axioms rising_edge

/-- **The item goes up after four game ticks**: it is in the dropper after game tick 5 and in
the hopper after game tick 6. The hopper, which was empty, is put on its cooldown of 8 game
ticks and has 7 left after its own tick. -/
theorem goes_up :
    pair (rules.runSchedule (schedule.take 5) circuit) = inDropper ∧
      pair (rules.runSchedule (schedule.take 6) circuit) = inHopper ∧
      cooldown (rules.runSchedule (schedule.take 6) circuit) = 7 ∧
      (rules.runSchedule (schedule.take 6) circuit).overflow = false := by
  rw [state_run_5, state_run_6]
  circuit_decide

assert_standard_axioms goes_up

/-- **The locked hopper holds the item.** After each of the game ticks 7 to 11 the item is in
the hopper, which is on cooldown. -/
theorem held :
    [pair (rules.runSchedule (schedule.take 7) circuit),
        pair (rules.runSchedule (schedule.take 8) circuit),
        pair (rules.runSchedule (schedule.take 9) circuit),
        pair (rules.runSchedule (schedule.take 10) circuit),
        pair (rules.runSchedule (schedule.take 11) circuit)] = List.replicate 5 inHopper ∧
      cooldown (rules.runSchedule (schedule.take 11) circuit) = 2 ∧
      (rules.runSchedule (schedule.take 11) circuit).overflow = false := by
  rw [state_run_7, state_run_8, state_run_9, state_run_10, state_run_11]
  circuit_decide

assert_standard_axioms held

/-- **It holds the item after its cooldown has run out, too.** The cooldown is at 1 after game
tick 12 and at 0 from game tick 13 on; after each of the game ticks 12 to 16 the item is still
in the hopper. The hopper does not push because it is locked. -/
theorem held_off_cooldown :
    [pair (rules.runSchedule (schedule.take 12) circuit),
        pair (rules.runSchedule (schedule.take 13) circuit),
        pair (rules.runSchedule (schedule.take 14) circuit),
        pair (rules.runSchedule (schedule.take 15) circuit),
        pair (rules.runSchedule (schedule.take 16) circuit)] = List.replicate 5 inHopper ∧
      [cooldown (rules.runSchedule (schedule.take 12) circuit),
        cooldown (rules.runSchedule (schedule.take 13) circuit),
        cooldown (rules.runSchedule (schedule.take 16) circuit)] = [1, 0, 0] ∧
      (rules.runSchedule (schedule.take 16) circuit).blocksAt [dropper, hopper] =
        [.dropper ⟨.up, true⟩, .hopper ⟨false, .down⟩] ∧
      (rules.runSchedule (schedule.take 16) circuit).overflow = false := by
  rw [state_run_12, state_run_13, state_run_14, state_run_15, state_run_16]
  circuit_decide

assert_standard_axioms held_off_cooldown

/-- **The item comes back in the game tick of the falling edge.** After game tick 17 the lever
is off, the dropper is not triggered, the hopper is unlocked and on cooldown again, and the
item is in the dropper. -/
theorem comes_back :
    (rules.runSchedule (schedule.take 17) circuit).blocksAt [lever, dropper, hopper] =
        [.lever ⟨.wall, .east, false⟩, .dropper ⟨.up, false⟩, .hopper ⟨true, .down⟩] ∧
      pair (rules.runSchedule (schedule.take 17) circuit) = inDropper ∧
      cooldown (rules.runSchedule (schedule.take 17) circuit) = 8 ∧
      (rules.runSchedule (schedule.take 17) circuit).pending = [] ∧
      (rules.runSchedule (schedule.take 17) circuit).overflow = false := by
  rw [state_run_17]
  circuit_decide

assert_standard_axioms comes_back

/-- The items in the dropper and in the hopper, together, after `k` game ticks. -/
def total (k : ℕ) : ℕ := itemTotal (rules.runSchedule (schedule.take k) circuit) [dropper, hopper]

/-- **No item is lost or made**: at the start and after every one of the 24 game ticks the
dropper and the hopper hold one item together. -/
theorem conservation (k : ℕ) (hk : k ≤ 24) : total k = 1 := by
  unfold total
  interval_cases k
  · rw [List.take_zero, Rules.runSchedule_nil]
    circuit_decide
  all_goals first
    | (rw [state_run_1]; circuit_decide)
    | (rw [state_run_2]; circuit_decide)
    | (rw [state_run_3]; circuit_decide)
    | (rw [state_run_4]; circuit_decide)
    | (rw [state_run_5]; circuit_decide)
    | (rw [state_run_6]; circuit_decide)
    | (rw [state_run_7]; circuit_decide)
    | (rw [state_run_8]; circuit_decide)
    | (rw [state_run_9]; circuit_decide)
    | (rw [state_run_10]; circuit_decide)
    | (rw [state_run_11]; circuit_decide)
    | (rw [state_run_12]; circuit_decide)
    | (rw [state_run_13]; circuit_decide)
    | (rw [state_run_14]; circuit_decide)
    | (rw [state_run_15]; circuit_decide)
    | (rw [state_run_16]; circuit_decide)
    | (rw [state_run_17]; circuit_decide)
    | (rw [state_run_18]; circuit_decide)
    | (rw [state_run_19]; circuit_decide)
    | (rw [state_run_20]; circuit_decide)
    | (rw [state_run_21]; circuit_decide)
    | (rw [state_run_22]; circuit_decide)
    | (rw [state_run_23]; circuit_decide)
    | (rw [state_run_24]; circuit_decide)

assert_standard_axioms conservation

/-- **At the end**, seven game ticks after the item came back, it is still in the dropper, the
blocks are as they were built, and the hopper's cooldown has run down to 1. -/
theorem final :
    pair (rules.runSchedule schedule circuit) = inDropper ∧
      (rules.runSchedule schedule circuit).blocksAt [lever, dropper, hopper] =
        [.lever ⟨.wall, .east, false⟩, .dropper ⟨.up, false⟩, .hopper ⟨true, .down⟩] ∧
      cooldown (rules.runSchedule schedule circuit) = 1 ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run]
  circuit_decide

assert_standard_axioms final

end Redstone.Theorems.Dropper.HopperLoop
