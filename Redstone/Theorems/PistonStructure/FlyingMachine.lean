import Redstone.Proof.Circuit

/-!
# The two-way flying machine: one block per cycle

The smallest two-way flying machine engine of the community: two observers, two slime blocks
and two sticky pistons, six blocks in the air with nothing else around. It is two halves that
are images of each other under a half turn; each half is an observer that looks outwards, a
slime block behind the observer, and a sticky piston that touches the slime block of its own
half and has the slime block of the other half in front of it.

Seen from the south (x to the right, y up), all in the plane `z = 0`:

```
y = 2   X  Ow S  P←           Ow observer facing west (it watches X), S slime,
y = 1   .  .  P→ S  Oe        P← sticky piston facing west; P→ sticky piston facing east,
       -2 -1  0  1  2  = x    S slime, Oe observer facing east
```

`X` is a stone block that holds the machine at rest; breaking it is seen by the west observer
and starts the machine towards the east. (By symmetry, an update at the east observer starts
it towards the west; that direction is not stated here.)

How one cycle goes, in game ticks counted from the game tick in which the west observer
switches on (one redstone tick is two game ticks); `cycle_phases` states it:

* 0: the west observer switches on. Its slime block is powered and powers the lower piston
  under it, which extends and pushes the *front half*: the lower slime block, and stuck to it
  the east observer and the upper piston.
* 2: the west observer switches off. The lower piston has had a pulse of two game ticks; it
  retracts and lets go of the blocks it was pushing, which arrive in the same game tick.
  The front half is now one cell further east. The east observer has been moved, so it
  schedules its own pulse.
* 4: the east observer switches on. Its slime block powers the upper piston above it, which
  extends into the gap between the halves.
* 6: the east observer switches off. The upper piston retracts, and this time it pulls: its
  head is stuck to the upper slime block, which takes along the west observer and the lower
  piston, the *rear half*.
* 8: the rear half has arrived. The machine is whole again, one cell further east, and the
  west observer, which has been moved, schedules the next pulse: the cycle starts again two
  game ticks later.

So a cycle is ten game ticks, and the machine moves one block per cycle.

What the theorems say:

* `at_rest`: with the stone block in place the machine is at rest.
* `first_cycle`, `second_cycle`: the stone block is broken before game tick 1. After game
  tick 10 the level consists of exactly the six blocks of the machine, each one cell east of
  where it was built, with one scheduled tick (the west observer's, two game ticks ahead) and
  nothing moving; after game tick 20 the same holds two cells east. `machine k` and
  `pendingAt k` are the blocks and the scheduled tick of the machine `k` cells east, so the
  two theorems say that the second cycle is the first one, translated by one block.
* `cycle_phases`: the blocks at game ticks 4, 6 and 8 of the first cycle, and the same,
  translated by one block, at game ticks 14, 16 and 18.

Not proved: that the machine flies for ever. The two cycles are checked game tick by game
tick; a proof for all `k` needs a lemma that a game tick commutes with the translation of a
level by one block, which the foundation does not have (`Rules.periodic_of_shiftInvariant` is
about translation in time only). What is not stated either: the machine carrying anything
(entities are not on moving blocks in the model), and stopping it at an obstacle.
-/

set_option Elab.async false

namespace Redstone.Theorems.PistonStructure.FlyingMachine

/-- The stone block that the west observer watches while the machine is at rest. -/
def stop : Pos := ⟨-2, 2, 0⟩

/-- The machine, `dx` cells east of where it is built. Upper row: the observer facing west,
its slime block, the sticky piston facing west. Lower row: the sticky piston facing east, the
slime block of the east observer, and the observer facing east. -/
def machine (dx : ℤ) : List (Pos × Block) :=
  [(⟨-1 + dx, 2, 0⟩, .observer ⟨.west, false⟩), (⟨dx, 2, 0⟩, .plain .slime_block),
    (⟨1 + dx, 2, 0⟩, .pistonBase .sticky_piston ⟨false, .west⟩),
    (⟨dx, 1, 0⟩, .pistonBase .sticky_piston ⟨false, .east⟩),
    (⟨1 + dx, 1, 0⟩, .plain .slime_block), (⟨2 + dx, 1, 0⟩, .observer ⟨.east, false⟩)]

/-- The machine at rest: the six blocks, and the stone block in front of the west observer. -/
def circuit : Level := .ofCells ((stop, .plain .stone) :: machine 0)

/-- The stone block is broken before game tick 1; twenty game ticks. -/
def schedule : Schedule := .first [.destroy stop] 20

checkpoints state := schedule from circuit

/-- With the stone block in place the machine is at rest. -/
theorem at_rest : circuit.Quiescent := by circuit_decide

assert_standard_axioms at_rest

/-- The scheduled ticks of the machine `dx` cells east at the end of a cycle: the tick of the
west observer, which has just been moved, two game ticks ahead. -/
def pendingAt (dx : ℤ) : List (Pos × BlockId × ℕ × TickPriority) :=
  [(⟨-1 + dx, 2, 0⟩, .observer, 2, .normal)]

/-- **The first cycle: one block east in ten game ticks.** After game tick 10 the blocks of
the level are exactly the six blocks of the machine, each one cell east of where it was
built; the stone block is gone. The only scheduled tick is the west observer's, two game
ticks ahead; no block is moving and no block event is waiting. -/
theorem first_cycle :
    circuit.world = World.ofList ((stop, .plain .stone) :: machine 0) ∧
      (rules.runSchedule (schedule.take 10) circuit).world = World.ofList (machine 1) ∧
      (rules.runSchedule (schedule.take 10) circuit).pending = pendingAt 1 ∧
      (rules.runSchedule (schedule.take 10) circuit).blockEntityTickers = [] ∧
      (rules.runSchedule (schedule.take 10) circuit).blockEvents = [] ∧
      (rules.runSchedule (schedule.take 10) circuit).overflow = false := by
  rw [state_run_10]
  circuit_decide

assert_standard_axioms first_cycle

/-- **The second cycle: one more block in ten more game ticks.** After game tick 20 the level
is what it was after game tick 10, one block further east: exactly the six blocks of the
machine two cells east of where it was built, the west observer's tick two game ticks ahead,
nothing moving. -/
theorem second_cycle :
    (rules.runSchedule schedule circuit).world = World.ofList (machine 2) ∧
      (rules.runSchedule schedule circuit).pending = pendingAt 2 ∧
      (rules.runSchedule schedule circuit).blockEntityTickers = [] ∧
      (rules.runSchedule schedule circuit).blockEvents = [] ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run]
  circuit_decide

assert_standard_axioms second_cycle

/-- The `moving_piston` block with `type=sticky`: a sticky head on its way, or the base of a
sticky piston while it retracts. -/
def movingSticky (facing : Direction) : Block := .movingPiston ⟨facing, .sticky⟩

/-- The `moving_piston` block with `type=normal`: a block that is pushed or pulled. -/
def movingNormal (facing : Direction) : Block := .movingPiston ⟨facing, .normal⟩

/-- Four game ticks into a cycle that starts with the machine `dx` cells east: the front half
(lower slime block, east observer, upper piston) has been dropped one cell further east, and
the lower piston is retracting. -/
def frontDropped (dx : ℤ) : List (Pos × Block) :=
  [(⟨-1 + dx, 2, 0⟩, .observer ⟨.west, false⟩), (⟨dx, 2, 0⟩, .plain .slime_block),
    (⟨2 + dx, 2, 0⟩, .pistonBase .sticky_piston ⟨false, .west⟩),
    (⟨dx, 1, 0⟩, movingSticky .east),
    (⟨2 + dx, 1, 0⟩, .plain .slime_block), (⟨3 + dx, 1, 0⟩, .observer ⟨.east, false⟩)]

/-- Six game ticks into the cycle: the east observer is on, and the upper piston extends its
head into the gap. -/
def reaching (dx : ℤ) : List (Pos × Block) :=
  [(⟨-1 + dx, 2, 0⟩, .observer ⟨.west, false⟩), (⟨dx, 2, 0⟩, .plain .slime_block),
    (⟨1 + dx, 2, 0⟩, movingSticky .west),
    (⟨2 + dx, 2, 0⟩, .pistonBase .sticky_piston ⟨true, .west⟩),
    (⟨dx, 1, 0⟩, .pistonBase .sticky_piston ⟨false, .east⟩),
    (⟨2 + dx, 1, 0⟩, .plain .slime_block), (⟨3 + dx, 1, 0⟩, .observer ⟨.east, true⟩)]

/-- Eight game ticks into the cycle: the upper piston retracts and pulls the rear half (upper
slime block, west observer, lower piston), which is on its way. -/
def rearPulled (dx : ℤ) : List (Pos × Block) :=
  [(⟨dx, 2, 0⟩, movingNormal .west), (⟨1 + dx, 2, 0⟩, movingNormal .west),
    (⟨2 + dx, 2, 0⟩, movingSticky .west), (⟨1 + dx, 1, 0⟩, movingNormal .west),
    (⟨2 + dx, 1, 0⟩, .plain .slime_block), (⟨3 + dx, 1, 0⟩, .observer ⟨.east, false⟩)]

/-- **The phases of a cycle, twice.** In the first cycle the west observer switches on in game
tick 2. After game tick 4 the front half has been dropped one cell east; after game tick 6
the upper piston is reaching back; after game tick 8 the rear half is being pulled. Ten game
ticks later the level holds the same blocks one cell further east. -/
theorem cycle_phases :
    (rules.runSchedule (schedule.take 4) circuit).world = World.ofList (frontDropped 0) ∧
      (rules.runSchedule (schedule.take 6) circuit).world = World.ofList (reaching 0) ∧
      (rules.runSchedule (schedule.take 8) circuit).world = World.ofList (rearPulled 0) ∧
      (rules.runSchedule (schedule.take 14) circuit).world = World.ofList (frontDropped 1) ∧
      (rules.runSchedule (schedule.take 16) circuit).world = World.ofList (reaching 1) ∧
      (rules.runSchedule (schedule.take 18) circuit).world = World.ofList (rearPulled 1) := by
  rw [state_run_4, state_run_6, state_run_8, state_run_14, state_run_16, state_run_18]
  circuit_decide

assert_standard_axioms cycle_phases

end Redstone.Theorems.PistonStructure.FlyingMachine
