import Redstone.Proof.Circuit

/-!
# A lightning rod and a target that are placed powered

A stone block with a lamp beside the cell above it, and, apart from them, a lamp beside an
empty cell. Side view (z = 0):

```
y = 1:   R  M  .  .  T  M        R, T: empty cells; M lamps
y = 0:   S                       S stone
x =      0  1  2  3  4  5
```

Before the first game tick a lightning rod that is already `powered` is set into `R`
(pointing up, standing on the stone), and a target with `power = 9` into `T`. Neither has
been struck or hit: these are the states lightning and a projectile leave behind, put there
as `/setblock` does. What the blocks do with them is their own, block-only part of the two
pulses:

* **Lightning rod.** `LightningRodBlock.onPlace` schedules the tick that ends the signal, 8
  game ticks later, as a strike does. The rod gives 15 to its neighbours for 8 game ticks: the
  lamp is lit from the game tick of the placement, the rod is off after game tick 8, and the
  lamp goes dark four game ticks later.
* **Target.** `TargetBlock.onPlace` finds a target with a signal and no tick to end it, and
  resets it at once: the target has `power = 0` before the game tick runs, and the lamp beside
  it never lights. A target gives a signal only for the time a hit has scheduled.

The strike and the hit themselves need an entity (a lightning bolt, a projectile) and are out
of reach of these proofs (`Overview`).

The level is loaded raw; `circuit_quiescent` shows that it is at rest.
-/

set_option Elab.async false

namespace Redstone.Theorems.RailMisc.PlacedSensors

/-- The cell of the lightning rod. -/
def rod : Pos := ⟨0, 1, 0⟩

/-- The lamp beside the lightning rod. -/
def rodLamp : Pos := ⟨1, 1, 0⟩

/-- The cell of the target. -/
def target : Pos := ⟨4, 1, 0⟩

/-- The lamp beside the target. -/
def targetLamp : Pos := ⟨5, 1, 0⟩

/-- The empty cell west of the rod, where its signal is read. -/
def beside : Pos := ⟨-1, 1, 0⟩

/-- A lightning rod that points up and is powered. -/
def rodOn : Block := blk% "minecraft:lightning_rod[facing=up,powered=true,waterlogged=false]"

/-- A lightning rod that points up and is not powered. -/
def rodOff : Block := blk% "minecraft:lightning_rod[facing=up,powered=false,waterlogged=false]"

/-- A target with the given power. -/
def targetState (power : Fin 16) : Block := .target ⟨power⟩

/-- A lamp, lit or dark. -/
def lampState (lit : Bool) : Block := .redstoneLamp ⟨lit⟩

/-- The stone block and the two lamps. -/
def circuit : Level :=
  .ofCells [(⟨0, 0, 0⟩, .plain .stone), (rodLamp, lampState false), (targetLamp, lampState false)]

/-- The powered rod and the powered target are set before game tick 1; fifteen game ticks in
all. -/
def schedule : Schedule := .first [.set rod rodOn, .set target (targetState 9)] 15

checkpoints state := schedule from circuit

/-- The observed blocks: rod, its lamp, target, its lamp. -/
def cells : List Pos := [rod, rodLamp, target, targetLamp]

/-- The level as built is at rest. -/
theorem circuit_quiescent : circuit.Quiescent := by circuit_decide

assert_standard_axioms circuit_quiescent

/-- **A target placed with a signal loses it at once**: right after the input, before the
game tick runs, the target has `power = 0`, and nothing is scheduled for it. -/
theorem target_resets_on_place :
    (rules.input (.set target (targetState 9)) circuit).blockAt target = targetState 0 ∧
      (rules.input (.set target (targetState 9)) circuit).pending = [] ∧
      (rules.input (.set target (targetState 9)) circuit).overflow = false := by
  circuit_decide

assert_standard_axioms target_resets_on_place

/-- **A rod placed powered gives 15 and lights its lamp at once**, and its tick is due eight
game ticks after the placement; the target is off and its lamp dark. -/
theorem rod_powers_on_place :
    (rules.runSchedule (schedule.take 1) circuit).blocksAt cells =
        [rodOn, lampState true, targetState 0, lampState false] ∧
      (rules.runSchedule (schedule.take 1) circuit).signalTo beside = 15 ∧
      (rules.runSchedule (schedule.take 1) circuit).pending =
        [(rod, .lightning_rod, 7, .normal)] ∧
      (rules.runSchedule (schedule.take 1) circuit).overflow = false := by
  rw [state_run_1]
  circuit_decide

assert_standard_axioms rod_powers_on_place

/-- **The rod's pulse is eight game ticks long.** The rod is still powered and gives 15 after
game tick 7, and is off and gives nothing after game tick 8. Its lamp is lit after game tick
11 and dark after game tick 12, four game ticks after the rod went off. The target's lamp is
dark throughout. -/
theorem rod_pulse_length :
    (rules.runSchedule (schedule.take 7) circuit).blocksAt cells =
        [rodOn, lampState true, targetState 0, lampState false] ∧
      (rules.runSchedule (schedule.take 7) circuit).signalTo beside = 15 ∧
      (rules.runSchedule (schedule.take 8) circuit).blocksAt cells =
        [rodOff, lampState true, targetState 0, lampState false] ∧
      (rules.runSchedule (schedule.take 8) circuit).signalTo beside = 0 ∧
      (rules.runSchedule (schedule.take 11) circuit).blockAt rodLamp = lampState true ∧
      (rules.runSchedule (schedule.take 12) circuit).blocksAt cells =
        [rodOff, lampState false, targetState 0, lampState false] ∧
      (rules.runSchedule (schedule.take 12) circuit).overflow = false := by
  rw [state_run_7, state_run_8, state_run_11, state_run_12]
  circuit_decide

assert_standard_axioms rod_pulse_length

/-- **Afterwards both are off for ever**: after the schedule the level is at rest, with the
rod and the target off and both lamps dark. -/
theorem off_afterwards (n : ℕ) :
    (rules.steps n (rules.runSchedule schedule circuit)).blocksAt cells =
        [rodOff, lampState false, targetState 0, lampState false] ∧
      (rules.steps n (rules.runSchedule schedule circuit)).overflow = false := by
  rw [state_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms off_afterwards

end Redstone.Theorems.RailMisc.PlacedSensors
