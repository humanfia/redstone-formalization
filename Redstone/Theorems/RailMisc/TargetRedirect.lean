import Redstone.Proof.Circuit

/-!
# A target block redirects redstone dust

One redstone dust with a lever to its west, a target block to its north and a lamp to its
east; a second lamp behind the target. Top view (x to the right, z down), everything at y = 1
on a floor of stone:

```
z = -2:      N            N lamp behind the target
z = -1:      T            T target
z =  0:   L  d  E         L lever, d dust, E lamp east of the dust
x =       0  1  2
```

Dust connects to a target block as it does to a lever (`RedstoneWireBlock.shouldConnectTo`
is true for every signal source, and the target is one). So the dust is a corner, west and
north, and does not point at the lamp `E`: when the lever is on, the dust powers the target,
which is a full block and passes the power on to the lamp `N`, and `E` stays dark. Without
the target the dust has the lever as its only connection and becomes a line, west and east,
which points at `E`: now `E` lights and `N` does not.

| target | lever | dust | lamp `N` | lamp `E` |
|---|---|---|---|---|
| present | off | corner, 0 | dark | dark |
| present | on | corner, 15 | lit | dark |
| removed | off | line, 0 | dark | dark |
| removed | on | line, 15 | dark | lit |

The target itself keeps `power = 0` throughout: it emits a signal of its own only after a
projectile has hit it (`TargetBlock.onProjectileHit`), and a projectile is an entity, which
is out of reach of these proofs (see `Overview`).

The level is loaded raw with the lever off and the dust already a corner, as the model leaves
it after the lever has been used once; `circuit_quiescent` shows that this is a state of
rest.
-/

set_option Elab.async false

namespace Redstone.Theorems.RailMisc.TargetRedirect

/-- The position of the lever. -/
def lever : Pos := ⟨0, 1, 0⟩

/-- The position of the dust. -/
def dust : Pos := ⟨1, 1, 0⟩

/-- The position of the target: north of the dust. -/
def target : Pos := ⟨1, 1, -1⟩

/-- The lamp behind the target. -/
def lampN : Pos := ⟨1, 1, -2⟩

/-- The lamp east of the dust. -/
def lampE : Pos := ⟨2, 1, 0⟩

/-- The lever, on or off. -/
def leverState (on : Bool) : Block := .lever ⟨.floor, .north, on⟩

/-- The dust as a corner that joins west and north. -/
def corner (power : Fin 16) : Block :=
  .redstoneWire { east := .none, north := .side, power := power, south := .none, west := .side }

/-- The dust as a line that joins west and east. -/
def line (power : Fin 16) : Block :=
  .redstoneWire { east := .side, north := .none, power := power, south := .none, west := .side }

/-- The target that has not been hit. -/
def targetOff : Block := .target ⟨0⟩

/-- A lamp, lit or dark. -/
def lampState (lit : Bool) : Block := .redstoneLamp ⟨lit⟩

/-- The floor: three by four blocks of stone under the layout. -/
def floor : List (Pos × Block) :=
  (List.range 3).flatMap fun i => (List.range 4).map fun j =>
    ((⟨(i : ℤ), 0, (j : ℤ) - 2⟩ : Pos), Block.plain .stone)

/-- The layout with the lever off. -/
def circuit : Level :=
  .ofCells (floor ++ [(lever, leverState false), (dust, corner 0), (target, targetOff),
    (lampN, lampState false), (lampE, lampState false)])

/-- The lever is switched on before game tick 1 and off before game tick 4; the target is
destroyed before game tick 10; the lever is switched on again before game tick 12. Fourteen
game ticks in all. -/
def schedule : Schedule :=
  .first [.use lever .up] 3 ++ .first [.use lever .up] 6 ++ .first [.destroy target] 2 ++
    .first [.use lever .up] 3

checkpoints state := schedule from circuit

/-- The observed blocks: lever, dust, target, lamp behind the target, lamp east of the dust. -/
def cells : List Pos := [lever, dust, target, lampN, lampE]

/-- With the lever off the layout is at rest, and the target gives no signal in any
direction. -/
theorem circuit_quiescent :
    circuit.Quiescent ∧
      ([.north, .south, .west, .east, .up, .down] : List Direction).map (circuit.emits target) =
        List.replicate 6 0 := by
  circuit_decide

assert_standard_axioms circuit_quiescent

/-- **With the target: the dust is a corner, the lamp behind the target lights and the lamp
east of the dust stays dark**, in the game tick in which the lever is used. The target keeps
`power = 0`. -/
theorem with_target_on :
    (rules.runSchedule (schedule.take 1) circuit).blocksAt cells =
        [leverState true, corner 15, targetOff, lampState true, lampState false] ∧
      (rules.runSchedule (schedule.take 1) circuit).overflow = false := by
  rw [state_run_1]
  circuit_decide

assert_standard_axioms with_target_on

/-- With the target and the lever on, the layout stays so for ever. -/
theorem with_target_stays_on (n : ℕ) :
    (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).blocksAt cells =
        [leverState true, corner 15, targetOff, lampState true, lampState false] ∧
      (rules.steps n (rules.runSchedule (schedule.take 1) circuit)).overflow = false := by
  rw [state_run_1, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms with_target_stays_on

/-- **With the target, lever off again**: the dust loses its power in the same game tick
(game tick 4), and the lamp behind the target goes dark four game ticks later (it is lit after
game tick 6 and dark after game tick 7). After game tick 9 the blocks are those the layout
started with. -/
theorem with_target_off :
    (rules.runSchedule (schedule.take 4) circuit).blocksAt cells =
        [leverState false, corner 0, targetOff, lampState true, lampState false] ∧
      (rules.runSchedule (schedule.take 6) circuit).blockAt lampN = lampState true ∧
      (rules.runSchedule (schedule.take 7) circuit).blockAt lampN = lampState false ∧
      (rules.runSchedule (schedule.take 9) circuit).world = circuit.world ∧
      (rules.runSchedule (schedule.take 9) circuit).overflow = false := by
  rw [state_run_4, state_run_6, state_run_7, state_run_9]
  circuit_decide

assert_standard_axioms with_target_off

/-- **The target is removed: the dust turns into a line** that points at the lamp east of it,
in the game tick in which the target is destroyed (game tick 10). Nothing is lit: the lever is
off. -/
theorem target_removed :
    (rules.runSchedule (schedule.take 10) circuit).blocksAt cells =
        [leverState false, line 0, .AIR, lampState false, lampState false] ∧
      (rules.runSchedule (schedule.take 10) circuit).overflow = false := by
  rw [state_run_10]
  circuit_decide

assert_standard_axioms target_removed

/-- **Without the target: the lamp east of the dust lights and the other stays dark**, in the
game tick in which the lever is used (game tick 12), and for ever after. -/
theorem without_target_on (n : ℕ) :
    (rules.runSchedule (schedule.take 12) circuit).blocksAt cells =
        [leverState true, line 15, .AIR, lampState false, lampState true] ∧
      (rules.steps n (rules.runSchedule (schedule.take 12) circuit)).blocksAt cells =
        [leverState true, line 15, .AIR, lampState false, lampState true] ∧
      (rules.steps n (rules.runSchedule (schedule.take 12) circuit)).overflow = false := by
  rw [state_run_12, rules.steps_of_quiescent (by circuit_decide)]
  simp only [Level.blocksAt_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms without_target_on

end Redstone.Theorems.RailMisc.TargetRedirect
