import Redstone.Lemmas.ContainerSignal
import Redstone.Proof.Circuit

/-!
# A comparator reads how full a container is

A comparator behind a container gives `14 * filled / capacity`, rounded down, plus one if the
container holds anything, where a slot counts as full with a full stack of whatever it holds
(`Redstone.Lemmas.ContainerSignal`). Here that is checked on the containers redstone is built
with, each with a comparator behind it and a lamp in front of the comparator:

```
y = 1:   B   C   L      B: the container;  C: comparator reading it;  L: lamp
y = 0:       S          S: stone under the comparator
x:       0   1   2      one such row for every container, two blocks apart along z
```

| container | contents | signal |
|---|---|---|
| chest | nothing | 0 |
| chest | 123 items (64 + 59) | 1 |
| chest | 124 items (64 + 60) | 2 |
| double chest, read at one half | 27 full stacks in the other half | 8 |
| dropper | 5 swords, which do not stack | 8 |
| dropper | 2 stacks of 16 ender pearls | 4 |
| hopper | 22 pieces of redstone | 1 |
| hopper | 23 pieces of redstone | 2 |
| furnace | 64 iron ingots in the result slot | 5 |
| barrel | 27 full stacks | 15 |

The comparators start off, with output 0. A lamp put in front of each one makes it look at its
container (a neighbour update); the comparator's tick runs two game ticks later.

What is proved:

* `passive_at_rest`: the level with the chests and the droppers is quiescent.
* `reads_after_two_ticks`: after game tick 1 every comparator still has output 0; after game
  tick 2 the outputs are those of the table, and each lamp is lit except that of the empty
  chest.
* `reads_closed_form`: these outputs are `signalOf slots stackSize items`, the closed form of
  the lemma file, for 27, 54 and 9 slots and stack sizes 64, 1 and 16.
* `reads_for_ever`: the level after the run is quiescent: the outputs and the lamps stay as
  they are for ever.
* `ticking_read`: the two hoppers, with 22 and 23 items, give 1 and 2, and the furnace gives 5
  (a bounded run: hoppers and furnaces are ticking block entities, and a level with one is
  never quiescent).
* `barrel_reads`: the full barrel gives 15.

The levels are loaded raw.

## Not proved

* The barrel is not followed tick by tick with checkpoints: the command `checkpoints` cannot
  write a level with a barrel as a term (the block state of a barrel has a property `open`,
  and what `Repr` prints for it does not parse back). `barrel_reads` is one evaluation of the
  two game ticks.
* Brewing stand, shulker box, trapped chest, dispenser, crafter and the containers with one
  slot: their signal is the same function of their slots (`Container.redstoneSignalAt`), or,
  for the crafter, a count of slots; they are not evaluated here.
-/

set_option Elab.async false

namespace Redstone.Theorems.ContainerSignal.Fullness

open Component.Container (signalOf)

/-- The container of the row at `z`. -/
def container (z : ℤ) : Pos := ⟨0, 1, z⟩

/-- The comparator of the row at `z`, which reads the container. -/
def comparator (z : ℤ) : Pos := ⟨1, 1, z⟩

/-- The lamp of the row at `z`, in front of the comparator. -/
def lamp (z : ℤ) : Pos := ⟨2, 1, z⟩

/-- A comparator on a stone block, reading the container of the row at `z`; it is off. -/
def reader (z : ℤ) : List (Pos × Block) :=
  [(⟨1, 0, z⟩, .plain .stone), (comparator z, .comparator ⟨.west, .compare, false⟩)]

/-- `k` full stacks of cobblestone, and `size - k` empty slots. -/
def fullStacks (k size : ℕ) : Inventory :=
  List.replicate k (.of "minecraft:cobblestone" 64) ++ Inventory.empty (size - k)

/-- The slots of a chest with a stack of 64 pieces of redstone and a stack of `n` pieces of
cobblestone. -/
def twoStacks (n : ℕ) : Inventory :=
  ((Inventory.empty 27).setItem 0 (.of "minecraft:redstone" 64)).setItem 5
    (.of "minecraft:cobblestone" n)

/-- The slots of a dropper with five swords, which do not stack. -/
def swords : Inventory := List.replicate 5 (.of "minecraft:iron_sword" 1) ++ Inventory.empty 4

/-- The slots of a dropper with two stacks of 16 ender pearls. -/
def pearls : Inventory := List.replicate 2 (.of "minecraft:ender_pearl" 16) ++ Inventory.empty 7

/-- The slots of a hopper with `n` pieces of redstone. -/
def redstone (n : ℕ) : Inventory := (Inventory.empty 5).setItem 0 (.of "minecraft:redstone" n)

/-- The slots of a furnace with a full stack of iron ingots in its result slot. -/
def ingots : Inventory := (Inventory.empty 3).setItem 2 (.of "minecraft:iron_ingot" 64)

/-- The rows of the containers that are not ticked. -/
def rows : List ℤ := [0, 2, 4, 6, 9, 11]

/-- Containers that are not ticked, each read by a comparator, in rows two blocks apart:

* `z = 0`: an empty chest;
* `z = 2`: a chest with 123 items (a stack of 64 and one of 59);
* `z = 4`: a chest with 124 items;
* `z = 6, 7`: a double chest, 27 full stacks in the half at `z = 7`; the comparator reads the
  half at `z = 6`;
* `z = 9`: a dropper with five swords, which do not stack;
* `z = 11`: a dropper with two stacks of 16 ender pearls. -/
def passive : Level :=
  .ofCells ([
      (container 0, .chest ⟨.west, .single, false⟩),
      (container 2, .chest ⟨.west, .single, false⟩),
      (container 4, .chest ⟨.west, .single, false⟩),
      (container 6, .chest ⟨.west, .right, false⟩), (container 7, .chest ⟨.west, .left, false⟩),
      (container 9, .dropper ⟨.west, false⟩),
      (container 11, .dropper ⟨.west, false⟩)] ++
      reader 0 ++ reader 2 ++ reader 4 ++ reader 6 ++ reader 9 ++ reader 11)
    [(container 2, .chest { items := twoStacks 59 }),
      (container 4, .chest { items := twoStacks 60 }),
      (container 7, .chest { items := fullStacks 27 27 }),
      (container 9, .dropper { items := swords }), (container 11, .dropper { items := pearls })]

/-- The rows of the containers that are ticked. -/
def tickingRows : List ℤ := [0, 2, 4]

/-- Containers with a ticking block entity, each read by a comparator: a hopper with 22 items
at `z = 0`, a hopper with 23 items at `z = 2`, and at `z = 4` a furnace with a full stack of
iron ingots in its result slot. The hoppers point down at nothing, so they keep what they
have. -/
def ticking : Level :=
  .ofCells ([(container 0, .hopper ⟨true, .down⟩), (container 2, .hopper ⟨true, .down⟩),
      (container 4, .furnace ⟨.west, false⟩)] ++ reader 0 ++ reader 2 ++ reader 4)
    [(container 0, .hopper { items := redstone 22 }),
      (container 2, .hopper { items := redstone 23 }),
      (container 4, .furnace { items := ingots })]

/-- A full barrel, read by a comparator. -/
def barrel : Level :=
  .ofCells ((container 0, .barrel ⟨.west, false⟩) :: reader 0)
    [(container 0, .barrel { items := fullStacks 27 27 })]

/-- A lamp is put in front of every comparator before game tick 1, which makes each comparator
look at its container; four game ticks. -/
def schedule : Schedule := .first (rows.map fun z => .set (lamp z) (.redstoneLamp ⟨false⟩)) 4

/-- The same for the ticking containers. -/
def tickingSchedule : Schedule :=
  .first (tickingRows.map fun z => .set (lamp z) (.redstoneLamp ⟨false⟩)) 4

/-- The same for the barrel; two game ticks. -/
def barrelSchedule : Schedule := .first [.set (lamp 0) (.redstoneLamp ⟨false⟩)] 2

/-- The output the comparator at `p` has stored. -/
def output (l : Level) (p : Pos) : ℕ :=
  match l.blockEntities p with
  | some (.comparator d) => d.output
  | _ => 0

/-- The outputs of the comparators of the rows `zs`. -/
def outputs (l : Level) (zs : List ℤ) : List ℕ := zs.map fun z => output l (comparator z)

/-- Which lamps of the rows `zs` are lit. -/
def lit (l : Level) (zs : List ℤ) : List Bool :=
  zs.map fun z => l.blockAt (lamp z) == .redstoneLamp ⟨true⟩

checkpoints state := schedule from passive
checkpoints tick := tickingSchedule from ticking

/-- The level with the containers that are not ticked is at rest, and every comparator has
output 0. -/
theorem passive_at_rest : passive.Quiescent ∧ outputs passive rows = [0, 0, 0, 0, 0, 0] := by
  circuit_decide

assert_standard_axioms passive_at_rest

/-- **The comparators read their containers two game ticks after they are updated.** After game
tick 1 every output is still 0. After game tick 2: the empty chest 0, the chest with 123 items
1, the chest with 124 items 2, the double chest that is half full 8, the dropper with five
swords 8, the dropper with 32 ender pearls 4; every lamp but the first is lit. -/
theorem reads_after_two_ticks :
    outputs (rules.runSchedule (schedule.take 1) passive) rows = [0, 0, 0, 0, 0, 0] ∧
      outputs (rules.runSchedule (schedule.take 2) passive) rows = [0, 1, 2, 8, 8, 4] ∧
      lit (rules.runSchedule (schedule.take 2) passive) rows =
        [false, true, true, true, true, true] ∧
      (rules.runSchedule (schedule.take 2) passive).overflow = false := by
  rw [state_run_1, state_run_2]
  circuit_decide

assert_standard_axioms reads_after_two_ticks

/-- **What the comparators read is the closed form**: `signalOf slots stackSize items` for a
chest (27 slots) with 0, 123 and 124 items, a double chest (54 slots) with 1728, a dropper (9
slots) with 5 items that do not stack, and a dropper with 32 items that stack to 16. -/
theorem reads_closed_form :
    outputs (rules.runSchedule (schedule.take 2) passive) rows =
      [signalOf 27 64 0, signalOf 27 64 123, signalOf 27 64 124, signalOf 54 64 1728,
        signalOf 9 1 5, signalOf 9 16 32] := by
  rw [state_run_2]
  circuit_decide

assert_standard_axioms reads_closed_form

/-- The outputs do not depend on the clocks. -/
theorem outputs_advance (l : Level) (n : ℕ) (zs : List ℤ) :
    outputs (l.advance n) zs = outputs l zs := rfl

/-- The lamps do not depend on the clocks. -/
theorem lit_advance (l : Level) (n : ℕ) (zs : List ℤ) : lit (l.advance n) zs = lit l zs := rfl

/-- **The readings stay for ever.** The level after the four game ticks is quiescent, so after
any number of further game ticks the outputs and the lamps are the same, and the model reaches
no bound. -/
theorem reads_for_ever (n : ℕ) :
    outputs (rules.steps n (rules.runSchedule schedule passive)) rows = [0, 1, 2, 8, 8, 4] ∧
      lit (rules.steps n (rules.runSchedule schedule passive)) rows =
        [false, true, true, true, true, true] ∧
      (rules.steps n (rules.runSchedule schedule passive)).overflow = false := by
  rw [state_run, rules.steps_of_quiescent (by circuit_decide)]
  simp only [outputs_advance, lit_advance, Level.overflow_advance]
  circuit_decide

assert_standard_axioms reads_for_ever

/-- **A hopper with 22 items gives 1, a hopper with 23 gives 2, a furnace with one full slot of
three gives 5.** After game tick 1 the comparators still have output 0; after game ticks 2 to 4
they have 1, 2 and 5, the values of the closed form, and the lamps are lit. -/
theorem ticking_read :
    outputs (rules.runSchedule (tickingSchedule.take 1) ticking) tickingRows = [0, 0, 0] ∧
      outputs (rules.runSchedule (tickingSchedule.take 2) ticking) tickingRows = [1, 2, 5] ∧
      outputs (rules.runSchedule (tickingSchedule.take 3) ticking) tickingRows = [1, 2, 5] ∧
      outputs (rules.runSchedule (tickingSchedule.take 4) ticking) tickingRows = [1, 2, 5] ∧
      lit (rules.runSchedule (tickingSchedule.take 4) ticking) tickingRows = [true, true, true] ∧
      outputs (rules.runSchedule (tickingSchedule.take 4) ticking) tickingRows =
        [signalOf 5 64 22, signalOf 5 64 23, signalOf 3 64 64] ∧
      (rules.runSchedule (tickingSchedule.take 4) ticking).overflow = false := by
  rw [tick_run_1, tick_run_2, tick_run_3, tick_run_4]
  circuit_decide

assert_standard_axioms ticking_read

/-- **A full barrel gives 15**, the value of the closed form for 1728 items in 27 slots. Two
game ticks after the comparator is updated its output is 15 and the lamp is lit. -/
theorem barrel_reads :
    output (rules.runSchedule barrelSchedule barrel) (comparator 0) = 15 ∧
      signalOf 27 64 1728 = 15 ∧
      lit (rules.runSchedule barrelSchedule barrel) [0] = [true] ∧
      (rules.runSchedule barrelSchedule barrel).overflow = false := by
  circuit_decide

assert_standard_axioms barrel_reads

end Redstone.Theorems.ContainerSignal.Fullness
