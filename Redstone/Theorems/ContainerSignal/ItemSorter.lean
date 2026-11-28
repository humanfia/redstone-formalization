import Redstone.Proof.Circuit

/-!
# The hopper item sorter

The standard item filter: a hopper that holds the item to sort in its first slot and one filler
item in each of the other four takes nothing but that item out of the transport line above it;
a comparator measures it, and when it holds one item too many the hopper below it is unlocked
for just long enough to take that one item out.

One cell, seen from the side, `x` to the right. The cells stand next to each other along `z`,
and the dust of neighbouring cells is connected:

```
y =  3:      T   .   .   .      T: transport hopper, points north along the line of cells
y =  2:      F   C   d   .      F: filter hopper, points east (at the comparator, so nowhere)
y =  1:  c   L   S   S   d      C: comparator reading F;  d: dust, the second one block lower
y =  0:      t   S   R   S      c: chest;  L: lower hopper, points west into the chest
y = -1:      .   .   S   .      t: torch on the west side of the stone at x = 1, under L
x:      -1   0   1   2   3      R: repeater (delay 1) reading the stone under the second dust
```

The filter holds 18 pieces of the sorted item and 4 sticks: 22 items, for which a hopper
gives the signal 1 (`Redstone.Component.Container.hopper_signal_one_two_three`: 1 up to 22
items, 2 from 23, 3 from 46). The comparator's 1 reaches the first dust and dies there: the
second dust is off, the repeater is off, the torch is lit and locks the lower hopper. A 23rd
item raises the signal to 2; now the second dust has power 1, which the repeater picks up
through the block under it; it powers the block the torch is on, the torch goes out, and the
lower hopper pulls one item out of the first slot of the filter. With 22 items again the
signal drops and the torch locks the lower hopper before its cooldown of 8 game ticks is over.

The level here has two cells: the cell at `z = 0` sorts redstone, its neighbour at `z = 1`
sorts iron ingots. The transport hoppers point north, so an item put into the transport hopper
at `z = 1` moves to the one at `z = 0`, the end of the line.

What is proved (1 redstone tick is 2 game ticks; all times are game ticks):

* `start`, `rest_holds`: with 22 items in each filter the lower hoppers are locked, and four
  game ticks change nothing.
* `filter_signal`: the signal of the filter hopper is 1 with 18 + 4 items and 2 with 19 + 4.
  (For the other common filter, 41 + 4, it is 2, and 3 with 42 + 4. That filter needs a sorter
  whose repeater reacts to 3 only; it is not this layout.)
* `one_item_sorted`: one piece of redstone in the line. Game tick 1: it is in the filter (23
  items). Game tick 3: the comparator gives 2, the dust has power 2 and 1. Game tick 5: the
  repeater is on. Game tick 7: the torch is out, the lower hopper is unlocked and takes one
  item. Game tick 9: the comparator is back at 1. Game tick 11: the repeater is off. Game tick
  13: the torch is lit and the lower hopper locked again, six game ticks after it took the
  item and so before it could take a second one. **Exactly one item has left the filter.**
* `back_at_rest`: after 16 game ticks every block of both cells is as it was at the start, and
  nothing is scheduled. The item is in the lower hopper, which is locked: it reaches the chest
  when the next item unlocks the hopper (`two_items_sorted`).
* `neighbour_not_triggered`: all the while the neighbouring cell does not react: its dust
  stays at 1 and 0 although it is connected to dust of power 2 and 1, its torch stays lit. This
  is why the cells can stand side by side, and why the filter must never reach the signal 3:
  the neighbour's first dust would then have power 2 and its second dust 1, as in a cell that
  sorts.
* `two_items_sorted`: two pieces of redstone, eight game ticks apart. The second one finds the
  lower hopper still unlocked; the lower hopper pushes the first item into the chest and takes
  the second in game tick 15, and the sorter is at rest from game tick 21.
* `other_item_passes`: a piece of cobblestone goes along the line to its end and stays there;
  no filter takes it and nothing switches.

Hoppers are ticking block entities that record the game time, so no level here is quiescent
(`Level.Quiescent`): every statement is about a bounded run.

The level is loaded raw. The dust shapes and powers, the lit torches, the locked lower hoppers
and the comparator outputs are those the model settles in when the redstone is placed block by
block next to the filled filter hoppers. The hoppers are ticked cell by cell, the cell at
`z = 1` first, and in each cell from top to bottom.

## Not proved

* What happens at the signal 3 (46 items in a filter): it is not a state of rest of this
  layout, since the lower hopper drains the filter from 23 items on, and reaching it needs
  items to arrive faster than one every 8 game ticks, which one transport line does not do.
* Items that arrive as entities (dropped on a hopper, or from a water stream): entity motion is
  `Float`, which the kernel does not evaluate.
-/

set_option Elab.async false

-- The theorems are conjunctions of many equations between tuples, and the instance that
-- decides such an equation is large.
set_option synthInstance.maxSize 100000

namespace Redstone.Theorems.ContainerSignal.ItemSorter

/-- The transport hopper of the cell at `z`. -/
def transport (z : ℤ) : Pos := ⟨0, 3, z⟩

/-- The filter hopper of the cell at `z`. -/
def filter (z : ℤ) : Pos := ⟨0, 2, z⟩

/-- The lower hopper of the cell at `z`, which the torch locks. -/
def lower (z : ℤ) : Pos := ⟨0, 1, z⟩

/-- The chest of the cell at `z`. -/
def chest (z : ℤ) : Pos := ⟨-1, 1, z⟩

/-- The comparator of the cell at `z`. -/
def comparator (z : ℤ) : Pos := ⟨1, 2, z⟩

/-- The first piece of dust of the cell at `z`, in front of the comparator. -/
def dust1 (z : ℤ) : Pos := ⟨2, 2, z⟩

/-- The second piece of dust of the cell at `z`, one block lower, on the block the repeater
reads. -/
def dust2 (z : ℤ) : Pos := ⟨3, 1, z⟩

/-- The repeater of the cell at `z`. -/
def repeater (z : ℤ) : Pos := ⟨2, 0, z⟩

/-- The torch of the cell at `z`, under the lower hopper. -/
def torch (z : ℤ) : Pos := ⟨0, 0, z⟩

/-- The filter: `n` pieces of the item to sort in the first slot, and one stick in each of the
other four. -/
def filterItems (item : String) (n : ℕ) : Inventory :=
  [.of item n, .of "minecraft:stick" 1, .of "minecraft:stick" 1, .of "minecraft:stick" 1,
    .of "minecraft:stick" 1]

/-- A repeater of delay 1 (two game ticks) that reads the block east of it. -/
def repeaterBlock (powered : Bool) : Block :=
  .repeater ⟨⟨1, by decide, by decide⟩, .east, false, powered⟩

/-- The blocks of the cell at `z`, without its two pieces of dust: the three hoppers and the
chest, the comparator on its block, the block under the first dust, the block under the second
dust, the repeater on its floor, the block the repeater powers and the torch on its side. -/
def cellBlocks (z : ℤ) : List (Pos × Block) :=
  [(transport z, .hopper ⟨true, .north⟩), (filter z, .hopper ⟨true, .east⟩),
    (lower z, .hopper ⟨false, .west⟩), (chest z, .chest ⟨.west, .single, false⟩),
    (⟨1, 1, z⟩, .plain .stone), (⟨2, 1, z⟩, .plain .stone), (⟨3, 0, z⟩, .plain .stone),
    (⟨2, -1, z⟩, .plain .stone), (⟨1, 0, z⟩, .plain .stone),
    (comparator z, .comparator ⟨.west, .compare, true⟩),
    (repeater z, repeaterBlock false),
    (torch z, .redstoneWallTorch ⟨.west, true⟩)]

/-- Two cells of the sorter at rest, with `items` in the transport hopper of the cell at
`z = 1`. -/
def sorter (items : Inventory) : Level :=
  .ofCells (cellBlocks 1 ++ cellBlocks 0 ++ [
      (dust1 0, .redstoneWire ⟨.side, .none, 1, .side, .side⟩),
      (dust2 0, .redstoneWire ⟨.none, .none, 0, .side, .up⟩),
      (dust1 1, .redstoneWire ⟨.side, .side, 1, .none, .side⟩),
      (dust2 1, .redstoneWire ⟨.none, .side, 0, .none, .up⟩),
      (⟨0, 3, -1⟩, .plain .stone)])
    [(filter 0, .hopper { items := filterItems "minecraft:redstone" 18 }),
      (filter 1, .hopper { items := filterItems "minecraft:iron_ingot" 18 }),
      (transport 1, .hopper { items := items }),
      (comparator 0, .comparator { output := 1 }), (comparator 1, .comparator { output := 1 })]

/-- The number of items in the chest at `p`. -/
def chestCount (l : Level) (p : Pos) : ℕ :=
  match l.blockEntities p with
  | some (.chest d) => (d.items.map (·.count)).sum
  | _ => 0

/-- Where the items of the cell at `z` are: the numbers of items in its transport hopper, its
filter hopper, its lower hopper and its chest. -/
def items (l : Level) (z : ℤ) : ℕ × ℕ × ℕ × ℕ :=
  (l.itemCount (transport z), l.itemCount (filter z), l.itemCount (lower z),
    chestCount l (chest z))

/-- The output the comparator at `p` has stored. -/
def output (l : Level) (p : Pos) : ℕ :=
  match l.blockEntities p with
  | some (.comparator d) => d.output
  | _ => 0

/-- The redstone of the cell at `z`: the output of the comparator, the power of the two pieces
of dust, whether the repeater is on, whether the torch is lit, and whether the lower hopper is
enabled (not locked). -/
def redstone (l : Level) (z : ℤ) : ℕ × ℕ × ℕ × Bool × Bool × Bool :=
  (output l (comparator z), l.dustPower (dust1 z), l.dustPower (dust2 z),
    l.blockAt (repeater z) == repeaterBlock true,
    l.blockAt (torch z) == .redstoneWallTorch ⟨.west, true⟩,
    l.blockAt (lower z) == .hopper ⟨true, .west⟩)

/-- The sorter with nothing in the transport hoppers. -/
def idleSorter : Level := sorter (Inventory.empty 5)

/-- The sorter with one piece of redstone in the transport hopper of the cell at `z = 1`. -/
def circuit : Level := sorter ((Inventory.empty 5).setItem 0 (.of "minecraft:redstone" 1))

/-- The sorter with two pieces of redstone in that hopper. -/
def circuit2 : Level := sorter ((Inventory.empty 5).setItem 0 (.of "minecraft:redstone" 2))

/-- The sorter with a piece of cobblestone, which neither cell sorts, in that hopper. -/
def circuitOther : Level := sorter ((Inventory.empty 5).setItem 0 (.of "minecraft:cobblestone" 1))


/-- Four game ticks without input. -/
def idleSchedule : Schedule := .idle 4

/-- 16 game ticks without input. -/
def schedule : Schedule := .idle 16

/-- 24 game ticks without input. -/
def schedule2 : Schedule := .idle 24

/-- 12 game ticks without input. -/
def scheduleOther : Schedule := .idle 12

checkpoints idle := idleSchedule from idleSorter
checkpoints state := schedule from circuit
checkpoints second := schedule2 from circuit2
checkpoints other := scheduleOther from circuitOther

/-- At the start each filter holds 22 items, the comparators give 1, the first dust has power
1 and the second none, the repeaters are off, the torches are lit and the lower hoppers are
locked; the piece of redstone is in the transport hopper at `z = 1`; nothing is scheduled; the
hoppers are ticked cell by cell, from top to bottom. -/
theorem start :
    items circuit 0 = (0, 22, 0, 0) ∧ redstone circuit 0 = (1, 1, 0, false, true, false) ∧
      items circuit 1 = (1, 22, 0, 0) ∧ redstone circuit 1 = (1, 1, 0, false, true, false) ∧
      circuit.pending = [] ∧
      circuit.blockEntityTickers =
        [transport 1, filter 1, lower 1, transport 0, filter 0, lower 0] := by
  circuit_decide

assert_standard_axioms start

/-- **The signal of the filter.** With 18 pieces of the sorted item and the four sticks the
filter hopper gives 1; with 19 it gives 2. With 41 it gives 2, and with 42 it gives 3. -/
theorem filter_signal :
    Component.Container.redstoneSignal (filterItems "minecraft:redstone" 18) = 1 ∧
      Component.Container.redstoneSignal (filterItems "minecraft:redstone" 19) = 2 ∧
      Component.Container.redstoneSignal (filterItems "minecraft:redstone" 41) = 2 ∧
      Component.Container.redstoneSignal (filterItems "minecraft:redstone" 42) = 3 := by
  circuit_decide

assert_standard_axioms filter_signal

/-- **The sorter at rest stays at rest.** With nothing in the transport line, after each of
four game ticks both filters hold their 22 items, both lower hoppers are empty and locked, and
the redstone of both cells is as it was; nothing is scheduled. -/
theorem rest_holds :
    items (rules.runSchedule (idleSchedule.take 1) idleSorter) 0 = (0, 22, 0, 0) ∧
      redstone (rules.runSchedule (idleSchedule.take 1) idleSorter) 0 =
        (1, 1, 0, false, true, false) ∧
      items (rules.runSchedule (idleSchedule.take 1) idleSorter) 1 = (0, 22, 0, 0) ∧
      redstone (rules.runSchedule (idleSchedule.take 1) idleSorter) 1 =
        (1, 1, 0, false, true, false) ∧
      items (rules.runSchedule (idleSchedule.take 2) idleSorter) 0 = (0, 22, 0, 0) ∧
      redstone (rules.runSchedule (idleSchedule.take 2) idleSorter) 0 =
        (1, 1, 0, false, true, false) ∧
      items (rules.runSchedule (idleSchedule.take 2) idleSorter) 1 = (0, 22, 0, 0) ∧
      redstone (rules.runSchedule (idleSchedule.take 2) idleSorter) 1 =
        (1, 1, 0, false, true, false) ∧
      items (rules.runSchedule (idleSchedule.take 3) idleSorter) 0 = (0, 22, 0, 0) ∧
      redstone (rules.runSchedule (idleSchedule.take 3) idleSorter) 0 =
        (1, 1, 0, false, true, false) ∧
      items (rules.runSchedule (idleSchedule.take 3) idleSorter) 1 = (0, 22, 0, 0) ∧
      redstone (rules.runSchedule (idleSchedule.take 3) idleSorter) 1 =
        (1, 1, 0, false, true, false) ∧
      items (rules.runSchedule (idleSchedule.take 4) idleSorter) 0 = (0, 22, 0, 0) ∧
      redstone (rules.runSchedule (idleSchedule.take 4) idleSorter) 0 =
        (1, 1, 0, false, true, false) ∧
      items (rules.runSchedule (idleSchedule.take 4) idleSorter) 1 = (0, 22, 0, 0) ∧
      redstone (rules.runSchedule (idleSchedule.take 4) idleSorter) 1 =
        (1, 1, 0, false, true, false) ∧
      (rules.runSchedule (idleSchedule.take 4) idleSorter).pending = [] ∧
      (rules.runSchedule (idleSchedule.take 4) idleSorter).overflow = false := by
  rw [idle_run_1, idle_run_2, idle_run_3, idle_run_4]
  circuit_decide

assert_standard_axioms rest_holds

/-- **One item is sorted.** The piece of redstone is in the filter after game tick 1 (23
items). The comparator gives 2 after game tick 3, and the dust has power 2 and 1. The repeater
is on after game tick 5. After game tick 7 the torch is out, the lower hopper is unlocked and
has taken one item: the filter is back at 22. The comparator is back at 1 after game tick 9,
the repeater off after game tick 11, and after game tick 13 the torch is lit and the lower
hopper locked, with the one item in it. Each line is the state after one game tick: where the
items of the cell are (transport, filter, lower hopper, chest), and its redstone (comparator
output, first dust, second dust, repeater on, torch lit, lower hopper unlocked). -/
theorem one_item_sorted :
    items (rules.runSchedule (schedule.take 1) circuit) 0 = (0, 23, 0, 0) ∧
      redstone (rules.runSchedule (schedule.take 1) circuit) 0 = (1, 1, 0, false, true, false) ∧
      items (rules.runSchedule (schedule.take 2) circuit) 0 = (0, 23, 0, 0) ∧
      redstone (rules.runSchedule (schedule.take 2) circuit) 0 = (1, 1, 0, false, true, false) ∧
      items (rules.runSchedule (schedule.take 3) circuit) 0 = (0, 23, 0, 0) ∧
      redstone (rules.runSchedule (schedule.take 3) circuit) 0 = (2, 2, 1, false, true, false) ∧
      items (rules.runSchedule (schedule.take 4) circuit) 0 = (0, 23, 0, 0) ∧
      redstone (rules.runSchedule (schedule.take 4) circuit) 0 = (2, 2, 1, false, true, false) ∧
      items (rules.runSchedule (schedule.take 5) circuit) 0 = (0, 23, 0, 0) ∧
      redstone (rules.runSchedule (schedule.take 5) circuit) 0 = (2, 2, 1, true, true, false) ∧
      items (rules.runSchedule (schedule.take 6) circuit) 0 = (0, 23, 0, 0) ∧
      redstone (rules.runSchedule (schedule.take 6) circuit) 0 = (2, 2, 1, true, true, false) ∧
      items (rules.runSchedule (schedule.take 7) circuit) 0 = (0, 22, 1, 0) ∧
      redstone (rules.runSchedule (schedule.take 7) circuit) 0 = (2, 2, 1, true, false, true) ∧
      items (rules.runSchedule (schedule.take 8) circuit) 0 = (0, 22, 1, 0) ∧
      redstone (rules.runSchedule (schedule.take 8) circuit) 0 = (2, 2, 1, true, false, true) ∧
      items (rules.runSchedule (schedule.take 9) circuit) 0 = (0, 22, 1, 0) ∧
      redstone (rules.runSchedule (schedule.take 9) circuit) 0 = (1, 1, 0, true, false, true) ∧
      items (rules.runSchedule (schedule.take 10) circuit) 0 = (0, 22, 1, 0) ∧
      redstone (rules.runSchedule (schedule.take 10) circuit) 0 = (1, 1, 0, true, false, true) ∧
      items (rules.runSchedule (schedule.take 11) circuit) 0 = (0, 22, 1, 0) ∧
      redstone (rules.runSchedule (schedule.take 11) circuit) 0 = (1, 1, 0, false, false, true) ∧
      items (rules.runSchedule (schedule.take 12) circuit) 0 = (0, 22, 1, 0) ∧
      redstone (rules.runSchedule (schedule.take 12) circuit) 0 = (1, 1, 0, false, false, true) ∧
      items (rules.runSchedule (schedule.take 13) circuit) 0 = (0, 22, 1, 0) ∧
      redstone (rules.runSchedule (schedule.take 13) circuit) 0 = (1, 1, 0, false, true, false) ∧
      items (rules.runSchedule (schedule.take 14) circuit) 0 = (0, 22, 1, 0) ∧
      redstone (rules.runSchedule (schedule.take 14) circuit) 0 = (1, 1, 0, false, true, false) ∧
      items (rules.runSchedule (schedule.take 15) circuit) 0 = (0, 22, 1, 0) ∧
      redstone (rules.runSchedule (schedule.take 15) circuit) 0 = (1, 1, 0, false, true, false) ∧
      items (rules.runSchedule (schedule.take 16) circuit) 0 = (0, 22, 1, 0) ∧
      redstone (rules.runSchedule (schedule.take 16) circuit) 0 = (1, 1, 0, false, true, false) ∧
      (rules.runSchedule (schedule.take 16) circuit).overflow = false := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7,
    state_run_8, state_run_9, state_run_10, state_run_11, state_run_12, state_run_13,
    state_run_14, state_run_15, state_run_16]
  circuit_decide

assert_standard_axioms one_item_sorted

/-- **The neighbouring cell is not triggered.** While the cell at `z = 0` sorts its item, with
its dust at power 2 and 1, the redstone of the cell at `z = 1` stays as it is after every game
tick: comparator 1, dust 1 and 0, repeater off, torch lit, lower hopper locked; and its filter
keeps its 22 items. -/
theorem neighbour_not_triggered :
    redstone (rules.runSchedule (schedule.take 1) circuit) 1 = (1, 1, 0, false, true, false) ∧
      redstone (rules.runSchedule (schedule.take 2) circuit) 1 = (1, 1, 0, false, true, false) ∧
      redstone (rules.runSchedule (schedule.take 3) circuit) 1 = (1, 1, 0, false, true, false) ∧
      redstone (rules.runSchedule (schedule.take 4) circuit) 1 = (1, 1, 0, false, true, false) ∧
      redstone (rules.runSchedule (schedule.take 5) circuit) 1 = (1, 1, 0, false, true, false) ∧
      redstone (rules.runSchedule (schedule.take 6) circuit) 1 = (1, 1, 0, false, true, false) ∧
      redstone (rules.runSchedule (schedule.take 7) circuit) 1 = (1, 1, 0, false, true, false) ∧
      redstone (rules.runSchedule (schedule.take 8) circuit) 1 = (1, 1, 0, false, true, false) ∧
      redstone (rules.runSchedule (schedule.take 9) circuit) 1 = (1, 1, 0, false, true, false) ∧
      redstone (rules.runSchedule (schedule.take 10) circuit) 1 = (1, 1, 0, false, true, false) ∧
      redstone (rules.runSchedule (schedule.take 11) circuit) 1 = (1, 1, 0, false, true, false) ∧
      redstone (rules.runSchedule (schedule.take 12) circuit) 1 = (1, 1, 0, false, true, false) ∧
      redstone (rules.runSchedule (schedule.take 13) circuit) 1 = (1, 1, 0, false, true, false) ∧
      redstone (rules.runSchedule (schedule.take 14) circuit) 1 = (1, 1, 0, false, true, false) ∧
      redstone (rules.runSchedule (schedule.take 15) circuit) 1 = (1, 1, 0, false, true, false) ∧
      redstone (rules.runSchedule (schedule.take 16) circuit) 1 = (1, 1, 0, false, true, false) ∧
      items (rules.runSchedule (schedule.take 16) circuit) 1 = (0, 22, 0, 0) := by
  rw [state_run_1, state_run_2, state_run_3, state_run_4, state_run_5, state_run_6, state_run_7,
    state_run_8, state_run_9, state_run_10, state_run_11, state_run_12, state_run_13,
    state_run_14, state_run_15, state_run_16]
  circuit_decide

assert_standard_axioms neighbour_not_triggered

/-- The positions of all blocks of the two cells. -/
def positions : List Pos :=
  ([0, 1] : List ℤ).flatMap fun z => (cellBlocks z).map (·.1) ++ [dust1 z, dust2 z]

/-- **The sorter is back at rest.** After the 16 game ticks every block of both cells is the
block it was at the start, the comparator of the sorting cell has output 1, nothing is
scheduled, and exactly one item has left the filter: it is in the lower hopper. -/
theorem back_at_rest :
    (rules.runSchedule schedule circuit).blocksAt positions = circuit.blocksAt positions ∧
      output (rules.runSchedule schedule circuit) (comparator 0) = 1 ∧
      (rules.runSchedule schedule circuit).pending = [] ∧
      items (rules.runSchedule schedule circuit) 0 = (0, 22, 1, 0) ∧
      (rules.runSchedule schedule circuit).overflow = false := by
  rw [state_run]
  circuit_decide

assert_standard_axioms back_at_rest

/-- **Two items, one after the other.** The second piece of redstone reaches the filter in game
tick 9, when the comparator has just gone back to 1 and the lower hopper is still unlocked. The
comparator gives 2 again after game tick 11. In game tick 15, eight game ticks after it took
the first item, the lower hopper pushes that item into the chest and takes the second. The
torch is lit again after game tick 21: one item is in the chest, one in the locked lower
hopper, the filter holds 22, and nothing is scheduled. -/
theorem two_items_sorted :
    items (rules.runSchedule (schedule2.take 1) circuit2) 0 = (0, 23, 0, 0) ∧
      redstone (rules.runSchedule (schedule2.take 1) circuit2) 0 = (1, 1, 0, false, true, false) ∧
      items (rules.runSchedule (schedule2.take 2) circuit2) 0 = (0, 23, 0, 0) ∧
      redstone (rules.runSchedule (schedule2.take 2) circuit2) 0 = (1, 1, 0, false, true, false) ∧
      items (rules.runSchedule (schedule2.take 3) circuit2) 0 = (0, 23, 0, 0) ∧
      redstone (rules.runSchedule (schedule2.take 3) circuit2) 0 = (2, 2, 1, false, true, false) ∧
      items (rules.runSchedule (schedule2.take 4) circuit2) 0 = (0, 23, 0, 0) ∧
      redstone (rules.runSchedule (schedule2.take 4) circuit2) 0 = (2, 2, 1, false, true, false) ∧
      items (rules.runSchedule (schedule2.take 5) circuit2) 0 = (0, 23, 0, 0) ∧
      redstone (rules.runSchedule (schedule2.take 5) circuit2) 0 = (2, 2, 1, true, true, false) ∧
      items (rules.runSchedule (schedule2.take 6) circuit2) 0 = (0, 23, 0, 0) ∧
      redstone (rules.runSchedule (schedule2.take 6) circuit2) 0 = (2, 2, 1, true, true, false) ∧
      items (rules.runSchedule (schedule2.take 7) circuit2) 0 = (0, 22, 1, 0) ∧
      redstone (rules.runSchedule (schedule2.take 7) circuit2) 0 = (2, 2, 1, true, false, true) ∧
      items (rules.runSchedule (schedule2.take 8) circuit2) 0 = (0, 22, 1, 0) ∧
      redstone (rules.runSchedule (schedule2.take 8) circuit2) 0 = (2, 2, 1, true, false, true) ∧
      items (rules.runSchedule (schedule2.take 9) circuit2) 0 = (0, 23, 1, 0) ∧
      redstone (rules.runSchedule (schedule2.take 9) circuit2) 0 = (1, 1, 0, true, false, true) ∧
      items (rules.runSchedule (schedule2.take 10) circuit2) 0 = (0, 23, 1, 0) ∧
      redstone (rules.runSchedule (schedule2.take 10) circuit2) 0 = (1, 1, 0, true, false, true) ∧
      items (rules.runSchedule (schedule2.take 11) circuit2) 0 = (0, 23, 1, 0) ∧
      redstone (rules.runSchedule (schedule2.take 11) circuit2) 0 = (2, 2, 1, false, false, true) ∧
      items (rules.runSchedule (schedule2.take 12) circuit2) 0 = (0, 23, 1, 0) ∧
      redstone (rules.runSchedule (schedule2.take 12) circuit2) 0 = (2, 2, 1, false, false, true) ∧
      items (rules.runSchedule (schedule2.take 13) circuit2) 0 = (0, 23, 1, 0) ∧
      redstone (rules.runSchedule (schedule2.take 13) circuit2) 0 = (2, 2, 1, true, false, true) ∧
      items (rules.runSchedule (schedule2.take 14) circuit2) 0 = (0, 23, 1, 0) ∧
      redstone (rules.runSchedule (schedule2.take 14) circuit2) 0 = (2, 2, 1, true, false, true) ∧
      items (rules.runSchedule (schedule2.take 15) circuit2) 0 = (0, 22, 1, 1) ∧
      redstone (rules.runSchedule (schedule2.take 15) circuit2) 0 = (2, 2, 1, true, false, true) ∧
      items (rules.runSchedule (schedule2.take 16) circuit2) 0 = (0, 22, 1, 1) ∧
      redstone (rules.runSchedule (schedule2.take 16) circuit2) 0 = (2, 2, 1, true, false, true) ∧
      items (rules.runSchedule (schedule2.take 17) circuit2) 0 = (0, 22, 1, 1) ∧
      redstone (rules.runSchedule (schedule2.take 17) circuit2) 0 = (1, 1, 0, true, false, true) ∧
      items (rules.runSchedule (schedule2.take 18) circuit2) 0 = (0, 22, 1, 1) ∧
      redstone (rules.runSchedule (schedule2.take 18) circuit2) 0 = (1, 1, 0, true, false, true) ∧
      items (rules.runSchedule (schedule2.take 19) circuit2) 0 = (0, 22, 1, 1) ∧
      redstone (rules.runSchedule (schedule2.take 19) circuit2) 0 = (1, 1, 0, false, false, true) ∧
      items (rules.runSchedule (schedule2.take 20) circuit2) 0 = (0, 22, 1, 1) ∧
      redstone (rules.runSchedule (schedule2.take 20) circuit2) 0 = (1, 1, 0, false, false, true) ∧
      items (rules.runSchedule (schedule2.take 21) circuit2) 0 = (0, 22, 1, 1) ∧
      redstone (rules.runSchedule (schedule2.take 21) circuit2) 0 = (1, 1, 0, false, true, false) ∧
      items (rules.runSchedule (schedule2.take 22) circuit2) 0 = (0, 22, 1, 1) ∧
      redstone (rules.runSchedule (schedule2.take 22) circuit2) 0 = (1, 1, 0, false, true, false) ∧
      items (rules.runSchedule (schedule2.take 23) circuit2) 0 = (0, 22, 1, 1) ∧
      redstone (rules.runSchedule (schedule2.take 23) circuit2) 0 = (1, 1, 0, false, true, false) ∧
      items (rules.runSchedule (schedule2.take 24) circuit2) 0 = (0, 22, 1, 1) ∧
      redstone (rules.runSchedule (schedule2.take 24) circuit2) 0 = (1, 1, 0, false, true, false) ∧
      (rules.runSchedule (schedule2.take 24) circuit2).pending = [] ∧
      (rules.runSchedule (schedule2.take 24) circuit2).overflow = false := by
  rw [second_run_1, second_run_2, second_run_3, second_run_4, second_run_5, second_run_6,
    second_run_7, second_run_8, second_run_9, second_run_10, second_run_11, second_run_12,
    second_run_13, second_run_14, second_run_15, second_run_16, second_run_17, second_run_18,
    second_run_19, second_run_20, second_run_21, second_run_22, second_run_23, second_run_24]
  circuit_decide

assert_standard_axioms two_items_sorted

/-- **An item that is not sorted passes.** The piece of cobblestone moves to the transport
hopper at `z = 0`, the end of the line, in game tick 1 and stays there for the twelve game
ticks of the run; both filters keep their 22 items, and after the run the redstone of both
cells is at rest and nothing is scheduled. -/
theorem other_item_passes :
    items (rules.runSchedule (scheduleOther.take 1) circuitOther) 0 = (1, 22, 0, 0) ∧
      items (rules.runSchedule (scheduleOther.take 1) circuitOther) 1 = (0, 22, 0, 0) ∧
      items (rules.runSchedule (scheduleOther.take 2) circuitOther) 0 = (1, 22, 0, 0) ∧
      items (rules.runSchedule (scheduleOther.take 2) circuitOther) 1 = (0, 22, 0, 0) ∧
      items (rules.runSchedule (scheduleOther.take 3) circuitOther) 0 = (1, 22, 0, 0) ∧
      items (rules.runSchedule (scheduleOther.take 3) circuitOther) 1 = (0, 22, 0, 0) ∧
      items (rules.runSchedule (scheduleOther.take 4) circuitOther) 0 = (1, 22, 0, 0) ∧
      items (rules.runSchedule (scheduleOther.take 4) circuitOther) 1 = (0, 22, 0, 0) ∧
      items (rules.runSchedule (scheduleOther.take 5) circuitOther) 0 = (1, 22, 0, 0) ∧
      items (rules.runSchedule (scheduleOther.take 5) circuitOther) 1 = (0, 22, 0, 0) ∧
      items (rules.runSchedule (scheduleOther.take 6) circuitOther) 0 = (1, 22, 0, 0) ∧
      items (rules.runSchedule (scheduleOther.take 6) circuitOther) 1 = (0, 22, 0, 0) ∧
      items (rules.runSchedule (scheduleOther.take 7) circuitOther) 0 = (1, 22, 0, 0) ∧
      items (rules.runSchedule (scheduleOther.take 7) circuitOther) 1 = (0, 22, 0, 0) ∧
      items (rules.runSchedule (scheduleOther.take 8) circuitOther) 0 = (1, 22, 0, 0) ∧
      items (rules.runSchedule (scheduleOther.take 8) circuitOther) 1 = (0, 22, 0, 0) ∧
      items (rules.runSchedule (scheduleOther.take 9) circuitOther) 0 = (1, 22, 0, 0) ∧
      items (rules.runSchedule (scheduleOther.take 9) circuitOther) 1 = (0, 22, 0, 0) ∧
      items (rules.runSchedule (scheduleOther.take 10) circuitOther) 0 = (1, 22, 0, 0) ∧
      items (rules.runSchedule (scheduleOther.take 10) circuitOther) 1 = (0, 22, 0, 0) ∧
      items (rules.runSchedule (scheduleOther.take 11) circuitOther) 0 = (1, 22, 0, 0) ∧
      items (rules.runSchedule (scheduleOther.take 11) circuitOther) 1 = (0, 22, 0, 0) ∧
      items (rules.runSchedule (scheduleOther.take 12) circuitOther) 0 = (1, 22, 0, 0) ∧
      items (rules.runSchedule (scheduleOther.take 12) circuitOther) 1 = (0, 22, 0, 0) ∧
      redstone (rules.runSchedule (scheduleOther.take 12) circuitOther) 0 =
        (1, 1, 0, false, true, false) ∧
      redstone (rules.runSchedule (scheduleOther.take 12) circuitOther) 1 =
        (1, 1, 0, false, true, false) ∧
      (rules.runSchedule (scheduleOther.take 12) circuitOther).pending = [] ∧
      (rules.runSchedule (scheduleOther.take 12) circuitOther).overflow = false := by
  rw [other_run_1, other_run_2, other_run_3, other_run_4, other_run_5, other_run_6, other_run_7,
    other_run_8, other_run_9, other_run_10, other_run_11, other_run_12]
  circuit_decide

assert_standard_axioms other_item_passes

end Redstone.Theorems.ContainerSignal.ItemSorter
