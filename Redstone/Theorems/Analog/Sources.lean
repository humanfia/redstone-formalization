import Redstone.Theorems.Analog.Common

/-!
# Analog sources that are measured by their block state

A source block, a comparator that reads it, and a piece of redstone dust in front of the
comparator, on a stone floor; one such level for each source.

```
z = 0:  S  C  o        S: the source, C: comparator (reads west, emits east), o: output dust
x =     0  1  2        y = 1, seen from above
```

For each source the block is changed by a player or by `Level.setBlock`, and the comparator
and the dust are read four game ticks later, on a level at rest. That the comparator follows
in the second game tick (1 redstone tick = 2 game ticks) is checked for the cauldron and the
frame (`cauldron_delay`, `frame_table`). The formulas for every block state are in
`Redstone/Lemmas/AnalogSource.lean`; here the whole chain to the dust is observed. The four
levels have the same layout, which is why they share a file.

* **Cauldron** (`cauldron_table`): a bucket of water, of lava or of powder snow fills an empty
  cauldron, which then gives 3; an empty bucket empties it again, to 0; water at level 1 and 2
  gives 1 and 2.
* **End portal frame** (`frame_table`): 15 with an eye, 0 without.
* **Respawn anchor** (`anchor_table`): each piece of glowstone adds a charge; 1, 2, 3 and 4
  charges give 3, 7, 11 and 15.
* **Copper golem statue** (`statue_table`): a statue gives 1 to 4 by its pose; using an item
  on it turns it to the next pose, and after four turns it stands again: 1, 2, 3, 4, 1.

Cake and composter have files of their own (`Cake.lean`, `Composter.lean`); the sources that
keep their measure in a block entity are in `Stored.lean`, the copper bulb in
`CopperBulb.lean`.

The levels are loaded raw with the source in the state that gives 0 (for the statue, which
always gives a signal, without the statue), and are at rest (`circuit_quiescent`).
-/

set_option Elab.async false
-- The statements are conjunctions of comparisons of tuples; finding their `Decidable`
-- instance takes more steps than the default allows.
set_option synthInstance.maxSize 4096

namespace Redstone.Theorems.Analog.Sources

/-- The source. -/
def src : Pos := ⟨0, 1, 0⟩

/-- The comparator that reads the source. -/
def cmp : Pos := ⟨1, 1, 0⟩

/-- The dust in front of the comparator. -/
def out : Pos := ⟨2, 1, 0⟩

/-- The block `source`, a comparator that reads it and a piece of dust, on a stone floor. -/
def reader (source : Block) : Level :=
  .ofCells (floor [0, 1, 2] [0] ++
    [(src, source), (cmp, .comparator ⟨.west, .compare, false⟩), (out, wireEW)])

/-- What is observed: the source block, the comparator, and the power of the dust at the
output. -/
def observe (l : Level) : Block × (Bool × ℕ) × ℕ :=
  (l.blockAt src, comparator l cmp, l.dustPower out)

/-! ### Cauldron -/

/-- A water cauldron of the given level. -/
def water (level : IntRange 1 3) : Block := .layeredCauldron .water_cauldron ⟨level⟩

/-- The reader with an empty cauldron. -/
def cauldron : Level := reader (.plain .cauldron)

/-- A water bucket, an empty bucket, a lava bucket, an empty bucket and a powder snow bucket
are used on the cauldron, four game ticks apart; then the cauldron is set to water of level 1
and of level 2. -/
def cauldronSchedule : Schedule :=
  .first [.useItem src .up "minecraft:water_bucket"] 4 ++
    .first [.useItem src .up "minecraft:bucket"] 4 ++
    .first [.useItem src .up "minecraft:lava_bucket"] 4 ++
    .first [.useItem src .up "minecraft:bucket"] 4 ++
    .first [.useItem src .up "minecraft:powder_snow_bucket"] 4 ++
    .first [.set src (water ⟨1, by decide, by decide⟩)] 4 ++
    .first [.set src (water ⟨2, by decide, by decide⟩)] 4

checkpoints cd := cauldronSchedule from cauldron

/-- **A cauldron gives its level; lava counts as 3.** -/
theorem cauldron_table :
    observe cauldron = (.plain .cauldron, (false, 0), 0) ∧
      observe (rules.runSchedule (cauldronSchedule.take 4) cauldron) =
        (water ⟨3, by decide, by decide⟩, (true, 3), 3) ∧
      observe (rules.runSchedule (cauldronSchedule.take 8) cauldron) =
        (.plain .cauldron, (false, 0), 0) ∧
      observe (rules.runSchedule (cauldronSchedule.take 12) cauldron) =
        (.plain .lava_cauldron, (true, 3), 3) ∧
      observe (rules.runSchedule (cauldronSchedule.take 16) cauldron) =
        (.plain .cauldron, (false, 0), 0) ∧
      observe (rules.runSchedule (cauldronSchedule.take 20) cauldron) =
        (.layeredCauldron .powder_snow_cauldron ⟨⟨3, by decide, by decide⟩⟩, (true, 3), 3) ∧
      observe (rules.runSchedule (cauldronSchedule.take 24) cauldron) =
        (water ⟨1, by decide, by decide⟩, (true, 1), 1) ∧
      observe (rules.runSchedule (cauldronSchedule.take 28) cauldron) =
        (water ⟨2, by decide, by decide⟩, (true, 2), 2) ∧
      (rules.runSchedule cauldronSchedule cauldron).Quiescent ∧
      (rules.runSchedule cauldronSchedule cauldron).overflow = false := by
  rw [cd_run_4, cd_run_8, cd_run_12, cd_run_16, cd_run_20,
    cd_run_24, cd_run_28, cd_run]
  circuit_decide

assert_standard_axioms cauldron_table

/-- The comparator follows the cauldron two game ticks later: the water bucket is used before
game tick 1; the comparator is off after game tick 1 and emits 3 after game tick 2. -/
theorem cauldron_delay :
    observe (rules.runSchedule (cauldronSchedule.take 1) cauldron) =
        (water ⟨3, by decide, by decide⟩, (false, 0), 0) ∧
      observe (rules.runSchedule (cauldronSchedule.take 2) cauldron) =
        (water ⟨3, by decide, by decide⟩, (true, 3), 3) := by
  rw [cd_run_1, cd_run_2]
  circuit_decide

assert_standard_axioms cauldron_delay

/-! ### End portal frame -/

/-- An end portal frame, with or without an eye. -/
def frameBlock (eye : Bool) : Block := .endPortalFrame ⟨eye, .north⟩

/-- The reader with an end portal frame without an eye. -/
def frame : Level := reader (frameBlock false)

/-- The frame gets its eye before game tick 1 and loses it before game tick 5. -/
def frameSchedule : Schedule :=
  .first [.set src (frameBlock true)] 4 ++ .first [.set src (frameBlock false)] 4

checkpoints fr := frameSchedule from frame

/-- **An end portal frame gives 15 with an eye and nothing without.** -/
theorem frame_table :
    observe frame = (frameBlock false, (false, 0), 0) ∧
      observe (rules.runSchedule (frameSchedule.take 1) frame) =
        (frameBlock true, (false, 0), 0) ∧
      observe (rules.runSchedule (frameSchedule.take 2) frame) =
        (frameBlock true, (true, 15), 15) ∧
      observe (rules.runSchedule (frameSchedule.take 4) frame) =
        (frameBlock true, (true, 15), 15) ∧
      observe (rules.runSchedule (frameSchedule.take 6) frame) =
        (frameBlock false, (false, 0), 0) ∧
      (rules.runSchedule (frameSchedule.take 4) frame).Quiescent ∧
      (rules.runSchedule frameSchedule frame).Quiescent ∧
      (rules.runSchedule frameSchedule frame).overflow = false := by
  rw [fr_run_1, fr_run_2, fr_run_4, fr_run_6, fr_run]
  circuit_decide

assert_standard_axioms frame_table

/-! ### Respawn anchor -/

/-- The reader with a respawn anchor without a charge. -/
def anchor : Level := reader (.respawnAnchor ⟨0⟩)

/-- Glowstone is used on the anchor before game ticks 1, 5, 9 and 13. -/
def anchorSchedule : Schedule :=
  (List.replicate 4 (Schedule.first [.useItem src .up "minecraft:glowstone"] 4)).flatten

checkpoints an := anchorSchedule from anchor

/-- **A respawn anchor gives 3, 7, 11 and 15 for one to four charges** (`charges * 15 / 4`,
rounded down). -/
theorem anchor_table :
    observe anchor = (.respawnAnchor ⟨0⟩, (false, 0), 0) ∧
      observe (rules.runSchedule (anchorSchedule.take 4) anchor) =
        (.respawnAnchor ⟨1⟩, (true, 3), 3) ∧
      observe (rules.runSchedule (anchorSchedule.take 8) anchor) =
        (.respawnAnchor ⟨2⟩, (true, 7), 7) ∧
      observe (rules.runSchedule (anchorSchedule.take 12) anchor) =
        (.respawnAnchor ⟨3⟩, (true, 11), 11) ∧
      observe (rules.runSchedule (anchorSchedule.take 16) anchor) =
        (.respawnAnchor ⟨4⟩, (true, 15), 15) ∧
      (rules.runSchedule anchorSchedule anchor).Quiescent ∧
      (rules.runSchedule anchorSchedule anchor).overflow = false := by
  rw [an_run_4, an_run_8, an_run_12, an_run_16, an_run]
  circuit_decide

assert_standard_axioms anchor_table

/-! ### Copper golem statue -/

/-- A waxed copper golem statue in the given pose. -/
def statueBlock (pose : Pose) : Block :=
  .copperGolemStatue .waxed_copper_golem_statue ⟨pose, .north, false⟩

/-- The reader without a source: the statue is placed by the schedule. -/
def statue : Level := reader .AIR

/-- A standing statue is placed before game tick 1; a stick is used on it before game ticks 5,
9, 13 and 17. -/
def statueSchedule : Schedule :=
  .first [.set src (statueBlock .standing)] 4 ++
    (List.replicate 4 (Schedule.first [.useItem src .up "minecraft:stick"] 4)).flatten

checkpoints st := statueSchedule from statue

/-- **A copper golem statue gives 1, 2, 3, 4 by its pose**, and four turns bring it back to
the first. -/
theorem statue_table :
    observe (rules.runSchedule (statueSchedule.take 4) statue) =
        (statueBlock .standing, (true, 1), 1) ∧
      observe (rules.runSchedule (statueSchedule.take 8) statue) =
        (statueBlock .sitting, (true, 2), 2) ∧
      observe (rules.runSchedule (statueSchedule.take 12) statue) =
        (statueBlock .running, (true, 3), 3) ∧
      observe (rules.runSchedule (statueSchedule.take 16) statue) =
        (statueBlock .star, (true, 4), 4) ∧
      observe (rules.runSchedule (statueSchedule.take 20) statue) =
        (statueBlock .standing, (true, 1), 1) ∧
      (rules.runSchedule statueSchedule statue).Quiescent ∧
      (rules.runSchedule statueSchedule statue).overflow = false := by
  rw [st_run_4, st_run_8, st_run_12, st_run_16, st_run_20, st_run]
  circuit_decide

assert_standard_axioms statue_table

/-- Before the schedules, each of the four levels is at rest. -/
theorem circuit_quiescent :
    cauldron.Quiescent ∧ frame.Quiescent ∧ anchor.Quiescent ∧ statue.Quiescent := by
  circuit_decide

assert_standard_axioms circuit_quiescent

end Redstone.Theorems.Analog.Sources
