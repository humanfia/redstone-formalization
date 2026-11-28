import Redstone.Proof.Circuit
import Redstone.Lemmas.Hopper

/-!
# Hoppers: item transfer without comparators

The theorems of this directory are about hoppers that move items between containers, with no
comparator anywhere. Each file is one layout.

* `ChestPipe.lean`: a chest, a hopper, a chest. One item every 8 game ticks; push before pull;
  the slots of the chest are drained in order; no item is lost.
* `DoubleChest.lean`: a hopper under either half of a double chest. The half of type `right`
  is drained first.
* `Chain.lean`: three hoppers in a row and a dropper. 7 game ticks per hop, 8 between items,
  the same in both orders of ticking.
* `PairOrder.lean`: a hopper on a hopper. The order in which the two are ticked decides
  whether the second item moves in game tick 1 or in game tick 8.
* `Locking.lean`: a hopper pipe and a lever. A powered hopper neither pushes nor pulls, for
  ever; it resumes in the game tick in which the signal goes.
* `FurnaceSlots.lean`: hoppers above, beside and below a furnace. Which slot each face gives
  access to.
* `BrewingStandSlots.lean`: hoppers above and beside a brewing stand. The same.
* `Composter.lean`: a hopper, a composter, a hopper. Seven items fill the composter, and the
  bone meal leaves through the bottom.
* `Bounce.lean`: two hoppers that face each other. One item goes back and forth every 7 game
  ticks; cycle certificate.

`CycleStamps.lean` has the time shift that a cycle certificate of a level with hoppers needs:
`Level.shift` of the foundation leaves the game time a hopper was last ticked at where it
was. The generic lemmas, and the notion of rest for levels with locked hoppers
(`Level.HoppersLocked`), are in `Redstone/Lemmas/Hopper.lean`.

This file has the observations the theorems are stated with.

A level with a hopper is never quiescent in the sense of `Level.Quiescent`: the hopper is
ticked in every game tick and records the game time. The statements here are therefore about
bounded runs, with two exceptions: the locked hopper, which is at rest in the sense of
`Level.HoppersLocked` and stays so for ever, and the cycle certificate of the two hoppers that
face each other.

## Not yet proved

* **For ever, for hoppers that are enabled.** A hopper pipe that has run empty, or two hoppers
  that pass an item back and forth, are stated over a bounded run (and one period). The
  statement for all later times needs the game tick to be known on a level with an arbitrary
  game time; for a locked hopper that is `Level.step_of_hoppersLocked`, for an enabled one the
  tick reads the containers around it and no such lemma is proved.
* **A count for every number of items.** "After `t` game ticks the lower chest holds
  `min k ((t + 7) / 8)` items" is checked for the five items of `ChestPipe.lean`, not as a
  statement for all `k ≤ 64`: each `k` is a run of its own (`8 k` game ticks of kernel
  evaluation), and a proof by induction on `k` needs the lemma of the previous point.
* **Item entities, hopper minecarts, water streams.** A hopper that picks up dropped items, or
  a dropper that throws them, has an entity in the level, and the motion of an entity is
  computed in `Float`, which the kernel cannot evaluate.
* **Hoppers read by comparators** (item sorter, hopper clock with comparators, item counter):
  they belong to the comparator unit.
-/

namespace Redstone.Theorems.Hopper

/-- Redstone dust, the item. -/
def redstone : String := "minecraft:redstone"

/-- An iron ingot. -/
def ironIngot : String := "minecraft:iron_ingot"

/-- A piece of coal. -/
def coal : String := "minecraft:coal"

/-- The non-empty slots of the container at `p`, in order: slot number, item and count. Empty
if there is no container. -/
def slots (l : Level) (p : Pos) : List (ℕ × String × ℕ) :=
  (((l.containerItems p).getD []).zipIdx.filter fun e => !e.1.isEmpty).map fun e =>
    (e.2, e.1.id, e.1.count)

/-- The number of items in the container at `p`; zero if there is no container. -/
def count (l : Level) (p : Pos) : ℕ := (((l.containerItems p).getD []).map (·.count)).sum

/-- The transfer cooldown of the hopper at `p`; zero if there is no hopper. -/
def cooldown (l : Level) (p : Pos) : ℤ :=
  match l.blockEntities p with
  | some (.hopper d) => d.cooldownTime
  | _ => 0

/-- The hopper at `p` is enabled: its block state has `enabled = true`. A hopper that receives
a signal is not. -/
def enabled (l : Level) (p : Pos) : Bool :=
  match l.blockAt p with
  | .hopper s => s.enabled
  | _ => false

/-- In a level whose hoppers are locked the slots of every container stay as they are. -/
theorem slots_steps_of_hoppersLocked {l : Level} (h : l.HoppersLocked) (n : ℕ) (p : Pos) :
    slots (rules.steps n l) p = slots l p := by
  rw [slots, Level.containerItems_steps_of_hoppersLocked h, slots]

/-- In a level whose hoppers are locked the number of items in every container stays as it
is. -/
theorem count_steps_of_hoppersLocked {l : Level} (h : l.HoppersLocked) (n : ℕ) (p : Pos) :
    count (rules.steps n l) p = count l p := by
  rw [count, Level.containerItems_steps_of_hoppersLocked h, count]

/-- In a level whose hoppers are locked no hopper is enabled again. -/
theorem enabled_steps_of_hoppersLocked {l : Level} (h : l.HoppersLocked) (n : ℕ) (p : Pos) :
    enabled (rules.steps n l) p = enabled l p := by
  rw [enabled, Level.blockAt_steps_of_hoppersLocked h, enabled]

end Redstone.Theorems.Hopper
