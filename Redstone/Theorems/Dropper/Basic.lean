import Redstone.Proof.Circuit

/-!
# Droppers, dispensers and crafters as containers

The circuits of this directory are about the three blocks that are triggered by a rising edge
of redstone power and act four game ticks later (`DispenserBlock`, `DropperBlock`,
`CrafterBlock`), as far as they move items between containers. One circuit per file:

* `IntoContainer`: lever, dropper, chest. One item per rising edge, four game ticks after it;
  `triggered` follows the lever; an empty dropper does nothing; at rest for ever in between.
* `FullTarget`: lever, dropper, and a dropper that is almost full. The last item that fits is
  moved; then nothing moves and nothing is lost.
* `QuasiConnectivity`: a lever beside the air above a dropper. The dropper is powered through
  the position above it, but reacts only when it gets a block update, both for the rising and
  for the falling edge.
* `Elevator`: a button on the middle one of three droppers facing up, a chest on top. Every
  press triggers the three droppers together; two items reach the chest in three presses;
  items are conserved.
* `SeveralSlots`: a dropper with three kinds of item. The order in which the slots are chosen,
  for the generator of the model's empty level.
* `HopperLoop`: a dropper facing up into a hopper facing down, a lever on the dropper. The item
  goes up four game ticks after the lever is switched on, is held by the locked hopper, and
  comes back when the lever is switched off.
* `Crafter`: lever, crafter with nine stacks of redstone, chest. One block of redstone per
  rising edge after four game ticks; how long `crafting` shows; the comparator signal.
* `CrafterDisabledSlots`: a crafter with two planks and seven disabled slots. Sticks are
  crafted; the signal counts the disabled slots; an empty grid crafts nothing.
* `DispenserTrigger`: a lever and an empty dispenser. The `triggered` state machine of the
  dispenser.

The generic lemmas about the blocks are in `Redstone/Lemmas/Dropper.lean` and
`Redstone/Lemmas/Crafter.lean`.

This file has what the circuits share: the observation of what a container holds.

## Not yet proved

* **A dropper or crafter that faces air, and a dispenser that holds an item.** The item leaves
  as an item entity. Its motion is computed in `Float`, which the kernel does not evaluate, and
  a level with an entity has no checkpoint (`Redstone/Proof/README.md`). Every dropper and
  crafter here faces a container, and the dispenser is empty.
* **The dispenser's behaviours for particular items** (water bucket, arrows, TNT, flint and
  steel, minecarts, ...). The model does not have them (`Redstone.Component.Dispenser` sets
  `Level.overflow`), and they act on fluids and entities.
* **The slot a dropper picks, for an arbitrary state of the level's generator.** `SeveralSlots`
  is the instance for the generator of `Level.empty` (seed 0); in the game the state of the
  generator is not known. What holds for every state is the case of one filled slot
  (`Redstone.Component.Dispenser.getRandomSlot_single` in `Redstone/Lemmas/Dropper.lean`), and
  that is the case of the other circuits.
* **A dropper elevator of four droppers with its own clock** (the observer or torch chain of
  the community designs). `Elevator` has three droppers, which one button on the middle
  dropper triggers together without any dust; a taller column needs a wire or a torch tower
  beside it, and the pulses then reach the droppers at different game ticks.
* **Slots of a crafter toggled by a player.** The model changes `disabled` through the menu
  only, which no input of a schedule reaches; `CrafterDisabledSlots` starts with the slots
  disabled.
* **A barrel as the container.** The circuits use a chest. The block state of a barrel has the
  property `open`, and the literal of a level is read back from what `Repr` prints
  (`Redstone.Proof.parseRepr`), where a field of that name is not a term: `checkpoints` fails
  on any level with a barrel (and `blk%` on a barrel). The model handles barrels; it is the
  proof foundation that cannot write them down yet.
* **Comparator readouts** of the dropper and hopper loop and of a crafter (a comparator
  behind the block) belong to the unit of the hopper circuits. The crafter's own signal, which
  is what a comparator reads, is stated here as `analogSignal`.
-/

namespace Redstone.Theorems.Dropper

/-- The slots of the container at `p` (dropper, dispenser, crafter, hopper or chest);
no slots if there is none. -/
def slotsAt (l : Level) (p : Pos) : Inventory :=
  match l.blockEntities p with
  | some (.dropper d) => d.items
  | some (.dispenser d) => d.items
  | some (.crafter d) => d.items
  | some (.hopper d) => d.items
  | some (.chest d) => d.items
  | _ => []

/-- What the container at `p` holds: for every slot that is not empty, in order, the number of
the slot, the name of the item and the count. -/
def contents (l : Level) (p : Pos) : List (ℕ × String × ℕ) :=
  (slotsAt l p).zipIdx.filterMap fun (s, i) => if s.isEmpty then none else some (i, s.id, s.count)

/-- The number of items in the containers at the positions `ps`, all kinds together. -/
def itemTotal (l : Level) (ps : List Pos) : ℕ :=
  (ps.map fun p => ((slotsAt l p).map (·.count)).sum).sum

/-- The game time does not matter for what a container holds. -/
@[simp]
theorem contents_advance (l : Level) (n : ℕ) : contents (l.advance n) = contents l := rfl

/-- The game time does not matter for the number of items. -/
@[simp]
theorem itemTotal_advance (l : Level) (n : ℕ) : itemTotal (l.advance n) = itemTotal l := rfl

/-- The signal a comparator reads from the block at `p` (`getAnalogOutputSignal`), under the
rules of the game. -/
def analog (l : Level) (p : Pos) : ℕ := (rules.block (l.blockAt p)).analogSignal l p .north

end Redstone.Theorems.Dropper
