module

public import Redstone.Block.Entity.Dispenser

/-!
# Block entity `minecraft:crafter`

The data that the model keeps of the block entity `CrafterBlockEntity`: its nine item stacks,
which slots are disabled, the `triggered` value shown in its menu, and the number of game
ticks for which the block still shows `crafting=true`.

Not kept: the custom name and the lock, and loot tables (see `Redstone.Block.Entity.Dispenser`).
-/

@[expose] public section

namespace Redstone.BlockEntities

/-- The data of a `minecraft:crafter` block entity. -/
structure Crafter where
  /-- The nine slots, row by row. -/
  items : Dispenser.Slots := Dispenser.Slots.empty 9
  /-- `craftingTicksRemaining`. -/
  craftingTicksRemaining : ℤ := 0
  /-- `containerData` 0 to 8: for each slot, whether it is disabled. -/
  disabled : List Bool := List.replicate 9 false
  /-- `containerData` 9: 1 while the block is triggered. -/
  triggered : ℤ := 0
  deriving DecidableEq, Repr

instance : Inhabited Crafter := ⟨{}⟩

namespace Crafter

/-- `isSlotDisabled`. -/
def isSlotDisabled (c : Crafter) (slot : ℕ) : Bool := c.disabled.getD slot false

/-- `slotCanBeDisabled`: the slot exists and is empty. -/
def slotCanBeDisabled (c : Crafter) (slot : ℤ) : Bool :=
  0 ≤ slot && slot < 9 && (c.items.getD slot.toNat none).isNone

/-- Reads the data from the block entity's saved NBT (`loadAdditional`). Fields the model does
not keep are ignored. Fails if the block entity has a loot table. -/
def ofNbt? (t : Nbt) : Option Crafter :=
  if (t.get? "LootTable").isSome then none
  else
    let c : Crafter :=
      { items := Dispenser.Slots.ofNbt 9 t
        craftingTicksRemaining := t.intD "crafting_ticks_remaining" 0
        triggered := t.intD "triggered" 0 }
    let slots :=
      match t.get? "disabled_slots" with
      | some (.intArray l) => l
      | _ => []
    some (slots.foldl (init := c) fun c i =>
      if c.slotCanBeDisabled i then { c with disabled := c.disabled.set i.toNat true } else c)

end Crafter

end Redstone.BlockEntities
