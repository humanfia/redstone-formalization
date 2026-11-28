module

public import Redstone.Component.Crafter
public import Redstone.Lemmas.Dropper

/-!
# Lemmas about the crafter

Generic facts about `Redstone.Component.Crafter`, over an arbitrary level, as opposed to the
theorems about concrete circuits in `Redstone/Theorems/Dropper`.

* **The signal a comparator reads** (`CrafterBlockEntity.getRedstoneSignal`) is the number of
  slots that are filled, plus the number of empty slots that are disabled
  (`redstoneSignal_eq`); when every disabled slot is empty, as in the game, it is the number
  of filled slots plus the number of disabled slots (`redstoneSignal_eq_filled_add_disabled`).
  It is at most 9 (`redstoneSignal_le`) and 0 for a new crafter (`redstoneSignal_default`),
  and it is what the block answers a comparator (`analogSignal_crafter`).
* **The `triggered` state machine** (`CrafterBlock.neighborChanged`). A crafter looks at the
  signal at its own position only: unlike the dropper it has no quasi-connectivity. A
  neighbour update of a powered crafter that is not `triggered` schedules one tick, due four
  game ticks later, sets `triggered` and records it in the block entity
  (`neighborChanged_rising`); of a `triggered` crafter without power, it clears `triggered`
  and `crafting` (`neighborChanged_falling`); when the two agree it does nothing
  (`neighborChanged_of_agrees`).
* **An empty grid has no recipe** (`getPotentialResults_of_no_ingredient`).

Left out:

* What the tick of a crafter does when a recipe matches, over an arbitrary level: it searches
  the 1185 modelled recipes for the grid and pushes the result through `Container.addItem`.
  For a fixed grid the search is a computation, and it is done by evaluation in
  `Redstone/Theorems/Dropper/Crafter.lean` and `CrafterDisabledSlots.lean`.
* The whole delay over an arbitrary level, as for the dropper.
-/

@[expose] public section

namespace Redstone.Component.Crafter

open Container ItemDrop Dispenser

/-! ### The signal for a comparator -/

/-- The signal is at most 9. -/
theorem redstoneSignal_le (c : BlockEntities.Crafter) : redstoneSignal c ≤ 9 :=
  List.countP_le_length.trans (by simp)

/-- A new crafter, with nothing in it and no slot disabled, gives the signal 0. -/
theorem redstoneSignal_default : redstoneSignal {} = 0 := by decide

/-- In a list, the entries with `p` or `q` are those with `p` and those with `q` but not
`p`. -/
theorem countP_or {α : Type} (p q : α → Bool) (l : List α) :
    l.countP (fun a => p a || q a) = l.countP p + l.countP (fun a => !p a && q a) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.countP_cons, ih]
    cases p a <;> cases q a <;> simp <;> omega

/-- **The signal is the number of filled slots plus the number of empty slots that are
disabled.** -/
theorem redstoneSignal_eq (c : BlockEntities.Crafter) :
    redstoneSignal c =
      (List.range 9).countP (fun i => !(c.items.getItem i).isEmpty) +
        (List.range 9).countP (fun i => (c.items.getItem i).isEmpty && c.isSlotDisabled i) := by
  unfold redstoneSignal
  rw [countP_or]
  simp only [Bool.not_not]

/-- **The signal is the number of filled slots plus the number of disabled slots**, when every
disabled slot is empty. The game only lets an empty slot be disabled
(`CrafterBlockEntity.slotCanBeDisabled`). -/
theorem redstoneSignal_eq_filled_add_disabled (c : BlockEntities.Crafter)
    (h : ∀ i, c.isSlotDisabled i = true → (c.items.getItem i).isEmpty = true) :
    redstoneSignal c =
      (List.range 9).countP (fun i => !(c.items.getItem i).isEmpty) +
        (List.range 9).countP c.isSlotDisabled := by
  rw [redstoneSignal_eq]
  congr 1
  apply List.countP_congr
  intro i _
  have hi := h i
  cases hd : c.isSlotDisabled i
  · simp
  · simp [hi hd]

/-- What a comparator reads from a crafter is the signal of its block entity. -/
theorem analogSignal_crafter (s : Blocks.Crafter) (l : Level) (p : Pos) (d : Direction)
    (be : BlockEntities.Crafter) (h : l.blockEntities p = some (.crafter be)) :
    (behaviour (.crafter s)).analogSignal l p d = redstoneSignal be := by
  change (match l.blockEntities p with
    | some (.crafter be) => redstoneSignal be
    | _ => 0) = _
  rw [h]

/-! ### The `triggered` state machine -/

/-- `CrafterBlock.neighborChanged` as a function of the signal at the crafter's position. -/
theorem neighborChanged_eq (s : Blocks.Crafter) (p : Pos) (b : BlockId) (moved : Bool) (env : Env)
    (l : Level) :
    (behaviour (.crafter s)).neighborChanged p b moved env l =
      (if (l.hasNeighborSignalAt env p && !s.triggered) = true then do
        Level.scheduleTick p .crafter 4
        discard <| Level.setBlock p (.crafter { s with triggered := true }) 2
        setBlockEntityTriggered p true
      else if (!l.hasNeighborSignalAt env p && s.triggered) = true then do
        discard <| Level.setBlock p (.crafter { s with triggered := false, crafting := false }) 2
        setBlockEntityTriggered p false
      else pure ()) env l := rfl

/-- **The rising edge.** A crafter that is not `triggered` gets a neighbour update while its
position receives a signal, and has no tick of its own waiting. It schedules one tick, due four
game ticks later, then sets `triggered` on the block (with flag 2: no neighbour is updated) and
in the block entity. -/
theorem neighborChanged_rising (s : Blocks.Crafter) (p : Pos) (b : BlockId) (moved : Bool)
    (env : Env) (l : Level) (hs : s.triggered = false)
    (hsig : l.hasNeighborSignalAt env p = true)
    (hsched : l.hasScheduledTick p .crafter = false) :
    (behaviour (.crafter s)).neighborChanged p b moved env l =
      (do
        discard <| Level.setBlock p (.crafter { s with triggered := true }) 2
        setBlockEntityTriggered p true : M Unit) env
        ({ l with
          subTickCount := l.subTickCount + 1
          ticks := l.ticks ++ [⟨p, .crafter, l.gameTime + 4, .normal, l.subTickCount⟩] } :
          Level) := by
  rw [neighborChanged_eq, hsig, hs]
  change (Level.scheduleTick p .crafter 4 >>= fun _ => do
    discard <| Level.setBlock p (.crafter { s with triggered := true }) 2
    setBlockEntityTriggered p true) env l = _
  rw [bind_apply, scheduleTick_apply p .crafter 4 env l hsched]

/-- **The falling edge.** A crafter that is `triggered` gets a neighbour update while its
position receives no signal. It clears `triggered` and `crafting` on the block and `triggered`
in the block entity, and schedules nothing. -/
theorem neighborChanged_falling (s : Blocks.Crafter) (p : Pos) (b : BlockId) (moved : Bool)
    (env : Env) (l : Level) (hs : s.triggered = true)
    (hsig : l.hasNeighborSignalAt env p = false) :
    (behaviour (.crafter s)).neighborChanged p b moved env l =
      (do
        discard <| Level.setBlock p (.crafter { s with triggered := false, crafting := false }) 2
        setBlockEntityTriggered p false : M Unit) env l := by
  rw [neighborChanged_eq, hsig, hs]
  rfl

/-- **No edge, no reaction.** A neighbour update of a crafter whose `triggered` property agrees
with the signal at its position leaves the level as it is. -/
theorem neighborChanged_of_agrees (s : Blocks.Crafter) (p : Pos) (b : BlockId) (moved : Bool)
    (env : Env) (l : Level) (hsig : l.hasNeighborSignalAt env p = s.triggered) :
    (behaviour (.crafter s)).neighborChanged p b moved env l = ((), l) := by
  rw [neighborChanged_eq, hsig]
  cases s.triggered <;> rfl

/-- Recording `triggered` in the block entity of a crafter changes that field of the block
entity and nothing else in the level. -/
theorem setBlockEntityTriggered_apply (p : Pos) (triggered : Bool) (env : Env) (l : Level)
    (be : BlockEntities.Crafter) (h : l.blockEntities p = some (.crafter be)) :
    setBlockEntityTriggered p triggered env l =
      ((), { l with
        blockEntities :=
          l.blockEntities.insert p (.crafter { be with triggered := if triggered then 1 else 0 })
        }) := by
  unfold setBlockEntityTriggered
  rw [bind_apply, getBlockEntity_apply p env l _ h]
  rfl

/-- The scheduled tick of a crafter is `dispenseFrom`. -/
theorem tick_crafter (s : Blocks.Crafter) (p : Pos) :
    (behaviour (.crafter s)).tick p = dispenseFrom s p := rfl

/-! ### Recipes -/

/-- **An empty grid has no recipe.** -/
theorem getPotentialResults_of_no_ingredient (input : CraftingInput)
    (h : input.ingredientCount = 0) : getPotentialResults input = .none := by
  simp [getPotentialResults, h]

end Redstone.Component.Crafter
