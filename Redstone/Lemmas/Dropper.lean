module

public import Redstone.Component.Dispenser

/-!
# Lemmas about the dropper and the dispenser

Generic facts about `Redstone.Component.Dispenser`, over an arbitrary level, as opposed to the
theorems about concrete circuits in `Redstone/Theorems/Dropper`.

* **The `triggered` state machine** (`DispenserBlock.neighborChanged`), for both blocks. The
  block counts as powered when its own position or the position above receives a signal
  (quasi-connectivity). A neighbour update of a block that is powered and not `triggered`
  schedules one tick, due four game ticks later, and then sets `triggered`
  (`common_neighborChanged_rising`, `dropper_neighborChanged_rising`,
  `dispenser_neighborChanged_rising`); of a block that is `triggered` and not powered, it
  clears `triggered` and schedules nothing (`..._falling`); when the two agree, it does nothing
  (`common_neighborChanged_of_agrees`). Nothing happens without a neighbour update: these are
  statements about `neighborChanged`.
* **The slot that is picked** (`DispenserBlockEntity.getRandomSlot`). The loop over the slots
  is the pure function `pickSlot` of the state of the level's random number generator
  (`getRandomSlot_eq`). With no filled slot it answers `none` and draws nothing
  (`getRandomSlot_of_isEmpty`). **With exactly one filled slot it picks that slot whatever the
  state of the generator** (`getRandomSlot_single`): the one draw is `nextInt(1)`, which is 0
  (`JavaRandom.nextInt_one`).
* **An empty dropper**: its tick leaves the level as it is (`dispenseFromDropper_of_isEmpty`).

Left out:

* "`dispenseFromDropper` into a container with room moves exactly one item, and into a full
  one nothing", over an arbitrary level. The transfer goes through `Container.addItem`, which
  finds the container at a position (single and double chests, the faces of a furnace, the
  side a hopper may be filled from), merges stacks, sets a hopper's cooldown and updates the
  comparators around; a statement over an arbitrary level needs a specification of all of
  that, which belongs to the lemmas about containers. Both facts are proved for concrete
  levels in `Redstone/Theorems/Dropper/IntoContainer.lean` and `FullTarget.lean`.
* The whole delay ("the item moves four game ticks after the edge") over an arbitrary level:
  between the scheduling and the tick the rest of the level runs. Proved for concrete circuits
  by evaluation.
* The dispenser's tick with an item in it: it makes an item entity or sets `Level.overflow`.
-/

@[expose] public section

namespace Redstone

namespace JavaRandom

/-- `next(31)` is below `2 ^ 31`. -/
theorem next_lt (r : JavaRandom) : (r.next 31).1 < 2 ^ 31 := by
  have h : (r.seed * 0x5DEECE66D + 0xB) &&& mask < 2 ^ 48 :=
    Nat.and_lt_two_pow _ (by norm_num [mask])
  change ((r.seed * 0x5DEECE66D + 0xB) &&& mask) >>> 17 < 2 ^ 31
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_of_lt_mul (lt_of_lt_of_eq h (by norm_num))

/-- **`nextInt(1)` is 0**, whatever the state of the generator. -/
theorem nextInt_one (r : JavaRandom) : (r.nextInt 1).1 = 0 := by
  change (1 * (r.next 31).1) >>> 31 = 0
  rw [one_mul, Nat.shiftRight_eq_div_pow]
  exact Nat.div_eq_of_lt (next_lt r)

end JavaRandom

namespace Component.Dispenser

open Container ItemDrop

/-! ### Running a reaction on a level -/

/-- A reaction followed by another: the second runs on the level the first leaves. -/
theorem bind_apply {α β : Type} (x : M α) (f : α → M β) (env : Env) (l : Level) :
    (x >>= f) env l = f (x env l).1 env (x env l).2 := rfl

/-- A reaction that only returns a value leaves the level as it is. -/
theorem pure_apply {α : Type} (a : α) (env : Env) (l : Level) : (pure a : M α) env l = (a, l) :=
  rfl

/-- `level.getRandom().nextInt(bound)` returns the number drawn and moves the generator on. -/
theorem nextInt_apply (bound : ℕ) (env : Env) (l : Level) :
    nextInt bound env l =
      ((l.random.nextInt bound).1, { l with random := (l.random.nextInt bound).2 }) := rfl

/-- Scheduling a tick of a block that has none waiting adds it to the scheduled ticks, due
`delay` game ticks from now, and moves on the counter that orders the ticks. -/
theorem scheduleTick_apply (p : Pos) (id : BlockId) (delay : ℕ) (env : Env) (l : Level)
    (hsched : l.hasScheduledTick p id = false) :
    (Level.scheduleTick p id delay) env l =
      ((), { l with
        subTickCount := l.subTickCount + 1
        ticks := l.ticks ++ [⟨p, id, l.gameTime + delay, .normal, l.subTickCount⟩] }) := by
  have hsched' : Level.hasScheduledTick { l with subTickCount := l.subTickCount + 1 } p id
      = false := hsched
  simp only [Level.scheduleTick, modify, modifyGet, MonadStateOf.modifyGet, monadLift,
    MonadLift.monadLift, StateT.modifyGet, hsched', pure, Bool.false_eq_true, ite_false]

/-- The block entity of a position that has one is read without changing the level. -/
theorem getBlockEntity_apply (p : Pos) (env : Env) (l : Level) (be : BlockEntity)
    (h : l.blockEntities p = some be) : Level.getBlockEntity p env l = (some be, l) := by
  have h' : Level.peekBlockEntity p env l = (some be, l) := by
    change (l.blockEntities p, l) = _
    rw [h]
  unfold Level.getBlockEntity
  rw [bind_apply, h']
  rfl

/-! ### The `triggered` state machine -/

/-- `DispenserBlock.neighborChanged` as a function of the signal at the block's position and at
the position above it. -/
theorem common_neighborChanged (self : Block) (id : BlockId) (triggered : Bool)
    (withTriggered : Bool → Block) (dispenseFrom : Pos → M Unit) (p : Pos) (b : BlockId)
    (moved : Bool) (env : Env) (l : Level) :
    (common self id triggered withTriggered dispenseFrom).neighborChanged p b moved env l =
      (if ((l.hasNeighborSignalAt env p || l.hasNeighborSignalAt env (p.step .up)) &&
          !triggered) = true then do
        Level.scheduleTick p id 4
        discard <| Level.setBlock p (withTriggered true) 2
      else if (!(l.hasNeighborSignalAt env p || l.hasNeighborSignalAt env (p.step .up)) &&
          triggered) = true then
        discard <| Level.setBlock p (withTriggered false) 2
      else pure ()) env l := rfl

/-- **The rising edge.** A dropper or dispenser that is not `triggered` gets a neighbour update
while its own position or the position above it receives a signal, and has no tick of its own
waiting. It schedules one tick, due four game ticks later, and then sets `triggered` (with
flag 2: no neighbour is updated). -/
theorem common_neighborChanged_rising (self : Block) (id : BlockId) (withTriggered : Bool → Block)
    (dispenseFrom : Pos → M Unit) (p : Pos) (b : BlockId) (moved : Bool) (env : Env) (l : Level)
    (hsig : (l.hasNeighborSignalAt env p || l.hasNeighborSignalAt env (p.step .up)) = true)
    (hsched : l.hasScheduledTick p id = false) :
    (common self id false withTriggered dispenseFrom).neighborChanged p b moved env l =
      (discard <| Level.setBlock p (withTriggered true) 2) env
        { l with
          subTickCount := l.subTickCount + 1
          ticks := l.ticks ++ [⟨p, id, l.gameTime + 4, .normal, l.subTickCount⟩] } := by
  rw [common_neighborChanged, hsig]
  change (Level.scheduleTick p id 4 >>= fun _ =>
    discard (Level.setBlock p (withTriggered true) 2)) env l = _
  rw [bind_apply, scheduleTick_apply p id 4 env l hsched]

/-- **The falling edge.** A dropper or dispenser that is `triggered` gets a neighbour update
while neither its own position nor the position above it receives a signal. It clears
`triggered` and schedules nothing. -/
theorem common_neighborChanged_falling (self : Block) (id : BlockId)
    (withTriggered : Bool → Block) (dispenseFrom : Pos → M Unit) (p : Pos) (b : BlockId)
    (moved : Bool) (env : Env) (l : Level)
    (hsig : (l.hasNeighborSignalAt env p || l.hasNeighborSignalAt env (p.step .up)) = false) :
    (common self id true withTriggered dispenseFrom).neighborChanged p b moved env l =
      (discard <| Level.setBlock p (withTriggered false) 2) env l := by
  rw [common_neighborChanged, hsig]
  rfl

/-- **No edge, no reaction.** A neighbour update of a dropper or dispenser whose `triggered`
property agrees with the signal it receives leaves the level as it is. -/
theorem common_neighborChanged_of_agrees (self : Block) (id : BlockId) (triggered : Bool)
    (withTriggered : Bool → Block) (dispenseFrom : Pos → M Unit) (p : Pos) (b : BlockId)
    (moved : Bool) (env : Env) (l : Level)
    (hsig : (l.hasNeighborSignalAt env p || l.hasNeighborSignalAt env (p.step .up)) = triggered) :
    (common self id triggered withTriggered dispenseFrom).neighborChanged p b moved env l =
      ((), l) := by
  rw [common_neighborChanged, hsig]
  cases triggered <;> rfl

/-- The rising edge of a dropper: one tick is scheduled, due four game ticks later, and the
dropper becomes `triggered`. -/
theorem dropper_neighborChanged_rising (facing : Direction) (p : Pos) (b : BlockId) (moved : Bool)
    (env : Env) (l : Level)
    (hsig : (l.hasNeighborSignalAt env p || l.hasNeighborSignalAt env (p.step .up)) = true)
    (hsched : l.hasScheduledTick p .dropper = false) :
    (behaviour (.dropper ⟨facing, false⟩)).neighborChanged p b moved env l =
      (discard <| Level.setBlock p (.dropper ⟨facing, true⟩) 2) env
        { l with
          subTickCount := l.subTickCount + 1
          ticks := l.ticks ++ [⟨p, .dropper, l.gameTime + 4, .normal, l.subTickCount⟩] } :=
  common_neighborChanged_rising (.dropper ⟨facing, false⟩) .dropper (fun t => .dropper ⟨facing, t⟩)
    (dispenseFromDropper · facing) p b moved env l hsig hsched

/-- The falling edge of a dropper: `triggered` is cleared. -/
theorem dropper_neighborChanged_falling (facing : Direction) (p : Pos) (b : BlockId)
    (moved : Bool) (env : Env) (l : Level)
    (hsig : (l.hasNeighborSignalAt env p || l.hasNeighborSignalAt env (p.step .up)) = false) :
    (behaviour (.dropper ⟨facing, true⟩)).neighborChanged p b moved env l =
      (discard <| Level.setBlock p (.dropper ⟨facing, false⟩) 2) env l :=
  common_neighborChanged_falling (.dropper ⟨facing, true⟩) .dropper (fun t => .dropper ⟨facing, t⟩)
    (dispenseFromDropper · facing) p b moved env l hsig

/-- A dropper whose `triggered` property agrees with the signal it receives does not react to a
neighbour update. -/
theorem dropper_neighborChanged_of_agrees (s : Blocks.Dropper) (p : Pos) (b : BlockId)
    (moved : Bool) (env : Env) (l : Level)
    (hsig : (l.hasNeighborSignalAt env p || l.hasNeighborSignalAt env (p.step .up)) =
      s.triggered) :
    (behaviour (.dropper s)).neighborChanged p b moved env l = ((), l) :=
  common_neighborChanged_of_agrees (.dropper s) .dropper s.triggered
    (fun t => .dropper { s with triggered := t }) (dispenseFromDropper · s.facing) p b moved env l
    hsig

/-- The rising edge of a dispenser: one tick is scheduled, due four game ticks later, and the
dispenser becomes `triggered`. -/
theorem dispenser_neighborChanged_rising (facing : Direction) (p : Pos) (b : BlockId)
    (moved : Bool) (env : Env) (l : Level)
    (hsig : (l.hasNeighborSignalAt env p || l.hasNeighborSignalAt env (p.step .up)) = true)
    (hsched : l.hasScheduledTick p .dispenser = false) :
    (behaviour (.dispenser ⟨facing, false⟩)).neighborChanged p b moved env l =
      (discard <| Level.setBlock p (.dispenser ⟨facing, true⟩) 2) env
        { l with
          subTickCount := l.subTickCount + 1
          ticks := l.ticks ++ [⟨p, .dispenser, l.gameTime + 4, .normal, l.subTickCount⟩] } :=
  common_neighborChanged_rising (.dispenser ⟨facing, false⟩) .dispenser
    (fun t => .dispenser ⟨facing, t⟩) (dispenseFromDispenser · facing) p b moved env l hsig hsched

/-- The falling edge of a dispenser: `triggered` is cleared. -/
theorem dispenser_neighborChanged_falling (facing : Direction) (p : Pos) (b : BlockId)
    (moved : Bool) (env : Env) (l : Level)
    (hsig : (l.hasNeighborSignalAt env p || l.hasNeighborSignalAt env (p.step .up)) = false) :
    (behaviour (.dispenser ⟨facing, true⟩)).neighborChanged p b moved env l =
      (discard <| Level.setBlock p (.dispenser ⟨facing, false⟩) 2) env l :=
  common_neighborChanged_falling (.dispenser ⟨facing, true⟩) .dispenser
    (fun t => .dispenser ⟨facing, t⟩) (dispenseFromDispenser · facing) p b moved env l hsig

/-- A dispenser whose `triggered` property agrees with the signal it receives does not react to
a neighbour update. -/
theorem dispenser_neighborChanged_of_agrees (s : Blocks.Dispenser) (p : Pos) (b : BlockId)
    (moved : Bool) (env : Env) (l : Level)
    (hsig : (l.hasNeighborSignalAt env p || l.hasNeighborSignalAt env (p.step .up)) =
      s.triggered) :
    (behaviour (.dispenser s)).neighborChanged p b moved env l = ((), l) :=
  common_neighborChanged_of_agrees (.dispenser s) .dispenser s.triggered
    (fun t => .dispenser { s with triggered := t }) (dispenseFromDispenser · s.facing) p b moved
    env l hsig

/-- The scheduled tick of a dropper is `dispenseFromDropper`, and that of a dispenser
`dispenseFromDispenser`. -/
theorem tick_dropper (s : Blocks.Dropper) (p : Pos) :
    (behaviour (.dropper s)).tick p = dispenseFromDropper p s.facing := rfl

@[inherit_doc tick_dropper]
theorem tick_dispenser (s : Blocks.Dispenser) (p : Pos) :
    (behaviour (.dispenser s)).tick p = dispenseFromDispenser p s.facing := rfl

/-! ### The slot that is picked -/

/-- One round of the loop of `getRandomSlot`, for the stack `x.1` in slot `x.2`: `st` is the
slot chosen so far and the number of the next filled slot, counted from 1. -/
def slotStep : ItemStack × ℕ → Option ℕ × ℕ → M (ForInStep (Option ℕ × ℕ))
  | (stack, i), (slot, odds) =>
    if !stack.isEmpty then do
      if (← nextInt odds) == 0 then pure (.yield (some i, odds + 1))
      else pure (.yield (slot, odds + 1))
    else pure (.yield (slot, odds))

/-- `getRandomSlot` is the loop of `slotStep` over the slots with their numbers. -/
theorem getRandomSlot_eq_forIn (items : Inventory) :
    getRandomSlot items = (do
      let st ← forIn items.zipIdx ((none : Option ℕ), 1) slotStep
      pure st.1) := rfl

/-- The loop of `getRandomSlot` as a function of the state of the random number generator: the
slot chosen and the number of the next filled slot after the slots `xs`, and the generator
after the draws. The `k`-th filled slot replaces the choice when `nextInt(k)` is 0. -/
def pickSlot : List (ItemStack × ℕ) → Option ℕ × ℕ → JavaRandom → (Option ℕ × ℕ) × JavaRandom
  | [], st, r => (st, r)
  | (stack, i) :: xs, (slot, odds), r =>
    if stack.isEmpty then pickSlot xs (slot, odds) r
    else
      pickSlot xs (if (r.nextInt odds).1 == 0 then some i else slot, odds + 1) (r.nextInt odds).2

/-- One round over an empty slot changes nothing. -/
theorem slotStep_of_isEmpty (stack : ItemStack) (i : ℕ) (st : Option ℕ × ℕ) (env : Env)
    (l : Level) (h : stack.isEmpty = true) : slotStep (stack, i) st env l = (.yield st, l) := by
  obtain ⟨slot, odds⟩ := st
  simp only [slotStep, h, Bool.not_true, Bool.false_eq_true, ite_false, pure_apply]

/-- One round over a filled slot draws once. -/
theorem slotStep_of_filled (stack : ItemStack) (i : ℕ) (st : Option ℕ × ℕ) (env : Env)
    (l : Level) (h : stack.isEmpty = false) :
    slotStep (stack, i) st env l =
      (.yield (if (l.random.nextInt st.2).1 == 0 then some i else st.1, st.2 + 1),
        { l with random := (l.random.nextInt st.2).2 }) := by
  obtain ⟨slot, odds⟩ := st
  have hstep : slotStep (stack, i) (slot, odds) env l =
      if stack.isEmpty = true then (.yield (slot, odds), l)
      else
        (if ((l.random.nextInt odds).1 == 0) = true then
          (pure (.yield (some i, odds + 1)) : M (ForInStep (Option ℕ × ℕ)))
        else pure (.yield (slot, odds + 1))) env
          { l with random := (l.random.nextInt odds).2 } := by
    simp only [slotStep]
    cases stack.isEmpty <;> rfl
  rw [hstep, h]
  cases (l.random.nextInt odds).1 == 0 <;> rfl

/-- The loop of `getRandomSlot` changes nothing in the level but the random number generator,
and what it computes is `pickSlot`. -/
theorem forIn_slotStep (xs : List (ItemStack × ℕ)) (st : Option ℕ × ℕ) (env : Env) (l : Level) :
    forIn xs st slotStep env l =
      ((pickSlot xs st l.random).1, { l with random := (pickSlot xs st l.random).2 }) := by
  induction xs generalizing st l with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨stack, i⟩ := x
    obtain ⟨slot, odds⟩ := st
    rw [List.forIn_cons, bind_apply]
    cases h : stack.isEmpty with
    | true =>
      rw [slotStep_of_isEmpty stack i _ env l h]
      simp only [pickSlot, h, ite_true]
      exact ih _ _
    | false =>
      rw [slotStep_of_filled stack i _ env l h]
      simp only [pickSlot, h, Bool.false_eq_true, ite_false]
      exact ih _ _

/-- **`getRandomSlot` as a function of the generator.** It leaves the level as it is but for
the random number generator. -/
theorem getRandomSlot_eq (items : Inventory) (env : Env) (l : Level) :
    getRandomSlot items env l =
      ((pickSlot items.zipIdx (none, 1) l.random).1.1,
        { l with random := (pickSlot items.zipIdx (none, 1) l.random).2 }) := by
  rw [getRandomSlot_eq_forIn, bind_apply, forIn_slotStep]
  rfl

/-- Empty slots are passed over without a draw. -/
theorem pickSlot_zipIdx_of_isEmpty (inv : Inventory) (k : ℕ) (st : Option ℕ × ℕ) (r : JavaRandom)
    (h : ∀ s ∈ inv, s.isEmpty = true) : pickSlot (inv.zipIdx k) st r = (st, r) := by
  induction inv generalizing k with
  | nil => rfl
  | cons s inv ih =>
    obtain ⟨slot, odds⟩ := st
    rw [List.zipIdx_cons]
    simp only [pickSlot, h s List.mem_cons_self, ite_true]
    exact ih _ fun s' hs' => h s' (List.mem_cons_of_mem _ hs')

/-- The loop over two lists of slots, one after the other. -/
theorem pickSlot_append (xs ys : List (ItemStack × ℕ)) (st : Option ℕ × ℕ) (r : JavaRandom) :
    pickSlot (xs ++ ys) st r = pickSlot ys (pickSlot xs st r).1 (pickSlot xs st r).2 := by
  induction xs generalizing st r with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨stack, i⟩ := x
    obtain ⟨slot, odds⟩ := st
    cases h : stack.isEmpty <;> simp only [List.cons_append, pickSlot, h, ite_true,
      Bool.false_eq_true, ite_false] <;> exact ih _ _

/-- **A container without a filled slot**: `getRandomSlot` answers `none`, draws nothing and
leaves the level as it is. -/
theorem getRandomSlot_of_isEmpty (items : Inventory) (env : Env) (l : Level)
    (h : ∀ s ∈ items, s.isEmpty = true) : getRandomSlot items env l = (none, l) := by
  rw [getRandomSlot_eq, pickSlot_zipIdx_of_isEmpty items 0 _ _ h]

/-- **A container with exactly one filled slot**: `getRandomSlot` picks that slot, whatever the
state of the level's random number generator. The slots before (`pre`) and after (`post`) the
stack `s` are empty. The generator is moved on by the one draw, `nextInt(1)`; nothing else in
the level changes. -/
theorem getRandomSlot_single (pre post : Inventory) (s : ItemStack) (env : Env) (l : Level)
    (hpre : ∀ x ∈ pre, x.isEmpty = true) (hs : s.isEmpty = false)
    (hpost : ∀ x ∈ post, x.isEmpty = true) :
    getRandomSlot (pre ++ s :: post) env l =
      (some pre.length, { l with random := (l.random.nextInt 1).2 }) := by
  rw [getRandomSlot_eq, List.zipIdx_append, List.zipIdx_cons, pickSlot_append,
    pickSlot_zipIdx_of_isEmpty pre 0 _ _ hpre]
  simp only [pickSlot, hs, Bool.false_eq_true, ite_false, JavaRandom.nextInt_one, beq_self_eq_true,
    ite_true, pickSlot_zipIdx_of_isEmpty post _ _ _ hpost, Nat.zero_add]

/-! ### An empty dropper -/

/-- **The tick of an empty dropper leaves the level as it is**: no slot is picked, nothing is
drawn, nothing moves. -/
theorem dispenseFromDropper_of_isEmpty (p : Pos) (facing : Direction) (env : Env) (l : Level)
    (be : BlockEntities.Dropper) (hbe : l.blockEntities p = some (.dropper be))
    (h : ∀ s ∈ be.items, s.isEmpty = true) : dispenseFromDropper p facing env l = ((), l) := by
  unfold dispenseFromDropper
  rw [bind_apply, getBlockEntity_apply p env l _ hbe]
  change (getRandomSlot be.items >>= _) env l = _
  rw [bind_apply, getRandomSlot_of_isEmpty be.items env l h]
  rfl

end Component.Dispenser

end Redstone
