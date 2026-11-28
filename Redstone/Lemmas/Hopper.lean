module

public import Redstone.Mechanics.Dispatch
public import Redstone.Lemmas.Tick

/-!
# Lemmas about the hopper

Generic facts about the hopper, over an arbitrary level; the theorems about concrete layouts
are in `Redstone/Theorems/Hopper`.

* **The ticker on cooldown** (`pushItemsTick_of_cooldown`): the block entity tick of a hopper
  whose cooldown is above 1 lowers the cooldown by one, records the game time, and does
  nothing else.
* **A locked hopper is inert** (`tryMoveItems_of_disabled`, `pushItemsTick_of_disabled`): a
  hopper whose block state says `enabled = false` moves no item, whatever is around it. Its
  ticker only counts the cooldown down to zero and records the game time: the slots of the
  hopper and every other block entity are as they were.
* **A hopper on cooldown moves nothing** (`tryMoveItems_of_cooldown`), also when an item entity
  touches it.
* **The lock follows the signal** (`checkPoweredState_of_agrees`, `checkPoweredState_of_differs`):
  a neighbour update changes the block state exactly when `enabled` is not the negation of
  "the hopper receives a signal", and then it sets it to that, with flags 2.
* **Locked hoppers at rest** (`Level.HoppersLocked`, `step_of_hoppersLocked`,
  `steps_of_hoppersLocked`): a level in which nothing is waiting to happen and whose only
  ticking block entities are locked hoppers stays as it is for ever, under the rules of the
  game: a game tick moves the clocks, counts the cooldowns of the hoppers down and writes the
  game time into them, and nothing else (`Level.tickLocked`). The blocks and the slots of
  every container never change (`blockAt_steps_of_hoppersLocked`,
  `containerItems_steps_of_hoppersLocked`). This is the notion of rest for levels with hoppers
  that `Level.Quiescent` cannot give, since a hopper is ticked in every game tick. It is
  decidable (`Level.hoppersLocked`), so a checkpoint of a circuit can be shown to satisfy it
  by evaluation.

## What is left out

* The same notion of rest for hoppers that are enabled but have nothing to do (empty, with
  nothing above; or full, in front of a full container). Their tick reads the containers
  around them (`ejectItems`, `suckInItems`), so the statement needs hypotheses about every one
  of those reads. For concrete layouts it is checked over bounded runs by evaluation.
* "One successful `ejectItems` moves exactly one item and sets the cooldown to 8", and the
  conservation of items over a game tick, over an arbitrary level: both go through
  `Container.addItem`, which loops over the slots of an arbitrary container. They are stated
  and checked for concrete layouts in `Redstone/Theorems/Hopper`.
* The rule for the cooldown of a hopper that receives an item while empty (8, or 7 when it was
  ticked no earlier than the sender): it is inside `Container.tryMoveInItem`; its effect is
  stated for concrete layouts (`Redstone/Theorems/Hopper/Chain.lean`).
-/

@[expose] public section

namespace Redstone.Component.Hopper

open Container

/-! ### Attribute lemmas -/

/-- An empty hopper is not full. -/
theorem inventoryFull_empty : inventoryFull (Inventory.empty 5) = false := by decide

/-- A hopper with an empty slot is not full. -/
theorem inventoryFull_of_mem_empty (items : Inventory) (s : ItemStack) (hs : s ∈ items)
    (he : s.isEmpty = true) : inventoryFull items = false := by
  simp only [inventoryFull, List.all_eq_false]
  exact ⟨s, hs, by simp [he]⟩

/-! ### Single-reaction lemmas -/

/-- What the ticker of a hopper writes when it moves nothing: one game tick less of cooldown,
not below zero, and the game time `time`. -/
def ticked (h : BlockEntities.Hopper) (time : ℕ) : BlockEntities.Hopper :=
  { h with cooldownTime := max (h.cooldownTime - 1) 0, tickedGameTime := time }

/-- The ticker leaves the slots alone when it moves nothing. -/
@[simp]
theorem items_ticked (h : BlockEntities.Hopper) (time : ℕ) : (ticked h time).items = h.items := rfl

/-- The data of the hopper at `p`, when the level has it. -/
theorem getHopper_of_eq (p : Pos) (env : Env) (l : Level) (h : BlockEntities.Hopper)
    (hbe : l.blockEntities p = some (.hopper h)) : getHopper p env l = (some h, l) := by
  simp only [getHopper, Level.getBlockEntity, Level.peekBlockEntity, bind, ReaderT.bind,
    StateT.bind, get, getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift,
    StateT.get, pure, ReaderT.pure, StateT.pure, hbe]

/-- **A hopper on cooldown moves nothing**: `tryMoveItems` leaves the level as it is. -/
theorem tryMoveItems_of_cooldown (s : Blocks.Hopper) (p : Pos) (action : M Bool) (env : Env)
    (l : Level) (h : BlockEntities.Hopper) (hbe : l.blockEntities p = some (.hopper h))
    (hc : 0 < h.cooldownTime) : tryMoveItems s p action env l = ((), l) := by
  have hc' : (decide (h.cooldownTime > 0)) = true := by simpa using hc
  simp only [tryMoveItems, bind, ReaderT.bind, StateT.bind, getHopper_of_eq p env l h hbe, hc',
    Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false, pure, ReaderT.pure,
    StateT.pure]

/-- **A locked hopper moves nothing**: `tryMoveItems` of a hopper whose block state has
`enabled = false` leaves the level as it is, whatever `action` would take in. -/
theorem tryMoveItems_of_disabled (s : Blocks.Hopper) (p : Pos) (action : M Bool) (env : Env)
    (l : Level) (h : BlockEntities.Hopper) (hbe : l.blockEntities p = some (.hopper h))
    (hs : s.enabled = false) : tryMoveItems s p action env l = ((), l) := by
  simp only [tryMoveItems, bind, ReaderT.bind, StateT.bind, getHopper_of_eq p env l h hbe, hs,
    Bool.and_false, Bool.false_eq_true, ite_false, pure, ReaderT.pure, StateT.pure]

/-- **The ticker of a hopper on cooldown only counts down.** If the cooldown is above 1, the
block entity tick lowers it by one and records the game time; nothing else in the level
changes. -/
theorem pushItemsTick_of_cooldown (s : Blocks.Hopper) (p : Pos) (env : Env) (l : Level)
    (h : BlockEntities.Hopper) (hbe : l.blockEntities p = some (.hopper h))
    (hc : 1 < h.cooldownTime) :
    pushItemsTick s p env l =
      ((), { l with
        blockEntities := l.blockEntities.insert p (.hopper (ticked h l.gameTime)) }) := by
  have hc' : h.cooldownTime - 1 > 0 := by omega
  have hmax : max (h.cooldownTime - 1) 0 = h.cooldownTime - 1 := by omega
  simp only [pushItemsTick, bind, ReaderT.bind, StateT.bind, getHopper_of_eq p env l h hbe, get,
    getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get, pure,
    hc', ite_true, Level.setBlockEntity, modify, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, ticked, hmax]

/-- **The ticker of a locked hopper only counts down.** The block entity tick of a hopper whose
block state has `enabled = false` lowers the cooldown by one, not below zero, and records the
game time. The slots of the hopper, the other block entities, the blocks and everything else
in the level are as they were: a locked hopper neither pushes nor pulls. -/
theorem pushItemsTick_of_disabled (s : Blocks.Hopper) (p : Pos) (env : Env) (l : Level)
    (h : BlockEntities.Hopper) (hbe : l.blockEntities p = some (.hopper h))
    (hs : s.enabled = false) :
    pushItemsTick s p env l =
      ((), { l with
        blockEntities := l.blockEntities.insert p (.hopper (ticked h l.gameTime)) }) := by
  by_cases hc : 1 < h.cooldownTime
  · exact pushItemsTick_of_cooldown s p env l h hbe hc
  · have hc' : ¬ (h.cooldownTime - 1 > 0) := by omega
    have hmax : max (h.cooldownTime - 1) 0 = 0 := by omega
    have hbe' : ∀ be : BlockEntity,
        ({ l with blockEntities := l.blockEntities.insert p be } : Level).blockEntities p =
          some be := fun be => by simp [PosMap.insert_apply]
    simp only [pushItemsTick, bind, ReaderT.bind, StateT.bind, getHopper_of_eq p env l h hbe, get,
      getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get, pure,
      hc', ite_false, Level.setBlockEntity, modify, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, ticked, hmax]
    exact tryMoveItems_of_disabled s p (suckInItems p) env _ _ (hbe' _) hs

/-- **The lock agrees with the signal: nothing happens.** A hopper whose `enabled` property is
already the negation of "it receives a signal" ignores a neighbour update. -/
theorem checkPoweredState_of_agrees (s : Blocks.Hopper) (p : Pos) (env : Env) (l : Level)
    (h : l.hasNeighborSignalAt env p = !s.enabled) : checkPoweredState s p env l = ((), l) := by
  simp only [checkPoweredState, Level.hasNeighborSignal, bind, ReaderT.bind, StateT.bind, get,
    getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get, read,
    readThe, MonadReaderOf.read, ReaderT.read, pure, ReaderT.pure, StateT.pure, h,
    Bool.not_not, bne_self_eq_false, Bool.false_eq_true, ite_false]

/-- **The lock follows the signal.** A hopper whose `enabled` property is not the negation of
"it receives a signal" reacts to a neighbour update by flipping the property, with flags 2 (the
clients are told, the neighbours are not): it is locked in the same game tick in which the
signal arrives, and released in the game tick in which it goes. -/
theorem checkPoweredState_of_differs (s : Blocks.Hopper) (p : Pos) (env : Env) (l : Level)
    (h : l.hasNeighborSignalAt env p = s.enabled) :
    checkPoweredState s p env l =
      (discard <| Level.setBlock p (.hopper { s with enabled := !s.enabled }) 2) env l := by
  simp only [checkPoweredState, Level.hasNeighborSignal, bind, ReaderT.bind, StateT.bind, get,
    getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift, StateT.get, read,
    readThe, MonadReaderOf.read, ReaderT.read, pure, ReaderT.pure, StateT.pure, h,
    Bool.not_bne_self, ite_true]

end Redstone.Component.Hopper

/-! ### Locked hoppers at rest -/

namespace Redstone.Level

open Component

/-- The slots of the container whose block entity is at `p`, if there is one. -/
def containerItems (l : Level) (p : Pos) : Option Inventory :=
  (l.blockEntities p).bind Container.items?

/-- The block entity after it was ticked at game time `time`, if it is a hopper that moved
nothing: one game tick less of cooldown and the new time stamp (`Hopper.ticked`). Any other
block entity is as it was. -/
def stampHopper (time : ℕ) : BlockEntity → BlockEntity
  | .hopper h => .hopper (Hopper.ticked h time)
  | be => be

/-- The block entities after the hoppers at the positions `ps` were ticked at game time `time`
without moving anything (`stampHopper`). -/
def stampHoppers (time : ℕ) (m : PosMap BlockEntity) (ps : List Pos) : PosMap BlockEntity :=
  ps.foldl (fun m p =>
    match m p with
    | some be => m.insert p (stampHopper time be)
    | none => m) m

/-- The block entity is a hopper. -/
def isHopperEntity : Option BlockEntity → Bool
  | some (.hopper _) => true
  | _ => false

/-- There is a locked hopper at `p`: the block is a hopper with `enabled = false`, and it has
its block entity. -/
def lockedHopperAt (l : Level) (p : Pos) : Bool :=
  (match l.blockAt p with
    | .hopper s => !s.enabled
    | _ => false) &&
  isHopperEntity (l.blockEntities p)

/-- Nothing in the level is waiting to happen, and its ticking block entities are locked
hoppers. See `HoppersLocked`. -/
def hoppersLocked (l : Level) : Bool :=
  decide (l.ticks = []) && decide (l.ticksToRun = []) && decide (l.fluidTicks = []) &&
  decide (l.fluidTicksToRun = []) && decide (l.blockEvents = []) && l.entities.isEmpty &&
  decide (l.pendingBlockEntityTickers = []) && decide (l.handlingTick = false) &&
  decide (l.tickingBlockEntities = false) && decide (l.randomTickSpeed = 0) &&
  decide (l.updateStack = []) && decide (l.lightWorld = l.world) &&
  l.blockEntityTickers.all l.lockedHopperAt

/-- The level is at rest between two game ticks but for its hoppers, and they are locked: no
scheduled block or fluid tick, no block event, no entity, no pending neighbour update, no
random ticks, the light engine has seen the blocks as they are, and every ticking block entity
is a hopper whose block state has `enabled = false`. This is `Level.Quiescent` with locked
hoppers allowed. -/
def HoppersLocked (l : Level) : Prop := l.hoppersLocked = true

instance (l : Level) : Decidable l.HoppersLocked := inferInstanceAs (Decidable (_ = true))

/-- A game tick of a level whose hoppers are locked (`step_of_hoppersLocked`): the clocks move
on by one, every hopper is ticked without moving anything, and the list of the block entities
ticked in this game tick is filled. -/
def tickLocked (l : Level) : Level :=
  { l with
    gameTime := l.gameTime + 1
    dayTime := if l.advanceTime then l.dayTime + 1 else l.dayTime
    tickedBlockEntities := l.blockEntityTickers.reverse
    blockEntities := stampHoppers (l.gameTime + 1) l.blockEntities l.blockEntityTickers }

theorem stampHoppers_cons (time : ℕ) (m : PosMap BlockEntity) (p : Pos) (ps : List Pos) :
    stampHoppers time m (p :: ps) = stampHoppers time (stampHoppers time m [p]) ps := rfl

theorem stampHoppers_singleton (time : ℕ) (m : PosMap BlockEntity) (p q : Pos) :
    stampHoppers time m [p] q = if q = p then (m q).map (stampHopper time) else m q := by
  simp only [stampHoppers, List.foldl_cons, List.foldl_nil]
  by_cases hq : q = p
  · subst hq
    cases hp : m q with
    | none => simp [hp]
    | some be => simp [PosMap.insert_apply]
  · cases hp : m p with
    | none => simp [hq]
    | some be => simp [hq, PosMap.insert_apply]

theorem items_stampHopper (time : ℕ) (be : BlockEntity) :
    Container.items? (stampHopper time be) = Container.items? be := by
  cases be <;> rfl

theorem isHopperEntity_stampHopper (time : ℕ) (be : Option BlockEntity) :
    isHopperEntity (be.map (stampHopper time)) = isHopperEntity be := by
  cases be with
  | none => rfl
  | some be => cases be <;> rfl

/-- Ticking a hopper without moving anything leaves the slots of every container as they
were. -/
theorem items_stampHoppers (time : ℕ) (m : PosMap BlockEntity) (ps : List Pos) (q : Pos) :
    (stampHoppers time m ps q).bind Container.items? = (m q).bind Container.items? := by
  induction ps generalizing m with
  | nil => rfl
  | cons p ps ih =>
    rw [stampHoppers_cons, ih, stampHoppers_singleton]
    split
    · cases m q with
      | none => rfl
      | some be => exact items_stampHopper time be
    · rfl

/-- Ticking a hopper without moving anything leaves a hopper where there was one, and none
where there was none. -/
theorem isHopperEntity_stampHoppers (time : ℕ) (m : PosMap BlockEntity) (ps : List Pos)
    (q : Pos) : isHopperEntity (stampHoppers time m ps q) = isHopperEntity (m q) := by
  induction ps generalizing m with
  | nil => rfl
  | cons p ps ih =>
    rw [stampHoppers_cons, ih, stampHoppers_singleton]
    split
    · exact isHopperEntity_stampHopper time (m q)
    · rfl

@[simp]
theorem world_tickLocked (l : Level) : l.tickLocked.world = l.world := rfl

@[simp]
theorem blockAt_tickLocked (l : Level) : l.tickLocked.blockAt = l.blockAt := rfl

@[simp]
theorem overflow_tickLocked (l : Level) : l.tickLocked.overflow = l.overflow := rfl

@[simp]
theorem gameTime_tickLocked (l : Level) : l.tickLocked.gameTime = l.gameTime + 1 := rfl

@[simp]
theorem containerItems_tickLocked (l : Level) (p : Pos) :
    l.tickLocked.containerItems p = l.containerItems p :=
  items_stampHoppers _ _ _ p

theorem lockedHopperAt_tickLocked (l : Level) (p : Pos) :
    l.tickLocked.lockedHopperAt p = l.lockedHopperAt p := by
  simp only [lockedHopperAt, blockAt_tickLocked]
  congr 1
  exact isHopperEntity_stampHoppers _ _ _ p

/-- A level whose hoppers are locked is one after the game tick. -/
theorem HoppersLocked.tickLocked {l : Level} (h : l.HoppersLocked) :
    l.tickLocked.HoppersLocked := by
  simp only [HoppersLocked, hoppersLocked, Bool.and_eq_true, decide_eq_true_eq,
    List.isEmpty_iff, List.all_eq_true, and_assoc] at h ⊢
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃⟩ := h
  refine ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, fun p hp => ?_⟩
  rw [lockedHopperAt_tickLocked]
  exact h₁₃ p hp

/-- What `Level.tickBlockEntities` does for one locked hopper. -/
def tickLockedHopper (l : Level) (p : Pos) : Level :=
  { l with
    tickedBlockEntities := p :: l.tickedBlockEntities
    blockEntities := stampHoppers l.gameTime l.blockEntities [p] }

theorem foldl_tickLockedHopper (ps : List Pos) (l : Level) :
    ps.foldl tickLockedHopper l =
      { l with
        tickedBlockEntities := ps.reverse ++ l.tickedBlockEntities
        blockEntities := stampHoppers l.gameTime l.blockEntities ps } := by
  induction ps generalizing l with
  | nil => rfl
  | cons p ps ih =>
    rw [List.foldl_cons, ih, stampHoppers_cons]
    simp [tickLockedHopper]

/-- The ticker that the rules of the game give a hopper is `Hopper.pushItemsTick`. -/
theorem blockEntityTick_hopper (s : Blocks.Hopper) (p : Pos) :
    ((rules.env maxDepth).block (.hopper s)).blockEntityTick p =
      Hopper.pushItemsTick s p (rules.env 511) := rfl

/-- A run of block entity tickers, each of which is a locked hopper, changes the level as
`tickLockedHopper` says. -/
theorem forM_lockedHoppers (f : Pos → M Unit) (env : Env) (ps : List Pos) (l : Level)
    (hf : ∀ p ∈ ps, ∀ l' : Level, l'.lockedHopperAt p = true →
      l'.blockEntityTickers = l.blockEntityTickers → f p env l' = ((), l'.tickLockedHopper p))
    (hl : ∀ p ∈ ps, l.lockedHopperAt p = true) :
    ps.forM f env l = ((), ps.foldl tickLockedHopper l) := by
  induction ps generalizing l with
  | nil => rfl
  | cons p ps ih =>
    have h₁ := hf p List.mem_cons_self l (hl p List.mem_cons_self) rfl
    have h₂ : ∀ q, (l.tickLockedHopper p).lockedHopperAt q = l.lockedHopperAt q := by
      intro q
      simp only [lockedHopperAt]
      congr 1
      exact isHopperEntity_stampHoppers _ _ _ q
    have h₃ : (p :: ps).forM f = (do f p; ps.forM f) := rfl
    rw [h₃, List.foldl_cons]
    simp only [bind, ReaderT.bind, StateT.bind, h₁]
    exact ih (l.tickLockedHopper p)
      (fun q hq l' hl' ht => hf q (List.mem_cons_of_mem _ hq) l' hl' ht)
      (fun q hq => (h₂ q).trans (hl q (List.mem_cons_of_mem _ hq)))

/-- A bind in the monad of reactions, applied to an environment and a level. -/
private theorem bind_apply {α β : Type} (x : M α) (f : α → M β) (env : Env) (l : Level) :
    (x >>= f) env l = f (x env l).1 env (x env l).2 := rfl

/-- `modify` in the monad of reactions, applied to an environment and a level. -/
private theorem modify_apply (g : Level → Level) (env : Env) (l : Level) :
    (modify g : M Unit) env l = ((), g l) := rfl

/-- `get` in the monad of reactions, applied to an environment and a level. -/
private theorem get_apply (env : Env) (l : Level) : (get : M Level) env l = (l, l) := rfl

/-- `Level.getBlock` applied to an environment and a level. -/
private theorem getBlock_apply (p : Pos) (env : Env) (l : Level) :
    getBlock p env l = (l.blockAt p, l) := rfl

/-- `Level.behaviour` applied to an environment and a level. -/
private theorem behaviour_apply (b : Block) (env : Env) (l : Level) :
    behaviour b env l = (env.block b, l) := rfl

/-- A closed reaction, lifted into the monad of reactions, applied to an environment and a
level. -/
private theorem liftM_apply {α : Type} (x : StateM Level α) (env : Env) (l : Level) :
    (liftM x : M α) env l = x l := rfl

/-- In a level without entities the entity phase leaves the level as it is. -/
private theorem tickEntities_of_empty (env : Env) (l : Level) (h : l.entities = []) :
    tickEntities env l = ((), l) := by
  obtain ⟨⟩ := l
  simp only at h
  subst h
  rfl

/-- The block entity phase of a level whose tickers are all locked hoppers: every hopper is
ticked without moving anything. -/
theorem tickBlockEntities_of_lockedHoppers (l : Level) (hp : l.pendingBlockEntityTickers = [])
    (ht : l.tickingBlockEntities = false)
    (hl : ∀ p ∈ l.blockEntityTickers, l.lockedHopperAt p = true) :
    tickBlockEntities (rules.env maxDepth) l =
      ((), { l with
        tickedBlockEntities := l.blockEntityTickers.reverse ++ l.tickedBlockEntities
        blockEntities := stampHoppers l.gameTime l.blockEntities l.blockEntityTickers }) := by
  rw [tickBlockEntities, bind_apply, modify_apply, bind_apply, get_apply]
  dsimp only
  rw [hp, List.append_nil, bind_apply, forM_lockedHoppers, foldl_tickLockedHopper, modify_apply]
  · cases l
    simp only at hp ht
    subst hp ht
    rfl
  · intro p hp l' hl' ht'
    have hc : l'.blockEntityTickers.contains p = true := by
      rw [ht']
      simpa using hp
    simp only [lockedHopperAt, Bool.and_eq_true] at hl'
    obtain ⟨hb, he⟩ := hl'
    split at hb
    · next s hblock =>
      have hs : s.enabled = false := by simpa using hb
      unfold isHopperEntity at he
      split at he
      · next h hbe =>
        have hbe' : ({ l' with tickedBlockEntities := p :: l'.tickedBlockEntities } :
            Level).blockEntities p = some (.hopper h) := hbe
        have hblock' : ({ l' with tickedBlockEntities := p :: l'.tickedBlockEntities } :
            Level).blockAt p = .hopper s := hblock
        have hcond : (l'.blockEntityTickers.contains p && (l'.blockEntities p).isSome) = true := by
          rw [hc, hbe]
          rfl
        have hstamp : stampHoppers l'.gameTime l'.blockEntities [p] =
            l'.blockEntities.insert p (.hopper (Hopper.ticked h l'.gameTime)) := by
          simp only [stampHoppers, List.foldl_cons, List.foldl_nil, hbe, stampHopper]
        rw [bind_apply, get_apply]
        dsimp only
        rw [hcond]
        simp only [↓reduceIte]
        rw [bind_apply, modify_apply, bind_apply, getBlock_apply, bind_apply, behaviour_apply]
        dsimp only
        rw [liftM_apply, hblock', blockEntityTick_hopper,
          Hopper.pushItemsTick_of_disabled s p _ _ h hbe' hs, tickLockedHopper, hstamp]
      · exact absurd he (by simp)
    · exact absurd hb (by simp)
  · exact hl

/-- **A game tick of a level whose hoppers are locked** moves the clocks and ticks the hoppers,
which move nothing: the level after it is `tickLocked`. -/
theorem tick_of_hoppersLocked {l : Level} (h : l.HoppersLocked) :
    Level.tick (rules.env maxDepth) l = ((), l.tickLocked) := by
  simp only [HoppersLocked, hoppersLocked, Bool.and_eq_true, decide_eq_true_eq,
    List.isEmpty_iff, List.all_eq_true, and_assoc] at h
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃⟩ := h
  have key := tickBlockEntities_of_lockedHoppers
    { l with
      gameTime := l.gameTime + 1
      handlingTick := false
      dayTime := if l.advanceTime then l.dayTime + 1 else l.dayTime
      lightWorld := l.world
      tickedBlockEntities := [] } h₇ h₉ h₁₃
  cases l
  simp only at h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ key
  subst h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂
  simp only [List.append_nil] at key
  have e₁ : ∀ L : Level, L.ticks = [] → L.ticksToRun = [] →
      runScheduledTicks (rules.env maxDepth) L = ((), L) :=
    fun L a b => runScheduledTicks_of_empty _ L a b
  have e₂ : ∀ L : Level, L.fluidTicks = [] → L.fluidTicksToRun = [] →
      runFluidTicks (rules.env maxDepth) L = ((), L) :=
    fun L a b => runFluidTicks_of_empty _ L a b
  have e₃ : ∀ L : Level, L.randomTickSpeed = 0 → tickChunks (rules.env maxDepth) L = ((), L) :=
    fun L a => tickChunks_of_speed_zero _ L a
  have e₄ : ∀ L : Level, L.blockEvents = [] → runBlockEvents (rules.env maxDepth) L = ((), L) :=
    fun L a => runBlockEvents_of_empty _ L a
  have e₅ : ∀ L : Level, L.entities = [] → tickEntities (rules.env maxDepth) L = ((), L) :=
    fun L a => tickEntities_of_empty _ L a
  rw [Level.tick, bind_apply, modify_apply, bind_apply, e₁ _ rfl rfl, bind_apply, e₂ _ rfl rfl,
    bind_apply, e₃ _ rfl, bind_apply, e₄ _ rfl, bind_apply, modify_apply, bind_apply, e₅ _ rfl]
  exact key

/-- **A level whose hoppers are locked stays as it is over a game tick**, under the rules of
the game, up to its clocks and the time stamps and cooldowns of the hoppers. -/
theorem step_of_hoppersLocked {l : Level} (h : l.HoppersLocked) : rules.step l = l.tickLocked := by
  rw [Rules.step, Rules.run, ReaderT.run, StateT.run, tick_of_hoppersLocked h]

/-- **A level whose hoppers are locked stays so for ever**: after any number of game ticks it
is the level with `tickLocked` applied as many times. -/
theorem steps_of_hoppersLocked {l : Level} (h : l.HoppersLocked) (n : ℕ) :
    rules.steps n l = tickLocked^[n] l ∧ (rules.steps n l).HoppersLocked := by
  induction n generalizing l with
  | zero =>
    have h₀ : rules.steps 0 l = l := rfl
    rw [h₀]
    exact ⟨rfl, h⟩
  | succ n ih =>
    have h' := ih h.tickLocked
    rw [← step_of_hoppersLocked h] at h'
    rw [Rules.steps, Function.iterate_succ_apply, Function.iterate_succ_apply,
      ← step_of_hoppersLocked h]
    exact h'

/-- The blocks of a level whose hoppers are locked never change. -/
theorem world_steps_of_hoppersLocked {l : Level} (h : l.HoppersLocked) (n : ℕ) :
    (rules.steps n l).world = l.world := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [Rules.steps, Function.iterate_succ_apply, step_of_hoppersLocked h]
    exact (ih h.tickLocked).trans (world_tickLocked l)

/-- The block at a position of a level whose hoppers are locked never changes. -/
theorem blockAt_steps_of_hoppersLocked {l : Level} (h : l.HoppersLocked) (n : ℕ) (p : Pos) :
    (rules.steps n l).blockAt p = l.blockAt p := by
  rw [Level.blockAt, world_steps_of_hoppersLocked h]
  rfl

/-- **Locked hoppers hold their items for ever**: in a level whose hoppers are locked, the
slots of every container are the same after any number of game ticks. -/
theorem containerItems_steps_of_hoppersLocked {l : Level} (h : l.HoppersLocked) (n : ℕ)
    (p : Pos) : (rules.steps n l).containerItems p = l.containerItems p := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [Rules.steps, Function.iterate_succ_apply, step_of_hoppersLocked h]
    exact (ih h.tickLocked).trans (containerItems_tickLocked l p)

/-- A level whose hoppers are locked never reaches a bound of the model. -/
theorem overflow_steps_of_hoppersLocked {l : Level} (h : l.HoppersLocked) (n : ℕ) :
    (rules.steps n l).overflow = l.overflow := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [Rules.steps, Function.iterate_succ_apply, step_of_hoppersLocked h]
    exact (ih h.tickLocked).trans (overflow_tickLocked l)

end Redstone.Level
