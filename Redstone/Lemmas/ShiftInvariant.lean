import Redstone.Proof.Quiescent
import Redstone.Proof.Axioms

/-!
# A game tick commutes with the time shift

A clock never rests, so what `Redstone/Proof` can check about it is a *cycle certificate*
(`Rules.Cycle`): after one period the level is itself, moved on in time (`Level.shift`). That
the clock then repeats for ever needs one more fact (`Rules.periodic_of_shiftInvariant`): a
game tick does the same thing to a level and to the level moved on in time. This file proves
that fact for a class of levels.

**The class** (`ShiftInvariant.Calm`): every block is air, stone, a block of redstone, a
repeater or a redstone torch (on the floor or on a wall); and the level has no entity, no
ticking block entity, no scheduled fluid tick and no random ticks. `ShiftInvariant.calm` is
the decidable form, for a level between two game ticks (`Calm.of_calm`); a checkpoint is
shown to be calm by `Calm.of_calm (by circuit_decide)`.

**The theorem** (`ShiftInvariant.step_shift`): for a calm level `l` and any `dt` and `dc`,
`rules.step (l.shift dt dc) = (rules.step l).shift dt dc`, and `rules.step l` is calm again.
With a cycle certificate this gives periodicity for ever (`steps_cycle`,
`blockAt_steps_cycle`, `overflow_steps_cycle`): the blocks after `n` game ticks are the blocks
after `n % period` game ticks, for every `n`. `Redstone/Theorems/Clock/RepeaterRing.lean` and
`Redstone/Theorems/Clock/TorchRepeater.lean` use it.

## How it is proved

What the shift changes is the game time, the due time and the order of every scheduled tick,
the counter the order is drawn from, and the times on the torches' burn-out list. The model
reads these in few places: the collection of the due ticks (`ScheduledTickOf.dueInOrder`,
which compares due times with the game time and orders with each other),
`Level.scheduleTick`, and the burn-out list of the torch. Nothing else looks at them. The
proof makes that precise, reaction by reaction.

* `Inv Q x` says that the state transformer `x` commutes with the shift on calm levels, keeps
  them calm, and returns the same result on both sides, which satisfies `Q`. `InvM` is the
  same for a reaction, in every environment whose behaviours of the allowed blocks are
  themselves good (`EnvOK`). `Rel` and `RelM` are the two-sided forms, needed where a
  reaction first reads the level (`InvM.get_bind`).
* These predicates are closed under `bind`, `pure`, `if`, `forM` and the rest of what `do`
  blocks are made of, and the tactic `inv` applies those rules together with the lemmas
  already proved for the parts. Each definition of `Redstone/Mechanics/Update`, `Power` and
  `Tick` that a game tick of a calm level can reach gets a lemma (`setBlock_inv`,
  `runUpdatesLoop_inv`, `runScheduledTicks_inv`, ...), and so do the reactions of the torch,
  of `DiodeBlock` and of the repeater.
* The order of the due ticks is invariant because every comparison in it is
  (`ScheduledTickOf.dueInOrder_shift`).
* The environment of the rules is good at every nesting depth (`envOK_rules`), by induction
  on the depth.

The definitions the lemmas are about are made irreducible, locally, once their lemma is
proved, so that the tactic fails fast on a lemma that does not fit.

## What is left out

* **Redstone dust, the comparator, the lamp and every other block.** Adding a block means
  proving `BehOK` for its behaviour, as `behOK_torch` and `behOK_repeater` do, and extending
  `allowed`. Dust does not read the clocks, so nothing is in the way but the size of its
  code. Blocks that do read them (the daylight detector, the sculk sensor, the hopper) do
  not commute with the shift as it is defined.
* Levels with entities or ticking block entities.
* Inputs: the theorem is about `Rules.step`, a game tick without input.
-/

namespace Redstone

namespace ShiftInvariant

theorem ite_pos {α : Sort _} {c : Prop} [Decidable c] {t e : α} (h : c) : ite c t e = t := by
  simp [h]

theorem ite_neg {α : Sort _} {c : Prop} [Decidable c] {t e : α} (h : ¬c) : ite c t e = e := by
  simp [h]

end ShiftInvariant

open ShiftInvariant (ite_pos ite_neg)

/-! ### The shift and the fields it leaves alone -/

namespace Level

variable (l : Level) (dt dc : ℕ)

@[simp] theorem entities_shift : (l.shift dt dc).entities = l.entities := rfl
@[simp] theorem updateStack_shift : (l.shift dt dc).updateStack = l.updateStack := rfl
@[simp] theorem updatesAdded_shift : (l.shift dt dc).updatesAdded = l.updatesAdded := rfl
@[simp] theorem blockEvents_shift : (l.shift dt dc).blockEvents = l.blockEvents := rfl
@[simp] theorem blockDrops_shift : (l.shift dt dc).blockDrops = l.blockDrops := rfl
@[simp] theorem supportAttrs_shift : (l.shift dt dc).supportAttrs = l.supportAttrs := rfl
@[simp] theorem gameTime_shift : (l.shift dt dc).gameTime = l.gameTime + dt := rfl
@[simp] theorem ticks_shift : (l.shift dt dc).ticks = l.ticks.map (·.shift dt dc) := rfl
@[simp] theorem ticksToRun_shift :
    (l.shift dt dc).ticksToRun = l.ticksToRun.map (·.shift dt dc) := rfl
@[simp] theorem recentTorchToggles_shift :
    (l.shift dt dc).recentTorchToggles = l.recentTorchToggles.map fun e => (e.1, e.2 + dt) := rfl

@[simp] theorem willTickThisTick_shift (p : Pos) (b : BlockId) :
    (l.shift dt dc).willTickThisTick p b = l.willTickThisTick p b := by
  simp [willTickThisTick, List.any_map, Function.comp_def, ScheduledTickOf.shift]

@[simp] theorem hasScheduledTick_shift (p : Pos) (b : BlockId) :
    (l.shift dt dc).hasScheduledTick p b = l.hasScheduledTick p b := by
  simp [hasScheduledTick, List.any_map, Function.comp_def, ScheduledTickOf.shift]

end Level

/-! ### The order of the due ticks -/

namespace ScheduledTickOf

variable {α : Type} (dt dc : ℕ)

theorem shift_injective : Function.Injective (shift dt dc : ScheduledTickOf α → _) := by
  intro a b h
  cases a
  cases b
  simp only [shift, mk.injEq, Nat.add_right_cancel_iff] at h
  simp only [mk.injEq]
  exact h

@[simp] theorem intraLE_shift (a b : ScheduledTickOf α) :
    (a.shift dt dc).intraLE (b.shift dt dc) = a.intraLE b := by
  change (decide (a.priority.value < b.priority.value) ||
    (a.priority.value == b.priority.value && decide (a.order + dc ≤ b.order + dc))) = _
  simp only [Nat.add_le_add_iff_right]
  rfl

@[simp] theorem drainLE_shift (a b : ScheduledTickOf α) :
    (a.shift dt dc).drainLE (b.shift dt dc) = a.drainLE b := by
  have h : (a.trigger + dt == b.trigger + dt) = (a.trigger == b.trigger) := by
    rw [Bool.eq_iff_iff]
    simp
  change (decide (a.trigger + dt < b.trigger + dt) ||
    (a.trigger + dt == b.trigger + dt && (a.shift dt dc).intraLE (b.shift dt dc))) = _
  simp only [h, intraLE_shift, Nat.add_lt_add_iff_right]
  rfl

@[simp] theorem chunk_shift (t : ScheduledTickOf α) : (t.shift dt dc).chunk = t.chunk := rfl

theorem insertSorted_shift (t : ScheduledTickOf α) (q : List (ScheduledTickOf α)) :
    insertSorted (t.shift dt dc) (q.map (shift dt dc)) = (insertSorted t q).map (shift dt dc) := by
  induction q with
  | nil => rfl
  | cons u us ih =>
    simp only [List.map_cons, insertSorted, drainLE_shift]
    split
    · rfl
    · simp [ih]

/-- The shift on the queue of a chunk. -/
def shiftQueue (c : (ℤ × ℤ) × List (ScheduledTickOf α)) : (ℤ × ℤ) × List (ScheduledTickOf α) :=
  (c.1, c.2.map (shift dt dc))

theorem addToQueues_shift (t : ScheduledTickOf α) (qs : List ((ℤ × ℤ) × List (ScheduledTickOf α))) :
    addToQueues (t.shift dt dc) (qs.map (shiftQueue dt dc)) =
      (addToQueues t qs).map (shiftQueue dt dc) := by
  induction qs with
  | nil => rfl
  | cons c qs ih =>
    obtain ⟨c, q⟩ := c
    by_cases h : c = t.chunk
    · have e1 : addToQueues (t.shift dt dc) (List.map (shiftQueue dt dc) ((c, q) :: qs)) =
          (c, insertSorted (t.shift dt dc) (q.map (shift dt dc))) ::
            qs.map (shiftQueue dt dc) := by
        change (if c = t.chunk then _ else _) = _
        rw [ite_pos h]
      have e2 : addToQueues t ((c, q) :: qs) = (c, insertSorted t q) :: qs := by
        change (if c = t.chunk then _ else _) = _
        rw [ite_pos h]
      rw [e1, e2, insertSorted_shift]
      rfl
    · have e1 : addToQueues (t.shift dt dc) (List.map (shiftQueue dt dc) ((c, q) :: qs)) =
          (c, q.map (shift dt dc)) ::
            addToQueues (t.shift dt dc) (qs.map (shiftQueue dt dc)) := by
        change (if c = t.chunk then _ else _) = _
        rw [ite_neg h]
      have e2 : addToQueues t ((c, q) :: qs) = (c, q) :: addToQueues t qs := by
        change (if c = t.chunk then _ else _) = _
        rw [ite_neg h]
      rw [e1, e2, ih]
      rfl

theorem foldl_addToQueues_shift (ts : List (ScheduledTickOf α))
    (qs : List ((ℤ × ℤ) × List (ScheduledTickOf α))) :
    (ts.map (shift dt dc)).foldl (fun qs t => addToQueues t qs) (qs.map (shiftQueue dt dc)) =
      (ts.foldl (fun qs t => addToQueues t qs) qs).map (shiftQueue dt dc) := by
  induction ts generalizing qs with
  | nil => rfl
  | cons t ts ih => simp only [List.map_cons, List.foldl_cons, addToQueues_shift, ih]

theorem pickQueue_shift (qs : List (List (ScheduledTickOf α))) :
    pickQueue (qs.map (List.map (shift dt dc))) =
      (pickQueue qs).map fun r => (r.1.map (shift dt dc), r.2.map (List.map (shift dt dc))) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    cases q with
    | nil => simpa [pickQueue] using ih
    | cons t ts =>
      simp only [List.map_cons, pickQueue, ih]
      cases pickQueue qs with
      | none => rfl
      | some r =>
        obtain ⟨r, rest⟩ := r
        cases r with
        | nil => rfl
        | cons u us =>
          simp only [Option.map_some, List.map_cons, intraLE_shift]
          split <;> rfl

theorem takeUpTo_shift (bound : Option (ScheduledTickOf α)) (ts : List (ScheduledTickOf α)) :
    takeUpTo (bound.map (shift dt dc)) (ts.map (shift dt dc)) =
      ((takeUpTo bound ts).1.map (shift dt dc), (takeUpTo bound ts).2.map (shift dt dc)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have hb : (bound.map (shift dt dc)).all (t.shift dt dc).intraLE = bound.all t.intraLE := by
      cases bound <;> simp
    simp only [List.map_cons, takeUpTo, hb, ih]
    split <;> rfl

theorem mergeQueues_succ (fuel : ℕ) (qs : List (List (ScheduledTickOf α))) :
    mergeQueues (fuel + 1) qs =
      match pickQueue qs with
      | none => []
      | some ([], _) => []
      | some (t :: ts, rest) =>
        t :: (takeUpTo ((pickQueue rest).bind fun x => x.1.head?) ts).1 ++
          mergeQueues fuel
            ((takeUpTo ((pickQueue rest).bind fun x => x.1.head?) ts).2 :: rest) := by
  rw [mergeQueues]
  cases pickQueue qs with
  | none => rfl
  | some r =>
    obtain ⟨r, rest⟩ := r
    cases r <;> rfl

theorem mergeQueues_shift (fuel : ℕ) (qs : List (List (ScheduledTickOf α))) :
    mergeQueues fuel (qs.map (List.map (shift dt dc))) =
      (mergeQueues fuel qs).map (shift dt dc) := by
  induction fuel generalizing qs with
  | zero => rfl
  | succ fuel ih =>
    rw [mergeQueues_succ, mergeQueues_succ, pickQueue_shift]
    cases pickQueue qs with
    | none => rfl
    | some r =>
      obtain ⟨r, rest⟩ := r
      cases r with
      | nil => rfl
      | cons t ts =>
        have hb : (pickQueue (rest.map (List.map (shift dt dc)))).bind (fun x => x.1.head?) =
            ((pickQueue rest).bind fun x => x.1.head?).map (shift dt dc) := by
          rw [pickQueue_shift]
          cases pickQueue rest with
          | none => rfl
          | some r => obtain ⟨r, rest⟩ := r; cases r <;> rfl
        simp only [Option.map_some, List.map_cons]
        rw [hb, takeUpTo_shift]
        simp only [List.map_append, List.map_cons, ← ih]

theorem dueInOrder_shift (now : ℕ) (ts : List (ScheduledTickOf α)) :
    dueInOrder (now + dt) (ts.map (shift dt dc)) = (dueInOrder now ts).map (shift dt dc) := by
  have hf : (ts.map (shift dt dc)).filter (fun t => decide (t.trigger ≤ now + dt)) =
      (ts.filter fun t => decide (t.trigger ≤ now)).map (shift dt dc) := by
    rw [List.filter_map]
    congr 2
    funext t
    simp [shift]
  simp only [dueInOrder, hf, List.length_map]
  have h := foldl_addToQueues_shift dt dc (ts.filter fun t => decide (t.trigger ≤ now)) []
  simp only [List.map_nil] at h
  rw [h, List.map_map]
  have hq : (fun x : (ℤ × ℤ) × List (ScheduledTickOf α) => x.2) ∘ shiftQueue dt dc =
      List.map (shift dt dc) ∘ fun x => x.2 := rfl
  rw [hq, ← List.map_map, mergeQueues_shift]

theorem contains_shift (ts : List (ScheduledTickOf α)) [DecidableEq α] (t : ScheduledTickOf α) :
    (ts.map (shift dt dc)).contains (t.shift dt dc) = ts.contains t := by
  have := List.mem_map_of_injective (shift_injective (α := α) dt dc) (a := t) (l := ts)
  rw [Bool.eq_iff_iff]
  simpa using this

end ScheduledTickOf

/-! ### The levels the theorem is about -/

namespace ShiftInvariant

/-- The blocks of the levels for which the commutation is proved: air, stone, the block of
redstone, the repeater and the redstone torch on the floor or on a wall. -/
def allowed : Block → Bool
  | .plain .air | .plain .stone | .plain .redstone_block => true
  | .repeater _ | .redstoneTorch _ | .redstoneWallTorch _ => true
  | _ => false

theorem allowed_cases {b : Block} (h : allowed b = true) :
    b = .plain .air ∨ b = .plain .stone ∨ b = .plain .redstone_block ∨ (∃ s, b = .repeater s) ∨
      (∃ s, b = .redstoneTorch s) ∨ ∃ s, b = .redstoneWallTorch s := by
  unfold allowed at h
  split at h <;> simp_all

theorem hasBlockEntity_of_allowed {b : Block} (h : allowed b = true) :
    b.hasBlockEntity = false := by
  obtain rfl | rfl | rfl | ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩ := allowed_cases h <;>
    first
    | rfl
    | (obtain ⟨_ | _⟩ := s <;> rfl)
    | (obtain ⟨_ | _ | _ | _, _ | _⟩ := s <;> rfl)

theorem allowed_fluidBlock {b : Block} (h : allowed b = true) : allowed b.fluidBlock = true := by
  obtain rfl | rfl | rfl | ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩ := allowed_cases h <;> rfl

/-- A neighbour update that only carries allowed block states. -/
@[reducible] def UpdOK : NeighborUpdate → Prop
  | .shape _ neighborState _ _ _ _ => allowed neighborState = true
  | .full state _ _ _ => allowed state = true
  | _ => True

/-- The levels for which the commutation is proved: every block is allowed, and the level has
no entity, no ticking block entity, no scheduled fluid tick and no random ticks. -/
def Calm (l : Level) : Prop :=
  (∀ p, allowed (l.blockAt p) = true) ∧ l.entities = [] ∧ l.blockEntityTickers = [] ∧
    l.pendingBlockEntityTickers = [] ∧ l.fluidTicks = [] ∧ l.fluidTicksToRun = [] ∧
    l.randomTickSpeed = 0 ∧ (∀ u ∈ l.updateStack, UpdOK u) ∧ ∀ u ∈ l.updatesAdded, UpdOK u

theorem updOK_nil : ∀ u ∈ ([] : List NeighborUpdate), UpdOK u := fun _ h => nomatch h

/-- What a state transformer does to a level, as a pair. -/
def run {α : Type} (x : StateM Level α) (l : Level) : α × Level := x l

/-- The postcondition that holds of everything. -/
abbrev T {α : Type} : α → Prop := fun _ => True

section Framework

variable (dt dc : ℕ)

/-- `x` on a calm level and `x'` on the shifted level: the results are related by `S`, the
level after `x'` is the level after `x`, shifted, and the level after `x` is calm. -/
def Rel {α : Type} (S : α → α → Prop) (x x' : StateM Level α) : Prop :=
  ∀ l, Calm l → S (run x l).1 (run x' (l.shift dt dc)).1 ∧
    (run x' (l.shift dt dc)).2 = (run x l).2.shift dt dc ∧ Calm (run x l).2

/-- `x` commutes with the shift on calm levels, keeps them calm, gives the same result on the
level and on the shifted level, and the result satisfies `Q`. -/
def Inv {α : Type} (Q : α → Prop) (x : StateM Level α) : Prop :=
  Rel dt dc (fun a a' => a = a' ∧ Q a) x x

/-- The reactions of a closed behaviour that a game tick of a calm level can reach commute
with the shift, and its signals do not depend on the clocks. -/
structure HooksOK (B : BehaviourOf (StateM Level)) : Prop where
  signal : ∀ l p d, B.signal (l.shift dt dc) p d = B.signal l p d
  directSignal : ∀ l p d, B.directSignal (l.shift dt dc) p d = B.directSignal l p d
  neighborChanged : ∀ p b m, Inv dt dc T (B.neighborChanged p b m)
  onPlace : ∀ p o m, Inv dt dc T (B.onPlace p o m)
  affectNeighborsAfterRemoval : ∀ p m, Inv dt dc T (B.affectNeighborsAfterRemoval p m)
  updateShape : ∀ p d q s, allowed s = true →
    Inv dt dc (fun b => allowed b = true) (B.updateShape p d q s)
  updateIndirectNeighbourShapes : ∀ p f n, Inv dt dc T (B.updateIndirectNeighbourShapes p f n)
  tick : ∀ p, Inv dt dc T (B.tick p)
  triggerEvent : ∀ p a b, Inv dt dc T (B.triggerEvent p a b)

/-- The environment gives every allowed block a behaviour whose reactions commute with the
shift, and its game events do too. -/
def EnvOK (env : Env) : Prop :=
  (∀ b, allowed b = true → HooksOK dt dc (env.block b)) ∧
    ∀ n p c, Inv dt dc T (env.gameEvent n p c)

/-- `Rel` for reactions, in every good environment. -/
def RelM {α : Type} (S : α → α → Prop) (x x' : M α) : Prop :=
  ∀ env, EnvOK dt dc env → Rel dt dc S (x.run env) (x'.run env)

/-- `Inv` for reactions, in every good environment. -/
def InvM {α : Type} (Q : α → Prop) (x : M α) : Prop :=
  RelM dt dc (fun a a' => a = a' ∧ Q a) x x

end Framework

section Combinators

variable {dt dc : ℕ} {α β : Type}

theorem Rel.bind {S : α → α → Prop} {S' : β → β → Prop} {x x' : StateM Level α}
    {f f' : α → StateM Level β} (hx : Rel dt dc S x x')
    (hf : ∀ a a', S a a' → Rel dt dc S' (f a) (f' a')) : Rel dt dc S' (x >>= f) (x' >>= f') := by
  intro l hl
  obtain ⟨h1, h2, h3⟩ := hx l hl
  have e : ∀ (y : StateM Level α) (g : α → StateM Level β) s,
      run (y >>= g) s = run (g (run y s).1) (run y s).2 := fun _ _ _ => rfl
  rw [e, e, h2]
  exact hf _ _ h1 _ h3

theorem RelM.bind {S : α → α → Prop} {S' : β → β → Prop} {x x' : M α} {f f' : α → M β}
    (hx : RelM dt dc S x x') (hf : ∀ a a', S a a' → RelM dt dc S' (f a) (f' a')) :
    RelM dt dc S' (x >>= f) (x' >>= f') :=
  fun env henv => Rel.bind (hx env henv) fun a a' h => hf a a' h env henv

theorem InvM.bind {Q : α → Prop} {R : β → Prop} {x : M α} {f : α → M β}
    (hx : InvM dt dc Q x) (hf : ∀ a, Q a → InvM dt dc R (f a)) : InvM dt dc R (x >>= f) :=
  RelM.bind hx (by rintro a _ ⟨rfl, ha⟩; exact hf a ha)

theorem InvM.pure {Q : α → Prop} {a : α} (h : Q a) : InvM dt dc Q (pure a : M α) :=
  fun _ _ _ hl => ⟨⟨rfl, h⟩, rfl, hl⟩

theorem InvM.mono {Q R : α → Prop} {x : M α} (h : ∀ a, Q a → R a) (hx : InvM dt dc Q x) :
    InvM dt dc R x :=
  fun env henv l hl => ⟨⟨(hx env henv l hl).1.1, h _ (hx env henv l hl).1.2⟩,
    (hx env henv l hl).2⟩

theorem InvM.discard {Q : α → Prop} {x : M α} (hx : InvM dt dc Q x) :
    InvM dt dc T (discard x) :=
  fun env henv l hl => ⟨⟨rfl, trivial⟩, (hx env henv l hl).2.1, (hx env henv l hl).2.2⟩

/-- A reaction that begins by reading the level. -/
theorem InvM.get_bind {R : β → Prop} {f : Level → M β}
    (h : ∀ l, Calm l → RelM dt dc (fun a a' => a = a' ∧ R a) (f l) (f (l.shift dt dc))) :
    InvM dt dc R (get >>= f) :=
  fun env henv l hl => h l hl env henv l hl

theorem InvM.modify {f : Level → Level}
    (h : ∀ l, Calm l → f (l.shift dt dc) = (f l).shift dt dc ∧ Calm (f l)) :
    InvM dt dc T (modify f : M Unit) :=
  fun _ _ l hl => ⟨⟨rfl, trivial⟩, (h l hl).1, (h l hl).2⟩

theorem InvM.modifyGet {Q : α → Prop} {f : Level → α × Level}
    (h : ∀ l, Calm l → (f l).1 = (f (l.shift dt dc)).1 ∧
      (f (l.shift dt dc)).2 = (f l).2.shift dt dc ∧ Calm (f l).2 ∧ Q (f l).1) :
    InvM dt dc Q (modifyGet f : M α) :=
  fun _ _ l hl => ⟨⟨(h l hl).1, (h l hl).2.2.2⟩, (h l hl).2.1, (h l hl).2.2.1⟩

theorem RelM.set {s s' : Level} (h : s' = s.shift dt dc) (hs : Calm s) :
    RelM dt dc (fun a a' => a = a' ∧ T a) (set s : M PUnit) (set s') :=
  fun _ _ _ _ => ⟨⟨rfl, trivial⟩, h, hs⟩

theorem InvM.forM {l : List α} {f : α → M PUnit} (h : ∀ a ∈ l, InvM dt dc T (f a)) :
    InvM dt dc T (l.forM f) := by
  induction l with
  | nil => exact InvM.pure trivial
  | cons a l ih =>
    change InvM dt dc T (f a >>= fun _ => l.forM f)
    exact InvM.bind (h a (List.mem_cons_self ..)) fun _ _ =>
      ih fun b hb => h b (List.mem_cons_of_mem _ hb)

end Combinators


section Lift

variable {dt dc : ℕ} {α : Type}

/-- A closed reaction, called from a reaction. -/
theorem InvM.lift {Q : α → Prop} {x : StateM Level α} (h : Inv dt dc Q x) :
    InvM dt dc Q (monadLift x : M α) :=
  fun _ _ => h

/-- A reaction that begins by reading the level, when what follows reads nothing that the
shift changes. -/
theorem InvM.get_bind' {β : Type} {R : β → Prop} {f : Level → M β}
    (h : ∀ l, Calm l → f (l.shift dt dc) = f l ∧ InvM dt dc R (f l)) :
    InvM dt dc R (get >>= f) :=
  InvM.get_bind fun l hl => by rw [(h l hl).1]; exact (h l hl).2

theorem InvM.ite {Q : α → Prop} {c : Prop} [Decidable c] {x y : M α}
    (hx : c → InvM dt dc Q x) (hy : ¬c → InvM dt dc Q y) :
    InvM dt dc Q (if c then x else y) := by
  by_cases hc : c
  · rw [ite_pos hc]
    exact hx hc
  · rw [ite_neg hc]
    exact hy hc

variable {B : BehaviourOf (StateM Level)} (h : HooksOK dt dc B)

include h

theorem lift_neighborChanged {p : Pos} {b : BlockId} {m : Bool} :
    InvM dt dc T (liftM (B.neighborChanged p b m) : M Unit) :=
  InvM.lift (h.neighborChanged p b m)

theorem lift_onPlace {p : Pos} {o : Block} {m : Bool} :
    InvM dt dc T (liftM (B.onPlace p o m) : M Unit) :=
  InvM.lift (h.onPlace p o m)

theorem lift_affectNeighborsAfterRemoval {p : Pos} {m : Bool} :
    InvM dt dc T (liftM (B.affectNeighborsAfterRemoval p m) : M Unit) :=
  InvM.lift (h.affectNeighborsAfterRemoval p m)

theorem lift_updateShape {p q : Pos} {d : Direction} {s : Block} (hs : allowed s = true) :
    InvM dt dc (fun b => allowed b = true) (liftM (B.updateShape p d q s) : M Block) :=
  InvM.lift (h.updateShape p d q s hs)

theorem lift_updateIndirectNeighbourShapes {p : Pos} {f n : ℕ} :
    InvM dt dc T (liftM (B.updateIndirectNeighbourShapes p f n) : M Unit) :=
  InvM.lift (h.updateIndirectNeighbourShapes p f n)

theorem lift_tick {p : Pos} : InvM dt dc T (liftM (B.tick p) : M Unit) :=
  InvM.lift (h.tick p)

theorem lift_triggerEvent {p : Pos} {a b : ℤ} :
    InvM dt dc T (liftM (B.triggerEvent p a b) : M Bool) :=
  InvM.lift (h.triggerEvent p a b)

end Lift

/-- Proves that a reaction commutes with the shift from the same fact about its parts: the
lemmas given in brackets, the hypotheses, and the reactions of allowed blocks. -/
syntax "inv" (" [" term,* "]")? : tactic

macro_rules
  | `(tactic| inv) => `(tactic| inv [])
  | `(tactic| inv [$ls,*]) => do
    let alts ← ls.getElems.mapM fun l => `(tacticSeq| with_reducible exact $l)
    let alts' ← ls.getElems.mapM fun l =>
      `(tacticSeq| with_reducible exact InvM.mono (fun _ _ => trivial) $l)
    `(tactic| repeat' first
      | with_reducible assumption
      | with_reducible exact trivial
      | ((with_reducible apply InvM.pure); first | exact trivial | exact rfl | assumption)
      $[| $alts]*
      | with_reducible apply InvM.discard
      | (with_reducible apply InvM.forM; intro _ _)
      | (with_reducible apply InvM.bind; rotate_left; intro _ _; rotate_right)
      | (with_reducible apply InvM.ite <;> intro _)
      | with_reducible exact lift_neighborChanged (by assumption)
      | with_reducible exact lift_onPlace (by assumption)
      | with_reducible exact lift_affectNeighborsAfterRemoval (by assumption)
      | with_reducible exact lift_updateShape (by assumption) (by assumption)
      | with_reducible exact lift_updateIndirectNeighbourShapes (by assumption)
      | with_reducible exact lift_tick (by assumption)
      | with_reducible exact lift_triggerEvent (by assumption)
      $[| $alts']*
      | split)

/-! ### Changing blocks -/

section Mechanics

open Level

variable {dt dc : ℕ}

theorem getBlock_inv (p : Pos) : InvM dt dc (fun b => allowed b = true) (getBlock p) :=
  fun _ _ _ hl => ⟨⟨rfl, hl.1 p⟩, rfl, hl⟩

attribute [local irreducible] Level.getBlock

theorem behaviour_inv {b : Block} (hb : allowed b = true) :
    InvM dt dc (HooksOK dt dc) (behaviour b) :=
  fun _ henv _ hl => ⟨⟨rfl, henv.1 b hb⟩, rfl, hl⟩

attribute [local irreducible] Level.behaviour

theorem setOverflow_inv : InvM dt dc T setOverflow :=
  InvM.modify fun _ hl => ⟨rfl, hl⟩

attribute [local irreducible] Level.setOverflow

theorem peekBlockEntity_inv (p : Pos) : InvM dt dc T (peekBlockEntity p) :=
  fun _ _ _ hl => ⟨⟨rfl, trivial⟩, rfl, hl⟩

attribute [local irreducible] Level.peekBlockEntity

theorem scheduleTick_inv (p : Pos) (block : BlockId) (delay : ℕ) (priority : TickPriority) :
    InvM dt dc T (scheduleTick p block delay priority) := by
  refine InvM.modify fun l hl => ⟨?_, ?_⟩
  · have hs : hasScheduledTick { l.shift dt dc with
        subTickCount := (l.shift dt dc).subTickCount + 1 } p block =
        hasScheduledTick { l with subTickCount := l.subTickCount + 1 } p block :=
      hasScheduledTick_shift l dt dc p block
    simp only [hs]
    cases l
    split
    · simp only [Level.shift, Level.mk.injEq, true_and, and_true]
      omega
    · simp [Level.shift, ScheduledTickOf.shift]
      omega
  · dsimp only
    split <;> exact hl

attribute [local irreducible] Level.scheduleTick

theorem gameEvent_inv (event : String) (p : Pos) (context : GameEventContext) :
    InvM dt dc T (gameEvent event p context) :=
  fun _ henv => henv.2 event p context

attribute [local irreducible] Level.gameEvent

theorem getDrops_inv (state : Block) (p : Pos) (be : Option BlockEntity) :
    InvM dt dc T (getDrops state p be) := by
  unfold getDrops
  split
  · exact InvM.modifyGet fun _ hl => ⟨rfl, rfl, hl, trivial⟩
  · split
    · exact InvM.pure trivial
    · inv [setOverflow_inv]

attribute [local irreducible] Level.getDrops

theorem dropResources_inv (state : Block) (p : Pos) (be : Option BlockEntity) :
    InvM dt dc T (dropResources state p be) := by
  unfold dropResources
  have hm : ∀ n, InvM dt dc T (modify fun l : Level =>
      { l with random := (·.nextDouble53.2)^[n] l.random } : M Unit) :=
    fun n => InvM.modify fun _ hl => ⟨rfl, hl⟩
  refine InvM.get_bind' fun l hl => ⟨by simp only [Level.blockDrops_shift]; rfl, ?_⟩
  inv [setOverflow_inv, getDrops_inv state p be, hm _]

attribute [local irreducible] Level.dropResources

theorem enqueueUpdate_inv {u : NeighborUpdate} (hu : UpdOK u) :
    InvM dt dc T (enqueueUpdate u) := by
  refine InvM.modifyGet fun l hl => ?_
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hl
  have hc : (l.shift dt dc).updateCount = l.updateCount := rfl
  dsimp only
  rw [hc]
  by_cases c1 : l.updateCount ≥ maxChainedNeighborUpdates
  · rw [ite_pos c1, ite_pos c1]
    exact ⟨rfl, rfl, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, trivial⟩
  · rw [ite_neg c1, ite_neg c1]
    by_cases c2 : (l.updateCount == 0) = true
    · rw [ite_pos c2, ite_pos c2]
      refine ⟨rfl, rfl, ⟨h1, h2, h3, h4, h5, h6, h7, ?_, h9⟩, trivial⟩
      intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact hu
      · exact h8 v hv
    · rw [ite_neg c2, ite_neg c2]
      refine ⟨rfl, rfl, ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩, trivial⟩
      intro v hv
      rcases List.mem_append.1 hv with hv | hv
      · exact h9 v hv
      · rw [List.mem_singleton.1 hv]
        exact hu

attribute [local irreducible] Level.enqueueUpdate

/-- The result of `setBlockInChunk`, if there is one, is an allowed block. -/
@[reducible] def OptOK (o : Option Block) : Prop :=
  match o with
  | some b => allowed b = true
  | none => True

/-- The update with which `runNext` continues, if there is one, only carries allowed blocks. -/
@[reducible] def OptUpdOK (o : Option NeighborUpdate) : Prop :=
  match o with
  | some u => UpdOK u
  | none => True

theorem addAndRun_inv {kick : M Unit} (hk : InvM dt dc T kick) {u : NeighborUpdate} (hu : UpdOK u) :
    InvM dt dc T (Core.addAndRun kick u) := by
  unfold Core.addAndRun
  inv [enqueueUpdate_inv hu]

attribute [local irreducible] Level.Core.addAndRun

theorem core_updateNeighborsAtExceptFromFacing_inv {kick : M Unit} (hk : InvM dt dc T kick)
    (p : Pos) (block : BlockId)
    (skip : Option Direction) :
    InvM dt dc T (Core.updateNeighborsAtExceptFromFacing kick p block skip) :=
  addAndRun_inv hk trivial

theorem core_updateNeighborsAt_inv {kick : M Unit} (hk : InvM dt dc T kick)
    (p : Pos) (block : BlockId) :
    InvM dt dc T (Core.updateNeighborsAt kick p block) :=
  addAndRun_inv hk trivial

theorem core_neighborChanged_inv {kick : M Unit} (hk : InvM dt dc T kick)
    (p : Pos) (block : BlockId) :
    InvM dt dc T (Core.neighborChanged kick p block) :=
  addAndRun_inv hk trivial

theorem core_neighborChangedFor_inv {kick : M Unit} (hk : InvM dt dc T kick)
    {state : Block} (hs : allowed state = true) (p : Pos)
    (block : BlockId) (moved : Bool) :
    InvM dt dc T (Core.neighborChangedFor kick state p block moved) :=
  addAndRun_inv hk hs

theorem core_neighborShapeChanged_inv {kick : M Unit} (hk : InvM dt dc T kick)
    (dir : Direction) (p q : Pos) {neighborState : Block}
    (hs : allowed neighborState = true) (flags limit : ℕ) :
    InvM dt dc T (Core.neighborShapeChanged kick dir p q neighborState flags limit) :=
  addAndRun_inv hk hs

attribute [local irreducible] Level.Core.updateNeighborsAtExceptFromFacing
  Level.Core.updateNeighborsAt Level.Core.neighborChanged Level.Core.neighborChangedFor
  Level.Core.neighborShapeChanged

theorem core_updateNeighbourShapes_inv {kick : M Unit} (hk : InvM dt dc T kick)
    {state : Block} (hs : allowed state = true) (p : Pos)
    (flags limit : ℕ) : InvM dt dc T (Core.updateNeighbourShapes kick state p flags limit) :=
  InvM.forM fun _ _ => core_neighborShapeChanged_inv hk _ _ _ hs _ _

attribute [local irreducible] Level.Core.updateNeighbourShapes

theorem core_updateNeighbourForOutputSignal_inv {kick : M Unit} (hk : InvM dt dc T kick)
    (p : Pos) (block : BlockId) :
    InvM dt dc T (Core.updateNeighbourForOutputSignal kick p block) := by
  unfold Core.updateNeighbourForOutputSignal
  refine InvM.forM fun d _ => ?_
  inv [getBlock_inv _, core_neighborChangedFor_inv hk (by assumption) _ _ _]

attribute [local irreducible] Level.Core.updateNeighbourForOutputSignal

theorem core_setBlockInChunk_inv (p : Pos) {state : Block} (hs : allowed state = true)
    (flags : ℕ) : InvM dt dc OptOK (Core.setBlockInChunk p state flags) := by
  unfold Core.setBlockInChunk
  dsimp only
  have hm : InvM dt dc T (modify (·.setBlockRaw p state) : M Unit) := by
    refine InvM.modify fun l hl => ⟨rfl, ?_⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hl
    refine ⟨fun q => ?_, h2, h3, h4, h5, h6, h7, h8, h9⟩
    change allowed ((l.world.set p state).blockAt q) = true
    rw [World.blockAt_set]
    split
    · exact hs
    · exact h1 q
  have hold : ∀ {old : Block} {c : Bool} {d : Bool}, allowed old = true →
      ¬((c && old.hasBlockEntity && d) = true) := by
    intro old c d h
    simp [hasBlockEntity_of_allowed h]
  have hnew : ∀ {c : Bool}, ¬((state.hasBlockEntity && c) = true) := by
    intro c
    simp [hasBlockEntity_of_allowed hs]
  repeat' first
    | with_reducible assumption
    | exact absurd (by assumption) (hold (by assumption))
    | exact absurd (by assumption) hnew
    | (with_reducible apply InvM.pure; first | exact trivial | assumption)
    | with_reducible exact getBlock_inv _
    | with_reducible exact behaviour_inv (by assumption)
    | with_reducible exact lift_onPlace (by assumption)
    | with_reducible exact lift_affectNeighborsAfterRemoval (by assumption)
    | (with_reducible apply InvM.bind; on_goal 2 => intro _ _)
    | (with_reducible apply InvM.ite <;> intro _)

attribute [local irreducible] Level.Core.setBlockInChunk

theorem core_setBlock_inv {kick : M Unit} (hk : InvM dt dc T kick)
    (p : Pos) {state : Block} (hs : allowed state = true)
    (flags limit : ℕ) : InvM dt dc T (Core.setBlock kick p state flags limit) := by
  unfold Core.setBlock
  inv [core_setBlockInChunk_inv p hs flags, getBlock_inv _, core_updateNeighborsAt_inv hk _ _,
    core_updateNeighbourForOutputSignal_inv hk _ _, behaviour_inv (by assumption),
    behaviour_inv hs, core_updateNeighbourShapes_inv hk hs _ _ _]

attribute [local irreducible] Level.Core.setBlock

theorem core_destroyBlock_inv {kick : M Unit} (hk : InvM dt dc T kick)
    (p : Pos) (drop : Bool) (limit : ℕ) :
    InvM dt dc T (Core.destroyBlock kick p drop limit) := by
  unfold Core.destroyBlock
  inv [getBlock_inv _, dropResources_inv _ _ _, peekBlockEntity_inv _,
    core_setBlock_inv hk _ (allowed_fluidBlock (by assumption)) _ _, gameEvent_inv _ _ _]

attribute [local irreducible] Level.Core.destroyBlock

theorem core_removeBlock_inv {kick : M Unit} (hk : InvM dt dc T kick) (p : Pos) (moved : Bool) :
    InvM dt dc T (Core.removeBlock kick p moved) := by
  unfold Core.removeBlock
  inv [getBlock_inv _, core_setBlock_inv hk _ (allowed_fluidBlock (by assumption)) _ _]

attribute [local irreducible] Level.Core.removeBlock

theorem core_updateOrDestroy_inv {kick : M Unit} (hk : InvM dt dc T kick)
    (state : Block) {newState : Block}
    (hs : allowed newState = true) (p : Pos) (flags limit : ℕ) :
    InvM dt dc T (Core.updateOrDestroy kick state newState p flags limit) := by
  unfold Core.updateOrDestroy
  inv [core_destroyBlock_inv hk _ _ _, core_setBlock_inv hk _ hs _ _]

attribute [local irreducible] Level.Core.updateOrDestroy

theorem core_executeShapeUpdate_inv {kick : M Unit} (hk : InvM dt dc T kick)
    (dir : Direction) (p q : Pos) {neighborState : Block}
    (hs : allowed neighborState = true) (flags limit : ℕ) :
    InvM dt dc T (Core.executeShapeUpdate kick dir p q neighborState flags limit) := by
  unfold Core.executeShapeUpdate
  inv [getBlock_inv _, behaviour_inv (by assumption),
    core_updateOrDestroy_inv hk _ (by assumption) _ _ _]

attribute [local irreducible] Level.Core.executeShapeUpdate

theorem core_runNext_inv {kick : M Unit} (hk : InvM dt dc T kick)
    {u : NeighborUpdate} (hu : UpdOK u) :
    InvM dt dc OptUpdOK (Core.runNext kick u) := by
  cases u with
  | shape dir ns p q flags limit =>
    have hs : allowed ns = true := hu
    simp only [Core.runNext]
    inv [core_executeShapeUpdate_inv hk dir p q hs flags limit]
  | simple p block =>
    simp only [Core.runNext]
    inv [getBlock_inv _, behaviour_inv (by assumption)]
  | full state p block moved =>
    have hs : allowed state = true := hu
    simp only [Core.runNext]
    inv [behaviour_inv hs]
  | multi source block skip idx =>
    simp only [Core.runNext]
    inv [getBlock_inv _, behaviour_inv (by assumption)]

attribute [local irreducible] Level.Core.runNext

theorem runUpdatesLoop_inv (fuel : ℕ) : InvM dt dc T (runUpdatesLoop fuel) := by
  induction fuel with
  | zero =>
    refine InvM.modify fun l hl => ⟨rfl, ?_⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, -⟩ := hl
    exact ⟨h1, h2, h3, h4, h5, h6, h7, updOK_nil, updOK_nil⟩
  | succ fuel ih =>
    unfold runUpdatesLoop
    refine InvM.get_bind fun l hl => ?_
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hl
    have hall : ∀ u ∈ l.updatesAdded ++ l.updateStack, UpdOK u := fun u hu =>
      (List.mem_append.1 hu).elim (h9 u) (h8 u)
    have e1 : (l.shift dt dc).updatesAdded = l.updatesAdded := rfl
    have e2 : (l.shift dt dc).updateStack = l.updateStack := rfl
    rw [e1, e2]
    rcases hlist : l.updatesAdded ++ l.updateStack with _ | ⟨u, rest⟩
    · refine RelM.set (s := { l with updateStack := [], updatesAdded := [], updateCount := 0 })
        rfl ?_
      exact ⟨h1, h2, h3, h4, h5, h6, h7, updOK_nil, updOK_nil⟩
    · rw [hlist] at hall
      have hu : UpdOK u := hall u (List.mem_cons_self ..)
      have hrest : ∀ v ∈ rest, UpdOK v := fun v hv => hall v (List.mem_cons_of_mem _ hv)
      refine RelM.bind (RelM.set
        (s := { l with updateStack := u :: rest, updatesAdded := [] }) rfl
        ⟨h1, h2, h3, h4, h5, h6, h7, hall, updOK_nil⟩) fun _ _ _ => ?_
      change InvM dt dc T _
      refine InvM.bind (core_runNext_inv setOverflow_inv hu) fun next hnext =>
        InvM.bind (InvM.modify fun l' hl' => ⟨rfl, ?_⟩) fun _ _ => ih
      obtain ⟨g1, g2, g3, g4, g5, g6, g7, -, g9⟩ := hl'
      refine ⟨g1, g2, g3, g4, g5, g6, g7, fun v hv => ?_, g9⟩
      rcases List.mem_append.1 hv with hv | hv
      · cases next with
        | none => exact nomatch hv
        | some w =>
          rw [List.mem_singleton.1 hv]
          exact hnext
      · exact hrest v hv

theorem runUpdates_inv : InvM dt dc T runUpdates := runUpdatesLoop_inv _

attribute [local irreducible] Level.runUpdatesLoop Level.runUpdates

theorem updateNeighborsAt_inv (p : Pos) (block : BlockId) :
    InvM dt dc T (updateNeighborsAt p block) :=
  core_updateNeighborsAt_inv runUpdates_inv p block

theorem updateNeighborsAtExceptFromFacing_inv (p : Pos) (block : BlockId)
    (skip : Option Direction) : InvM dt dc T (updateNeighborsAtExceptFromFacing p block skip) :=
  core_updateNeighborsAtExceptFromFacing_inv runUpdates_inv p block skip

theorem neighborChanged_inv (p : Pos) (block : BlockId) :
    InvM dt dc T (Level.neighborChanged p block) :=
  core_neighborChanged_inv runUpdates_inv p block

theorem setBlock_inv (p : Pos) {state : Block} (hs : allowed state = true) (flags limit : ℕ) :
    InvM dt dc T (setBlock p state flags limit) :=
  core_setBlock_inv runUpdates_inv p hs flags limit

theorem removeBlock_inv (p : Pos) (moved : Bool) : InvM dt dc T (removeBlock p moved) :=
  core_removeBlock_inv runUpdates_inv p moved

attribute [local irreducible] Level.updateNeighborsAt Level.updateNeighborsAtExceptFromFacing
  Level.neighborChanged Level.setBlock Level.removeBlock


/-! ### Signals -/

theorem signalAt_shift {env : Env} (henv : EnvOK dt dc env) {l : Level} (hl : Calm l) (p : Pos)
    (d : Direction) : (l.shift dt dc).signalAt env p d = l.signalAt env p d := by
  have key : ∀ q d, (env.block (l.blockAt q)).signal (l.shift dt dc) q d =
      (env.block (l.blockAt q)).signal l q d := fun q d => (henv.1 _ (hl.1 q)).signal l q d
  have key' : ∀ q d, (env.block (l.blockAt q)).directSignal (l.shift dt dc) q d =
      (env.block (l.blockAt q)).directSignal l q d :=
    fun q d => (henv.1 _ (hl.1 q)).directSignal l q d
  simp only [Level.signalAt, Level.directSignalTo, Level.directSignalAt, Level.blockAt_shift,
    key, key']

theorem directSignalAt_shift {env : Env} (henv : EnvOK dt dc env) {l : Level} (hl : Calm l)
    (p : Pos) (d : Direction) :
    (l.shift dt dc).directSignalAt env p d = l.directSignalAt env p d :=
  (henv.1 _ (hl.1 p)).directSignal l p d

theorem getSignal_inv (p : Pos) (d : Direction) : InvM dt dc T (getSignal p d) :=
  fun _ henv _ hl => ⟨⟨(signalAt_shift henv hl p d).symm, trivial⟩, rfl, hl⟩

theorem getDirectSignal_inv (p : Pos) (d : Direction) : InvM dt dc T (getDirectSignal p d) :=
  fun _ henv _ hl => ⟨⟨(directSignalAt_shift henv hl p d).symm, trivial⟩, rfl, hl⟩

attribute [local irreducible] Level.getSignal Level.getDirectSignal

theorem hasSignal_inv (p : Pos) (d : Direction) : InvM dt dc T (hasSignal p d) := by
  unfold hasSignal
  inv [getSignal_inv _ _]

attribute [local irreducible] Level.hasSignal

/-! ### The redstone torch and the block of redstone -/

section Torch

open Component

theorem allowed_torch (k : Torch.Kind) : allowed k.toBlock = true := by
  cases k <;> rfl

theorem torch_hasNeighborSignal_inv (k : Torch.Kind) (p : Pos) :
    InvM dt dc T (Torch.hasNeighborSignal k p) :=
  hasSignal_inv _ _

theorem torch_notifyNeighbors_inv (k : Torch.Kind) (p : Pos) :
    InvM dt dc T (Torch.notifyNeighbors k p) :=
  InvM.forM fun _ _ => updateNeighborsAt_inv _ _

theorem toggleCount_shift (l : Level) (p : Pos) :
    ((l.shift dt dc).recentTorchToggles.filter (·.1 == p)).length =
      (l.recentTorchToggles.filter (·.1 == p)).length := by
  rw [Level.recentTorchToggles_shift, List.filter_map, List.length_map]
  rfl

theorem isToggledTooFrequently_inv (p : Pos) (add : Bool) :
    InvM dt dc T (Torch.isToggledTooFrequently p add) := by
  unfold Torch.isToggledTooFrequently
  dsimp only
  have hget : InvM dt dc T (get >>= fun l : Level => (pure (decide
      ((l.recentTorchToggles.filter (·.1 == p)).length ≥ Torch.maxRecentToggles)) : M Bool)) :=
    InvM.get_bind' (R := T) fun l hl => ⟨by rw [toggleCount_shift], InvM.pure trivial⟩
  have hmod : InvM dt dc T (modify fun l : Level =>
      { l with recentTorchToggles := l.recentTorchToggles ++ [(p, l.gameTime)] } : M Unit) := by
    refine InvM.modify fun l hl => ⟨?_, hl⟩
    cases l
    simp [Level.shift]
  inv [hget, hmod]

theorem dropWhile_toggles_shift (g : ℕ) (ts : List (Pos × ℕ)) :
    (ts.map fun e => (e.1, e.2 + dt)).dropWhile
        (fun e => decide (g + dt - e.2 > Torch.recentToggleTimer)) =
      (ts.dropWhile fun e => decide (g - e.2 > Torch.recentToggleTimer)).map
        fun e => (e.1, e.2 + dt) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, List.dropWhile_cons, Nat.add_sub_add_right]
    split
    · exact ih
    · rfl

theorem dropOldToggles_inv : InvM dt dc T Torch.dropOldToggles := by
  refine InvM.modify fun l hl => ⟨?_, hl⟩
  have h := dropWhile_toggles_shift (dt := dt) l.gameTime l.recentTorchToggles
  cases l
  simp only [Level.shift, Level.mk.injEq, true_and, and_true] at h ⊢
  exact h

attribute [local irreducible] Torch.hasNeighborSignal Torch.notifyNeighbors
  Torch.isToggledTooFrequently Torch.dropOldToggles

theorem torch_tick_inv (k : Torch.Kind) (p : Pos) : InvM dt dc T (Torch.tick k p) := by
  unfold Torch.tick
  inv [torch_hasNeighborSignal_inv k p, dropOldToggles_inv, setBlock_inv p (allowed_torch _) _ _,
    isToggledTooFrequently_inv p _, scheduleTick_inv _ _ _ _, getBlock_inv _]

theorem torch_neighborChanged_inv (k : Torch.Kind) (p : Pos) :
    InvM dt dc T (Torch.neighborChanged k p) := by
  unfold Torch.neighborChanged
  refine InvM.bind (torch_hasNeighborSignal_inv k p) fun s _ => InvM.get_bind' fun l hl =>
    ⟨by simp only [Level.willTickThisTick_shift], ?_⟩
  inv [scheduleTick_inv _ _ _ _]

theorem torch_updateShape_inv (k : Torch.Kind) (p : Pos) (d : Direction) :
    InvM dt dc (fun b => allowed b = true) (Torch.updateShape k p d) := by
  unfold Torch.updateShape
  refine InvM.get_bind' fun l hl => ⟨rfl, ?_⟩
  refine InvM.ite (fun _ => InvM.pure rfl) fun _ => InvM.pure (allowed_torch k)

end Torch

/-! ### Diodes and the repeater -/

section Diode

open Component

theorem getInputSignal_inv (facing : Direction) (p : Pos) :
    InvM dt dc T (Diode.getInputSignal facing p) := by
  unfold Diode.getInputSignal
  inv [getSignal_inv _ _, getBlock_inv _]

theorem getControlInputSignal_inv (p : Pos) (direction : Direction) (onlyDiodes : Bool) :
    InvM dt dc T (Diode.getControlInputSignal p direction onlyDiodes) := by
  unfold Diode.getControlInputSignal
  inv [getBlock_inv _, getDirectSignal_inv _ _]

attribute [local irreducible] Diode.getInputSignal Diode.getControlInputSignal

theorem getAlternateSignal_inv (facing : Direction) (p : Pos) (sideInputDiodesOnly : Bool) :
    InvM dt dc T (Diode.getAlternateSignal facing p sideInputDiodesOnly) := by
  unfold Diode.getAlternateSignal
  inv [getControlInputSignal_inv _ _ _]

attribute [local irreducible] Diode.getAlternateSignal

/-- What the lemmas about `DiodeBlock` need to know about a diode: its two questions commute
with the shift, and it only ever becomes an allowed block. -/
structure DiodeOK (dt dc : ℕ) (d : Diode) : Prop where
  isLocked : ∀ p, InvM dt dc T (d.isLocked p)
  shouldTurnOn : ∀ p, InvM dt dc T (d.shouldTurnOn p)
  setPowered : ∀ v, allowed (d.setPowered v) = true

theorem diode_updateNeighborsInFront_inv (d : Diode) (p : Pos) :
    InvM dt dc T (d.updateNeighborsInFront p) := by
  unfold Diode.updateNeighborsInFront
  inv [neighborChanged_inv _ _, updateNeighborsAtExceptFromFacing_inv _ _ _]

variable {d : Diode} (hd : DiodeOK dt dc d)

include hd

theorem diode_tick_inv (p : Pos) : InvM dt dc T (d.tick p) := by
  unfold Diode.tick
  inv [hd.isLocked p, hd.shouldTurnOn p, setBlock_inv p (hd.setPowered _) _ _,
    scheduleTick_inv _ _ _ _]

theorem diode_checkTickOnNeighbor_inv (p : Pos) : InvM dt dc T (d.checkTickOnNeighbor p) := by
  unfold Diode.checkTickOnNeighbor
  refine InvM.bind (hd.isLocked p) fun locked _ => InvM.ite (fun _ => ?_) fun _ =>
    InvM.pure trivial
  refine InvM.bind (hd.shouldTurnOn p) fun on _ => InvM.get_bind' fun l hl =>
    ⟨by simp only [Level.willTickThisTick_shift]; rfl, ?_⟩
  inv [scheduleTick_inv _ _ _ _]

attribute [local irreducible] Diode.updateNeighborsInFront Diode.tick Diode.checkTickOnNeighbor

theorem diode_neighborChanged_inv (p : Pos) : InvM dt dc T (d.neighborChanged p) := by
  unfold Diode.neighborChanged
  refine InvM.bind (getBlock_inv p) fun b _ => InvM.ite (fun _ => ?_) fun _ => InvM.pure trivial
  refine InvM.get_bind' fun l hl => ⟨rfl, ?_⟩
  inv [diode_checkTickOnNeighbor_inv hd p, removeBlock_inv p _, updateNeighborsAt_inv _ _]

end Diode

section Repeater

open Component

theorem repeater_isLocked_inv (s : Blocks.Repeater) (p : Pos) :
    InvM dt dc T (Repeater.isLocked s p) := by
  unfold Repeater.isLocked
  inv [getAlternateSignal_inv _ _ _]

attribute [local irreducible] Component.Repeater.isLocked

theorem repeater_diodeOK (s : Blocks.Repeater) : DiodeOK dt dc (Repeater.diode s) where
  isLocked := repeater_isLocked_inv s
  shouldTurnOn p := by
    change InvM dt dc T (do
      let x ← Diode.getInputSignal s.facing.toDirection p
      pure (decide (x > 0)) : M Bool)
    inv [getInputSignal_inv _ _]
  setPowered _ := rfl

theorem repeater_updateShape_inv (s : Blocks.Repeater) (p : Pos) (d : Direction)
    (neighbourState : Block) :
    InvM dt dc (fun b => allowed b = true) (Repeater.updateShape s p d neighbourState) := by
  unfold Repeater.updateShape
  inv [repeater_isLocked_inv s p]

end Repeater

/-! ### The behaviours of the allowed blocks -/

/-- The reactions of a behaviour that a game tick of a calm level can reach commute with the
shift, and its signals do not depend on the clocks. -/
structure BehOK (dt dc : ℕ) (b : Behaviour) : Prop where
  signal : ∀ l p d, b.signal (l.shift dt dc) p d = b.signal l p d
  directSignal : ∀ l p d, b.directSignal (l.shift dt dc) p d = b.directSignal l p d
  neighborChanged : ∀ p s m, InvM dt dc T (b.neighborChanged p s m)
  onPlace : ∀ p o m, InvM dt dc T (b.onPlace p o m)
  affectNeighborsAfterRemoval : ∀ p m, InvM dt dc T (b.affectNeighborsAfterRemoval p m)
  updateShape : ∀ p d q s, allowed s = true →
    InvM dt dc (fun b => allowed b = true) (b.updateShape p d q s)
  updateIndirectNeighbourShapes : ∀ p f n, InvM dt dc T (b.updateIndirectNeighbourShapes p f n)
  tick : ∀ p, InvM dt dc T (b.tick p)
  triggerEvent : ∀ p x y, InvM dt dc T (b.triggerEvent p x y)

theorem behOK_inert {self : Block} (h : allowed self = true) :
    BehOK dt dc (Behaviour.inert self) where
  signal _ _ _ := rfl
  directSignal _ _ _ := rfl
  neighborChanged _ _ _ := InvM.pure trivial
  onPlace _ _ _ := InvM.pure trivial
  affectNeighborsAfterRemoval _ _ := InvM.pure trivial
  updateShape _ _ _ _ _ := InvM.pure h
  updateIndirectNeighbourShapes _ _ _ := InvM.pure trivial
  tick _ := InvM.pure trivial
  triggerEvent _ _ _ := InvM.pure trivial

theorem behOK_poweredBlock {self : Block} (h : allowed self = true) :
    BehOK dt dc (Component.Torch.poweredBlock self) where
  signal _ _ _ := rfl
  directSignal _ _ _ := rfl
  neighborChanged _ _ _ := InvM.pure trivial
  onPlace _ _ _ := InvM.pure trivial
  affectNeighborsAfterRemoval _ _ := InvM.pure trivial
  updateShape _ _ _ _ _ := InvM.pure h
  updateIndirectNeighbourShapes _ _ _ := InvM.pure trivial
  tick _ := InvM.pure trivial
  triggerEvent _ _ _ := InvM.pure trivial

theorem behOK_torch (k : Component.Torch.Kind) : BehOK dt dc (Component.Torch.torch k) where
  signal _ _ _ := rfl
  directSignal _ _ _ := rfl
  neighborChanged p _ _ := torch_neighborChanged_inv k p
  onPlace p _ _ := torch_notifyNeighbors_inv k p
  affectNeighborsAfterRemoval p _ :=
    InvM.ite (fun _ => torch_notifyNeighbors_inv k p) fun _ => InvM.pure trivial
  updateShape p d _ _ _ := torch_updateShape_inv k p d
  updateIndirectNeighbourShapes _ _ _ := InvM.pure trivial
  tick p := torch_tick_inv k p
  triggerEvent _ _ _ := InvM.pure trivial

theorem behOK_repeater (s : Blocks.Repeater) : BehOK dt dc (Component.Repeater.repeater s) where
  signal _ _ _ := rfl
  directSignal _ _ _ := rfl
  neighborChanged p _ _ := diode_neighborChanged_inv (repeater_diodeOK s) p
  onPlace p _ _ := diode_updateNeighborsInFront_inv _ p
  affectNeighborsAfterRemoval p _ :=
    InvM.ite (fun _ => diode_updateNeighborsInFront_inv _ p) fun _ => InvM.pure trivial
  updateShape p d _ ns _ := repeater_updateShape_inv s p d ns
  updateIndirectNeighbourShapes _ _ _ := InvM.pure trivial
  tick p := diode_tick_inv (repeater_diodeOK s) p
  triggerEvent _ _ _ := InvM.pure trivial

/-- **Every allowed block has a behaviour whose reactions commute with the shift.** -/
theorem behOK_rules {b : Block} (h : allowed b = true) : BehOK dt dc (rules.block b) := by
  obtain rfl | rfl | rfl | ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩ := allowed_cases h
  · exact behOK_inert rfl
  · exact behOK_inert rfl
  · exact behOK_poweredBlock rfl
  · exact behOK_repeater s
  · exact behOK_torch (.floor s)
  · exact behOK_torch (.wall s)

theorem hooksOK_close {b : Behaviour} (hb : BehOK dt dc b) {env : Env} (henv : EnvOK dt dc env) :
    HooksOK dt dc (b.close env) where
  signal := hb.signal
  directSignal := hb.directSignal
  neighborChanged p s m := hb.neighborChanged p s m env henv
  onPlace p o m := hb.onPlace p o m env henv
  affectNeighborsAfterRemoval p m := hb.affectNeighborsAfterRemoval p m env henv
  updateShape p d q s hs := hb.updateShape p d q s hs env henv
  updateIndirectNeighbourShapes p f n := hb.updateIndirectNeighbourShapes p f n env henv
  tick p := hb.tick p env henv
  triggerEvent p x y := hb.triggerEvent p x y env henv

theorem hooksOK_exhausted {b : Behaviour} (hb : BehOK dt dc b) : HooksOK dt dc b.exhausted where
  signal := hb.signal
  directSignal := hb.directSignal
  neighborChanged _ _ _ := fun _ hl => ⟨⟨rfl, trivial⟩, rfl, hl⟩
  onPlace _ _ _ := fun _ hl => ⟨⟨rfl, trivial⟩, rfl, hl⟩
  affectNeighborsAfterRemoval _ _ := fun _ hl => ⟨⟨rfl, trivial⟩, rfl, hl⟩
  updateShape _ _ _ _ hs := fun _ hl => ⟨⟨rfl, hs⟩, rfl, hl⟩
  updateIndirectNeighbourShapes _ _ _ := fun _ hl => ⟨⟨rfl, trivial⟩, rfl, hl⟩
  tick _ := fun _ hl => ⟨⟨rfl, trivial⟩, rfl, hl⟩
  triggerEvent _ _ _ := fun _ hl => ⟨⟨rfl, trivial⟩, rfl, hl⟩

theorem onGameEvent_inv (event : String) (p : Pos) (context : GameEventContext) :
    InvM dt dc T (Component.Sculk.onGameEvent event p context) := by
  unfold Component.Sculk.onGameEvent Component.Sculk.onGameEventAt
  refine InvM.get_bind' fun l hl => ⟨rfl, ?_⟩
  have h : l.blockEntityTickers ++ l.pendingBlockEntityTickers = [] := by
    rw [hl.2.2.1, hl.2.2.2.1]
    rfl
  dsimp only
  rw [h]
  exact InvM.pure trivial

/-- **The environment of the rules, at any nesting depth, is good.** -/
theorem envOK_rules (depth : ℕ) : EnvOK dt dc (rules.env depth) := by
  induction depth with
  | zero =>
    exact ⟨fun b hb => hooksOK_exhausted (behOK_rules hb),
      fun _ _ _ _ hl => ⟨⟨rfl, trivial⟩, rfl, hl⟩⟩
  | succ depth ih =>
    refine ⟨fun b hb => ?_, fun n p c => onGameEvent_inv n p c _ ih⟩
    change HooksOK dt dc (b.pinned fun b => (rules.block b).close (rules.env depth))
    rw [Block.pinned_eq]
    exact hooksOK_close (behOK_rules hb) ih

/-! ### The game tick -/

theorem tickBlock_inv (t : ScheduledTick) : InvM dt dc T (tickBlock t) := by
  unfold tickBlock
  inv [getBlock_inv _, behaviour_inv (by assumption)]

theorem tickBlock_shift (t : ScheduledTick) : tickBlock (t.shift dt dc) = tickBlock t := rfl

attribute [local irreducible] Level.tickBlock

theorem forM_map_shift (due : List ScheduledTick) (f : ScheduledTick → M PUnit)
    (hf : ∀ t, f (t.shift dt dc) = f t) :
    (due.map (ScheduledTickOf.shift dt dc)).forM f = due.forM f := by
  induction due with
  | nil => rfl
  | cons t ts ih =>
    change (f (t.shift dt dc) >>= fun _ => (ts.map (ScheduledTickOf.shift dt dc)).forM f) =
      (f t >>= fun _ => ts.forM f)
    rw [hf, ih]

theorem runScheduledTicks_inv : InvM dt dc T runScheduledTicks := by
  unfold runScheduledTicks
  refine InvM.get_bind fun l hl => ?_
  have hdue : (ScheduledTickOf.dueInOrder (l.shift dt dc).gameTime (l.shift dt dc).ticks).take
      maxScheduledTicksPerTick =
      ((ScheduledTickOf.dueInOrder l.gameTime l.ticks).take maxScheduledTicksPerTick).map
        (ScheduledTickOf.shift dt dc) := by
    rw [Level.gameTime_shift, Level.ticks_shift, ScheduledTickOf.dueInOrder_shift, List.map_take]
  dsimp only
  rw [hdue]
  generalize (ScheduledTickOf.dueInOrder l.gameTime l.ticks).take maxScheduledTicksPerTick = due
  have hfilter : (l.shift dt dc).ticks.filter (fun t =>
      !(due.map (ScheduledTickOf.shift dt dc)).contains t) =
      (l.ticks.filter fun t => !due.contains t).map (ScheduledTickOf.shift dt dc) := by
    rw [Level.ticks_shift, List.filter_map]
    congr 2
    funext t
    simp only [Function.comp_apply, ScheduledTickOf.contains_shift]
  refine RelM.bind (S := fun a a' => a = a' ∧ T a) (RelM.set ?_ hl) fun _ _ _ => ?_
  · rw [hfilter]
    rfl
  · rw [forM_map_shift]
    · change InvM dt dc T _
      refine InvM.bind (Q := T) (InvM.forM fun t _ => ?_) fun _ _ =>
        InvM.modify fun _ hl => ⟨rfl, hl⟩
      refine InvM.bind (Q := T) (InvM.modify fun l hl => ⟨?_, hl⟩) fun _ _ => tickBlock_inv t
      cases l
      simp [Level.shift]
    · intro t
      rw [tickBlock_shift]

theorem runBlockEventsLoop_inv (fuel : ℕ) : InvM dt dc T (runBlockEventsLoop fuel) := by
  induction fuel with
  | zero =>
    unfold runBlockEventsLoop
    refine InvM.get_bind' fun l hl => ⟨rfl, ?_⟩
    inv [setOverflow_inv]
  | succ fuel ih =>
    unfold runBlockEventsLoop
    refine InvM.get_bind fun l hl => ?_
    have e : (l.shift dt dc).blockEvents = l.blockEvents := rfl
    dsimp only
    rw [e]
    rcases l.blockEvents with _ | ⟨e, rest⟩
    · exact InvM.pure trivial
    · refine RelM.bind (S := fun a a' => a = a' ∧ T a)
        (RelM.set (s := { l with blockEvents := rest }) rfl hl) fun _ _ _ => ?_
      change InvM dt dc T _
      inv [getBlock_inv _, behaviour_inv (by assumption)]

theorem runBlockEvents_inv : InvM dt dc T runBlockEvents := runBlockEventsLoop_inv _

attribute [local irreducible] Level.runScheduledTicks Level.runBlockEventsLoop
  Level.runBlockEvents

/-- A reaction that leaves calm levels and their shifts as they are. -/
theorem InvM.of_noop {x : M Unit} (h : ∀ env l, Calm l → (x.run env).run l = ((), l))
    (h' : ∀ env l, Calm l → (x.run env).run (l.shift dt dc) = ((), l.shift dt dc)) :
    InvM dt dc T x := by
  intro env _ l hl
  have e : run (x.run env) l = ((), l) := h env l hl
  have e' : run (x.run env) (l.shift dt dc) = ((), l.shift dt dc) := h' env l hl
  rw [e, e']
  exact ⟨⟨rfl, trivial⟩, rfl, hl⟩

theorem runFluidTicks_inv : InvM dt dc T runFluidTicks :=
  InvM.of_noop (fun env l hl => runFluidTicks_of_empty env l hl.2.2.2.2.1 hl.2.2.2.2.2.1)
    fun env l hl => runFluidTicks_of_empty env _
      (show l.fluidTicks.map _ = [] by rw [hl.2.2.2.2.1]; rfl)
      (show l.fluidTicksToRun.map _ = [] by rw [hl.2.2.2.2.2.1]; rfl)

theorem tickChunks_inv : InvM dt dc T tickChunks :=
  InvM.of_noop (fun env l hl => tickChunks_of_speed_zero env l hl.2.2.2.2.2.2.1)
    fun env _ hl => tickChunks_of_speed_zero env _ hl.2.2.2.2.2.2.1

theorem tickEntities_inv : InvM dt dc T tickEntities := by
  unfold tickEntities
  refine InvM.get_bind' fun l hl => ⟨rfl, ?_⟩
  dsimp only
  rw [hl.2.1]
  exact InvM.pure trivial

theorem tickBlockEntities_inv : InvM dt dc T tickBlockEntities := by
  unfold tickBlockEntities
  refine InvM.bind (Q := T) (InvM.modify fun l hl => ⟨rfl, ?_⟩) fun _ _ =>
    InvM.get_bind' (R := T) fun l hl => ⟨rfl, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hl
    refine ⟨h1, h2, ?_, rfl, h5, h6, h7, h8, h9⟩
    change l.blockEntityTickers ++ l.pendingBlockEntityTickers = []
    rw [h3, h4]
    rfl
  · dsimp only
    rw [hl.2.2.1]
    exact InvM.bind (Q := T) (InvM.pure trivial) fun _ _ => InvM.modify fun _ hl => ⟨rfl, hl⟩

attribute [local irreducible] Level.runFluidTicks Level.tickChunks Level.tickEntities
  Level.tickBlockEntities

theorem tickStart_inv : InvM dt dc T (modify fun l : Level => { l with
    gameTime := l.gameTime + 1
    handlingTick := true
    dayTime := if l.advanceTime then l.dayTime + 1 else l.dayTime
    lightWorld := l.world } : M Unit) := by
  refine InvM.modify fun l hl => ⟨?_, hl⟩
  cases l
  simp only [Level.shift, Level.mk.injEq, true_and, and_true]
  refine ⟨by omega, ?_⟩
  split <;> omega

theorem tickMiddle_inv : InvM dt dc T (modify fun l : Level =>
    { l with handlingTick := false, tickedBlockEntities := [] } : M Unit) :=
  InvM.modify fun _ hl => ⟨rfl, hl⟩

theorem tick_inv : InvM dt dc T Level.tick := by
  unfold Level.tick
  inv [tickStart_inv, tickMiddle_inv, runScheduledTicks_inv, runFluidTicks_inv, tickChunks_inv,
    runBlockEvents_inv, tickEntities_inv, tickBlockEntities_inv]

end Mechanics

/-! ### The theorem -/

section Main

variable {dt dc : ℕ}

attribute [local irreducible] Level.tick Rules.env maxDepth

/-- A game tick, as the state transformer the lemmas above are about. -/
theorem step_eq (l : Level) :
    rules.step l = (run (Level.tick.run (rules.env maxDepth)) l).2 := rfl

/-- **A game tick commutes with the time shift on calm levels, and keeps them calm.** -/
theorem step_shift {l : Level} (hl : Calm l) :
    rules.step (l.shift dt dc) = (rules.step l).shift dt dc ∧ Calm (rules.step l) := by
  rw [step_eq, step_eq]
  exact (tick_inv (rules.env maxDepth) (envOK_rules maxDepth) l hl).2

/-- A game tick of a calm level gives a calm level. -/
theorem calm_step {l : Level} (hl : Calm l) : Calm (rules.step l) :=
  (step_shift (dt := 0) (dc := 0) hl).2

/-- Any number of game ticks of a calm level gives a calm level. -/
theorem calm_steps {l : Level} (hl : Calm l) (n : ℕ) : Calm (rules.steps n l) := by
  induction n with
  | zero => exact hl
  | succ n ih =>
    rw [Rules.steps_add]
    exact calm_step ih

/-- **A clock of calm levels runs for ever.** If `period` game ticks take the calm level `l`
to itself, shifted (a cycle certificate), then `k` periods take it to itself shifted `k`
times, for every `k`. -/
theorem steps_cycle {l : Level} {period dc : ℕ} (hc : rules.Cycle l period dc) (hl : Calm l)
    (k : ℕ) : rules.steps (k * period) l = l.shift (k * period) (k * dc) :=
  rules.periodic_of_shiftInvariant hc (fun i _ _ => (step_shift (calm_steps hl i)).1) k

/-- **The blocks of a clock of calm levels repeat for ever**: the block at `p` after `n` game
ticks is the block after `n % period` game ticks. -/
theorem blockAt_steps_cycle {l : Level} {period dc : ℕ} (hc : rules.Cycle l period dc)
    (hl : Calm l) (hp : 0 < period) (n : ℕ) (p : Pos) :
    (rules.steps n l).blockAt p = (rules.steps (n % period) l).blockAt p := by
  have h := rules.blockAt_periodic hc (fun i _ _ => (step_shift (calm_steps hl i)).1)
    (n / period) (n % period) (Nat.le_of_lt (Nat.mod_lt n hp)) p
  rwa [Nat.div_add_mod'] at h

/-- A clock of calm levels never reaches a bound of the model, if it does not in one period. -/
theorem overflow_steps_cycle {l : Level} {period dc : ℕ} (hc : rules.Cycle l period dc)
    (hl : Calm l) (hp : 0 < period) (n : ℕ) :
    (rules.steps n l).overflow = (rules.steps (n % period) l).overflow := by
  have hinv : ∀ i < period, ∀ k, rules.step ((rules.steps i l).shift (k * period) (k * dc)) =
      (rules.step (rules.steps i l)).shift (k * period) (k * dc) :=
    fun i _ _ => (step_shift (calm_steps hl i)).1
  have h : rules.steps ((n / period) * period + n % period) l =
      (rules.steps (n % period) l).shift ((n / period) * period) ((n / period) * dc) := by
    rw [Rules.steps_add, rules.periodic_of_shiftInvariant hc hinv,
      rules.steps_shift_of_shiftInvariant (fun i hi => hinv i hi (n / period)) (n % period)
        (Nat.le_of_lt (Nat.mod_lt n hp))]
  rw [Nat.div_add_mod'] at h
  rw [h, Level.overflow_shift]

end Main

/-! ### Deciding that a level is calm -/

/-- Every value of the trie satisfies `P`. -/
def trieAll {α : Type} (P : α → Bool) : Trie α → Bool
  | .leaf => true
  | .node l v r => trieAll P l && v.all P && trieAll P r

theorem trieAll_get {α : Type} {P : α → Bool} :
    ∀ {t : Trie α}, trieAll P t = true → ∀ {k : ℕ} {v : α}, t.get k = some v → P v = true
  | .leaf, _, _, _, h => nomatch h
  | .node l w r, ht, k, v, h => by
    simp only [trieAll, Bool.and_eq_true] at ht
    obtain ⟨⟨hl, hw⟩, hr⟩ := ht
    cases k with
    | zero =>
      have e : w = some v := h
      rw [e] at hw
      exact hw
    | succ k =>
      have e : (if k % 2 = 0 then l.get (k / 2) else r.get (k / 2)) = some v := h
      split at e
      · exact trieAll_get hl e
      · exact trieAll_get hr e

/-- The decidable form of `Calm`, for a level between two game ticks: every block is allowed,
and the level has no entity, no ticking block entity, no scheduled fluid tick, no random ticks
and no pending neighbour update. -/
def calm (l : Level) : Bool :=
  trieAll allowed l.world.cells.tree && l.entities.isEmpty && l.blockEntityTickers.isEmpty &&
    l.pendingBlockEntityTickers.isEmpty && l.fluidTicks.isEmpty && l.fluidTicksToRun.isEmpty &&
    decide (l.randomTickSpeed = 0) && l.updateStack.isEmpty && l.updatesAdded.isEmpty

theorem Calm.of_calm {l : Level} (h : calm l = true) : Calm l := by
  simp only [calm, Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨fun p => ?_, h2, h3, h4, h5, h6, h7, ?_, ?_⟩
  · change allowed ((l.world.cells.tree.get p.key).getD .AIR) = true
    cases e : l.world.cells.tree.get p.key with
    | none => rfl
    | some v => exact trieAll_get h1 e
  · rw [h8]
    exact updOK_nil
  · rw [h9]
    exact updOK_nil

end ShiftInvariant

assert_standard_axioms ShiftInvariant.step_shift
assert_standard_axioms ShiftInvariant.steps_cycle
assert_standard_axioms ShiftInvariant.blockAt_steps_cycle
assert_standard_axioms ShiftInvariant.overflow_steps_cycle
assert_standard_axioms ShiftInvariant.Calm.of_calm

namespace ShiftInvariant

end ShiftInvariant

end Redstone
