import Redstone.Proof.Circuit

/-!
# Piston doors

What it means for a contraption to be a working piston door, and how large it is.

A `PistonDoor` is a level together with what one has to know to use it as a door: the block a
player uses to operate it (the *input*, a lever in every door of this project), the *doorway*
(a box of cells one block thick), the axis along which one walks through it, the block the
doorway is filled with when the door is closed, and how many game ticks opening and closing
take.

`PistonDoor.Works` says that the door does its job:

* the level it comes with is at rest, and the doorway is closed: every cell of the doorway holds
  the door block;
* using the input and waiting `openTicks` game ticks leaves the level at rest and *open*: no
  block of the whole level is left in the way through the doorway, neither in the doorway nor
  anywhere in front of it or behind it (`PistonDoor.IsOpen`). This is more than "the cells of
  the doorway are air": a door that pulls its blocks one cell back and leaves them, or the
  pistons that pulled them, in the corridor is not open;
* using the input again and waiting `closeTicks` game ticks leaves the level at rest with the
  blocks and block entities it started with (`Level.SameBlocks`), so the doorway is closed
  again and the door can be used again;
* the model reached none of its bounds on the way (`overflow = false`).

From `Works` it follows by the general theorem about levels at rest that the door stays open
for ever until the input is used, and stays closed for ever after it has closed
(`Works.stays_open`, `Works.stays_closed`).

`IsPistonDoor w h d` says that `d` works and that its doorway is `w` cells wide and `h` cells
high. The *volume* of a door (`PistonDoor.volume`) is the volume of the bounding box of every
cell that holds a block at some game tick of one opening and closing (`PistonDoor.trace`,
`Level.occupied`, `boundingVolume`). `minVolume w h` is the least volume of a working `w` by
`h` door, and `minVolume_le` says that every working door is an upper bound for it.

## What is not here

* **For ever.** `Works` says that one opening and closing brings back the blocks. The level
  after it differs from the first in its clocks, the counter that orders scheduled ticks and
  the random number generator, and that the second opening goes like the first is true only
  because the pistons, repeaters, torches and dust of these doors do not read them. That is not
  proved for any component (it is the same gap as in `Rules.periodic_of_shiftInvariant`), so
  "works for ever" is not a theorem here. `Theorems/PistonDoor/Simple2x2.lean` proves a second
  round trip by evaluation.
* **Nothing but pistons is asked for.** The definition does not say what the door is made of.
  A contraption that empties the doorway by other means and fills it again would count; none
  is known to the model without entities.
* **Lower bounds.** `minVolume` is defined, and bounded above by the doors proved in
  `Redstone/Theorems/PistonDoor`. A lower bound needs an argument about every level, and none
  is proved.
-/

namespace Redstone

/-! ### The cells of a map, and the cells a level occupies -/

namespace Trie

variable {α : Type}

/-- The list of entries of a trie holds exactly its entries. -/
theorem mem_toList_iff (t : Trie α) (k : ℕ) (v : α) : (k, v) ∈ t.toList ↔ t.get k = some v := by
  induction t generalizing k with
  | leaf => simp [toList]
  | node l x r ihl ihr =>
    rw [toList, List.mem_append, List.mem_append]
    cases k with
    | zero =>
      rw [get_node_zero]
      constructor
      · rintro ((h | h) | h)
        · cases x with
          | none => simp at h
          | some x =>
            simp only [Option.map_some, Option.toList_some, List.mem_singleton,
              Prod.mk.injEq, true_and] at h
            rw [h]
        · obtain ⟨e, -, he⟩ := List.mem_map.1 h
          simp at he
        · obtain ⟨e, -, he⟩ := List.mem_map.1 h
          simp at he
      · intro h
        exact Or.inl (Or.inl (by simp [h]))
    | succ k =>
      rw [get_node_succ]
      constructor
      · rintro ((h | h) | h)
        · cases x with
          | none => simp at h
          | some x => simp at h
        · obtain ⟨⟨k', v'⟩, hk', he⟩ := List.mem_map.1 h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hk, rfl⟩ := he
          have h0 : k % 2 = 0 := by omega
          have h1 : k / 2 = k' := by omega
          simp only [h0, ↓reduceIte, h1]
          exact (ihl _).1 hk'
        · obtain ⟨⟨k', v'⟩, hk', he⟩ := List.mem_map.1 h
          simp only [Prod.mk.injEq] at he
          obtain ⟨hk, rfl⟩ := he
          have h0 : ¬ k % 2 = 0 := by omega
          have h1 : k / 2 = k' := by omega
          simp only [h0, ↓reduceIte, h1]
          exact (ihr _).1 hk'
      · intro h
        split at h
        · next hk =>
          refine Or.inl (Or.inr (List.mem_map.2 ⟨(k / 2, v), (ihl _).2 h, ?_⟩))
          simp only [Prod.mk.injEq, and_true]
          omega
        · next hk =>
          refine Or.inr (List.mem_map.2 ⟨(k / 2, v), (ihr _).2 h, ?_⟩)
          simp only [Prod.mk.injEq, and_true]
          omega

end Trie

namespace PosMap

variable {α : Type}

/-- The list of entries of a map holds exactly its entries. -/
theorem mem_toList_iff (m : PosMap α) (p : Pos) (v : α) : (p, v) ∈ m.toList ↔ m p = some v := by
  constructor
  · intro h
    obtain ⟨⟨k, v'⟩, hk, he⟩ := List.mem_map.1 h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    change m.tree.get (Pos.ofKey k).key = some v'
    rw [Pos.key_ofKey]
    exact (Trie.mem_toList_iff _ _ _).1 hk
  · intro h
    exact List.mem_map.2 ⟨(p.key, v), (Trie.mem_toList_iff _ _ _).2 h, by simp⟩

end PosMap

namespace World

/-- The cells of a world are the positions that do not hold air, with their blocks. -/
theorem mem_toList_iff (w : World) (p : Pos) (b : Block) :
    (p, b) ∈ w.toList ↔ w.blockAt p = b ∧ b ≠ .AIR := by
  rw [toList, PosMap.mem_toList_iff]
  unfold blockAt
  constructor
  · intro h
    exact ⟨by rw [h]; rfl, fun hb => w.noAir p (hb ▸ h)⟩
  · rintro ⟨h, hb⟩
    cases hc : w.cells p with
    | none =>
      rw [hc] at h
      exact absurd h.symm hb
    | some c =>
      rw [hc] at h
      exact congrArg some h

end World

namespace Level

/-- The cells of the level that hold a block. -/
def occupied (l : Level) : List Pos := l.world.toList.map (·.1)

/-- The occupied cells are the cells that do not hold air. -/
theorem mem_occupied {l : Level} {p : Pos} : p ∈ l.occupied ↔ l.blockAt p ≠ .AIR := by
  constructor
  · intro h
    obtain ⟨⟨q, b⟩, hmem, rfl⟩ := List.mem_map.1 h
    obtain ⟨hb, hne⟩ := (l.world.mem_toList_iff q b).1 hmem
    exact fun h' => hne (hb ▸ h')
  · intro h
    exact List.mem_map.2 ⟨(p, l.blockAt p), (l.world.mem_toList_iff p _).2 ⟨rfl, h⟩, rfl⟩

/-- The two levels have the same blocks and the same block entities. -/
def SameBlocks (a b : Level) : Prop := a.world = b.world ∧ a.blockEntities = b.blockEntities

instance (a b : Level) : Decidable (a.SameBlocks b) := inferInstanceAs (Decidable (_ ∧ _))

theorem SameBlocks.blockAt_eq {a b : Level} (h : a.SameBlocks b) (p : Pos) :
    a.blockAt p = b.blockAt p := by
  unfold Level.blockAt
  rw [h.1]

end Level

namespace Contraption

/-- The least and the greatest of the numbers `lo`, `hi` and those of the list.

It is written with a comparison at every step, and not as two folds with `min` and `max`, so
that the kernel settles each step before it takes the next: a fold would leave it a chain of
pending `min`s as long as the list. -/
def bounds : List ℤ → ℤ → ℤ → ℤ × ℤ
  | [], lo, hi => (lo, hi)
  | v :: vs, lo, hi =>
    if v < lo then bounds vs v hi else if hi < v then bounds vs lo v else bounds vs lo hi

/-- The length of the interval the numbers of the list span, both ends counted; zero for the
empty list. -/
def span : List ℤ → ℕ
  | [] => 0
  | v :: vs => ((bounds vs v v).2 - (bounds vs v v).1 + 1).toNat

/-- `bounds` gives the least and the greatest. -/
theorem bounds_spec (vs : List ℤ) (lo hi : ℤ) (h : lo ≤ hi) :
    (bounds vs lo hi).1 ≤ lo ∧ hi ≤ (bounds vs lo hi).2 ∧
      (bounds vs lo hi).1 ≤ (bounds vs lo hi).2 ∧
      ∀ v ∈ vs, (bounds vs lo hi).1 ≤ v ∧ v ≤ (bounds vs lo hi).2 := by
  induction vs generalizing lo hi with
  | nil => simp [bounds, h]
  | cons v vs ih =>
    rw [bounds]
    split
    · next hv =>
      obtain ⟨h1, h2, h3, h4⟩ := ih v hi (by omega)
      refine ⟨by omega, h2, h3, fun u hu => ?_⟩
      rcases List.mem_cons.1 hu with rfl | hu
      · exact ⟨h1, by omega⟩
      · exact h4 u hu
    · split
      · next hv hv' =>
        obtain ⟨h1, h2, h3, h4⟩ := ih lo v (by omega)
        refine ⟨h1, by omega, h3, fun u hu => ?_⟩
        rcases List.mem_cons.1 hu with rfl | hu
        · exact ⟨by omega, h2⟩
        · exact h4 u hu
      · next hv hv' =>
        obtain ⟨h1, h2, h3, h4⟩ := ih lo hi h
        refine ⟨h1, h2, h3, fun u hu => ?_⟩
        rcases List.mem_cons.1 hu with rfl | hu
        · exact ⟨by omega, by omega⟩
        · exact h4 u hu

/-- Any two numbers of a list are less than its span apart. -/
theorem lt_span {vs : List ℤ} {u v : ℤ} (hu : u ∈ vs) (hv : v ∈ vs) : u - v < span vs := by
  cases vs with
  | nil => simp at hu
  | cons w ws =>
    obtain ⟨h1, h2, h3, h4⟩ := bounds_spec ws w w le_rfl
    have key : ∀ x ∈ w :: ws, (bounds ws w w).1 ≤ x ∧ x ≤ (bounds ws w w).2 := fun x hx => by
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨h1, h2⟩
      · exact h4 x hx
    have a := key u hu
    have b := key v hv
    simp only [span]
    omega

/-- The volume of the smallest box that holds all the positions. -/
def boundingVolume (ps : List Pos) : ℕ :=
  span (ps.map (·.x)) * span (ps.map (·.y)) * span (ps.map (·.z))

/-- The coordinate of a position along an axis. -/
def coord (p : Pos) : Axis → ℤ
  | .x => p.x
  | .y => p.y
  | .z => p.z

/-- A door: a level, the block that operates it, its doorway, and its timing. Whether it works
is `PistonDoor.Works`. -/
structure PistonDoor where
  /-- The contraption, closed and at rest. -/
  level : Level
  /-- The block a player uses to open and to close the door. -/
  input : Pos
  /-- The face of the input the player clicks. -/
  face : Direction
  /-- The corner of the doorway with the least coordinates. -/
  lo : Pos
  /-- The corner of the doorway with the greatest coordinates. -/
  hi : Pos
  /-- The axis along which one walks through the doorway. The doorway is one block thick in
  this direction. -/
  through : Axis
  /-- The block every cell of the doorway holds when the door is closed. -/
  door : Block
  /-- The number of game ticks from using the input until the door is open and at rest. -/
  openTicks : ℕ
  /-- The number of game ticks from using the input again until the door is closed and at
  rest. -/
  closeTicks : ℕ

namespace PistonDoor

variable (d : PistonDoor)

/-- The integers from `a` to `b`. -/
def fromTo (a b : ℤ) : List ℤ := (List.range (b - a + 1).toNat).map fun (i : ℕ) => a + (i : ℤ)

/-- The cells of the doorway: the box with corners `lo` and `hi`. -/
def doorway : List Pos :=
  (fromTo d.lo.x d.hi.x).flatMap fun x => (fromTo d.lo.y d.hi.y).flatMap fun y =>
    (fromTo d.lo.z d.hi.z).map fun z => ⟨x, y, z⟩

/-- The position lies in the way through the doorway: in the doorway, or straight in front of
it or behind it at any distance. -/
def inPassage (p : Pos) : Bool :=
  [Axis.x, Axis.y, Axis.z].all fun a =>
    a == d.through || (decide (coord d.lo a ≤ coord p a) && decide (coord p a ≤ coord d.hi a))

/-- The width and the height of the doorway: its extent along the two axes across the way
through, the horizontal one first (for a doorway in a floor, `x` and then `z`). -/
def size : ℕ × ℕ :=
  let e (a : Axis) : ℕ := (coord d.hi a - coord d.lo a + 1).toNat
  match d.through with
  | .x => (e .z, e .y)
  | .y => (e .x, e .z)
  | .z => (e .x, e .y)

/-- The doorway is a box one block thick along the way through it. -/
def WellFormed : Prop :=
  d.lo.x ≤ d.hi.x ∧ d.lo.y ≤ d.hi.y ∧ d.lo.z ≤ d.hi.z ∧ coord d.lo d.through = coord d.hi d.through

instance : Decidable d.WellFormed := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The door is closed in the level `l`: every cell of the doorway holds the door block. -/
def IsClosed (l : Level) : Prop := ∀ p ∈ d.doorway, l.blockAt p = d.door

instance (l : Level) : Decidable (d.IsClosed l) := inferInstanceAs (Decidable (∀ p ∈ _, _))

/-- The door is open in the level `l`: no cell in the way through the doorway holds a block. -/
def IsOpen (l : Level) : Prop := ∀ p, d.inPassage p = true → l.blockAt p = .AIR

/-- The test for `IsOpen` that can be evaluated: none of the finitely many cells of the level
that hold a block lies in the way. -/
def isOpen (l : Level) : Bool := l.occupied.all fun p => !d.inPassage p

theorem isOpen_iff (l : Level) : d.isOpen l = true ↔ d.IsOpen l := by
  constructor
  · intro h p hp
    by_contra hne
    have := List.all_eq_true.1 h p (Level.mem_occupied.2 hne)
    simp [hp] at this
  · intro h
    refine List.all_eq_true.2 fun p hp => ?_
    by_contra hin
    exact Level.mem_occupied.1 hp (h p (by simpa using hin))

instance (l : Level) : Decidable (d.IsOpen l) := decidable_of_iff _ (d.isOpen_iff l)

/-- The input is used, and then `n` game ticks pass. -/
def toggle (n : ℕ) : Schedule := .first [.use d.input d.face] n

/-- One opening and one closing: the input is used, `openTicks` game ticks pass, the input is
used again, and `closeTicks` game ticks pass. -/
def cycle : Schedule := d.toggle d.openTicks ++ d.toggle d.closeTicks

/-- The level after the door has been opened. -/
def opened : Level := rules.runSchedule (d.toggle d.openTicks) d.level

/-- The level after the door has been opened and closed again. -/
def closedAgain : Level := rules.runSchedule (d.toggle d.closeTicks) d.opened

theorem length_toggle (n : ℕ) : (d.toggle n).length = n := by
  cases n <;> simp [toggle, Schedule.first, Schedule.idle]

theorem length_cycle : d.cycle.length = d.openTicks + d.closeTicks := by
  simp [cycle, length_toggle]

/-- The opened level is the level after the first `openTicks` game ticks of the cycle. -/
theorem opened_eq : d.opened = rules.runSchedule (d.cycle.take d.openTicks) d.level := by
  rw [cycle, List.take_left' (d.length_toggle _), opened]

/-- The level after opening and closing is the level after the cycle. -/
theorem closedAgain_eq : d.closedAgain = rules.runSchedule d.cycle d.level := by
  rw [cycle, Rules.runSchedule_append, closedAgain, opened]

/-- **The door works**: closed and at rest; open and at rest `openTicks` game ticks after the
input is used; and `closeTicks` game ticks after it is used again, at rest with the blocks it
started with. -/
structure Works : Prop where
  /-- The doorway is a box one block thick. -/
  wellFormed : d.WellFormed
  /-- The input is not in the way. -/
  input_outside : d.inPassage d.input = false
  /-- The door block is a block. -/
  door_ne_air : d.door ≠ .AIR
  /-- The level is at rest. -/
  rest : d.level.Quiescent
  /-- The doorway is closed. -/
  closed : d.IsClosed d.level
  /-- After opening, nothing is left in the way. -/
  opens : d.IsOpen d.opened
  /-- After opening, the level is at rest. -/
  opened_rest : d.opened.Quiescent
  /-- Opening reached no bound of the model. -/
  opened_ok : d.opened.overflow = false
  /-- After closing, the blocks and block entities are those of the start. -/
  returns : d.closedAgain.SameBlocks d.level
  /-- After closing, the level is at rest. -/
  closed_rest : d.closedAgain.Quiescent
  /-- Closing reached no bound of the model. -/
  closed_ok : d.closedAgain.overflow = false

namespace Works

variable {d}

/-- After closing, the doorway is closed again. -/
theorem closes (h : d.Works) : d.IsClosed d.closedAgain := fun p hp => by
  rw [h.returns.blockAt_eq, h.closed p hp]

/-- **An opened door stays open**: as long as the input is not used, nothing comes into the
way, however many game ticks pass. -/
theorem stays_open (h : d.Works) (n : ℕ) : d.IsOpen (rules.steps n d.opened) := fun p hp => by
  rw [rules.blockAt_steps_of_quiescent h.opened_rest, h.opens p hp]

/-- **A closed door stays closed**, before it is first used. -/
theorem stays_closed (h : d.Works) (n : ℕ) : d.IsClosed (rules.steps n d.level) := fun p hp => by
  rw [rules.blockAt_steps_of_quiescent h.rest, h.closed p hp]

/-- A door that has been opened and closed stays closed. -/
theorem stays_closed_again (h : d.Works) (n : ℕ) :
    d.IsClosed (rules.steps n d.closedAgain) := fun p hp => by
  rw [rules.blockAt_steps_of_quiescent h.closed_rest, h.closes p hp]

/-- A closed door is not open: the two states of a working door differ. -/
theorem not_isOpen_level (h : d.Works) : ¬ d.IsOpen d.level := by
  intro ho
  obtain ⟨hx, hy, hz, ht⟩ := h.wellFormed
  have hmem : d.lo ∈ d.doorway := by
    have mem (a b : ℤ) (hab : a ≤ b) : a ∈ fromTo a b := by
      have hpos : 0 < (b - a + 1).toNat := by omega
      unfold fromTo
      exact List.mem_map.2 ⟨(0 : ℕ), List.mem_range.2 hpos, by simp⟩
    exact List.mem_flatMap.2 ⟨_, mem _ _ hx, List.mem_flatMap.2 ⟨_, mem _ _ hy,
      List.mem_map.2 ⟨_, mem _ _ hz, rfl⟩⟩⟩
  have hin : d.inPassage d.lo = true := by simp [inPassage, coord, hx, hy, hz]
  exact h.door_ne_air ((h.closed _ hmem).symm.trans (ho _ hin))

end Works

/-- `d` is a working door whose doorway is `w` cells wide and `h` cells high. -/
def IsPistonDoor (w h : ℕ) (d : PistonDoor) : Prop := d.size = (w, h) ∧ d.Works

/-! ### The size of a door -/

/-- The levels of one opening and closing: the level the door comes with, and the level after
each game tick of the cycle. -/
def trace : List Level :=
  (List.range (d.cycle.length + 1)).map fun k => rules.runSchedule (d.cycle.take k) d.level

/-- The trace is the list `ls`, if `ls` has the level after `k` game ticks at index `k`. -/
theorem trace_eq_of (ls : List Level) (hlen : ls.length = d.cycle.length + 1)
    (h : ∀ k (hk : k < ls.length), rules.runSchedule (d.cycle.take k) d.level = ls[k]) :
    d.trace = ls := by
  refine List.ext_getElem (by simp [trace, hlen]) fun k hk hk' => ?_
  simp [trace, h k hk']

/-- **The volume of a door**: the volume of the bounding box of every cell that holds a block
at some game tick of one opening and closing. -/
def volume : ℕ := boundingVolume (d.trace.flatMap Level.occupied)

end PistonDoor

/-- The least volume of a working door with a doorway `w` cells wide and `h` cells high (zero
if there is none). -/
noncomputable def minVolume (w h : ℕ) : ℕ :=
  sInf {v | ∃ d : PistonDoor, d.IsPistonDoor w h ∧ d.volume = v}

/-- Every working door bounds the least volume from above. -/
theorem minVolume_le {w h : ℕ} {d : PistonDoor} (hd : d.IsPistonDoor w h) :
    minVolume w h ≤ d.volume :=
  Nat.sInf_le ⟨d, hd, rfl⟩

end Contraption

end Redstone
