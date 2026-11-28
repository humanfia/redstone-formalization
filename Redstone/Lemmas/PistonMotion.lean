module

public import Redstone.Mechanics.PistonMotion

/-!
# Lemmas about piston motion

Generic facts about `Redstone.PistonMotion`, the model of `PistonStructureResolver` and of
`PistonBaseBlock.isPushable`, over an arbitrary level. The theorems about concrete structures
(slime, honey, the flying machine) are in `Redstone/Theorems/PistonStructure`.

* **Which blocks stick** (`canStickToEachOther`): the table. Slime sticks to everything but
  honey, honey to everything but slime, and two blocks of which neither is slime or honey do
  not stick (`canStickToEachOther_slime`, `canStickToEachOther_honey`,
  `canStickToEachOther_of_not_sticky`); the relation is symmetric (`canStickToEachOther_comm`).
* **Which blocks can be moved** (`isPushable`): `isPushable_eq` reads the answer off the
  attributes of a block that is not air and not a piston base, strictly inside the build
  height; its corollaries are the cases a builder knows: an immovable block never moves
  (`isPushable_of_immoveable`, `isPushable_obsidian`), a block that can only be pushed moves
  only when it is in the line of the push and is not dragged sideways by a slime block
  (`isPushable_of_push_only`, `isPushable_glazedTerracotta`); a piston base moves exactly
  when it is retracted (`isPushable_pistonBase`).
* **The resolver** (`resolve`), for a piston that extends:
  * nothing in front: it extends and moves nothing (`resolve_extending_of_isAir`);
  * a block in front that cannot be moved: it does not extend
    (`resolve_extending_of_not_pushable`), or it destroys the block if the block is one that
    pistons break (`resolve_extending_destroys`);
  * **the push limit**: a straight line of `k` blocks, none of them slime or honey, with air
    behind the last. For `1 ≤ k ≤ 12` the piston extends and moves exactly these blocks,
    listed from the piston outwards (`resolve_extending_line`); thirteen such blocks in front
    of the piston stop it (`resolve_extending_line_too_long`).

Left out, and why:

* The resolver on a structure with slime or honey over an arbitrary level: which blocks are
  dragged, and that the limit of twelve counts the whole structure. `addBranchingBlocks`
  starts lines that reorder `toPush` when they meet (`reorderListAtCollision`); a statement
  that covers this would be the definition again. For concrete structures it is proved by
  evaluation (`Redstone/Theorems/PistonStructure/SlimeStructure.lean`, `PushLimit.lean`).
* A piston that retracts (the pull of a sticky piston). The resolver then starts two cells in
  front of the piston and walks towards it; the lemmas about `walkForward` and
  `resolveBranches` here are stated for any direction of the push, but `resolve` itself is
  only treated for a piston that extends.
* `hashMapOrder`, the order in which the cells left empty are cleared.
-/

@[expose] public section

namespace Redstone.PistonMotion

/-- An `if` whose condition is false. -/
private theorem ite_right {α : Sort _} {c : Prop} [Decidable c] (a b : α) (h : c = False) :
    (if c then a else b) = b := by
  simp [h]

/-- An `if` whose condition is true. -/
private theorem ite_left {α : Sort _} {c : Prop} [Decidable c] (a b : α) (h : c = True) :
    (if c then a else b) = a := by
  simp [h]

/-! ### Which blocks stick -/

/-- The sticky blocks are the slime block and the honey block. -/
theorem isSticky_iff (b : Block) :
    isSticky b = true ↔ b.id = .slime_block ∨ b.id = .honey_block := by
  simp [isSticky, Block.is]

/-- No block is both a slime block and a honey block. -/
theorem not_slime_and_honey (b : Block) :
    ¬(b.is .slime_block = true ∧ b.is .honey_block = true) := by
  simp only [Block.is, beq_iff_eq]
  rintro ⟨h, h'⟩
  rw [h] at h'
  cases h'

/-- Sticking is symmetric. -/
theorem canStickToEachOther_comm (a b : Block) :
    canStickToEachOther a b = canStickToEachOther b a := by
  unfold canStickToEachOther isSticky
  cases a.is .honey_block <;> cases a.is .slime_block <;> cases b.is .honey_block <;>
    cases b.is .slime_block <;> rfl

/-- **A slime block sticks to every block but honey.** (Whether the neighbour is then dragged
along also depends on `isPushable`.) -/
theorem canStickToEachOther_slime {a : Block} (ha : a.is .slime_block = true) (b : Block) :
    canStickToEachOther a b = !b.is .honey_block := by
  have ha' : a.is .honey_block = false := by
    cases h : a.is .honey_block
    · rfl
    · exact absurd ⟨ha, h⟩ (not_slime_and_honey a)
  unfold canStickToEachOther isSticky
  rw [ha, ha']
  cases b.is .honey_block <;> cases b.is .slime_block <;> rfl

/-- **A honey block sticks to every block but slime.** -/
theorem canStickToEachOther_honey {a : Block} (ha : a.is .honey_block = true) (b : Block) :
    canStickToEachOther a b = !b.is .slime_block := by
  have ha' : a.is .slime_block = false := by
    cases h : a.is .slime_block
    · rfl
    · exact absurd ⟨h, ha⟩ (not_slime_and_honey a)
  unfold canStickToEachOther isSticky
  rw [ha, ha']
  cases b.is .honey_block <;> cases b.is .slime_block <;> rfl

/-- **Slime and honey do not stick to each other.** -/
theorem canStickToEachOther_slime_honey {a b : Block} (ha : a.is .slime_block = true)
    (hb : b.is .honey_block = true) :
    canStickToEachOther a b = false ∧ canStickToEachOther b a = false := by
  rw [← canStickToEachOther_comm a b, canStickToEachOther_slime ha, hb]
  exact ⟨rfl, rfl⟩

/-- Two blocks of which neither is slime or honey do not stick. -/
theorem canStickToEachOther_of_not_sticky {a b : Block} (ha : isSticky a = false)
    (hb : isSticky b = false) : canStickToEachOther a b = false := by
  simp only [isSticky, Bool.or_eq_false_iff] at ha hb
  unfold canStickToEachOther isSticky
  rw [ha.1, ha.2, hb.1, hb.2]
  rfl

/-! ### Which blocks can be moved -/

/-- Air can always be "moved": an empty cell inside the build height does not stop a piston. -/
theorem isPushable_of_isAir {state : Block} (h : state.isAir = true) {pos : Pos}
    (hlo : minY ≤ pos.y) (hhi : pos.y ≤ maxY) (d : Direction) (a : Bool) (c : Direction) :
    isPushable state pos d a c = true := by
  unfold isPushable
  rw [ite_right _ _ (eq_false (by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)),
    ite_left _ _ (eq_true h)]

/-- **What `isPushable` answers for an ordinary block.** A block that is not air and not a
piston base, strictly inside the build height, can be moved in direction `d` if it is not
unbreakable and its reaction to pistons allows it: never if it is immovable; if it is broken
by pistons, only where the caller accepts that (`a`); if it can only be pushed, only when it
is reached along the push (`d = c`, where `c` is the direction in which the resolver came to
the block); otherwise if it has no block entity. -/
theorem isPushable_eq {state : Block} {pos : Pos} (hair : state.isAir = false)
    (hbase : ∀ id s, state ≠ .pistonBase id s) (hlo : minY < pos.y) (hhi : pos.y < maxY)
    (d : Direction) (a : Bool) (c : Direction) :
    isPushable state pos d a c =
      (!state.attrs.unbreakable &&
        match state.attrs.push with
        | .immoveable => false
        | .popped => a
        | .push => decide (d = c)
        | _ => !state.hasBlockEntity) := by
  unfold isPushable
  rw [ite_right _ _ (eq_false (by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)),
    ite_right _ _ (eq_false (by simp [hair])),
    ite_right _ _ (eq_false (by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; rintro ⟨-, h⟩; omega)),
    ite_right _ _ (eq_false (by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; rintro ⟨-, h⟩; omega))]
  split
  · exact absurd rfl (hbase _ _)
  · cases state.attrs.unbreakable <;> rfl

/-- An immovable block (obsidian, for instance) is never moved, from any side. -/
theorem isPushable_of_immoveable {state : Block} {pos : Pos} (hair : state.isAir = false)
    (hbase : ∀ id s, state ≠ .pistonBase id s) (hlo : minY < pos.y) (hhi : pos.y < maxY)
    (hpush : state.attrs.push = .immoveable) (d : Direction) (a : Bool) (c : Direction) :
    isPushable state pos d a c = false := by
  rw [isPushable_eq hair hbase hlo hhi, hpush, Bool.and_false]

/-- **A block that can only be pushed** (glazed terracotta) is moved exactly when the resolver
reaches it along the push. A slime block beside it reaches it sideways, so it stays behind. -/
theorem isPushable_of_push_only {state : Block} {pos : Pos} (hair : state.isAir = false)
    (hbase : ∀ id s, state ≠ .pistonBase id s) (hlo : minY < pos.y) (hhi : pos.y < maxY)
    (hbreak : state.attrs.unbreakable = false) (hpush : state.attrs.push = .push)
    (d : Direction) (a : Bool) (c : Direction) :
    isPushable state pos d a c = decide (d = c) := by
  rw [isPushable_eq hair hbase hlo hhi, hpush, hbreak]
  rfl

/-- A block that pistons break is "movable" only for a caller that accepts to break it: the
block in the line of the push, not a block beside a slime block. -/
theorem isPushable_of_popped {state : Block} {pos : Pos} (hair : state.isAir = false)
    (hbase : ∀ id s, state ≠ .pistonBase id s) (hlo : minY < pos.y) (hhi : pos.y < maxY)
    (hbreak : state.attrs.unbreakable = false) (hpush : state.attrs.push = .popped)
    (d : Direction) (a : Bool) (c : Direction) :
    isPushable state pos d a c = a := by
  rw [isPushable_eq hair hbase hlo hhi, hpush, hbreak]
  rfl

/-- An ordinary block (stone, slime, honey, an observer) is moved from any side. -/
theorem isPushable_of_push_pull {state : Block} {pos : Pos} (hair : state.isAir = false)
    (hbase : ∀ id s, state ≠ .pistonBase id s) (hlo : minY < pos.y) (hhi : pos.y < maxY)
    (hbreak : state.attrs.unbreakable = false) (hpush : state.attrs.push = .push_pull)
    (hbe : state.hasBlockEntity = false) (d : Direction) (a : Bool) (c : Direction) :
    isPushable state pos d a c = true := by
  rw [isPushable_eq hair hbase hlo hhi, hpush, hbreak, hbe]
  rfl

/-- What does not move for a caller that breaks blocks does not move for one that does not:
the flag only adds the blocks that pistons break. -/
theorem isPushable_true_of_false {state : Block} {pos : Pos} {d c : Direction}
    (h : isPushable state pos d false c = true) : isPushable state pos d true c = true := by
  unfold isPushable at h ⊢
  repeat' split at h
  all_goals try cases h
  all_goals repeat' split
  all_goals first | rfl | assumption | simp_all

/-- A piston base is moved exactly when it is retracted: an extended piston stays where it
is, whatever pushes or pulls it. -/
theorem isPushable_pistonBase (id : Blocks.PistonBase.Id) (s : Blocks.PistonBase) {pos : Pos}
    (hlo : minY < pos.y) (hhi : pos.y < maxY) (d : Direction) (a : Bool) (c : Direction) :
    isPushable (.pistonBase id s) pos d a c = !s.extended := by
  have hair : (Block.pistonBase id s).isAir = false := by
    cases id <;> rcases s with ⟨_ | _, _ | _ | _ | _ | _ | _⟩ <;> rfl
  have hbe : (Block.pistonBase id s).hasBlockEntity = false := by
    cases id <;> rcases s with ⟨_ | _, _ | _ | _ | _ | _ | _⟩ <;> rfl
  unfold isPushable
  rw [ite_right _ _ (eq_false (by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)),
    ite_right _ _ (eq_false (by simp [hair])),
    ite_right _ _ (eq_false (by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; rintro ⟨-, h⟩; omega)),
    ite_right _ _ (eq_false (by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; rintro ⟨-, h⟩; omega))]
  simp only [hbe, Bool.not_false, Bool.and_true]

/-! ### The blocks of the usual structures -/

theorem isSticky_slime_block : isSticky (.plain .slime_block) = true := rfl

theorem isSticky_honey_block : isSticky (.plain .honey_block) = true := rfl

/-- Slime and honey, the two blocks themselves, do not stick to each other. -/
theorem canStickToEachOther_slime_block_honey_block :
    canStickToEachOther (.plain .slime_block) (.plain .honey_block) = false ∧
      canStickToEachOther (.plain .honey_block) (.plain .slime_block) = false :=
  ⟨rfl, rfl⟩

/-- Obsidian is never moved: not pushed, not pulled, not dragged by slime or honey. -/
theorem isPushable_obsidian {pos : Pos} (hlo : minY < pos.y) (hhi : pos.y < maxY)
    (d : Direction) (a : Bool) (c : Direction) :
    isPushable (.plain .obsidian) pos d a c = false :=
  isPushable_of_immoveable rfl (fun _ _ h => by cases h) hlo hhi rfl d a c

/-- **Glazed terracotta is pushed but never dragged.** It moves exactly when the resolver
reaches it along the push; slime or honey beside it, which reach it sideways, leave it. -/
theorem isPushable_glazedTerracotta (id : Blocks.GlazedTerracotta.Id)
    (s : Blocks.GlazedTerracotta) {pos : Pos} (hlo : minY < pos.y) (hhi : pos.y < maxY)
    (d : Direction) (a : Bool) (c : Direction) :
    isPushable (.glazedTerracotta id s) pos d a c = decide (d = c) :=
  isPushable_of_push_only (by cases id <;> rcases s with ⟨_ | _ | _ | _⟩ <;> rfl)
    (fun _ _ h => by cases h) hlo hhi (by cases id <;> rcases s with ⟨_ | _ | _ | _⟩ <;> rfl)
    (by cases id <;> rcases s with ⟨_ | _ | _ | _⟩ <;> rfl) d a c

/-! ### Positions along a line -/

/-- The coordinate of `p` along the direction `d`: it grows by one with every step in that
direction. -/
def along (d : Direction) (p : Pos) : ℤ :=
  match d with
  | .east => p.x
  | .west => -p.x
  | .up => p.y
  | .down => -p.y
  | .south => p.z
  | .north => -p.z

theorem along_step (d : Direction) (p : Pos) : along d (p.step d) = along d p + 1 := by
  cases d <;> simp only [along, Pos.step] <;> omega

theorem along_relative (d : Direction) (p : Pos) (n : ℕ) :
    along d (relative p d n) = along d p + n := by
  induction n generalizing p with
  | zero => simp [relative]
  | succ n ih =>
    rw [relative, ih, along_step]
    push_cast
    omega

/-- The positions `relative p d 0`, `relative p d 1`, ... are distinct. -/
theorem relative_injective (p : Pos) (d : Direction) : Function.Injective (relative p d) := by
  intro m n h
  have h' := congrArg (along d) h
  rw [along_relative, along_relative] at h'
  omega

/-! ### The resolver -/

/-- **A block that cannot be moved stops the piston.** If the block in front of the piston is
not pushable and is not one that pistons break, the piston does not extend. Obsidian, an
extended piston and a block with a block entity are such blocks. -/
theorem resolve_extending_of_not_pushable (level : Level) (pistonPos : Pos) (direction : Direction)
    (h : isPushable (level.blockAt (pistonPos.step direction)) (pistonPos.step direction)
      direction false direction = false)
    (h' : (level.blockAt (pistonPos.step direction)).attrs.push ≠ .popped) :
    resolve level pistonPos direction true = (false, {}) := by
  simp [resolve, h, h']

/-- **A block that pistons break is destroyed.** If the block in front of the piston is one
that pistons break, the piston extends, moves nothing and destroys that block. -/
theorem resolve_extending_destroys (level : Level) (pistonPos : Pos) (direction : Direction)
    (h : isPushable (level.blockAt (pistonPos.step direction)) (pistonPos.step direction)
      direction false direction = false)
    (h' : (level.blockAt (pistonPos.step direction)).attrs.push = .popped) :
    resolve level pistonPos direction true =
      (true, { toDestroy := [pistonPos.step direction] }) := by
  simp [resolve, h, h']

namespace ResolverCtx

variable (c : ResolverCtx)

/-- `x >>= f` in the state monad of the resolver, applied to a state. -/
theorem bind_apply {α β : Type} (x : StateM Resolver α) (f : α → StateM Resolver β)
    (r : Resolver) : (x >>= f) r = f (x r).1 (x r).2 := rfl

/-- `get` in the state monad of the resolver, applied to a state. -/
theorem get_apply (r : Resolver) : (get : StateM Resolver Resolver) r = (r, r) := rfl

/-- An empty cell ends a line at once: `addBlockLine` adds nothing. -/
theorem addBlockLine_of_isAir (fuel : ℕ) (start : Pos) (d : Direction) (r : Resolver)
    (h : (c.level.blockAt start).isAir = true) :
    c.addBlockLine (fuel + 1) start d r = (true, r) := by
  rw [addBlockLine]
  dsimp only
  rw [ite_left _ _ (eq_true h)]
  rfl

/-- **Without slime or honey there is nothing to branch from**: if no block of `toPush` is
sticky, the loop of `resolve` over `toPush` adds nothing. -/
theorem resolveBranches_of_not_sticky (r : Resolver)
    (h : ∀ p ∈ r.toPush, isSticky (c.level.blockAt p) = false) :
    ∀ fuel i, 0 < fuel → r.toPush.length < fuel + i → c.resolveBranches fuel i r = (true, r)
  | 0, _, h0, _ => absurd h0 (Nat.lt_irrefl 0)
  | fuel + 1, i, _, hf => by
    rw [resolveBranches, bind_apply, get_apply]
    dsimp only
    cases hi : r.toPush[i]? with
    | none => rfl
    | some pos =>
      have hlt : i < r.toPush.length := by
        by_contra hge
        rw [List.getElem?_eq_none (Nat.le_of_not_gt hge)] at hi
        cases hi
      have hs := h pos (List.mem_of_getElem? hi)
      dsimp only
      rw [ite_right _ _ (eq_false (by simp [hs]))]
      exact resolveBranches_of_not_sticky r h fuel (i + 1) (by omega) (by omega)

/-- The block at `q` is an ordinary link of a line that the resolver walks along: it is not
air, not slime or honey, it can be pushed in the direction of the push, pistons do not break
it, and it is not the piston itself. Stone is such a block; so is a retracted piston. -/
def Movable (q : Pos) : Prop :=
  (c.level.blockAt q).isAir = false ∧ isSticky (c.level.blockAt q) = false ∧
    isPushable (c.level.blockAt q) q c.pushDirection false c.pushDirection = true ∧
    (c.level.blockAt q).attrs.push ≠ .popped ∧ q ≠ c.pistonPos

/-- **Walking along a line that ends in air.** Let the first `k` cells from `start` in the
direction of the push hold ordinary blocks, let the next cell be empty, and let `toPush` hold
the first `i` of them. Then `walkForward` adds the others, in order, and succeeds, as long as
`k` is at most twelve. -/
theorem walkForward_line (line : Pos → Direction → StateM Resolver Bool) (start : Pos) (k : ℕ)
    (hk : k ≤ maxPushDepth)
    (hmov : ∀ i < k, c.Movable (relative start c.pushDirection i))
    (hair : (c.level.blockAt (relative start c.pushDirection k)).isAir = true) :
    ∀ fuel i (r : Resolver), i ≤ k → k < fuel + i →
      r.toPush = (List.range i).map (relative start c.pushDirection) →
      c.walkForward line start fuel i i r =
        (true, { r with toPush := (List.range k).map (relative start c.pushDirection) })
  | 0, i, _, hi, hf, _ => absurd hf (by omega)
  | fuel + 1, i, r, hi, hf, hr => by
    have hnot : ¬ r.toPush.idxOf (relative start c.pushDirection i) < r.toPush.length := by
      rw [List.idxOf_lt_length_iff, hr, List.mem_map]
      rintro ⟨j, hj, e⟩
      have := relative_injective start c.pushDirection e
      rw [List.mem_range] at hj
      omega
    rw [walkForward, bind_apply, get_apply]
    dsimp only
    rw [ite_right _ _ (eq_false hnot)]
    rcases Nat.eq_or_lt_of_le hi with heq | hlt
    · subst heq
      rw [ite_left _ _ (eq_true hair), ← hr]
      rfl
    · obtain ⟨h₁, -, h₃, h₄, h₅⟩ := hmov i hlt
      have hlen : ¬ r.toPush.length ≥ maxPushDepth := by
        rw [hr, List.length_map, List.length_range]
        omega
      rw [ite_right _ _ (eq_false (by simp [h₁])),
        ite_right _ _ (eq_false (by simp [isPushable_true_of_false h₃, h₅])),
        ite_right _ _ (eq_false h₄), ite_right _ _ (eq_false hlen)]
      exact walkForward_line line start k hk hmov hair fuel (i + 1)
        { r with toPush := r.toPush ++ [relative start c.pushDirection i] } (by omega) (by omega)
        (by
          change r.toPush ++ [_] = _
          rw [hr, List.range_succ, List.map_append]
          rfl)

/-- **The push limit.** If the first thirteen cells from `start` in the direction of the push
hold ordinary blocks and `toPush` holds the first `i` of them, `walkForward` fails: the
thirteenth block is one too many. -/
theorem walkForward_line_too_long (line : Pos → Direction → StateM Resolver Bool) (start : Pos)
    (hmov : ∀ i ≤ maxPushDepth, c.Movable (relative start c.pushDirection i)) :
    ∀ fuel i (r : Resolver), i ≤ maxPushDepth → maxPushDepth < fuel + i →
      r.toPush = (List.range i).map (relative start c.pushDirection) →
      (c.walkForward line start fuel i i r).1 = false
  | 0, i, _, hi, hf, _ => absurd hf (by omega)
  | fuel + 1, i, r, hi, hf, hr => by
    have hnot : ¬ r.toPush.idxOf (relative start c.pushDirection i) < r.toPush.length := by
      rw [List.idxOf_lt_length_iff, hr, List.mem_map]
      rintro ⟨j, hj, e⟩
      have := relative_injective start c.pushDirection e
      rw [List.mem_range] at hj
      omega
    obtain ⟨h₁, -, h₃, h₄, h₅⟩ := hmov i hi
    rw [walkForward, bind_apply, get_apply]
    dsimp only
    rw [ite_right _ _ (eq_false hnot),
      ite_right _ _ (eq_false (by simp [h₁])),
      ite_right _ _ (eq_false (by simp [isPushable_true_of_false h₃, h₅])),
      ite_right _ _ (eq_false h₄)]
    rcases Nat.eq_or_lt_of_le hi with heq | hlt
    · have hlen : r.toPush.length ≥ maxPushDepth := by
        rw [hr, List.length_map, List.length_range, heq]
      rw [ite_left _ _ (eq_true hlen)]
      rfl
    · have hlen : ¬ r.toPush.length ≥ maxPushDepth := by
        rw [hr, List.length_map, List.length_range]
        omega
      rw [ite_right _ _ (eq_false hlen)]
      exact walkForward_line_too_long line start hmov fuel (i + 1)
        { r with toPush := r.toPush ++ [relative start c.pushDirection i] } (by omega) (by omega)
        (by
          change r.toPush ++ [_] = _
          rw [hr, List.range_succ, List.map_append]
          rfl)

/-- The first step of `addBlockLine` on an ordinary block, from an empty resolver: the block
is added, nothing is dragged along behind it, and the walk forward starts. -/
theorem addBlockLine_of_movable (fuel : ℕ) (start : Pos) (h : c.Movable start) :
    c.addBlockLine (fuel + 1) start c.pushDirection {} =
      c.walkForward (c.addBlockLine fuel) start (maxPushDepth + 2) 1 1 { toPush := [start] } := by
  obtain ⟨h₁, h₂, h₃, -, h₅⟩ := h
  have hc : ∀ n, c.countBehind start n (maxPushDepth + 1) (c.level.blockAt start) 1 = some 1 := by
    intro n
    rw [show maxPushDepth + 1 = 12 + 1 from rfl, countBehind]
    simp [h₂]
  rw [addBlockLine]
  dsimp only
  rw [ite_right _ _ (eq_false (by simp [h₁])),
    ite_right _ _ (eq_false (by simp [h₃])),
    ite_right _ _ (eq_false h₅), bind_apply, get_apply]
  dsimp only
  rw [ite_right _ _ (eq_false (by simp)),
    ite_right _ _ (eq_false (by decide)), hc]
  rfl

end ResolverCtx

/-- **Nothing in front.** A piston with an empty cell in front of it extends and moves
nothing. -/
theorem resolve_extending_of_isAir (level : Level) (pistonPos : Pos) (direction : Direction)
    (hair : (level.blockAt (pistonPos.step direction)).isAir = true)
    (hlo : minY ≤ (pistonPos.step direction).y) (hhi : (pistonPos.step direction).y ≤ maxY) :
    resolve level pistonPos direction true = (true, {}) := by
  have hp := isPushable_of_isAir hair hlo hhi direction false direction
  unfold resolve
  simp only [ite_true, hp, Bool.not_true, Bool.false_eq_true, ite_false]
  change ((ResolverCtx.addBlockLine ⟨level, pistonPos, direction⟩ (maxPushDepth + 3 + 1)
    (pistonPos.step direction) direction >>= _) {}) = _
  rw [ResolverCtx.bind_apply, ResolverCtx.addBlockLine_of_isAir _ _ _ _ _ hair]
  rfl

/-- **A straight line within the limit.** Let the `k` cells in front of the piston hold
ordinary blocks (`ResolverCtx.Movable`: not air, not slime or honey, pushable, not broken by
pistons), with `1 ≤ k ≤ 12`, and let the cell after them be empty. Then the piston extends,
destroys nothing, and moves exactly these `k` blocks, listed from the piston outwards. -/
theorem resolve_extending_line (level : Level) (pistonPos : Pos) (direction : Direction) (k : ℕ)
    (hk₀ : 0 < k) (hk : k ≤ maxPushDepth)
    (hmov : ∀ i < k, ResolverCtx.Movable ⟨level, pistonPos, direction⟩
      (relative (pistonPos.step direction) direction i))
    (hair : (level.blockAt (relative (pistonPos.step direction) direction k)).isAir = true) :
    resolve level pistonPos direction true =
      (true, { toPush := (List.range k).map (relative (pistonPos.step direction) direction) }) := by
  have h0 := hmov 0 hk₀
  have hp : isPushable (level.blockAt (pistonPos.step direction)) (pistonPos.step direction)
      direction false direction = true := h0.2.2.1
  have hadd : ResolverCtx.addBlockLine ⟨level, pistonPos, direction⟩ (maxPushDepth + 3 + 1)
      (pistonPos.step direction) direction {} =
        (true, ⟨List.map (relative (pistonPos.step direction) direction) (List.range k), [],
          false⟩) :=
    (ResolverCtx.addBlockLine_of_movable ⟨level, pistonPos, direction⟩
      (maxPushDepth + 3) _ h0).trans
      (ResolverCtx.walkForward_line ⟨level, pistonPos, direction⟩ _ _ k hk hmov hair
        (maxPushDepth + 2) 1 { toPush := [pistonPos.step direction] } hk₀
        (by have : maxPushDepth = 12 := rfl; omega) rfl)
  unfold resolve
  simp only [ite_true, hp, Bool.not_true, Bool.false_eq_true, ite_false]
  change ((ResolverCtx.addBlockLine ⟨level, pistonPos, direction⟩ (maxPushDepth + 3 + 1)
    (pistonPos.step direction) direction >>= _) {}) = _
  rw [ResolverCtx.bind_apply, hadd]
  dsimp only
  rw [ite_right _ _ (eq_false (by simp))]
  refine ResolverCtx.resolveBranches_of_not_sticky ⟨level, pistonPos, direction⟩ _ ?_
    (maxPushDepth + 2) 0 (by decide) ?_
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    exact (hmov i (List.mem_range.mp hi)).2.1
  · change ((List.range k).map _).length < _
    rw [List.length_map, List.length_range]
    have : maxPushDepth = 12 := rfl
    omega

/-- **Thirteen blocks are one too many.** If the thirteen cells in front of the piston hold
ordinary blocks, the piston does not extend. -/
theorem resolve_extending_line_too_long (level : Level) (pistonPos : Pos) (direction : Direction)
    (hmov : ∀ i ≤ maxPushDepth, ResolverCtx.Movable ⟨level, pistonPos, direction⟩
      (relative (pistonPos.step direction) direction i)) :
    (resolve level pistonPos direction true).1 = false := by
  have h0 := hmov 0 (Nat.zero_le _)
  have hp : isPushable (level.blockAt (pistonPos.step direction)) (pistonPos.step direction)
      direction false direction = true := h0.2.2.1
  have hadd : ResolverCtx.addBlockLine ⟨level, pistonPos, direction⟩ (maxPushDepth + 3 + 1)
      (pistonPos.step direction) direction {} =
        ResolverCtx.walkForward ⟨level, pistonPos, direction⟩
          (ResolverCtx.addBlockLine ⟨level, pistonPos, direction⟩ (maxPushDepth + 3))
          (pistonPos.step direction) (maxPushDepth + 2) 1 1
          { toPush := [pistonPos.step direction] } :=
    ResolverCtx.addBlockLine_of_movable ⟨level, pistonPos, direction⟩ (maxPushDepth + 3) _ h0
  have hwalk := ResolverCtx.walkForward_line_too_long ⟨level, pistonPos, direction⟩
    (ResolverCtx.addBlockLine ⟨level, pistonPos, direction⟩ (maxPushDepth + 3)) _ hmov
    (maxPushDepth + 2) 1 { toPush := [pistonPos.step direction] } (by decide) (by decide) rfl
  unfold resolve
  simp only [ite_true, hp, Bool.not_true, Bool.false_eq_true, ite_false]
  change ((ResolverCtx.addBlockLine ⟨level, pistonPos, direction⟩ (maxPushDepth + 3 + 1)
    (pistonPos.step direction) direction >>= _) {}).1 = _
  rw [ResolverCtx.bind_apply, hadd, hwalk]
  rw [ite_left _ _ (eq_true (by simp))]
  rfl

end Redstone.PistonMotion
