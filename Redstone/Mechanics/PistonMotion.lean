module

public import Redstone.Mechanics.Tick

/-!
# Piston motion

Java classes: `PistonStructureResolver`, and `PistonBaseBlock.isPushable`.

Which blocks a piston moves when it extends or retracts: the line of blocks in front of it, at
most twelve, the blocks that slime and honey blocks drag along, the blocks that are destroyed
instead of moved, and the order in which the game lists them (which is the order in which it
then moves them and sends updates).

The resolver only reads the level. Its two lists are kept in `Resolver`, and its methods are
state transformers on it.

Also here: the iteration order of the `java.util.HashMap` in which `PistonBaseBlock.moveBlocks`
keeps the positions that the moved blocks leave empty. That order is observable, since the
positions are cleared and updated in it.

## What is left out

* The world border (`isPushable` refuses positions outside it).
* A `HashMap` bin that is turned into a tree. This needs nine positions among at most twelve
  whose hashes agree in their low six bits; `hashMapOrder` reports it instead of guessing.
-/

@[expose] public section

namespace Redstone

namespace PistonMotion

/-- `Level.getMinY()` of the overworld. -/
def minY : ℤ := -64

/-- `Level.getMaxY()` of the overworld. -/
def maxY : ℤ := 319

/-- `MAX_PUSH_DEPTH`: the number of blocks a piston can move. -/
def maxPushDepth : ℕ := 12

/-- `pos.relative(direction, n)`. -/
def relative (p : Pos) (d : Direction) : ℕ → Pos
  | 0 => p
  | n + 1 => relative (p.step d) d n

/-- `PistonBaseBlock.isPushable(state, level, pos, direction, allowDestroyable,
connectionDirection)`: the block `state` at `pos` can be moved in `direction`. The world border
is not checked. -/
def isPushable (state : Block) (pos : Pos) (direction : Direction) (allowDestroyable : Bool)
    (connectionDirection : Direction) : Bool :=
  if pos.y < minY || pos.y > maxY then false
  else if state.isAir then true
  else if direction = .down && pos.y = minY then false
  else if direction = .up && pos.y = maxY then false
  else
    match state with
    | .pistonBase _ s => !s.extended && !state.hasBlockEntity
    | _ =>
      if state.attrs.unbreakable then false
      else
        match state.attrs.push with
        | .immoveable => false
        | .popped => allowDestroyable
        | .push => direction = connectionDirection
        | _ => !state.hasBlockEntity

/-- `PistonStructureResolver.isSticky`. -/
def isSticky (state : Block) : Bool := state.is .slime_block || state.is .honey_block

/-- `PistonStructureResolver.canStickToEachOther`. -/
def canStickToEachOther (state1 state2 : Block) : Bool :=
  if state1.is .honey_block && state2.is .slime_block then false
  else if state1.is .slime_block && state2.is .honey_block then false
  else isSticky state1 || isSticky state2

/-- The lists of a `PistonStructureResolver`. -/
structure Resolver where
  /-- `toPush`: the positions of the blocks to move, in the order in which they were found. -/
  toPush : List Pos := []
  /-- `toDestroy`: the positions of the blocks to destroy. -/
  toDestroy : List Pos := []
  /-- A bound of the model was reached. This does not happen; see `resolveFuel`. -/
  overflow : Bool := false
  deriving Repr

/-- The fixed data of a `PistonStructureResolver`. -/
structure ResolverCtx where
  /-- The level, which the resolver only reads. -/
  level : Level
  /-- `pistonPos`. -/
  pistonPos : Pos
  /-- `pushDirection`: the direction in which the blocks move. -/
  pushDirection : Direction

namespace ResolverCtx

/-- `reorderListAtCollision(blocksAdded, collisionPos)`: moves the last `blocksAdded` entries of
`toPush` in front of the entry at `collisionPos`. -/
def reorderListAtCollision (blocksAdded collisionPos : ℕ) : StateM Resolver Unit :=
  modify fun r =>
    let n := r.toPush.length
    let head := r.toPush.take collisionPos
    let lastLineAdded := r.toPush.drop (n - blocksAdded)
    let collisionToLine := (r.toPush.take (n - blocksAdded)).drop collisionPos
    { r with toPush := head ++ lastLineAdded ++ collisionToLine }

variable (c : ResolverCtx)

/-- `addBranchingBlocks(fromPos)`, with `addBlockLine` given as `line`: starts a line at every
neighbour, sideways to the push, that sticks to the block at `fromPos`. -/
def addBranchingBlocks (line : Pos → Direction → StateM Resolver Bool) (fromPos : Pos) :
    StateM Resolver Bool := do
  let fromState := c.level.blockAt fromPos
  for direction in Direction.values do
    if direction.axis ≠ c.pushDirection.axis then
      let neighbourPos := fromPos.step direction
      let neighbourState := c.level.blockAt neighbourPos
      if canStickToEachOther neighbourState fromState then
        if !(← line neighbourPos direction) then return false
  return true

/-- The first loop of `addBlockLine`: counts the blocks behind `start` that are dragged along,
each sticking to the one before. `nextState` is the block `blockCount - 1` steps behind `start`.
Returns `none` if the push limit is exceeded. The first argument bounds the number of steps;
every step counts one more block and the limit is twelve, so thirteen steps are never used
up. -/
def countBehind (start : Pos) (pushed : ℕ) : ℕ → Block → ℕ → Option ℕ
  | 0, _, blockCount => some blockCount
  | fuel + 1, nextState, blockCount =>
    if !isSticky nextState then some blockCount
    else
      let pos := relative start c.pushDirection.opposite blockCount
      let previousState := nextState
      let nextState := c.level.blockAt pos
      if nextState.isAir || !canStickToEachOther previousState nextState
          || !isPushable nextState pos c.pushDirection false c.pushDirection.opposite
          || pos = c.pistonPos then
        some blockCount
      else if blockCount + 1 + pushed > maxPushDepth then none
      else countBehind start pushed fuel nextState (blockCount + 1)

/-- The loop of `addBlockLine` that runs `addBranchingBlocks` on the entries `j .. last` of
`toPush`. The list is read again at every step, because branching may reorder it. -/
def branchUpTo (line : Pos → Direction → StateM Resolver Bool) (last : ℕ) :
    ℕ → ℕ → StateM Resolver Bool
  | 0, _ => return true
  | fuel + 1, j => do
    if j > last then return true
    let some blockPos := (← get).toPush[j]? | return true
    if isSticky (c.level.blockAt blockPos) then
      if !(← c.addBranchingBlocks line blockPos) then return false
    branchUpTo line last fuel (j + 1)

/-- The second loop of `addBlockLine`: walks forward from `start`, adding the blocks in the way
until it finds air, a block that is destroyed, a block already in the list, or an obstacle. -/
def walkForward (line : Pos → Direction → StateM Resolver Bool) (start : Pos) :
    ℕ → ℕ → ℕ → StateM Resolver Bool
  | 0, _, _ => do
    modify fun r => { r with overflow := true }
    return false
  | fuel + 1, blocksAdded, i => do
    let posx := relative start c.pushDirection i
    let r ← get
    let collisionPos := r.toPush.idxOf posx
    if collisionPos < r.toPush.length then
      reorderListAtCollision blocksAdded collisionPos
      c.branchUpTo line (collisionPos + blocksAdded) (collisionPos + blocksAdded + 1) 0
    else
      let nextState := c.level.blockAt posx
      if nextState.isAir then return true
      if !isPushable nextState posx c.pushDirection true c.pushDirection || posx = c.pistonPos then
        return false
      if nextState.attrs.push = .popped then
        modify fun r => { r with toDestroy := r.toDestroy ++ [posx] }
        return true
      if r.toPush.length ≥ maxPushDepth then return false
      modify fun r => { r with toPush := r.toPush ++ [posx] }
      walkForward line start fuel (blocksAdded + 1) (i + 1)

/-- `addBlockLine(start, direction)`: adds the block at `start`, the blocks it drags along
behind it and the blocks in front of it. Returns false when the structure cannot move. The
first argument bounds the nesting of lines started from sticky blocks. -/
def addBlockLine : ℕ → Pos → Direction → StateM Resolver Bool
  | 0, _, _ => do
    modify fun r => { r with overflow := true }
    return false
  | fuel + 1, start, direction => do
    let nextState := c.level.blockAt start
    if nextState.isAir then return true
    if !isPushable nextState start c.pushDirection false direction then return true
    if start = c.pistonPos then return true
    let r ← get
    if r.toPush.contains start then return true
    if 1 + r.toPush.length > maxPushDepth then return false
    let some blockCount := c.countBehind start r.toPush.length (maxPushDepth + 1) nextState 1
      | return false
    let line := (List.range blockCount).reverse.map (relative start c.pushDirection.opposite)
    modify fun r => { r with toPush := r.toPush ++ line }
    c.walkForward (addBlockLine fuel) start (maxPushDepth + 2) blockCount 1

/-- The bound on the nesting of `addBlockLine`. A nested call that does not return at once has
added a block to `toPush` in each of the calls around it, and `toPush` holds at most twelve
positions, so the nesting never exceeds thirteen. -/
def resolveFuel : ℕ := maxPushDepth + 4

/-- The loop of `resolve` over `toPush`, which grows while it runs. -/
def resolveBranches : ℕ → ℕ → StateM Resolver Bool
  | 0, _ => do
    modify fun r => { r with overflow := true }
    return false
  | fuel + 1, i => do
    let some pos := (← get).toPush[i]? | return true
    if isSticky (c.level.blockAt pos) then
      if !(← c.addBranchingBlocks (c.addBlockLine resolveFuel) pos) then return false
    resolveBranches fuel (i + 1)

end ResolverCtx

/-- `new PistonStructureResolver(level, pistonPos, direction, extending).resolve()`: whether
the piston at `pistonPos` facing `direction` can move, and the blocks it moves and destroys. -/
def resolve (level : Level) (pistonPos : Pos) (direction : Direction) (extending : Bool) :
    Bool × Resolver :=
  let pushDirection := if extending then direction else direction.opposite
  let startPos := if extending then pistonPos.step direction else relative pistonPos direction 2
  let c : ResolverCtx := ⟨level, pistonPos, pushDirection⟩
  let nextState := level.blockAt startPos
  if !isPushable nextState startPos pushDirection false direction then
    if extending && nextState.attrs.push = .popped then (true, { toDestroy := [startPos] })
    else (false, {})
  else
    let run : StateM Resolver Bool := do
      if !(← c.addBlockLine ResolverCtx.resolveFuel startPos pushDirection) then return false
      c.resolveBranches (maxPushDepth + 2) 0
    run.run {}

/-! ### The order of a `HashMap` of positions -/

/-- `Vec3i.hashCode()` followed by `HashMap.hash`: the 32-bit hash under which a `HashMap`
files a position. -/
def javaHash (p : Pos) : ℕ :=
  let h := (((p.y + p.z * 31) * 31 + p.x) % (2 ^ 32)).toNat
  h ^^^ (h >>> 16)

/-- The number of buckets of a `HashMap` into which `keys` were put in order, starting from the
default sixteen, or `none` if one of its bins was turned into a tree. The table doubles when a
key is added to a bin that already holds eight (`treeifyBin` on a table of fewer than 64
buckets) and when it holds more than three quarters as many keys as buckets. -/
def hashMapCapacity (keys : List Pos) : Option ℕ :=
  (keys.foldl
    (fun (acc : Option (ℕ × List Pos)) k => do
      let (n, before) ← acc
      let bin := (before.filter fun q => javaHash q % n = javaHash k % n).length
      let n ← if bin ≥ 8 then (if n < 64 then some (2 * n) else none) else some n
      let n := if 4 * (before.length + 1) > 3 * n then 2 * n else n
      pure (n, before ++ [k]))
    (some (16, []))).map (·.1)

/-- The order in which a `java.util.HashMap` iterates over `keys`, distinct positions that were
put into it in the given order: by bucket, and within a bucket in the order of insertion.
Removing keys does not change the order of the others. Returns `none` if a bin was turned into
a tree, whose order is not modelled. -/
def hashMapOrder (keys : List Pos) : Option (List Pos) := do
  let n ← hashMapCapacity keys
  pure <| (List.range n).flatMap fun b => keys.filter fun k => javaHash k % n = b

end PistonMotion

end Redstone
