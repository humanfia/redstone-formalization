import Redstone.Mechanics.Dispatch
import Redstone.Mechanics.Input

/-!
# Building the level of a circuit, and what to observe in it

`Level.ofCells` builds a level from a list of blocks. It is a *raw load*, as the test harness
loads a scenario: the blocks are put in place without any reaction, at game time zero, with
nothing scheduled. A theorem about such a level says what happens from there; whether the
level is at rest to begin with is a separate fact (`Level.Quiescent`, or an idle tick that
leaves the blocks alone).

The observations are the decidable facts a theorem states about a level: the block at a
position (`Level.blockAt`, `Level.blocksAt`), the signal a position receives (`Level.powered`,
`Level.signalTo`, `Level.emits`), the scheduled ticks relative to the game time
(`Level.pending`), the block entity (`l.blockEntities p`, `Level.itemCount`), and that the
model did not hit one of its bounds (`l.overflow = false`, which every theorem should state).

Write block states with their constructors (`.lever ⟨.floor, .north, false⟩`) or with
`blk% "minecraft:lever[...]"` (`Redstone.Proof.Tactic`), never with `Block.parse?`: parsing is
string processing, which the kernel does slowly.

Left out: entities. A level built here has none.
-/

namespace Redstone

namespace Level

/-- The entries of a list of cells that are not replaced by a later entry for the same
position, in order. -/
def lastCells : List (Pos × Block) → List (Pos × Block)
  | [] => []
  | c :: cs => if cs.any (·.1 == c.1) then lastCells cs else c :: lastCells cs

/-- The level with the given blocks and nothing else, at game time zero: a raw load.

A later entry of `cells` for the same position replaces an earlier one. Every block that has a
block entity gets a fresh one (`BehaviourOf.newBlockEntity`), unless `blockEntities` gives one
for its position; an entry of `blockEntities` at a position whose block has no block entity is
ignored. The block entities that the game ticks (`BehaviourOf.ticksBlockEntity`, a hopper for
instance) are ticked in the order in which their blocks are listed. `lightWorld` is set to the
blocks, as it is after any game tick. -/
def ofCells (cells : List (Pos × Block)) (blockEntities : List (Pos × BlockEntity) := []) :
    Level :=
  let cells := lastCells cells
  let world := World.ofList cells
  let fresh := cells.filterMap fun c => (rules.block c.2).newBlockEntity.map fun be => (c.1, be)
  let given := blockEntities.filter fun e => (world.blockAt e.1).hasBlockEntity
  { Level.empty with
    world
    lightWorld := world
    blockEntities := PosMap.ofList (fresh ++ given)
    blockEntityTickers := (cells.filter fun c => (rules.block c.2).ticksBlockEntity).map (·.1) }

/-- The blocks at the positions `ps`, in order. -/
def blocksAt (l : Level) (ps : List Pos) : List Block := ps.map l.blockAt

/-- `hasNeighborSignal(pos)` under the rules of the game: some neighbour of `p` gives it a
signal. -/
def powered (l : Level) (p : Pos) : Bool := l.hasNeighborSignalAt (rules.env maxDepth) p

/-- `getBestNeighborSignal(pos)` under the rules of the game: the strongest signal a neighbour
gives to `p`. -/
def signalTo (l : Level) (p : Pos) : ℕ := l.bestNeighborSignalAt (rules.env maxDepth) p

/-- `getSignal(pos, direction)` under the rules of the game: the signal the block at `p` gives
to its neighbour in the direction opposite to `d`. -/
def emits (l : Level) (p : Pos) (d : Direction) : ℕ := l.signalAt (rules.env maxDepth) p d

/-- The power of the redstone dust at `p`; zero if there is no dust. -/
def dustPower (l : Level) (p : Pos) : ℕ :=
  match l.blockAt p with
  | .redstoneWire w => w.power.val
  | _ => 0

/-- The scheduled block ticks in the order in which they will run, with the number of game
ticks until each is due instead of its absolute time. A tick with delay `d` runs in the `d`-th
game tick from now (one that is overdue has delay zero and runs in the next). -/
def pending (l : Level) : List (Pos × BlockId × ℕ × TickPriority) :=
  (ScheduledTickOf.sortTicks l.ticks).map fun t =>
    (t.pos, t.block, t.trigger - l.gameTime, t.priority)

/-- The number of items in the hopper at `p`; zero if there is no hopper. -/
def itemCount (l : Level) (p : Pos) : ℕ :=
  match l.blockEntities p with
  | some (.hopper d) => (d.items.map (·.count)).sum
  | _ => 0

end Level

end Redstone
