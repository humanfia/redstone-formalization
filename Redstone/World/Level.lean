module

public import Redstone.Basic.Random
public import Redstone.World.Basic
public import Redstone.Entity.Basic

/-!
# Levels

The full state of a world between two moments of the game (`ServerLevel`): the blocks, the
block entities, the scheduled ticks, the pending block events, the entities, the clock and the
random number generator, together with the working state of the neighbour updater.

Only one dimension is modelled, every chunk is loaded and ticking, and there are no build
limits. Fluids do not flow: there are no fluid ticks.
-/

@[expose] public section

namespace Redstone

/-- The priority of a scheduled tick (`TickPriority`). Higher priorities run first. -/
inductive TickPriority
  | extremelyHigh
  | veryHigh
  | high
  | normal
  | low
  | veryLow
  | extremelyLow
  deriving DecidableEq, Repr

namespace TickPriority

/-- The value of the priority, from `-3` (runs first) to `3` (runs last). -/
def value : TickPriority → ℤ
  | extremelyHigh => -3
  | veryHigh => -2
  | high => -1
  | normal => 0
  | low => 1
  | veryLow => 2
  | extremelyLow => 3

/-- `TickPriority.byValue`. -/
def ofValue (v : ℤ) : TickPriority :=
  if v ≤ -3 then extremelyHigh else if v = -2 then veryHigh else if v = -1 then high
  else if v = 0 then normal else if v = 1 then low else if v = 2 then veryLow else extremelyLow

end TickPriority

/-- A scheduled block tick (`ScheduledTick<Block>`). -/
structure ScheduledTick where
  pos : Pos
  /-- The block that asked for the tick. The tick does nothing if another block is there when
  it runs. -/
  block : BlockId
  /-- The game time at which the tick is due. -/
  trigger : ℕ
  priority : TickPriority
  /-- A counter that orders ticks of equal time and priority by when they were scheduled. -/
  order : ℕ
  deriving DecidableEq, Repr

namespace ScheduledTick

/-- `INTRA_TICK_DRAIN_ORDER`: by priority, then by scheduling order. -/
def intraLE (a b : ScheduledTick) : Bool :=
  a.priority.value < b.priority.value || (a.priority.value == b.priority.value && a.order ≤ b.order)

/-- `DRAIN_ORDER`: by due time, then by priority, then by scheduling order. -/
def drainLE (a b : ScheduledTick) : Bool :=
  a.trigger < b.trigger || (a.trigger == b.trigger && a.intraLE b)

/-- The chunk a tick belongs to. Ticks are queued per chunk. -/
def chunk (t : ScheduledTick) : ℤ × ℤ := (t.pos.x / 16, t.pos.z / 16)

end ScheduledTick

/-- A pending block event (`BlockEventData`), such as a piston's order to extend. -/
structure BlockEvent where
  pos : Pos
  block : BlockId
  a : ℤ
  b : ℤ
  deriving DecidableEq, Repr

/-- An entry of the neighbour updater's stack (`CollectingNeighborUpdater.NeighborUpdates`). -/
inductive NeighborUpdate
  /-- The block at `pos` is told that its neighbour in direction `dir`, at `neighborPos`, now
  has the state `neighborState`. -/
  | shape (dir : Direction) (neighborState : Block) (pos neighborPos : Pos) (flags limit : ℕ)
  /-- The block at `pos` is told that a neighbour changed; `block` is the block that changed. -/
  | simple (pos : Pos) (block : BlockId)
  /-- As `simple`, but delivered to `state` whatever is at `pos` by then. -/
  | full (state : Block) (pos : Pos) (block : BlockId) (movedByPiston : Bool)
  /-- The neighbours of `source` are told, one after the other, that `block` changed. `idx` is
  the position in `Direction.updateOrder` of the next one. -/
  | multi (source : Pos) (block : BlockId) (skip : Option Direction) (idx : ℕ)
  deriving DecidableEq, Repr

/-- The state of a world. -/
structure Level where
  /-- The block at each position. -/
  world : World
  /-- The block entity at each position. -/
  blockEntities : Pos → Option BlockEntity
  /-- The positions of the block entities that are ticked, in ticking order. -/
  blockEntityTickers : List Pos
  /-- Tickers added while block entities are being ticked; they join the list on the next tick. -/
  pendingBlockEntityTickers : List Pos
  /-- Block entities are being ticked right now. -/
  tickingBlockEntities : Bool
  /-- The scheduled ticks that are waiting. No two have the same position and block. -/
  ticks : List ScheduledTick
  /-- The scheduled ticks collected for the current game tick that have not run yet. -/
  ticksToRun : List ScheduledTick
  /-- The counter from which `ScheduledTick.order` is drawn. -/
  subTickCount : ℕ
  /-- The pending block events, in order, without repetition. -/
  blockEvents : List BlockEvent
  /-- The living entities, in the order in which they are ticked. -/
  entities : List Entity
  /-- The index the next entity will get. -/
  nextEntityIndex : ℕ
  /-- The game time: the number of game ticks the level has run. -/
  gameTime : ℕ
  /-- The level's random number generator. -/
  random : JavaRandom
  /-- The neighbour updater's stack; the head is the top. -/
  updateStack : List NeighborUpdate
  /-- The updates added while the top of the stack was running. -/
  updatesAdded : List NeighborUpdate
  /-- The number of updates added since the updater started running; zero when it is idle. -/
  updateCount : ℕ
  /-- Set when a computation was cut short because a bound of the model was reached: the
  nesting depth of block reactions or the length of a loop. A level with this flag is not a
  faithful image of the game any more. -/
  overflow : Bool
  /-- The containers whose menu the player of the `use` actions has open (`containerMenu`): the
  positions of the chests or the barrel on which closing the menu will call `stopOpen`. Empty
  when the player has no menu open, or one whose container does not count its viewers. -/
  playerMenu : List Pos := []

namespace Level

/-- The level with no blocks, no entities and nothing pending, at game time zero. -/
def empty : Level where
  world := .empty
  blockEntities := fun _ => none
  blockEntityTickers := []
  pendingBlockEntityTickers := []
  tickingBlockEntities := false
  ticks := []
  ticksToRun := []
  subTickCount := 0
  blockEvents := []
  entities := []
  nextEntityIndex := 0
  gameTime := 0
  random := .ofSeed 0
  updateStack := []
  updatesAdded := []
  updateCount := 0
  overflow := false

instance : Inhabited Level := ⟨empty⟩

/-- The block at `p` (`getBlockState`). -/
def blockAt (l : Level) (p : Pos) : Block := l.world.blockAt p

/-- Replaces the block at `p` and nothing else: no reactions, no updates. -/
def setBlockRaw (l : Level) (p : Pos) (b : Block) : Level := { l with world := l.world.set p b }

/-- `hasScheduledTick`: a tick of `block` at `p` is waiting. Ticks collected for the current
game tick do not count. -/
def hasScheduledTick (l : Level) (p : Pos) (block : BlockId) : Bool :=
  l.ticks.any fun t => t.pos == p && t.block == block

/-- `willTickThisTick`: a tick of `block` at `p` was collected for the current game tick and has
not run yet. -/
def willTickThisTick (l : Level) (p : Pos) (block : BlockId) : Bool :=
  l.ticksToRun.any fun t => t.pos == p && t.block == block

/-- The entity with the given index, if it is alive. -/
def entity? (l : Level) (index : ℕ) : Option Entity := l.entities.find? (·.index == index)

end Level

/-! ### The order in which due ticks run -/

namespace ScheduledTick

/-- Inserts a tick into a queue sorted by `drainLE`. -/
def insertSorted (t : ScheduledTick) : List ScheduledTick → List ScheduledTick
  | [] => [t]
  | u :: us => if t.drainLE u then t :: u :: us else u :: insertSorted t us

/-- Adds a tick to the queue of its chunk, creating the queue if needed. -/
def addToQueues (t : ScheduledTick) :
    List ((ℤ × ℤ) × List ScheduledTick) → List ((ℤ × ℤ) × List ScheduledTick)
  | [] => [(t.chunk, [t])]
  | (c, q) :: qs => if c = t.chunk then (c, insertSorted t q) :: qs else (c, q) :: addToQueues t qs

/-- The queue whose first tick comes first in `intraLE`, and the other queues. Empty queues are
dropped. -/
def pickQueue : List (List ScheduledTick) → Option (List ScheduledTick × List (List ScheduledTick))
  | [] => none
  | [] :: qs => pickQueue qs
  | (t :: ts) :: qs =>
    match pickQueue qs with
    | none => some (t :: ts, [])
    | some ([], rest) => some (t :: ts, rest)
    | some (u :: us, rest) =>
      if t.intraLE u then some (t :: ts, (u :: us) :: rest) else some (u :: us, (t :: ts) :: rest)

/-- Splits a queue into its longest prefix of ticks that come no later than `bound`. -/
def takeUpTo (bound : Option ScheduledTick) :
    List ScheduledTick → List ScheduledTick × List ScheduledTick
  | [] => ([], [])
  | t :: ts =>
    if bound.all t.intraLE then
      let (a, b) := takeUpTo bound ts
      (t :: a, b)
    else ([], t :: ts)

/-- Merges the per-chunk queues of due ticks as `LevelTicks.drainContainers` does: take the
queue whose head comes first, drain it for as long as its head does not come after the head of
the next best queue, and repeat. -/
def mergeQueues : ℕ → List (List ScheduledTick) → List ScheduledTick
  | 0, _ => []
  | fuel + 1, qs =>
    match pickQueue qs with
    | none => []
    | some ([], _) => []
    | some (t :: ts, rest) =>
      let bound := (pickQueue rest).bind fun (q, _) => q.head?
      let (taken, left) := takeUpTo bound ts
      t :: taken ++ mergeQueues fuel (left :: rest)

/-- The ticks among `ticks` that are due at time `now`, in the order in which the game runs
them. When every due tick is due exactly at `now` this is the order of `intraLE`; ticks that
are overdue are favoured only within their own chunk. -/
def dueInOrder (now : ℕ) (ticks : List ScheduledTick) : List ScheduledTick :=
  let due := ticks.filter (·.trigger ≤ now)
  let queues := due.foldl (fun qs t => addToQueues t qs) []
  mergeQueues due.length (queues.map (·.2))

end ScheduledTick

end Redstone
