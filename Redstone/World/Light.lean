module

public import Redstone.World.Level
public import Redstone.Block.FaceShape
public import Redstone.Component.Sensor.Sky

/-!
# Light

Java classes: `LightEngine`, `BlockLightEngine`, `SkyLightEngine`, `ChunkSkyLightSources`,
`LevelLightEngine`, `BlockAndLightGetter`, `LevelReader`, `Shapes` (`faceShapeOccludes`),
`BlockBehaviour` (`getLightDampening`, `useShapeForLightOcclusion`, `getOcclusionShape`).

The game keeps two numbers from 0 to 15 for every cell: its *block light*, which comes from the
blocks that emit light, and its *sky light*. The light engine maintains them incrementally,
with queues of increases and decreases. This file describes directly what the engine
converges to, and computes it where it is asked for: nothing is stored, and neither `setBlock`
nor `Level.tick` computes any light.

## The light of a cell

Both kinds of light obey the same rule (`propagateIncrease`). Every cell has a level of its
own, its *source level*:

* for block light, the light the block emits (`getLightEmission`);
* for sky light, 15 if the cell is a *source*, a cell that the light of the sky reaches
  straight from above (`ChunkSkyLightSources`), and 0 otherwise.

Light passes from a cell into a neighbour unless the two shapes that meet at the face between
them close it (`shapeOccludes`), and on entering a cell it loses the *opacity* of that cell:
its light dampening, but at least 1 (`getOpacity`). The level of a cell is the largest of its
source level and of what reaches it from its neighbours. So it is the largest value of
`source level of c - loss of the path` over all cells `c` and all paths from `c` to the cell,
where the loss of a path is the sum of the opacities of the cells it enters. `search` finds it,
going backwards from the cell, by increasing loss.

A block that is `isSolidRender` has dampening 15: no light enters it, and its level is what it
emits itself (a lit redstone lamp has block light 15, and lights its neighbours with 14).

## Shapes

Whether a face lets light pass is decided by the *occlusion shapes* of the two blocks
(`LightEngine.getOcclusionShape`): the shape of a block that occludes and has
`useShapeForLightOcclusion` (slabs, stairs, piston bases and heads, daylight detectors,
farmland, snow layers, ...), and the empty shape for every other block, among them all full
cubes, which stop light by their dampening instead. The face is closed when the parts of the
two shapes that touch it cover it together (`Shapes.faceShapeOccludes`): the top of a bottom
slab lets light pass, its bottom does not, and the side of a bottom slab next to the side of a
top slab does not either.

The dampening and the occlusion shape of every block state are read from the server
(`Attrs.lightDampening`, `Attrs.lightOcclusion`), so every override of `getLightDampening` and
`propagatesSkylightDown` is the game's: tinted glass stops light, leaves, ice and water take
one level, glass, stained glass, copper grates, panes and fences take none.

## When light is read

In the game the light engine runs on a thread of its own, and it is only started when the main
thread runs its queued tasks (`ServerChunkCache.MainThreadExecutor.pollTask`), which it does
between two game ticks; the recording harness waits there until the engine is idle. So light
read during a game tick is the light of the world as it was when the tick began, after the
actions of the scenario: `Level.lightWorld`, which `Level.tick` sets. A block that changes
during a tick changes the light of the next tick.

## What is left out

* The world is the overworld: there is a sky, and its light comes from above every block.
* The engine stores light only in chunk sections that are next to a section with a block in
  it. A cell that is asked for its light is next to such a section in every use the model
  makes of it, and no path of at most 14 cells from an emitter leaves them, so this does not
  show in block light. For sky light the engine fills the sections without storage from above
  and from the sides (`propagateFromEmptySections`); the model takes the result to be the one
  of the rule above.
* Chunks that are not loaded count as bedrock for the engine; the model has no chunks.

`tests/pending/scenarios/sensor/dd-roof-rod-water` (a daylight detector under a waterlogged
lightning rod) still waits: the water of the rod flows, and fluids do not flow in the model yet.
-/

@[expose] public section

namespace Redstone

namespace Light

/-- The index of the full cube in the shape table of the block dump; index 0 is the empty
shape. -/
def fullBlockShape : ℕ := 1

/-- `BlockState.getLightDampening`. -/
def lightDampening (b : Block) : ℕ := b.attrs.lightDampening

/-- `LightEngine.getOpacity`: what light loses on entering the block. -/
def opacity (b : Block) : ℕ := max 1 b.attrs.lightDampening

/-- The block does not let light in: `LightEngine.getOpacity` is 15. -/
def isOpaque (b : Block) : Bool := decide (15 ≤ b.attrs.lightDampening)

/-- `Shapes.faceShapeOccludes(shape, occluder)`, for the faces in direction `d` of the shape
number `i` and in the opposite direction of the shape number `j`: the two face shapes cover
the face between them. A full cube closes the face alone, two empty shapes never do. Otherwise
the face is closed when no point of the unit cube lies outside both face shapes. -/
def faceShapeOccludes (i j : ℕ) (d : Direction) : Bool :=
  if i == 0 && j == 0 then false
  else if i == fullBlockShape || j == fullBlockShape then true
  else
    let first := (FaceShape.ofIndex i).faceShape d
    let second := (FaceShape.ofIndex j).faceShape d.opposite
    FaceShape.subset .block (.ofBoxes (first.boxes ++ second.boxes))

/-- `LightEngine.shapeOccludes(fromState, toState, direction)`: light does not pass from a cell
with the block `fromBlock` to its neighbour in direction `d`, which holds `toBlock`. -/
def shapeOccludes (fromBlock toBlock : Block) (d : Direction) : Bool :=
  faceShapeOccludes fromBlock.attrs.lightOcclusion toBlock.attrs.lightOcclusion d

/-- The number of steps between two cells. -/
def distance (p q : Pos) : ℕ := (p.x - q.x).natAbs + (p.y - q.y).natAbs + (p.z - q.z).natAbs

/-- Adds the cell `p` to the list number `i` of `buckets`. -/
def addAt : List (List Pos) → ℕ → Pos → List (List Pos)
  | [], 0, p => [[p]]
  | [], i + 1, p => [] :: addAt [] i p
  | b :: bs, 0, p => (p :: b) :: bs
  | b :: bs, i + 1, p => b :: addAt bs i p

/-- The level of a cell, found by going backwards along the paths of the light that reaches it.

`source` gives the source level of a cell. `loss` is the loss that is being looked at, `best`
the best level found with a smaller loss, `seen` the cells that have been reached with a
smaller loss, and the list number `i` of `buckets` holds cells from which light reaches the
cell with a loss of `loss + i`. `keep n k` may be false only for a cell `n` through which no
light can arrive when the loss from `n` on is `k`; it prunes the search.

Light that arrives with a loss of more than `loss` has a level of at most `14 - loss`, which
ends the search as soon as `best` is that large; so it never looks beyond a loss of 14, and
`fuel = 15` is enough. -/
def search (w : World) (source : Pos → ℕ) (keep : Pos → ℕ → Bool) :
    ℕ → ℕ → ℕ → PosMap Unit → List (List Pos) → ℕ
  | 0, _, best, _, _ => best
  | fuel + 1, loss, best, seen, buckets =>
    let (bucket, rest) : List Pos × List (List Pos) :=
      match buckets with
      | [] => ([], [])
      | b :: bs => (b, bs)
    -- The cells of the bucket that were not reached with a smaller loss, each once.
    let (seen, current) := bucket.foldl
      (fun (acc : PosMap Unit × List Pos) c =>
        if (acc.1 c).isSome then acc else (acc.1.insert c (), c :: acc.2))
      (seen, [])
    let best := current.foldl (fun best c => max best (source c - loss)) best
    if best + loss + 1 ≥ 15 then best
    else
      let rest := current.foldl
        (fun bs c =>
          let here := w.blockAt c
          let next := loss + opacity here
          if next > 14 then bs
          else
            Direction.values.foldl
              (fun bs d =>
                let n := c.step d
                if (seen n).isNone && !shapeOccludes (w.blockAt n) here d.opposite && keep n next
                then addAt bs (next - loss - 1) n
                else bs)
              bs)
        rest
      if rest.all List.isEmpty then best else search w source keep fuel (loss + 1) best seen rest

/-! ### The cells of a world

Block light starts from the cells that emit light, and the sky is open above the highest block,
so both computations go through the cells of the world once. `World.toList` gives them, but it
finds the position of a cell from its key with `Nat.sqrt`, which is defined by well-founded
recursion: the kernel cannot evaluate it, and a proof by evaluation would stop there. `cells`
is the same list (`cells_eq`), with the positions found by a square root the kernel can run. -/

/-- The loop of `isqrt`: the root of `n` lies in `[lo, hi)`, and the interval is halved until
it has one number. -/
def isqrtLoop (n : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then lo
    else
      let mid := (lo + hi) / 2
      if mid * mid ≤ n then isqrtLoop n fuel mid hi else isqrtLoop n fuel lo mid

/-- The integer square root of `n`, by bisection. Nothing relies on this being the root:
`posOfKey` checks what it derives from it. -/
def isqrt (n : ℕ) : ℕ := isqrtLoop n (n.log2 / 2 + 2) 0 (2 ^ (n.log2 / 2 + 1))

/-- `Nat.unpair`, with `isqrt` for the square root. -/
def unpair (n : ℕ) : ℕ × ℕ :=
  let s := isqrt n
  if n - s * s < s then (n - s * s, s) else (s, n - s * s - s)

/-- `Pos.ofKey`: the position that the key `k` stands for. The position is computed with
`isqrt` and then checked against the key, so the result is right whatever `isqrt` does. -/
def posOfKey (k : ℕ) : Pos :=
  let a := unpair k
  let b := unpair a.2
  let p : Pos := ⟨Pos.unzigzag a.1, Pos.unzigzag b.1, Pos.unzigzag b.2⟩
  if p.key = k then p else Pos.ofKey k

theorem posOfKey_eq (k : ℕ) : posOfKey k = Pos.ofKey k := by
  simp only [posOfKey]
  split_ifs with h
  · simpa using congrArg Pos.ofKey h
  · rfl

/-- The cells of the world that are not air: `World.toList`. -/
def cells (w : World) : List (Pos × Block) := w.cells.tree.toList.map fun e => (posOfKey e.1, e.2)

theorem cells_eq (w : World) : cells w = w.toList := by
  simp [cells, World.toList, PosMap.toList, posOfKey_eq]

/-! ### Block light -/

/-- The cells that emit light, with what they emit. -/
def emitters (w : World) : List (Pos × ℕ) :=
  (cells w).filterMap fun (q, b) => if b.attrs.light = 0 then none else some (q, b.attrs.light)

/-- `getBrightness(LightLayer.BLOCK, pos)`: the block light of the cell `p` in the world `w`.

Light of an emitter that is `n` steps away has lost at least `n`, so only the emitters that are
near enough matter, and the search only follows cells from which one of them can still be
reached with light to spare. -/
def blockLight (w : World) (p : Pos) : ℕ :=
  let near := (emitters w).filter fun e => distance e.1 p < e.2
  if near.isEmpty then 0
  else
    search w (fun c => (w.blockAt c).attrs.light)
      (fun n k => near.any fun e => k + distance n e.1 < e.2) 15 0 0 .empty [[p]]

/-! ### Sky light -/

/-- `ChunkSkyLightSources.isEdgeOccluded(topState, bottomState)`: the light of the sky does not
go on from a cell with the block `top` to the cell below it, with the block `bottom`. -/
def isEdgeOccluded (top bottom : Block) : Bool :=
  bottom.attrs.lightDampening != 0 || shapeOccludes top bottom .down

/-- The height of the highest cell that is not air, or `floor` if there is none above it. -/
def topY (w : World) (floor : ℤ) : ℤ := (cells w).foldl (fun y c => max y c.1.y) floor

/-- The cell `p` is a source of sky light: `p.y` is at least `getLowestSourceY` of its column.
Going down from the sky to `p`, no edge between two cells is occluded. `top` is a height above
which every cell is air; the edges above it are open. -/
def isSource (w : World) (top : ℤ) (p : Pos) : Bool :=
  (List.range (top + 1 - p.y).toNat).all fun i =>
    !isEdgeOccluded (w.blockAt ⟨p.x, p.y + i + 1, p.z⟩) (w.blockAt ⟨p.x, p.y + i, p.z⟩)

/-- `getBrightness(LightLayer.SKY, pos)`: the sky light of the cell `p` in the world `w`, as
the light engine stores it, before the time of day and the weather darken it. -/
def skyLight (w : World) (p : Pos) : ℕ :=
  let top := topY w p.y
  search w (fun c => if isSource w top c then 15 else 0) (fun _ _ => true) 15 0 0 .empty [[p]]

end Light

namespace Level

/-- `Level.getSkyDarken`: how much the time of day and the weather take from the light of the
sky. The game computes it with `float`s (`Redstone.Component.Sensor.Sky`). -/
def getSkyDarken (l : Level) : ℕ := Component.Sensor.Sky.skyDarken l.dayTime l.weather

/-- `getBrightness(LightLayer.BLOCK, pos)`: the block light of the cell `p`, as the light
engine has it during this game tick: the light of `Level.lightWorld`. A level that is built by
hand and asked for light before its first tick must have `lightWorld` set to its `world`. -/
def blockLight (l : Level) (p : Pos) : ℕ := Light.blockLight l.lightWorld p

/-- `getBrightness(LightLayer.SKY, pos)`: the sky light of the cell `p`, as the light engine
has it during this game tick. -/
def skyLight (l : Level) (p : Pos) : ℕ := Light.skyLight l.lightWorld p

/-- `BlockAndLightGetter.getRawBrightness(pos, darkening)`: the larger of the block light of the
cell `p` and its sky light less `skyDarken`. The darkening is only looked at where it matters:
not where the block light is 15, and not where there is no sky light. -/
def rawBrightness (l : Level) (p : Pos) (skyDarken : ℕ := 0) : ℕ :=
  let block := l.blockLight p
  if block ≥ 15 then block
  else
    let sky := l.skyLight p
    if sky = 0 then block else max block (sky - skyDarken)

/-- `LevelReader.getMaxLocalRawBrightness(pos)`: `rawBrightness` with the darkening of the sky
at this time and in this weather (`Level.getSkyDarken`). -/
def maxLocalRawBrightness (l : Level) (p : Pos) : ℕ := l.rawBrightness p l.getSkyDarken

end Level

end Redstone
