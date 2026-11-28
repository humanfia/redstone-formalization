module

public import Redstone.Mechanics.Update
public import Redstone.Component.Weathering

/-!
# Random ticks

`ServerChunkCache.tickChunks` with `ServerLevel.tickChunk`: in every game tick, for every
ticking chunk in turn, the game

1. draws `random_tick_speed` times `nextInt(48)` from the level's random number generator and,
   on a zero, picks a column of the chunk with `getBlockRandomPos` for the precipitation
   (`tickPrecipitation`: ice and snow forming, cauldrons filling);
2. goes through the sections of the chunk from the bottom, and gives every section that holds a
   randomly ticking block `random_tick_speed` random ticks: a position drawn with
   `getBlockRandomPos` (which advances `Level.randValue`, a generator of its own), then
   `randomTick` of the block there if it `isRandomlyTicking`, then `randomTick` of its fluid.

The phase runs between the fluid ticks and the block events (`Level.tick`). With the game rule
at zero it does nothing at all (`Level.tickChunks_of_speed_zero`): nothing is drawn.

## The chunks, and their order

What a random tick does depends on what the generators gave to the chunks ticked before, so
the model has to know which chunks tick and in which order, although it has no chunks
otherwise. The game goes through `DistanceManager.simulationChunkTracker.chunks`, a fastutil
`Long2ByteOpenHashMap` from packed chunk positions to ticket levels, in the order of its table
(`forEachEntityTickingChunk`), and that order depends on how the table was filled.

The model takes the world of the test harness (`tests/FORMAT.md`): the chunks with x and z from
-8 to 15 are force-loaded once, in the order of the two nested loops, x outside. Every
`ServerLevel.setChunkForced` puts the chunk into the table with level 31 and then its eight
neighbours with level 32 where they are not in it yet (`ChunkTracker`, run by the `getChunk`
that follows the ticket). `ChunkTable` is the hash table with the insertion and the growth of
fastutil, `harnessTable` the table filled this way, and `tickingChunks` its entries of level
31 in the order of the game's iteration. The result was compared with the table of a running
server, entry by entry (676 entries in 1024 slots), and the recorded scenarios of
`tests/scenarios/random-tick` that span several chunks depend on it.

A level with other loaded chunks, or loaded in another order, ticks in another order; the model
cannot express that (there is no such field in `Level`).

## What ticks

The blocks that can get a random tick are those inside `Level.randomTickBox`; a chunk that does
not meet the box only draws. The sections are those of the overworld, y from -64 to 319. When
the box reaches beyond the ticking chunks, or a position drawn outside the box holds a block
that would get a random tick, `Level.overflow` is set.

A block's random tick is `Component.Weathering.randomTick` for copper (by block id), and the
`randomTick` of its behaviour for every other block. A block that gets random ticks in the game
and whose behaviour defines none sets `Level.overflow` (`Behaviour.inert`).

## Left out

* Precipitation does nothing: the biome of the harness world, `the_void`, has none and never
  freezes. Only the draws are made.
* The random tick of a fluid (`LavaFluid.randomTick`, lava setting fire to what is around it)
  is not modelled: when lava gets one, `Level.overflow` is set
  (`tests/pending/scenarios/random-tick/lava-pit.json`).
* Thunder and mob spawning, which the game does in the same pass, need a player nearby
  (`collectSpawningChunks`); there is none.
-/

@[expose] public section

namespace Redstone

namespace RandomTick

/-! ### The table of ticking chunks -/

/-- `ChunkPos.pack(x, z)`. -/
def packChunk (x z : ℤ) : UInt64 :=
  let lo : UInt64 := (x % 2 ^ 32).toNat.toUInt64
  let hi : UInt64 := (z % 2 ^ 32).toNat.toUInt64
  lo ||| (hi <<< 32)

/-- The low 32 bits of `v` as a Java `int`. -/
def toInt32 (v : UInt64) : ℤ :=
  let n := (v &&& 0xFFFFFFFF).toNat
  if n < 2 ^ 31 then n else (n : ℤ) - 2 ^ 32

/-- `ChunkPos.unpack(key)`: the x and the z of the chunk. -/
def unpackChunk (key : UInt64) : ℤ × ℤ := (toInt32 key, toInt32 (key >>> 32))

/-- `HashCommon.mix(long)` of fastutil. -/
def mix (x : UInt64) : UInt64 :=
  let h := x * 0x9E3779B97F4A7C15
  let h := h ^^^ (h >>> 32)
  h ^^^ (h >>> 16)

/-- A `Long2ByteOpenHashMap` with load factor 0.75: open addressing with linear probing in a
table of `n` slots, `n` a power of two. The key 0 marks a free slot; the entry of the key 0 is
kept apart (`containsNullKey`, the slot `n` of the game's arrays). -/
structure ChunkTable where
  n : ℕ := 16
  key : Array UInt64 := Array.replicate 16 0
  value : Array ℕ := Array.replicate 16 0
  /-- The number of entries with a key other than 0. -/
  realSize : ℕ := 0
  /-- The value of the key 0, when it is in the map. -/
  nullValue : Option ℕ := none

namespace ChunkTable

/-- `size`. -/
def size (t : ChunkTable) : ℕ := t.realSize + (if t.nullValue.isSome then 1 else 0)

/-- `HashCommon.maxFill(n, 0.75)`. -/
def maxFill (n : ℕ) : ℕ := min ((3 * n + 3) / 4) (n - 1)

/-- The slot of `k`, or the free slot where it would go: linear probing from `pos`. -/
def probe (t : ChunkTable) (k : UInt64) : ℕ → ℕ → ℕ
  | 0, pos => pos
  | fuel + 1, pos =>
    let cur : UInt64 := t.key[pos]!
    if cur = 0 ∨ cur = k then pos else probe t k fuel ((pos + 1) % t.n)

/-- The home slot of `k` in a table of `n` slots. -/
def home (n : ℕ) (k : UInt64) : ℕ := (mix k).toNat % n

/-- `rehash(newN)`: the entries are moved into a table of `newN` slots, in the order of the old
table from its last slot down. -/
def rehash (t : ChunkTable) (newN : ℕ) : ChunkTable :=
  let empty : ChunkTable :=
    { n := newN, key := Array.replicate newN 0, value := Array.replicate newN 0
      realSize := t.realSize, nullValue := t.nullValue }
  (List.range t.n).reverse.foldl (init := empty) fun acc i =>
    let k : UInt64 := t.key[i]!
    if k = 0 then acc
    else
      let pos := acc.probe k newN (home newN k)
      { acc with key := acc.key.set! pos k, value := acc.value.set! pos t.value[i]! }

/-- `HashCommon.arraySize(expected, 0.75)`: the least power of two that is at least
`expected / 0.75`, and at least 2. -/
def arraySize (expected : ℕ) : ℕ := max 2 (2 ^ Nat.clog 2 ((4 * expected + 2) / 3))

/-- The end of `insert`: `if (size++ >= maxFill) rehash(arraySize(size + 1, f))`, for a table
whose size has been increased already. -/
def grow (t : ChunkTable) : ChunkTable :=
  if t.size - 1 ≥ maxFill t.n then t.rehash (arraySize (t.size + 1)) else t

/-- `put(k, v)`. -/
def put (t : ChunkTable) (k : UInt64) (v : ℕ) : ChunkTable :=
  if k = 0 then
    if t.nullValue.isSome then { t with nullValue := some v }
    else grow { t with nullValue := some v }
  else
    let pos := t.probe k t.n (home t.n k)
    if t.key[pos]! = k then { t with value := t.value.set! pos v }
    else
      grow { t with
        key := t.key.set! pos k, value := t.value.set! pos v, realSize := t.realSize + 1 }

/-- `containsKey(k)`. -/
def contains (t : ChunkTable) (k : UInt64) : Bool :=
  if k = 0 then t.nullValue.isSome else t.key[t.probe k t.n (home t.n k)]! = k

/-- The entries in the order of `Long2ByteMaps.fastIterable`: the key 0 first, then the table
from its last slot down. -/
def entries (t : ChunkTable) : List (UInt64 × ℕ) :=
  (t.nullValue.map fun v => ((0 : UInt64), v)).toList ++
    (List.range t.n).reverse.filterMap fun i =>
      let k : UInt64 := t.key[i]!
      if k = 0 then none else some (k, t.value[i]!)

end ChunkTable

/-- `ChunkMap.FORCED_TICKET_LEVEL`, the level of a force-loaded chunk: entity ticking. -/
def forcedTicketLevel : ℕ := 31

/-- `ServerLevel.setChunkForced(x, z, true)` as the simulation chunk tracker sees it: the chunk
gets the level of the ticket, and each of its eight neighbours that has none gets the next
level (`ChunkTracker.checkNeighborsAfterUpdate`, x outside, z inside). -/
def forceChunk (t : ChunkTable) (x z : ℤ) : ChunkTable :=
  let offsets : List ℤ := [-1, 0, 1]
  offsets.foldl (init := t.put (packChunk x z) forcedTicketLevel) fun t dx =>
    offsets.foldl (init := t) fun t dz =>
      let k := packChunk (x + dx) (z + dz)
      if (dx = 0 ∧ dz = 0) ∨ t.contains k then t else t.put k (forcedTicketLevel + 1)

/-- The chunk coordinates the harness force-loads, in each direction (`Recorder.REGION_MIN_CHUNK`
to `REGION_MAX_CHUNK`). -/
def harnessChunkRange : List ℤ := (List.range 24).map fun i => (i : ℤ) - 8

/-- `simulationChunkTracker.chunks` of the harness world. -/
def harnessTable : ChunkTable :=
  harnessChunkRange.foldl (init := {}) fun t x => harnessChunkRange.foldl (init := t) fun t z =>
    forceChunk t x z

/-- The chunks that tick, in the order in which `ChunkMap.forEachBlockTickingChunk` goes through
them: the entries of the table whose level makes them entity ticking
(`ChunkLevel.isEntityTicking`). -/
def tickingChunks : Array (ℤ × ℤ) :=
  (harnessTable.entries.filterMap fun (k, level) =>
    if level ≤ forcedTicketLevel then some (unpackChunk k) else none).toArray

-- The two ends of the order, as read from the table of a running server.
#guard tickingChunks.size = 576
#guard tickingChunks.toList.take 7 =
  [(0, 0), (-1, 14), (11, 13), (10, -1), (13, 8), (11, -7), (9, 4)]
#guard tickingChunks.toList.drop 573 = [(-7, 13), (9, 2), (-6, 12)]

/-! ### One chunk -/

/-- The step of `Level.randValue` in `getBlockRandomPos`. -/
def nextRandValue (randValue : ℕ) : ℕ := (randValue * 3 + 1013904223) % 2 ^ 32

/-- `Level.getBlockRandomPos(xo, yo, zo, 15)`: a position in the 16 × 16 × 16 cube at
`(xo, yo, zo)`, drawn from `Level.randValue`. -/
def getBlockRandomPos (xo yo zo : ℤ) : M Pos :=
  modifyGet fun l =>
    let r := nextRandValue l.randValue
    -- `val = randValue >> 2`, then `val & 15`, `val >> 16 & 15` and `val >> 8 & 15`.
    (⟨xo + ((r >>> 2) % 16 : ℕ), yo + ((r >>> 18) % 16 : ℕ), zo + ((r >>> 10) % 16 : ℕ)⟩,
      { l with randValue := r })

/-- The `iceandsnow` part of `ServerLevel.tickChunk` for one chunk: `speed` draws of
`nextInt(48)`, and for every zero a `getBlockRandomPos`, whose position goes to
`tickPrecipitation`, which does nothing in the world of the harness. Only the two generators
change, so this is a function on them: the level's random number generator and `randValue`. -/
def iceAndSnowRef : ℕ → JavaRandom × ℕ → JavaRandom × ℕ
  | 0, s => s
  | speed + 1, (random, randValue) =>
    let (v, random) := random.nextInt 48
    iceAndSnowRef speed (random, if v = 0 then nextRandValue randValue else randValue)

/-- The rejection loop of `nextInt(48)` on the 48-bit seed in 64-bit arithmetic, as Java has
it: the seed after the draw that was accepted. When the fuel runs out (`JavaRandom.nextIntLoop`
then answers 0) the top bit is set. -/
def nextInt48Seed : ℕ → UInt64 → UInt64
  | 0, seed => seed ||| 0x8000000000000000
  | fuel + 1, seed =>
    let seed := (seed * 0x5DEECE66D + 0xB) &&& 0xFFFFFFFFFFFF
    let bits := seed >>> 17
    if bits - bits % 48 + 47 < 0x80000000 then seed else nextInt48Seed fuel seed

/-- `speed` draws of `nextInt(48)` from the seed `seed`: the seed afterwards, and how many of
the draws gave zero, added to `zeros`. -/
def iceAndSnowLoop : ℕ → UInt64 → ℕ → UInt64 × ℕ
  | 0, seed, zeros => (seed, zeros)
  | speed + 1, seed, zeros =>
    let drawn := nextInt48Seed 128 seed
    let seed := drawn &&& 0xFFFFFFFFFFFF
    let zero := drawn ≥ 0x8000000000000000 || (seed >>> 17) % 48 == 0
    iceAndSnowLoop speed seed (if zero then zeros + 1 else zeros)

/-- `iceAndSnowRef` computed with machine words. The arithmetic of the generator is modulo
`2 ^ 48`, so the 64-bit product gives the same seed. -/
def iceAndSnowFast (speed : ℕ) (s : JavaRandom × ℕ) : JavaRandom × ℕ :=
  if speed = 0 then s
  else
    let (seed, zeros) := iceAndSnowLoop speed s.1.seed.toUInt64 0
    (⟨seed.toNat⟩, nextRandValue^[zeros] s.2)

/-- `iceAndSnowRef`. A game tick makes `random_tick_speed` draws for each of the 576 chunks,
and with numbers of arbitrary size that is what a scenario with a high speed spends its time
on, so compiled code runs `iceAndSnowFast` in its place. That the two agree is not proved in
general; the kernel checks it on the samples below, and every recorded scenario with random
ticks depends on it. -/
@[implemented_by iceAndSnowFast]
def iceAndSnow (speed : ℕ) (s : JavaRandom × ℕ) : JavaRandom × ℕ := iceAndSnowRef speed s

/-- `iceAndSnowRef` and `iceAndSnowFast` agree on `speed` draws from the given seed. -/
def iceAndSnowAgree (speed seed randValue : ℕ) : Bool :=
  decide (iceAndSnowRef speed (⟨seed⟩, randValue) = iceAndSnowFast speed (⟨seed⟩, randValue))

example : iceAndSnowAgree 0 (2 ^ 70 + 5) (2 ^ 40) = true := by decide +kernel
example : iceAndSnowAgree 3 0x5DEECE66D 0 = true := by decide +kernel
example : iceAndSnowAgree 500 0x5DEECE66D 0 = true := by decide +kernel
example : iceAndSnowAgree 400 0xFFFFFFFFFFFF 0xFFFFFFFF = true := by decide +kernel
example : iceAndSnowAgree 300 (2 ^ 90 + 12345) (2 ^ 35 + 9) = true := by decide +kernel

/-- `FluidState.isRandomlyTicking`: lava. -/
def fluidIsRandomlyTicking (s : FluidState) : Bool := s.fluid.isLava

/-- `LevelChunkSection.isRandomlyTicking` for the section with the corner `(minX, minY, minZ)`:
it holds a block that gets random ticks. Only the part of the section inside `box` is looked
at. -/
def sectionIsRandomlyTicking (l : Level) (box : Pos × Pos) (minX minY minZ : ℤ) : Bool :=
  let range (lo hi : ℤ) : List ℤ := (List.range (hi + 1 - lo).toNat).map fun i => lo + i
  (range (max minX box.1.x) (min (minX + 15) box.2.x)).any fun x =>
    (range (max minY box.1.y) (min (minY + 15) box.2.y)).any fun y =>
      (range (max minZ box.1.z) (min (minZ + 15) box.2.z)).any fun z =>
        let b := l.blockAt ⟨x, y, z⟩
        b.attrs.randomlyTicks || fluidIsRandomlyTicking b.fluidState

/-- The random tick of the block `state` at `p` (`BlockState.randomTick`): copper weathers
(the `randomTick` of every copper class is `Component.Weathering.randomTick`), and any other
block does what its behaviour says. -/
def randomTickBlock (state : Block) (p : Pos) : M Unit := do
  if (Block.Weathering.age? state.id).isSome then Component.Weathering.randomTick state p
  else (← Level.behaviour state).randomTick p

/-- The random tick of a fluid (`FluidState.randomTick`). Not modelled: `Level.overflow`. -/
def randomTickFluid (_state : FluidState) (_p : Pos) : M Unit := Level.setOverflow

/-- `p` lies in the box. -/
def inBox (box : Pos × Pos) (p : Pos) : Bool :=
  box.1.x ≤ p.x && p.x ≤ box.2.x && box.1.y ≤ p.y && p.y ≤ box.2.y &&
    box.1.z ≤ p.z && p.z ≤ box.2.z

/-- One random tick in the section with the corner `(minX, minY, minZ)`: the body of the inner
loop of `ServerLevel.tickChunk`. A block outside `box` that would get a random tick is one
the level did not announce (`Level.randomTickBox`): `Level.overflow`. -/
def randomTickIn (box : Pos × Pos) (minX minY minZ : ℤ) : M Unit := do
  let p ← getBlockRandomPos minX minY minZ
  let state ← Level.getBlock p
  let fluidState := state.fluidState
  if !inBox box p then
    if state.attrs.randomlyTicks || fluidIsRandomlyTicking fluidState then Level.setOverflow
  else
    if state.attrs.randomlyTicks then randomTickBlock state p
    if fluidIsRandomlyTicking fluidState then randomTickFluid fluidState p

/-- The section indices of a chunk of the overworld, from the bottom: section `i` begins at
y = `16 * i - 64`. -/
def sectionCount : ℕ := 24

/-- The chunk meets the box. -/
def chunkMeetsBox (box : Pos × Pos) (chunk : ℤ × ℤ) : Bool :=
  box.1.x ≤ chunk.1 * 16 + 15 && chunk.1 * 16 ≤ box.2.x &&
    box.1.z ≤ chunk.2 * 16 + 15 && chunk.2 * 16 ≤ box.2.z

/-- How many chunks meet the box. -/
def boxChunkCount (box : Pos × Pos) : ℕ :=
  ((box.2.x / 16 + 1 - box.1.x / 16).toNat) * ((box.2.z / 16 + 1 - box.1.z / 16).toNat)

/-- `ServerLevel.tickChunk(chunk, speed)` for the chunk `(cx, cz)`. -/
def tickChunk (box : Option (Pos × Pos)) (speed : ℕ) (chunk : ℤ × ℤ) : M Unit := do
  let minX := chunk.1 * 16
  let minZ := chunk.2 * 16
  modify fun l =>
    let (random, randValue) := iceAndSnow speed (l.random, l.randValue)
    { l with random, randValue }
  if let some box := box then
    if chunkMeetsBox box chunk then
      (List.range sectionCount).forM fun i => do
        let minY := 16 * (i : ℤ) - 64
        if sectionIsRandomlyTicking (← get) box minX minY minZ then
          (List.range speed).forM fun _ => randomTickIn box minX minY minZ

end RandomTick

namespace Level

/-- The random ticks of one game tick, for a positive `random_tick_speed`: every ticking chunk
in turn (`ChunkMap.forEachBlockTickingChunk`). A box that reaches beyond the ticking chunks
holds blocks whose random ticks the model cannot place in the order: `Level.overflow`. -/
def randomTicks : M Unit := do
  let l ← get
  if let some box := l.randomTickBox then
    if (RandomTick.tickingChunks.filter (RandomTick.chunkMeetsBox box)).size
        ≠ RandomTick.boxChunkCount box then
      setOverflow
  RandomTick.tickingChunks.forM (RandomTick.tickChunk l.randomTickBox l.randomTickSpeed)

/-- `ServerChunkCache.tickChunks`: the random ticks of one game tick. With the game rule
`random_tick_speed` at zero nothing is drawn and nothing happens. -/
def tickChunks : M Unit := do
  if (← get).randomTickSpeed = 0 then pure () else randomTicks

/-- With `random_tick_speed` at zero the random-tick phase leaves the level as it is. -/
theorem tickChunks_of_speed_zero (env : Env) (l : Level) (h : l.randomTickSpeed = 0) :
    (tickChunks.run env).run l = ((), l) := by
  change (if l.randomTickSpeed = 0 then (pure () : M Unit) else randomTicks) env l = ((), l)
  rw [h]
  rfl

end Level

end Redstone
