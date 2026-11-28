module

public import Redstone.Entity.FallingBlock

/-!
# Structures that fall apart

Java classes: `ScaffoldingBlock`, `SpeleothemBlock` with `PointedDripstoneBlock` and
`SulfurSpikeBlock`, `BrushableBlock` (suspicious sand and gravel), with
`FallingBlockEntity.fall` for the way they turn into falling blocks.

* **Scaffolding** keeps its distance from a supported column in its state. A shape update or
  its placement schedules a tick one game tick later; on that tick it computes the distance
  again (`getDistance`). At distance 7 it has no support: it breaks if its state did not say 7
  yet, and falls as a falling block if it did. A scaffolding that lands is put back with the
  state it fell with and corrects it one tick later.
* A **speleothem** (pointed dripstone, sulfur spike) points up (a stalagmite) or down (a
  stalactite). A shape update from above or below either gives it its thickness again
  (`calculateSpeleothemThickness`), or, if it comes from its base and the base no longer holds
  it, schedules a tick: one tick later a stalagmite breaks, so a column breaks from the bottom
  up one segment per tick; two ticks later a stalactite falls, and with it the whole column
  below it down to the tip, each segment as a falling block of its own. The tip is set to hurt
  entities.
* **Suspicious sand and gravel** fall like sand, two ticks after a shape update, but the
  falling block is set to vanish when it lands (`FallingBlockEntity.disableDrop`).

A waterlogged scaffolding or speleothem schedules the tick of its water on every shape update
(`Level.scheduleFluidTick`), before anything else, as the game does.

## What is left out

* Random ticks: the growth of a stalactite and of the stalagmite below it, the cauldron a
  stalactite fills and the mud it dries (`SpeleothemBlock.randomTick`,
  `PointedDripstoneBlock.maybeTransferFluid`). They belong to a later unit; `randomTick` is
  inert here.
* A trident that hits a speleothem breaks it (`SpeleothemBlock.onProjectileHit`). Tridents are
  not modelled: a trident that hits one sets `Level.overflow`.
* What a stalagmite does to an entity that falls on it (`PointedDripstoneBlock.fallOn`) and
  what a falling stalactite does to the living entities it lands on: `Redstone.Entity.Physics`
  and `Redstone.Entity.FallingBlock` set `Level.overflow` there.
* The collision shapes. That of scaffolding depends on the entity that asks, that of a
  speleothem on its position (a random horizontal offset), and a moving piston has none in the
  model. `Redstone.Entity.Physics` sets `Level.overflow` when an entity comes next to
  scaffolding, a pointed dripstone or a moving piston; for a sulfur spike it does not, and
  takes the shape without its offset, which is wrong. So a falling block or an item that comes
  down on or beside one of these is not followed: a scaffolding that falls past another one, a
  stalactite that falls on a stalagmite, a column that falls beside the piston that took its
  support. These scenarios wait in `tests/pending/scenarios/falling-structure`
  (`scaffolding-bridge-built`, `scaffolding-falls-beside-column`, `scaffolding-stack-falls`,
  `*-merged-ceiling-removed`, `*-piston-pulls-ceiling`, `*-piston-pushes-stalactite`,
  `dripstone-stalactite-onto-stalagmite`, `suspicious-piston`) for the units that give
  entities these shapes.
* Fluids do not flow (`Redstone.Mechanics.Fluid` is a stub): the tick of the water is
  scheduled, and does nothing. `scaffolding-waterlogged` and `dripstone-waterlogged` wait in
  `tests/pending` for that.
* A suspicious block that breaks on landing announces it (`BrushableBlock.onBrokenAfterFall`,
  in `Redstone.Entity.FallingBlock`). `Redstone.Component.Sculk` hears a game event at the
  centre of a block and without the UUID of its entity, where the game takes the centre of the
  falling block: `suspicious-lands-by-sensor` waits in `tests/pending` for that.
* A falling block that touches water, a waterlogged one in particular (it leaves its water
  behind), sets `Level.overflow` (`Redstone.Entity.FallingBlock`).
* Brushing. The brush is an item used by a player, so the block entity of a suspicious block
  never counts a brush, and `BrushableBlockEntity.checkReset`, which the tick of the block
  calls first, has nothing to take back. The loot of the block entity is not kept.
* Placement (`getStateForPlacement`), climbing and sneaking through scaffolding, and
  particles.
-/

@[expose] public section

namespace Redstone.Component.FallingStructure

open Entity.FallingBlock (isFree)

/-! ### Falling -/

/-- `FallingBlockEntity.fall(level, pos, state)`: the block at `p` is replaced by the fluid it
holds, and a falling block entity with the state, without its water, is added. `g` is what the
caller does to the entity it gets back (`disableDrop`, `setHurtsEntities`). The game creates
the entity before it removes the block and adds it afterwards; the model numbers entities when
they are added. -/
def fall (state : Block) (p : Pos) (g : Entities.FallingBlock → Entities.FallingBlock := id) :
    M Unit := do
  let pos : Vec3 := ⟨Phys.ofInt p.x + 0.5, Phys.ofInt p.y, Phys.ofInt p.z + 0.5⟩
  discard <| Level.setBlock p state.fluidBlock
  let entry := ((← get).gameTime, 0)
  let data : Entities.FallingBlock :=
    g { blockState := state.clearWaterlogged, phys := { sectionEntry := entry } }
  discard <| Level.addEntity ⟨pos, .zero, false⟩ (.fallingBlock data)

/-- `Fluids.WATER.getTickDelay(level)`. -/
def waterTickDelay : ℕ := 5

/-! ### Scaffolding -/

/-- `ScaffoldingBlock.STABILITY_MAX_DISTANCE`. -/
def stabilityMaxDistance : ℕ := 7

/-- The distance of the scaffolding at `p`, if there is one. -/
def scaffoldingDistance? (l : Level) (p : Pos) : Option ℕ :=
  match l.blockAt p with
  | .scaffolding s => some s.distance.val
  | _ => none

/-- `ScaffoldingBlock.getDistance(level, pos)`: 0 on a sturdy top face; otherwise the distance
of the scaffolding below, or one more than the least distance of the scaffolding at the four
sides, and at most 7. The game stops looking at the sides when it has reached 1, which is the
least a side can give. -/
def getDistance (l : Level) (p : Pos) : ℕ :=
  let q := p.step .down
  let fromBelow : Option ℕ :=
    match scaffoldingDistance? l q with
    | some d => some d
    | none => if (l.supportAttrs q).isFaceSturdy .up then none else some stabilityMaxDistance
  match fromBelow with
  | none => 0
  | some d =>
    Direction.horizontals.foldl
      (fun distance dir =>
        match scaffoldingDistance? l (p.step dir) with
        | some side => min distance (side + 1)
        | none => distance)
      d

/-- `ScaffoldingBlock.isBottom(level, pos, distance)`: the scaffolding is not on the ground and
has no scaffolding below it. -/
def isBottom (l : Level) (p : Pos) (distance : ℕ) : Bool :=
  distance > 0 && (scaffoldingDistance? l (p.step .down)).isNone

/-- The state of a scaffolding with the distance and the flag `bottom` computed again. -/
def scaffoldingState (s : Blocks.Scaffolding) (l : Level) (p : Pos) : Blocks.Scaffolding :=
  let distance := getDistance l p
  { s with
    distance := ⟨min distance stabilityMaxDistance, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
    bottom := isBottom l p distance }

/-- `ScaffoldingBlock.tick`: the scaffolding takes its distance. At distance 7 it falls if it
was at 7 before, and breaks if it was not. -/
def scaffoldingTick (s : Blocks.Scaffolding) (p : Pos) : M Unit := do
  let newState := scaffoldingState s (← get) p
  if newState.distance.val = stabilityMaxDistance then
    if s.distance.val = stabilityMaxDistance then fall (.scaffolding newState) p
    else discard <| Level.destroyBlock p true
  else if s ≠ newState then discard <| Level.setBlock p (.scaffolding newState)

/-- The behaviour of scaffolding. -/
def scaffolding (s : Blocks.Scaffolding) : Behaviour :=
  { Behaviour.inert (.scaffolding s) with
    canSurvive := fun l p => getDistance l p < stabilityMaxDistance
    onPlace := fun p _ _ => Level.scheduleTick p .scaffolding 1
    updateShape := fun p _ _ _ => do
      if s.waterlogged then Level.scheduleFluidTick p .water waterTickDelay
      Level.scheduleTick p .scaffolding 1
      return .scaffolding s
    tick := scaffoldingTick s }

/-! ### Speleothems -/

/-- A block state of `SpeleothemBlock`: a pointed dripstone, or a sulfur spike if `sulfur`. -/
structure Speleothem where
  /-- The block is a sulfur spike, not a pointed dripstone. -/
  sulfur : Bool
  /-- `THICKNESS`. -/
  thickness : SpeleothemThickness
  /-- `TIP_DIRECTION`. -/
  tipDirection : DirectionUpDown
  /-- `WATERLOGGED`. -/
  waterlogged : Bool
  deriving DecidableEq, Repr

namespace Speleothem

/-- The block state as a speleothem, if it is in the tag `minecraft:speleothems` (pointed
dripstone and sulfur spike). -/
def of? : Block → Option Speleothem
  | .pointedDripstone s => some ⟨false, s.thickness, s.vertical_direction, s.waterlogged⟩
  | .sulfurSpike s => some ⟨true, s.thickness, s.vertical_direction, s.waterlogged⟩
  | _ => none

/-- The block state of the speleothem. -/
def toBlock (s : Speleothem) : Block :=
  if s.sulfur then .sulfurSpike ⟨s.thickness, s.tipDirection, s.waterlogged⟩
  else .pointedDripstone ⟨s.thickness, s.tipDirection, s.waterlogged⟩

/-- The block of the speleothem. -/
def blockId (s : Speleothem) : BlockId := if s.sulfur then .sulfur_spike else .pointed_dripstone

/-- The direction the speleothem points in. -/
def tip (s : Speleothem) : Direction := s.tipDirection.toDirection

/-- `isTip(state, includeMergedTip)`. -/
def isTip (s : Speleothem) (includeMergedTip : Bool) : Bool :=
  s.thickness = .tip || (includeMergedTip && s.thickness = .tip_merge)

end Speleothem

/-- `SpeleothemBlock.isSpeleothemWithDirection(state, tipDirection)`: the block is a speleothem
of either kind that points in the direction. -/
def isSpeleothemWithDirection (b : Block) (tipDirection : Direction) : Bool :=
  match Speleothem.of? b with
  | some s => s.tip = tipDirection
  | none => false

/-- `isSpeleothemWithDirection(state, tipDirection) && state.is(this)`: the block is a
speleothem of the same kind as `self` that points in the direction. -/
def isOwnWithDirection (self : Speleothem) (b : Block) (tipDirection : Direction) : Bool :=
  match Speleothem.of? b with
  | some s => s.tip = tipDirection && s.sulfur = self.sulfur
  | none => false

/-- `SpeleothemBlock.isValidSpeleothemPlacement(level, pos, tipDirection)`: behind the
speleothem is a sturdy face, or a speleothem of its kind that points the same way. -/
def isValidSpeleothemPlacement (self : Speleothem) (l : Level) (p : Pos)
    (tipDirection : Direction) : Bool :=
  let behindPos := p.step tipDirection.opposite
  (l.supportAttrs behindPos).isFaceSturdy tipDirection ||
    isOwnWithDirection self (l.blockAt behindPos) tipDirection

/-- `SpeleothemBlock.canSurvive`. -/
def speleothemCanSurvive (self : Speleothem) (l : Level) (p : Pos) : Bool :=
  isValidSpeleothemPlacement self l p self.tip

/-- `SpeleothemBlock.calculateSpeleothemThickness(level, pos, tipDirection, mergeOpposingTips)`:
the thickness follows from the block in front of the tip and the block behind the base. -/
def calculateSpeleothemThickness (self : Speleothem) (l : Level) (p : Pos)
    (mergeOpposingTips : Bool) : SpeleothemThickness :=
  let tipDirection := self.tip
  let baseDirection := tipDirection.opposite
  match Speleothem.of? (l.blockAt (p.step tipDirection)) with
  | none => .tip
  | some inFront =>
    if inFront.tip = baseDirection && inFront.sulfur = self.sulfur then
      if !mergeOpposingTips && inFront.thickness ≠ .tip_merge then .tip else .tip_merge
    else if inFront.tip ≠ tipDirection then .tip
    else if inFront.thickness = .tip || inFront.thickness = .tip_merge then .frustum
    else if !isSpeleothemWithDirection (l.blockAt (p.step baseDirection)) tipDirection then .base
    else .middle

/-- `SpeleothemBlock.DELAY_BEFORE_FALLING`. -/
def delayBeforeFalling : ℕ := 2

/-- `SpeleothemBlock.updateShape`. An update from the side changes nothing. A stalactite that
is about to fall stays as it is. A speleothem whose base no longer holds it schedules its tick.
Otherwise the speleothem takes its thickness. -/
def speleothemUpdateShape (self : Speleothem) (p : Pos) (directionToNeighbour : Direction) :
    M Block := do
  if self.waterlogged then Level.scheduleFluidTick p .water waterTickDelay
  if directionToNeighbour ≠ .up && directionToNeighbour ≠ .down then return self.toBlock
  let l ← get
  if self.tipDirection = .down && l.hasScheduledTick p self.blockId then return self.toBlock
  if directionToNeighbour = self.tip.opposite && !speleothemCanSurvive self l p then
    Level.scheduleTick p self.blockId (if self.tipDirection = .down then delayBeforeFalling else 1)
    return self.toBlock
  let mergeOpposingTips := self.thickness = .tip_merge
  return { self with
    thickness := calculateSpeleothemThickness self l p mergeOpposingTips }.toBlock

/-- `SpeleothemBlock.MAX_STALACTITE_HEIGHT_FOR_DAMAGE_CALCULATION`. -/
def maxStalactiteHeightForDamageCalculation : ℕ := 6

/-- `STALACTITE_MAX_DAMAGE`. -/
def stalactiteMaxDamage : ℤ := 40

/-- `SpeleothemBlock.spawnFallingStalactite(state, level, pos)`, from the segment `depth`
blocks below the one that was ticked: every stalactite segment from `p` down falls, down to
and including the first tip, which is set to hurt entities by the length of the column that
fell, counted as at least 6. `fuel` bounds the walk; the build height does. -/
def spawnFallingStalactite : ℕ → ℕ → Block → Pos → M Unit
  | 0, _, _, _ => pure ()
  | fuel + 1, depth, fallState, fallPos => do
    match Speleothem.of? fallState with
    | some s =>
      if s.tipDirection = .down then
        if s.isTip true then
          let size := max (1 + depth) maxStalactiteHeightForDamageCalculation
          fall fallState fallPos fun dt =>
            { dt with
              hurtEntities := true
              fallDamagePerDistance := (Float32.ofNat size).toBits.toNat
              fallDamageMax := stalactiteMaxDamage }
        else
          fall fallState fallPos
          let below := fallPos.step .down
          spawnFallingStalactite fuel (depth + 1) ((← get).blockAt below) below
    | none => pure ()

/-- `SpeleothemBlock.tick`: a stalagmite that lost its base breaks; anything else falls as a
stalactite does, which leaves a stalagmite alone. -/
def speleothemTick (self : Speleothem) (p : Pos) : M Unit := do
  if self.tipDirection = .up && !speleothemCanSurvive self (← get) p then
    discard <| Level.destroyBlock p true
  else spawnFallingStalactite (p.y + 65).toNat 0 self.toBlock p

/-- The behaviour of a pointed dripstone or a sulfur spike. -/
def speleothem (self : Speleothem) : Behaviour :=
  { Behaviour.inert self.toBlock with
    canSurvive := speleothemCanSurvive self
    updateShape := fun p d _ _ => speleothemUpdateShape self p d
    tick := speleothemTick self
    onProjectileHit := fun _ _ _ i => do
      -- a trident that is fast enough breaks the block; tridents are not modelled
      match (← get).entity? i with
      | some ⟨_, _, .projectile "minecraft:trident" _⟩ => Level.setOverflow
      | _ => pure () }

/-! ### Suspicious sand and gravel -/

/-- `BrushableBlock.TICK_DELAY`. -/
def brushableTickDelay : ℕ := 2

/-- `BrushableBlock.tick`: the block falls if the block below is free, as a falling block that
vanishes when it lands. The block entity has no brush to take back (`checkReset`). -/
def brushableTick (self : Block) (p : Pos) : M Unit := do
  if isFree ((← get).blockAt (p.step .down)) && p.y ≥ -64 then
    fall self p fun dt => { dt with cancelDrop := true }

/-- The behaviour of suspicious sand and suspicious gravel. -/
def brushable (self : Block) : Behaviour :=
  { Behaviour.inert self with
    onPlace := fun p _ _ => Level.scheduleTick p self.id brushableTickDelay
    updateShape := fun p _ _ _ => do
      Level.scheduleTick p self.id brushableTickDelay
      return self
    tick := brushableTick self }

/-! ### The behaviours -/

/-- The behaviour of scaffolding, of a speleothem, of a suspicious block. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .scaffolding s => scaffolding s
  | .brushable _ _ => brushable self
  | _ =>
    match Speleothem.of? self with
    | some s => speleothem s
    | none => .inert self

end Redstone.Component.FallingStructure
