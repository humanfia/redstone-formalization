module

public import Redstone.Mechanics.Tick

/-!
# Big dripleaf

Java classes: `BigDripleafBlock` (with `Tilt`), `BigDripleafStemBlock`.

The leaf of a big dripleaf tilts under an entity standing on it: `unstable` at once, `partial`
after 10 game ticks, `full` after 10 more, and back to `none` after 100 more. A projectile tilts
it fully at once. A leaf that receives a redstone signal does not tilt, and goes back to `none`
when a neighbour changes or its scheduled tick runs.

A leaf with another leaf placed on it becomes a stem. A stem needs a stem or supporting block
below and a stem or leaf above; otherwise it breaks one game tick after a shape update from
above or below.

The two ways a leaf starts to tilt are `entityInside`, which the entity units call
(`Redstone.Entity.Touch`), and `onProjectileHit`, which a projectile that hits the leaf calls
(`Redstone.Entity.Projectile`).

Not modelled:

* Bone meal (`performBonemeal`) and world generation (`placeWithRandomHeight`).
* The sounds. The pitch of a tilt sound is drawn from the level's random generator, and this
  draw is modelled.
-/

@[expose] public section

namespace Redstone.Component.Dripleaf

/-- The block tag `minecraft:supports_big_dripleaf`. -/
def supportsBigDripleaf (b : Block) : Bool :=
  [BlockId.clay, .moss_block, .dirt, .grass_block, .podzol, .coarse_dirt, .mycelium,
    .rooted_dirt, .mud, .muddy_mangrove_roots, .farmland].contains b.id

/-- `canSurvive`: the block below is a big dripleaf, its stem, or a block that supports one. -/
def canSurvive (l : Level) (p : Pos) : Bool :=
  let below := l.blockAt (p.step .down)
  below.is .big_dripleaf || below.is .big_dripleaf_stem || supportsBigDripleaf below

/-- `Tilt.causesVibration`. -/
def causesVibration : Tilt → Bool
  | .unstable => false
  | _ => true

/-- `DELAY_UNTIL_NEXT_TILT_STATE`: the delay of the tick scheduled on reaching a tilt; none for
`Tilt.none`. -/
def delayUntilNextTiltState : Tilt → Option ℕ
  | .none => none
  | .unstable => some 10
  | .partial => some 10
  | .full => some 100

/-- `setTilt(state, level, pos, tilt)`. -/
def setTilt (s : Blocks.BigDripleaf) (p : Pos) (tilt : Tilt) : M Unit := do
  discard <| Level.setBlock p (.bigDripleaf { s with tilt := tilt }) 2
  if causesVibration tilt && tilt ≠ s.tilt then Level.gameEvent "minecraft:block_change" p

/-- `playTiltSound(level, pos, sound)`: the pitch is `Mth.randomBetween(level.getRandom(), ..)`,
one `nextFloat()`. Only the draw is kept. -/
def playTiltSound : M Unit :=
  modify fun l => { l with random := l.random.nextFloat24.2 }

/-- `setTiltAndScheduleTick(state, level, pos, tilt, sound)`; `sound` says whether a sound is
given. -/
def setTiltAndScheduleTick (s : Blocks.BigDripleaf) (p : Pos) (tilt : Tilt) (sound : Bool) :
    M Unit := do
  setTilt s p tilt
  if sound then playTiltSound
  if let some delay := delayUntilNextTiltState tilt then Level.scheduleTick p .big_dripleaf delay

/-- `resetTilt(state, level, pos)`. -/
def resetTilt (s : Blocks.BigDripleaf) (p : Pos) : M Unit := do
  setTilt s p .none
  if s.tilt ≠ .none then playTiltSound

/-- `canEntityTilt(pos, entity)`: the entity is on the ground and above the leaf. -/
def canEntityTilt (p : Pos) (e : Entity) : Bool :=
  e.base.onGround && e.base.pos.y > Float.ofInt p.y + 0.6875

/-- `BigDripleafStemBlock.canSurvive`: the block below is a stem or a block that supports a big
dripleaf, and the block above is a stem or a leaf. -/
def stemCanSurvive (l : Level) (p : Pos) : Bool :=
  let below := l.blockAt (p.step .down)
  let above := l.blockAt (p.step .up)
  (below.is .big_dripleaf_stem || supportsBigDripleaf below)
    && (above.is .big_dripleaf_stem || above.is .big_dripleaf)

/-- The behaviour of a big dripleaf and of its stem. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .bigDripleaf s =>
    { Behaviour.inert self with
      canSurvive := canSurvive
      updateShape := fun p d _ neighbour => do
        if d = .down && !canSurvive (← get) p then return .AIR
        if s.waterlogged then Level.scheduleFluidTick p .water Fluid.water.tickDelay
        if d = .up && neighbour.is .big_dripleaf then
          return .bigDripleafStem ⟨s.facing, s.waterlogged⟩
        else return self
      entityInside := fun p i => do
        let some e := (← get).entity? i | return
        if s.tilt = .none && canEntityTilt p e && !(← Level.hasNeighborSignal p) then
          setTiltAndScheduleTick s p .unstable false
      onProjectileHit := fun p _ _ _ => setTiltAndScheduleTick s p .full true
      tick := fun p => do
        if ← Level.hasNeighborSignal p then resetTilt s p
        else
          match s.tilt with
          | .unstable => setTiltAndScheduleTick s p .partial true
          | .partial => setTiltAndScheduleTick s p .full true
          | .full => resetTilt s p
          | .none => pure ()
      neighborChanged := fun p _ _ => do
        if ← Level.hasNeighborSignal p then resetTilt s p }
  | .bigDripleafStem s =>
    { Behaviour.inert self with
      canSurvive := stemCanSurvive
      updateShape := fun p d _ _ => do
        if (d = .down || d = .up) && !stemCanSurvive (← get) p then
          Level.scheduleTick p .big_dripleaf_stem 1
        if s.waterlogged then Level.scheduleFluidTick p .water Fluid.water.tickDelay
        return self
      tick := fun p => do
        if !stemCanSurvive (← get) p then discard <| Level.destroyBlock p true }
  | _ => .inert self

end Redstone.Component.Dripleaf
