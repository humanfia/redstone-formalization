module

public import Redstone.Mechanics.Tick
public import Redstone.Component.Sensor.Sky
public import Redstone.Component.Sensor.Light

/-!
# Target, lightning rod and daylight detector

Java classes: `TargetBlock`, `LightningRodBlock`, `WeatheringLightningRodBlock`,
`DaylightDetectorBlock`, `DaylightDetectorBlockEntity`.

* A target hit by a projectile emits a signal that grows towards the centre of the face that
  was hit, for 20 game ticks if the projectile is an arrow or a trident and for 8 otherwise.
  It is a conductor as well.
* A lightning rod struck by lightning emits a signal of 15 for 8 game ticks, and powers the
  block it stands on strongly.
* A daylight detector measures the light of the sky every 20 game ticks. In its normal mode
  the signal follows the sun; inverted, it is 15 minus the sky light.

## What is modelled, and what is not

* Target: `ownSignal`, `tick`, `onPlace`, and `updateRedstoneOutput` with `getRedstoneStrength`.
  `onProjectileHit` reads the point and the face of the hit, as `Redstone.Entity.Projectile`
  finds them. Statistics and advancements are left out.
* Lightning rod: `ownSignal`, `getDirectSignal`, `onLightningStrike`, `tick`, `onPlace`,
  `affectNeighborsAfterRemoval`. `updateShape` only schedules a fluid tick for a waterlogged
  rod, and fluids do not flow in the model. `randomTick` (the oxidation of copper) and the level
  event of a strike (particles) are left out. A lightning bolt calls `strike` for the block
  under it (`Redstone.Entity.Lightning`), and cleans the copper of a rod that weathers.
* Daylight detector: `ownSignal`, `useWithoutItem`, the ticker, `updateSignalStrength`. The sun
  angle and the darkening of the sky are computed from the clock and the weather in
  `Redstone.Component.Sensor.Sky`, the sky light of the cell in `Redstone.Component.Sensor.Light`;
  both files state their assumptions. The player always may build.
-/

@[expose] public section

namespace Redstone.Component.Sensor

/-! ### Target -/

/-- `TargetBlock.getRedstoneStrength(hitResult, hitLocation)`: the signal for a hit on the face
`face` at the point `hit`. It is 15 at the centre of the face and falls to 1 at its edge. -/
def redstoneStrength (face : Direction) (hit : Vec3) : ℕ :=
  let dist (v : Float) : Float := (v - v.floor - 0.5).abs
  let max (a b : Float) : Float := if a ≥ b then a else b
  let distance :=
    match face.axis with
    | .y => max (dist hit.x) (dist hit.z)
    | .z => max (dist hit.x) (dist hit.y)
    | .x => max (dist hit.y) (dist hit.z)
  let ratio := (0.5 - distance) / 0.5
  let ratio := if ratio < 0 then 0 else if ratio ≤ 1 then ratio else 1
  Nat.max 1 (15 * ratio).ceil.toUInt8.toNat

/-- `TargetBlock.setOutputPower` under the condition of `TargetBlock.updateRedstoneOutput`: unless
a tick of the target is already waiting, the target takes the signal `strength` and schedules
the tick that ends it, after 20 game ticks for an arrow and after 8 otherwise. -/
def updateRedstoneOutput (s : Blocks.Target) (p : Pos) (strength : Fin 16) (arrow : Bool) :
    M Unit := do
  if !(← get).hasScheduledTick p .target then
    discard <| Level.setBlock p (.target { s with power := strength })
    Level.scheduleTick p .target (if arrow then 20 else 8)

/-- The entity types that are `AbstractArrow`s. -/
def arrowTypes : List String := ["minecraft:arrow", "minecraft:spectral_arrow", "minecraft:trident"]

/-- The behaviour of a target. -/
def target (s : Blocks.Target) : Behaviour :=
  let self : Block := .target s
  { Behaviour.inert self with
    signal := fun _ _ _ => s.power
    ownSignal := fun _ _ => s.power
    onProjectileHit := fun p face hit index => do
      if let some e := (← get).entity? index then
        let strength := redstoneStrength face hit
        updateRedstoneOutput s p ⟨strength % 16, Nat.mod_lt _ (by decide)⟩
          (arrowTypes.contains e.data.typeName)
    tick := fun p => do
      if s.power.val != 0 then discard <| Level.setBlock p (.target { s with power := 0 })
    onPlace := fun p old _ => do
      if !old.is .target then
        if s.power.val > 0 && !(← get).hasScheduledTick p .target then
          -- `UPDATE_CLIENTS | UPDATE_KNOWN_SHAPE`
          discard <| Level.setBlock p (.target { s with power := 0 }) 18 }

/-! ### Lightning rod -/

/-- `LightningRodBlock.updateNeighbours`: neighbour updates around the block the rod points away
from, the one it stands on. -/
def updateNeighbours (id : BlockId) (facing : Direction) (p : Pos) : M Unit :=
  Level.updateNeighborsAt (p.step facing.opposite) id

/-- `LightningRodBlock.onLightningStrike(state, level, pos)`: lightning strikes the rod. `state`
gives the rod with the given value of `powered`. The level event (particles) is left out. -/
def onLightningStrike (id : BlockId) (facing : Direction) (state : Bool → Block) (p : Pos) :
    M Unit := do
  discard <| Level.setBlock p (state true)
  updateNeighbours id facing p
  Level.scheduleTick p id 8

/-- The behaviour of a lightning rod with block `id`, facing `facing`. `state` gives the rod
with the given value of `powered`. -/
def lightningRod (id : BlockId) (facing : Direction) (powered : Bool) (state : Bool → Block) :
    Behaviour :=
  { Behaviour.inert (state powered) with
    signal := fun _ _ _ => if powered then 15 else 0
    ownSignal := fun _ _ => if powered then 15 else 0
    directSignal := fun _ _ d => if powered && facing = d then 15 else 0
    tick := fun p => do
      discard <| Level.setBlock p (state false)
      updateNeighbours id facing p
    affectNeighborsAfterRemoval := fun p _ => do
      if powered then updateNeighbours id facing p
    onPlace := fun p old _ => do
      if !old.is id then
        if powered && !(← get).hasScheduledTick p id then Level.scheduleTick p id 8 }

/-- `LightningRodBlock.onLightningStrike` for the block at `p`, if it is a lightning rod. This
is what a lightning bolt calls. -/
def strike (p : Pos) : M Unit := do
  match ← Level.getBlock p with
  | .weatheringLightningRod id s =>
    onLightningStrike id.toBlockId s.facing
      (fun v => .weatheringLightningRod id { s with powered := v }) p
  | .lightningRod id s =>
    onLightningStrike id.toBlockId s.facing (fun v => .lightningRod id { s with powered := v }) p
  | _ => pure ()

/-! ### Daylight detector -/

/-- The signal `DaylightDetectorBlock.updateSignalStrength` computes, from the sky light `sky`
of the cell, the overworld clock and the weather. -/
def signalStrength (inverted : Bool) (sky clock : ℕ) (weather : Weather) : ℕ :=
  -- `getEffectiveSkyBrightness`
  let target := sky - Sky.skyDarken clock weather
  if inverted then 15 - target
  else if target > 0 then
    let sunAngle := Sky.sunAngle clock * Sky.degToRad
    let offset := if sunAngle < Sky.pi then 0 else Sky.twoPi
    let sunAngle := sunAngle + (offset - sunAngle) * Sky.fifth
    Sky.roundClamped (Float32.ofNat target * Sky.cos sunAngle)
  else 0

/-- `DaylightDetectorBlock.updateSignalStrength(state, level, pos)`. The sky light is the one
the light engine computed when the game tick began (`Level.lightWorld`). -/
def updateSignalStrength (s : Blocks.DaylightDetector) (p : Pos) : M Unit := do
  let l ← get
  let target := signalStrength s.inverted (Light.skyLight l.lightWorld p) l.dayTime l.weather
  if s.power.val != target then
    discard <| Level.setBlock p
      (.daylightDetector { s with power := ⟨target % 16, Nat.mod_lt _ (by decide)⟩ })

/-- The behaviour of a daylight detector. -/
def daylightDetector (s : Blocks.DaylightDetector) : Behaviour :=
  let self : Block := .daylightDetector s
  { Behaviour.inert self with
    signal := fun _ _ _ => s.power
    ownSignal := fun _ _ => s.power
    useWithoutItem := fun p _ => do
      let s := { s with inverted := !s.inverted }
      discard <| Level.setBlock p (.daylightDetector s) 2
      Level.gameEvent "minecraft:block_change" p
      updateSignalStrength s p
      return true
    -- `getTicker`: the overworld has sky light.
    ticksBlockEntity := true
    blockEntityTick := fun p => do
      if (← get).gameTime % 20 == 0 then updateSignalStrength s p }

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .target s => target s
  | .weatheringLightningRod id s =>
    lightningRod id.toBlockId s.facing s.powered
      fun v => .weatheringLightningRod id { s with powered := v }
  | .lightningRod id s =>
    lightningRod id.toBlockId s.facing s.powered fun v => .lightningRod id { s with powered := v }
  | .daylightDetector s => daylightDetector s
  | _ => .inert self

end Redstone.Component.Sensor
