module

public import Redstone.Mechanics.Tick

/-!
# Sculk sensors and shriekers

Java classes: `SculkSensorBlock`, `CalibratedSculkSensorBlock`, `SculkSensorBlockEntity`,
`CalibratedSculkSensorBlockEntity`, `SculkShriekerBlock`, `SculkShriekerBlockEntity`,
`SculkCatalystBlock`, and the vibration system they share: `VibrationSystem`,
`VibrationSelector`, `GameEventDispatcher`.

A sculk sensor hears the game events around it. An event it accepts becomes a vibration, which
travels one block per game tick; when it arrives the sensor is active for 30 game ticks (a
calibrated sensor for 10), with a signal that is stronger the nearer the event was, and then
cools down for 10 game ticks. A comparator reads the frequency of the event. A calibrated
sensor only accepts the frequency given by the signal at its back. A shrieker hears the
clicking of activated sensors, and shrieks when a player caused it.

`onGameEvent` is the hook that `Level.gameEvent` calls.

## What is left out

* A game event is heard at the centre of a block (`Level.gameEvent` with a block position).
  Only `stepOn` uses the exact position of an entity.
* Of the source entity of an event only the following is used: whether it is a player (for the
  shrieker), and that it is kept in the vibration. Sneaking, spectators and entities that dampen
  vibrations (`Entity.dampensVibrations`) are not modelled, nor is the owner of a projectile.
  A vibration read from saved data only has the UUID of its source, which the game looks up
  when the vibration arrives; no entity is ever found (`GameEventSource.resolve`). The UUID of
  the tests' player is the exception: it is read as the live player, which is wrong for a
  scenario that starts with such a vibration (pending scenarios `v-saved-player-uuid-*`).
* The shrieker never warns and never summons a warden (`canRespond` is false): the tests run
  with the game rule `spawn_wardens` off, and the warning level of a player is not part of the
  model. With that, `tryRespond` and `preRemoveSideEffects` do nothing.
* A waterlogged block does not schedule the fluid tick of `updateShape`; fluids do not flow.
* The catalyst does not react to deaths (mobs are not modelled) and its charge cursors do not
  spread; a catalyst that has cursors sets `Level.overflow`.
* `requiresAdjacentChunksToBeTicking`: every chunk is loaded and ticking.
* Sounds, particles and advancement triggers. The pitch of the sensor's sounds is drawn from the
  level's random generator, which is modelled.
-/

@[expose] public section

namespace Redstone.Component.Sculk

open BlockEntities (VibrationInfo VibrationData)

/-! ### Block tags -/

/-- The sixteen dye colours, as they appear in block names. -/
def dyeColors : List String :=
  ["white", "orange", "magenta", "light_blue", "yellow", "lime", "pink", "gray", "light_gray",
    "cyan", "purple", "blue", "brown", "green", "red", "black"]

/-- The names of the sixteen blocks `minecraft:<colour><suffix>`. -/
def coloredNames (suffix : String) : List String :=
  dyeColors.map fun c => "minecraft:" ++ c ++ suffix

/-- The names of the blocks of the tag `minecraft:occludes_vibration_signals`: wool. -/
def occludingNames : List String := coloredNames "_wool"

/-- The names of the blocks of the tag `minecraft:dampens_vibrations`: wool, and the carpets,
slabs and stairs made of it. -/
def dampeningNames : List String :=
  coloredNames "_wool" ++ coloredNames "_carpet" ++ coloredNames "_wool_slab" ++
    coloredNames "_wool_stairs"

/-- The block tag `minecraft:occludes_vibration_signals`. -/
def occludesVibrationSignals (b : Block) : Bool := occludingNames.contains b.id.name

/-- The block tag `minecraft:dampens_vibrations`. -/
def dampensVibrations (b : Block) : Bool := dampeningNames.contains b.id.name

/-- The block tag `minecraft:vibration_resonators`: the block of amethyst. -/
def isVibrationResonator (b : Block) : Bool := b.is .amethyst_block

/-! ### Game events -/

/-- `VibrationSystem.getResonanceEventByFrequency`. -/
def resonanceEvent (frequency : ℕ) : String := s!"minecraft:resonate_{frequency}"

/-- `VibrationSystem.getGameEventFrequency`: the frequency of a game event, from 1 to 15, or 0
for an event that is not a vibration. -/
def gameEventFrequency (event : String) : ℕ :=
  match event with
  | "minecraft:step" | "minecraft:swim" | "minecraft:flap" => 1
  | "minecraft:projectile_land" | "minecraft:hit_ground" | "minecraft:splash"
  | "minecraft:bounce" => 2
  | "minecraft:item_interact_finish" | "minecraft:projectile_shoot"
  | "minecraft:instrument_play" => 3
  | "minecraft:entity_action" | "minecraft:elytra_glide" | "minecraft:unequip" => 4
  | "minecraft:entity_dismount" | "minecraft:equip" => 5
  | "minecraft:entity_interact" | "minecraft:shear" | "minecraft:entity_mount" => 6
  | "minecraft:entity_damage" => 7
  | "minecraft:drink" | "minecraft:eat" => 8
  | "minecraft:container_close" | "minecraft:block_close" | "minecraft:block_deactivate"
  | "minecraft:block_detach" => 9
  | "minecraft:container_open" | "minecraft:block_open" | "minecraft:block_activate"
  | "minecraft:block_attach" | "minecraft:prime_fuse" | "minecraft:note_block_play" => 10
  | "minecraft:block_change" => 11
  | "minecraft:block_destroy" | "minecraft:fluid_pickup" => 12
  | "minecraft:block_place" | "minecraft:fluid_place" => 13
  | "minecraft:entity_place" | "minecraft:lightning_strike" | "minecraft:teleport" => 14
  | "minecraft:entity_die" | "minecraft:explode" => 15
  | _ => ((List.range 16).find? fun f => 0 < f && event == resonanceEvent f).getD 0

/-- The game event tag `minecraft:vibrations`. It lists exactly the events that have a
frequency. -/
def isVibration (event : String) : Bool := gameEventFrequency event != 0

/-- The game event tag `minecraft:shrieker_can_listen`. -/
def shriekerCanListen (event : String) : Bool :=
  event == "minecraft:sculk_sensor_tendrils_clicking"

/-! ### Points of space

Vibrations are computed in `double` and `float` arithmetic as the game does; Lean's `Float`
and `Float32` are these types. -/

/-- `Mth.floor`. -/
def floorInt (x : Float) : ℤ := x.floor.toInt64.toInt

/-- `Vec3.atCenterOf(pos)`. -/
def centerOf (p : Pos) : Vec3 :=
  ⟨Float.ofInt p.x + 0.5, Float.ofInt p.y + 0.5, Float.ofInt p.z + 0.5⟩

/-- `BlockPos.containing(vec)`. -/
def blockContaining (v : Vec3) : Pos := ⟨floorInt v.x, floorInt v.y, floorInt v.z⟩

/-- `Vec3.distanceTo`. -/
def distanceTo (a b : Vec3) : Float :=
  let xd := b.x - a.x
  let yd := b.y - a.y
  let zd := b.z - a.z
  Float.sqrt (xd * xd + yd * yd + zd * zd)

/-- `Vec3i.distSqr`, as an integer. -/
def distSqr (a b : Pos) : ℤ :=
  (a.x - b.x) * (a.x - b.x) + (a.y - b.y) * (a.y - b.y) + (a.z - b.z) * (a.z - b.z)

/-- `VibrationSystem.Listener.distanceBetweenInBlocks`. -/
def distanceBetweenInBlocks (origin dest : Pos) : Float32 :=
  (Float.sqrt (Float.ofInt (distSqr origin dest))).toFloat32

/-- The vibration of the event `event` at `origin`, for a listener at `dest`
(`new VibrationInfo(event, (float) origin.distanceTo(dest), origin, sourceEntity)`). -/
def vibrationInfo (event : String) (origin dest : Vec3) (source : Option GameEventSource) :
    VibrationInfo :=
  ⟨event, (distanceTo origin dest).toFloat32.toBits.toNat, origin.x.toBits.toNat,
    origin.y.toBits.toNat, origin.z.toBits.toNat, source⟩

/-- `VibrationInfo.distance`. -/
def distanceOf (v : VibrationInfo) : Float32 := Float32.ofBits (UInt32.ofNat v.distance)

/-- `VibrationInfo.pos`. -/
def posOf (v : VibrationInfo) : Vec3 :=
  ⟨Float.ofBits (UInt64.ofNat v.x), Float.ofBits (UInt64.ofNat v.y),
    Float.ofBits (UInt64.ofNat v.z)⟩

/-- `User.calculateTravelTimeInTicks`: one game tick per block, rounded down. -/
def travelTime (v : VibrationInfo) : ℕ := (floorInt (distanceOf v).toFloat).toNat

/-- `VibrationSystem.getRedstoneStrengthForDistance(distance, listenerRadius)`: 15 next to the
listener, falling to 1 at the edge of its range. -/
def redstoneStrengthForDistance (distance : Float32) (listenerRadius : ℕ) : ℕ :=
  let powerScale := 15.0 / Float.ofNat listenerRadius
  (max 1 (15 - floorInt (powerScale * distance.toFloat))).toNat

/-! ### Occlusion -/

/-- `Mth.lerp`. -/
def lerp (alpha p0 p1 : Float) : Float := p0 + alpha * (p1 - p0)

/-- `Mth.frac`. -/
def frac (x : Float) : Float := x - x.floor

/-- `Mth.sign`. -/
def sign (x : Float) : ℤ := if x == 0.0 then 0 else if x > 0.0 then 1 else -1

/-- `Double.MAX_VALUE`. -/
def maxDouble : Float := Float.ofBits 0x7FEFFFFFFFFFFFFF

/-- The `double` `-1.0E-7`, by which `traverseBlocks` moves the two ends of the line apart. -/
def nudgeEnds : Float := Float.ofBits 0xBE7AD7F29ABCAF48

/-- The loop of `BlockGetter.traverseBlocks`, bounded by `fuel` steps: walks from block to
block along the line, and tells whether a block satisfying `hit` is reached before the end. -/
def traverseLoop (hit : Pos → Bool) (signX signY signZ : ℤ) (tDeltaX tDeltaY tDeltaZ : Float) :
    ℕ → Pos → Float → Float → Float → Bool
  | 0, _, _, _, _ => false
  | fuel + 1, cur, tX, tY, tZ =>
    if tX ≤ 1.0 ∨ tY ≤ 1.0 ∨ tZ ≤ 1.0 then
      let (cur, tX, tY, tZ) :=
        if tX < tY then
          if tX < tZ then ({ cur with x := cur.x + signX }, tX + tDeltaX, tY, tZ)
          else ({ cur with z := cur.z + signZ }, tX, tY, tZ + tDeltaZ)
        else if tY < tZ then ({ cur with y := cur.y + signY }, tX, tY + tDeltaY, tZ)
        else ({ cur with z := cur.z + signZ }, tX, tY, tZ + tDeltaZ)
      if hit cur then true
      else traverseLoop hit signX signY signZ tDeltaX tDeltaY tDeltaZ fuel cur tX tY tZ
    else false

/-- `BlockGetter.traverseBlocks(from, to, ...)` for a visitor that stops at the blocks
satisfying `hit`: some block on the line from `start` to `stop` satisfies `hit`. The line is
at most `fuel` blocks long. -/
def traverseBlocks (hit : Pos → Bool) (start stop : Vec3) (fuel : ℕ) : Bool :=
  if start == stop then false
  else
    let toX := lerp nudgeEnds stop.x start.x
    let toY := lerp nudgeEnds stop.y start.y
    let toZ := lerp nudgeEnds stop.z start.z
    let fromX := lerp nudgeEnds start.x stop.x
    let fromY := lerp nudgeEnds start.y stop.y
    let fromZ := lerp nudgeEnds start.z stop.z
    let cur : Pos := ⟨floorInt fromX, floorInt fromY, floorInt fromZ⟩
    if hit cur then true
    else
      let dx := toX - fromX
      let dy := toY - fromY
      let dz := toZ - fromZ
      let signX := sign dx
      let signY := sign dy
      let signZ := sign dz
      let tDeltaX := if signX = 0 then maxDouble else Float.ofInt signX / dx
      let tDeltaY := if signY = 0 then maxDouble else Float.ofInt signY / dy
      let tDeltaZ := if signZ = 0 then maxDouble else Float.ofInt signZ / dz
      let tX := tDeltaX * (if signX > 0 then 1.0 - frac fromX else frac fromX)
      let tY := tDeltaY * (if signY > 0 then 1.0 - frac fromY else frac fromY)
      let tZ := tDeltaZ * (if signZ > 0 then 1.0 - frac fromZ else frac fromZ)
      traverseLoop hit signX signY signZ tDeltaX tDeltaY tDeltaZ fuel cur tX tY tZ

/-- The `float` `1.0E-5F`, as a `double`. -/
def nudge : Float := (Float32.ofBits 0x3727C5AC).toFloat

/-- `Vec3.relative(direction, distance)`. -/
def relative (v : Vec3) (d : Direction) (distance : Float) : Vec3 :=
  match d with
  | .down => { v with y := v.y - distance }
  | .up => { v with y := v.y + distance }
  | .north => { v with z := v.z - distance }
  | .south => { v with z := v.z + distance }
  | .west => { v with x := v.x - distance }
  | .east => { v with x := v.x + distance }

/-- `VibrationSystem.Listener.isOccluded`: wool lies between the block of the event and the
block of the listener. Six lines are tried, from points next to the centre of the first block
to the centre of the second; the vibration is occluded when each of them meets wool. -/
def isOccluded (l : Level) (origin dest : Vec3) : Bool :=
  let a := blockContaining origin
  let b := blockContaining dest
  let fuel := ((a.x - b.x).natAbs + (a.y - b.y).natAbs + (a.z - b.z).natAbs) + 8
  Direction.values.all fun d =>
    traverseBlocks (fun p => occludesVibrationSignals (l.blockAt p))
      (relative (centerOf a) d nudge) (centerOf b) fuel

/-! ### Block states -/

/-- The properties of a sculk sensor, calibrated or not. -/
structure SensorState where
  /-- `PHASE`. -/
  phase : SculkSensorPhase
  /-- `POWER`. -/
  power : Fin 16
  /-- `WATERLOGGED`. -/
  waterlogged : Bool
  /-- `FACING`, for a calibrated sensor. -/
  facing : Option Direction

/-- The properties of the block, if it is a sculk sensor (`SculkSensorBlock`). -/
def sensorState? : Block → Option SensorState
  | .sculkSensor s => some ⟨s.sculk_sensor_phase, s.power, s.waterlogged, none⟩
  | .calibratedSculkSensor s =>
    some ⟨s.sculk_sensor_phase, s.power, s.waterlogged, some s.facing.toDirection⟩
  | _ => none

/-- `state.setValue(PHASE, phase)`. -/
def withPhase (b : Block) (phase : SculkSensorPhase) : Block :=
  match b with
  | .sculkSensor s => .sculkSensor { s with sculk_sensor_phase := phase }
  | .calibratedSculkSensor s => .calibratedSculkSensor { s with sculk_sensor_phase := phase }
  | b => b

/-- `state.setValue(POWER, power)`. -/
def withPower (b : Block) (power : ℕ) : Block :=
  let power : Fin 16 := ⟨min power 15, by omega⟩
  match b with
  | .sculkSensor s => .sculkSensor { s with power := power }
  | .calibratedSculkSensor s => .calibratedSculkSensor { s with power := power }
  | b => b

/-- `getActiveTicks`: how long a sensor stays active. -/
def activeTicks (b : Block) : ℕ := if b.is .calibrated_sculk_sensor then 10 else 30

/-! ### Listeners -/

/-- The vibration data of a block entity that listens to vibrations
(`VibrationSystem.getVibrationData`). -/
def vibrationData? : BlockEntity → Option VibrationData
  | .sculkSensor d => some d.listener
  | .calibratedSculkSensor d => some d.listener
  | .sculkShrieker d => some d.listener
  | _ => none

/-- Replaces the vibration data of a block entity. -/
def setVibrationData (be : BlockEntity) (v : VibrationData) : BlockEntity :=
  match be with
  | .sculkSensor d => .sculkSensor { d with listener := v }
  | .calibratedSculkSensor d => .calibratedSculkSensor { d with listener := v }
  | .sculkShrieker d => .sculkShrieker { d with listener := v }
  | be => be

/-- `User.getListenerRadius`. -/
def listenerRadius : BlockEntity → ℕ
  | .calibratedSculkSensor _ => 16
  | _ => 8

/-- The block of the block entity's cached state (`BlockEntity.getBlockState().getBlock()`). -/
def listenerBlock : BlockEntity → BlockId
  | .calibratedSculkSensor _ => .calibrated_sculk_sensor
  | .sculkShrieker _ => .sculk_shrieker
  | _ => .sculk_sensor

/-- Changes the vibration data of the listener at `q`. In the game the data belongs to the
block entity object, which can be changed even after it was removed from the world; this is
not modelled, and sets `Level.overflow`. -/
def modifyData (q : Pos) (f : VibrationData → VibrationData) : M Unit := do
  match ← Level.getBlockEntity q with
  | some be =>
    match vibrationData? be with
    | some d => Level.setBlockEntity q (setVibrationData be (f d))
    | none => Level.setOverflow
  | none => Level.setOverflow

/-- `User.onDataChanged`, which is `BlockEntity.setChanged`: the comparators that read the
block are updated. -/
def onDataChanged (q : Pos) (block : BlockId) : M Unit :=
  Level.updateNeighbourForOutputSignal q block

/-- `level.getRandom().nextFloat()`, for the pitch of a sound. -/
def nextFloat : M Unit := modify fun l => { l with random := l.random.nextFloat24.2 }

/-! ### Hearing a game event -/

/-- `User.isValidVibration(event, context)`: the listener listens to events of this kind, and
the event is not about a block that dampens vibrations. -/
def isValidVibration (be : BlockEntity) (event : String) (context : GameEventContext) : Bool :=
  let listenable :=
    match be with
    | .sculkShrieker _ => shriekerCanListen event
    | _ => isVibration event
  listenable && !context.affectedState.any dampensVibrations

/-- `SculkSensorBlockEntity.VibrationUser.canReceiveVibration`: the event is not the placing or
breaking of the sensor itself, it has a frequency, and the sensor is inactive. -/
def sensorCanReceiveVibration (state : Block) (q src : Pos) (event : String) : Bool :=
  if src = q ∧ (event == "minecraft:block_destroy" || event == "minecraft:block_place") then
    false
  else if gameEventFrequency event = 0 then false
  else (sensorState? state).any (·.phase = .inactive)

/-- `User.canReceiveVibration(level, pos, event, context)` for the listener `be` at `q`, whose
block state is `state`; `src` is the block of the event. A calibrated sensor that receives a
signal at its back only accepts the events whose frequency is that signal. A shrieker accepts
the events caused by a player while it is not shrieking. -/
def canReceiveVibration (be : BlockEntity) (state : Block) (q src : Pos) (event : String)
    (context : GameEventContext) : M Bool := do
  match be with
  | .sculkSensor _ => return sensorCanReceiveVibration state q src event
  | .calibratedSculkSensor _ =>
    let some facing := (sensorState? state).bind (·.facing) | return false
    let back := facing.opposite
    let comparisonType ← Level.getSignal (q.step back) back
    if comparisonType ≠ 0 ∧ gameEventFrequency event ≠ comparisonType then return false
    else return sensorCanReceiveVibration state q src event
  | .sculkShrieker _ =>
    let .sculkShrieker s := state | return false
    return !s.shrieking && context.sourceEntity = some .player
  | _ => return false

/-- `VibrationSelector.shouldReplaceVibration`: among the events heard in one game tick the
nearest wins, and among equally near ones the one of highest frequency. A candidate left from
an earlier game tick is kept. -/
def shouldReplaceVibration (selector : Option (VibrationInfo × ℤ)) (new : VibrationInfo)
    (now : ℤ) : Bool :=
  match selector with
  | none => true
  | some (previous, tick) =>
    if now ≠ tick then false
    else if distanceOf new < distanceOf previous then true
    else if distanceOf new > distanceOf previous then false
    else gameEventFrequency new.gameEvent > gameEventFrequency previous.gameEvent

/-- `VibrationSystem.Listener.scheduleVibration`: proposes the event as the vibration of the
listener at `q` (`VibrationSelector.addCandidate`). -/
def scheduleVibration (q : Pos) (event : String) (source : Option GameEventSource)
    (origin : Vec3) : M Unit := do
  let now : ℤ := (← get).gameTime
  let new := vibrationInfo event origin (centerOf q) source
  modifyData q fun d =>
    if shouldReplaceVibration d.selector new now then { d with selector := some (new, now) }
    else d

/-- `VibrationSystem.Listener.handleGameEvent`: the listener at `q` hears the event `event`
that happened at `origin`. -/
def handleGameEvent (q : Pos) (event : String) (context : GameEventContext) (origin : Vec3) :
    M Unit := do
  let some be ← Level.getBlockEntity q | return
  let some data := vibrationData? be | return
  if data.currentVibration.isSome then return
  if !isValidVibration be event context then return
  let state ← Level.getBlock q
  if !(← canReceiveVibration be state q (blockContaining origin) event context) then return
  if isOccluded (← get) origin (centerOf q) then return
  scheduleVibration q event context.sourceEntity origin

/-- `GameEventDispatcher.post(event, position, context)`: every listener hears the event if
the block of the event is within its radius (`getPostableListenerPosition`).

The listeners are the block entities of sensors and shriekers. They are registered when the
block entity is added to the world, at the same time as its ticker, and removed with it, so
they are found in the list of ticking block entities. The order in which they hear the event
does not matter, because hearing only changes the listener's own data. The game only looks in
the chunk sections within the notification radius of the event, which is 16 for every event
these listeners accept and covers their radius. The catalyst also listens, but only for the
death of a mob. -/
def onGameEventAt (event : String) (origin : Vec3) (context : GameEventContext) : M Unit := do
  let l ← get
  let src := blockContaining origin
  (l.blockEntityTickers ++ l.pendingBlockEntityTickers).forM fun q => do
    let some be ← Level.getBlockEntity q | return
    if (vibrationData? be).isSome then
      let r : ℤ := listenerRadius be
      if distSqr q src ≤ r * r then handleGameEvent q event context origin

/-- `Level.gameEvent(event, pos, context)`: the reaction of vibration listeners to the game
event named `event` at the centre of the block `p`. -/
def onGameEvent (event : String) (p : Pos) (context : GameEventContext) : M Unit :=
  onGameEventAt event (centerOf p) context

/-! ### The sensor -/

/-- `SculkSensorBlock.updateNeighbours`: neighbour updates around the sensor and around the
block below it. -/
def updateNeighbours (q : Pos) (block : BlockId) : M Unit := do
  Level.updateNeighborsAt q block
  Level.updateNeighborsAt (q.step .down) block

/-- `SculkSensorBlock.tryResonateVibration`: every block of amethyst next to the sensor repeats
the vibration, as the resonance event of its frequency. -/
def tryResonateVibration (source : Option GameEventSource) (q : Pos) (frequency : ℕ) :
    M Unit :=
  Direction.values.forM fun d => do
    let relativePos := q.step d
    let blockState ← Level.getBlock relativePos
    if isVibrationResonator blockState then
      Level.gameEvent (resonanceEvent frequency) relativePos
        { sourceEntity := source, affectedState := some blockState }

/-- `SculkSensorBlock.activate`. -/
def activate (source : Option GameEventSource) (q : Pos) (state : Block) (st : SensorState)
    (calculatedPower vibrationFrequency : ℕ) : M Unit := do
  discard <| Level.setBlock q (withPower (withPhase state .active) calculatedPower)
  Level.scheduleTick q state.id (activeTicks state)
  updateNeighbours q state.id
  tryResonateVibration source q vibrationFrequency
  Level.gameEvent "minecraft:sculk_sensor_tendrils_clicking" q { sourceEntity := source }
  if !st.waterlogged then nextFloat

/-- `SculkSensorBlock.deactivate`. -/
def deactivate (q : Pos) (state : Block) : M Unit := do
  discard <| Level.setBlock q (withPower (withPhase state .cooldown) 0)
  Level.scheduleTick q state.id 10
  updateNeighbours q state.id

/-- `SculkSensorBlockEntity.setLastVibrationFrequency`, for the sensor at `q`. -/
def setLastVibrationFrequency (q : Pos) (frequency : ℕ) : M Unit := do
  match ← Level.getBlockEntity q with
  | some (.sculkSensor d) =>
    Level.setBlockEntity q (.sculkSensor { d with lastVibrationFrequency := frequency })
  | some (.calibratedSculkSensor d) =>
    Level.setBlockEntity q (.calibratedSculkSensor { d with lastVibrationFrequency := frequency })
  | _ => pure ()

/-- `SculkSensorBlockEntity.VibrationUser.onReceiveVibration`: a vibration that started at the
block `origin` arrives at the sensor at `q`. -/
def sensorOnReceiveVibration (be : BlockEntity) (q origin : Pos) (event : String)
    (source : Option GameEventSource) : M Unit := do
  let state ← Level.getBlock q
  let some st := sensorState? state | return
  if st.phase = .inactive then
    let eventFrequency := gameEventFrequency event
    setLastVibrationFrequency q eventFrequency
    let calculatedPower :=
      redstoneStrengthForDistance (distanceBetweenInBlocks origin q) (listenerRadius be)
    activate source q state st calculatedPower eventFrequency

/-! ### The shrieker -/

/-- `SculkShriekerBlockEntity.tryShriek(level, tryGetPlayer(sourceEntity))`: the shrieker at
`q` shrieks if a player set it off. `canRespond` is taken to be false, so no warning is given
(see the module docstring). -/
def tryShriek (q : Pos) (source : Option GameEventSource) : M Unit := do
  if source ≠ some .player then return
  let .sculkShrieker s ← Level.getBlock q | return
  if !s.shrieking then
    if let some (.sculkShrieker d) ← Level.getBlockEntity q then
      Level.setBlockEntity q (.sculkShrieker { d with warningLevel := 0 })
    -- `shriek`
    discard <| Level.setBlock q (.sculkShrieker { s with shrieking := true }) 2
    Level.scheduleTick q .sculk_shrieker 90
    Level.gameEvent "minecraft:shriek" q { sourceEntity := source }

/-! ### The vibration ticker -/

/-- `VibrationSystem.Ticker.receiveVibration`: the vibration arrives at the listener at `q`. -/
def receiveVibration (q : Pos) (be : BlockEntity) (vibration : VibrationInfo) : M Bool := do
  let origin := blockContaining (posOf vibration)
  -- `currentVibration.getEntity(serverLevel).orElse(null)`
  let source := GameEventSource.resolve vibration.source
  match be with
  | .sculkShrieker _ => tryShriek q source
  | _ => sensorOnReceiveVibration be q origin vibration.gameEvent source
  -- `data.setCurrentVibration(null)`, which changes nothing in the world if the listener was
  -- removed meanwhile
  if let some be ← Level.getBlockEntity q then
    if let some d := vibrationData? be then
      Level.setBlockEntity q (setVibrationData be { d with currentVibration := none })
  return true

/-- `VibrationSystem.Ticker.tick`, the ticker of the block entities of sensors and shriekers.
If no vibration is travelling, the candidate heard before this game tick starts travelling
(`trySelectAndScheduleVibration`). A travelling vibration comes one block nearer, and is
received when it arrives. -/
def vibrationTick (q : Pos) : M Unit := do
  let some be ← Level.getBlockEntity q | return
  let some data := vibrationData? be | return
  let block := listenerBlock be
  let now : ℤ := (← get).gameTime
  if data.currentVibration.isNone then
    if let some (info, tick) := data.selector then
      if tick < now then
        modifyData q fun _ => ⟨some info, travelTime info, none⟩
        onDataChanged q block
  let some be ← Level.getBlockEntity q | Level.setOverflow
  let some data := vibrationData? be | Level.setOverflow
  let some vibration := data.currentVibration | return
  let mut hasChanged : Bool := data.travelTimeInTicks > 0
  let travelTimeInTicks := data.travelTimeInTicks - 1
  modifyData q fun d => { d with travelTimeInTicks := travelTimeInTicks }
  if travelTimeInTicks = 0 then hasChanged ← receiveVibration q be vibration
  if hasChanged then onDataChanged q block

/-! ### Behaviours -/

/-- The behaviour of a sculk sensor, calibrated or not (`SculkSensorBlock`,
`CalibratedSculkSensorBlock`). -/
def sensor (self : Block) (st : SensorState) : Behaviour :=
  let signal (d : Direction) : ℕ := if st.facing = some d then 0 else st.power
  { Behaviour.inert self with
    signal := fun _ _ d => signal d
    ownSignal := fun _ _ => st.power
    directSignal := fun _ _ d => if d = .up then signal d else 0
    analogSignal := fun l p _ =>
      let frequency :=
        match l.blockEntities p with
        | some (.sculkSensor d) => d.lastVibrationFrequency
        | some (.calibratedSculkSensor d) => d.lastVibrationFrequency
        | _ => 0
      if st.phase = .active then frequency else 0
    ticksBlockEntity := true
    blockEntityTick := vibrationTick
    tick := fun p => do
      match st.phase with
      | .active => deactivate p self
      | .cooldown =>
        discard <| Level.setBlock p (withPhase self .inactive)
        if !st.waterlogged then nextFloat
      | .inactive => pure ()
    stepOn := fun p i => do
      if st.phase = .inactive then
        let some e := (← get).entity? i | return
        if e.data.typeName == "minecraft:warden" then return
        let some be ← Level.getBlockEntity p | return
        let step := "minecraft:step"
        match be with
        | .sculkSensor _ | .calibratedSculkSensor _ =>
          if ← canReceiveVibration be self p p step { affectedState := some self } then
            -- `forceScheduleVibration`
            scheduleVibration p step (some (.entity i)) e.base.pos
        | _ => pure ()
    onPlace := fun p oldState _ => do
      if !self.is oldState.id then
        if st.power.val > 0 && !(← get).hasScheduledTick p self.id then
          discard <| Level.setBlock p (withPower self 0) 18
    affectNeighborsAfterRemoval := fun p _ => do
      if st.phase = .active then updateNeighbours p self.id }

/-- The behaviour of a sculk shrieker (`SculkShriekerBlock`). `stepOn` does nothing: only a
player sets off the shrieker, and players do not walk in the model. -/
def shrieker (s : Blocks.SculkShrieker) : Behaviour :=
  let self : Block := .sculkShrieker s
  { Behaviour.inert self with
    ticksBlockEntity := true
    blockEntityTick := vibrationTick
    tick := fun p => do
      if s.shrieking then
        discard <| Level.setBlock p (.sculkShrieker { s with shrieking := false }) }

/-- The behaviour of a sculk catalyst (`SculkCatalystBlock`). Its block entity ticks the charge
cursors of the `SculkSpreader`, which does nothing while there are none. -/
def catalyst (s : Blocks.SculkCatalyst) : Behaviour :=
  let self : Block := .sculkCatalyst s
  { Behaviour.inert self with
    ticksBlockEntity := true
    blockEntityTick := fun p => do
      if let some (.sculkCatalyst d) ← Level.getBlockEntity p then
        if d.cursors ≠ 0 then Level.setOverflow
    tick := fun p => do
      if s.bloom then discard <| Level.setBlock p (.sculkCatalyst { s with bloom := false }) }

/-- The behaviour of the blocks of this component. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .sculkShrieker s => shrieker s
  | .sculkCatalyst s => catalyst s
  | _ =>
    match sensorState? self with
    | some st => sensor self st
    | none => .inert self

end Redstone.Component.Sculk
