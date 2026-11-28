module

public import Redstone.Entity.Still
public import Redstone.Block.Weathering
public import Redstone.Component.Sensor
public import Redstone.Component.Sculk
public import Redstone.Component.Fire

/-!
# Lightning bolts

Java class: `LightningBolt`, with `WeatheringCopper.getFirst` and `getPrevious`.

A bolt stays where it is. In its first tick it strikes the block just under it: a lightning rod
there is powered (`Component.Sensor.strike`), and copper there is cleaned, together with copper
found on a few random walks from it (`clearCopperOnLightningStrike`, drawn from the level's
random number generator). Vibration listeners hear the strike.

After that the bolt counts `life` down. Once it is negative the bolt flashes again with a
chance that grows every tick, as often as `flashes` says (1 to 3 times), and each new flash
lights a fire where the bolt is, if fire is allowed to spread
(`Component.Fire.canSpreadFireAround`). When no flash is left the bolt disappears. `flashes`
and the chances come from the bolt's own random number generator.

## The bolt's own random numbers

Every entity has a generator of its own (`Entity.random`, made by `RandomSource.create()`),
which the test harness seeds from the id of the entity (`Entity.randomOfId`). The constructor
of `Entity` draws a UUID from it (two `long`s, `Entity.randomAfterUuid`), then `LightningBolt`
draws `seed` and `flashes`.

The data of an entity is read from its saved NBT without knowing its id, so the model
constructs the bolt when it first ticks (`construct`), from the generator that belongs to its
id. Nothing draws from that generator between the constructor and the first tick, so this is
the same. It is exact under the assumption of `Entity.id`: every entity that was created
before the bolt was in the world at the end of its tick.

## Tests

`tests/scenarios/lightning`: the bolt is removed after its second tick, or (the `*-natural`
scenarios, and `tests/scenarios/sensor/rod-lightning`) lives as long as its own numbers say and
lights its fires. Still in `tests/pending/scenarios/lightning`:

* `entity-in-box`: an item in the bolt's box, which sets `Level.overflow` (see below).
* `sculk-hears`: the sensor hears the strike as the server does, but the vibration it keeps
  names its source by the UUID of the bolt, which the model does not have
  (`Redstone.Component.Sculk`).

## What is assumed

* The difficulty is easy, as in the harness: on normal and hard the bolt also lights fires in
  its first tick, in up to four more cells around it (`spawnFire(4)`).
* The bolt is not `visualOnly` and has no `cause` (no trident).

## What is left out

* `Entity.baseTick` (the bolt does not burn, fall out of the world or use portals).
* The entities in the bolt's box (3 blocks around it, 9 above): the bolt strikes them
  (`Entity.thunderHit`: they burn and are hurt, and some change). When any entity but another
  bolt is in the box the model sets `Level.overflow`. A bolt that is struck only starts to
  burn, which has no effect.
* Sounds, the sky flash, the level event of cleaned copper (particles), advancements.
-/

@[expose] public section

namespace Redstone.Entity.Lightning

open Redstone.Block

/-! ### The bolt's random numbers -/

/-- `RandomSource.nextLong()` of a `LegacyRandomSource`: two draws of 32 bits. Only the state
after the draws matters here. -/
def skipLong (r : JavaRandom) : JavaRandom := ((r.next 32).2.next 32).2

/-- The constructor of `LightningBolt`, with the generator `r` the constructor of `Entity`
left: the bolt's `seed` is drawn and not kept, then `flashes` is one to three. -/
def constructWith (r : JavaRandom) : Entities.Lightning :=
  let (n, r) := (skipLong r).nextInt 3
  { constructed := true, life := 2, flashes := n + 1, random := some r }

/-- The data of the bolt `e` once it has been constructed: `d` itself if it was, and otherwise
what the constructor makes with the generator of the entity (`Entity.randomAfterUuid`). -/
def construct (e : Entity) (d : Entities.Lightning) : Entities.Lightning :=
  if d.constructed then d else constructWith (Entity.randomAfterUuid e.id)

/-! ### Cleaning copper -/

/-- `Block.withPropertiesOf(state)`: the default state of the block `id` with the values of the
properties it shares with `b`. The stages of a copper block have the same properties. -/
def withPropertiesOf (id : BlockId) (b : Block) : Block :=
  let props := b.toProps
  (Block.ofProps? id fun k => (props.find? (·.1 == k)).map (·.2)).getD (Block.default id)

/-- The block is a `WeatheringCopper`: copper that is not waxed. -/
def isWeatheringCopper (b : Block) : Bool := (Weathering.age? b.id).isSome

/-- The block is a key of `HoneycombItem.WAX_OFF_BY_BLOCK`: waxed copper. All sixty waxed
copper blocks are, and no other block is named so. -/
def isWaxed (b : Block) : Bool := b.id.name.startsWith "minecraft:waxed_"

/-- `level.getRandom().nextInt(bound)`. -/
def nextInt (bound : ℕ) : M ℕ := Component.Fire.nextInt bound

/-- `LightningBolt.randomStepCleaningCopper(level, pos)`: looks at up to `tries` random cells
of the cube around `p` (`BlockPos.randomInCube(random, 10, pos, 1)`); the first one that holds
copper that weathers is cleaned by one stage, and is where the walk goes on. -/
def randomStepCleaningCopper (p : Pos) : ℕ → M (Option Pos)
  | 0 => return none
  | tries + 1 => do
    let x ← nextInt 3
    let y ← nextInt 3
    let z ← nextInt 3
    let candidate : Pos := ⟨p.x - 1 + x, p.y - 1 + y, p.z - 1 + z⟩
    let state ← Level.getBlock candidate
    if isWeatheringCopper state then
      if let some id := Weathering.previous? state.id then
        discard <| Level.setBlock candidate (withPropertiesOf id state)
      return some candidate
    else randomStepCleaningCopper p tries

/-- `LightningBolt.randomWalkCleaningCopper`: up to `steps` steps from `p`, each to a cell of
copper next to the last one; the walk ends when a step finds none. -/
def randomWalkCleaningCopper (p : Pos) : ℕ → M Unit
  | 0 => return
  | steps + 1 => do
    if let some q ← randomStepCleaningCopper p 10 then randomWalkCleaningCopper q steps

/-- `LightningBolt.clearCopperOnLightningStrike(level, struckPos)`: copper that is struck is
as new again, and three to five random walks of one to eight steps clean the copper around
it. Waxed copper is not changed itself, but the walks start from it all the same. -/
def clearCopperOnLightningStrike (p : Pos) : M Unit := do
  let struck ← Level.getBlock p
  let weathering := isWeatheringCopper struck
  if weathering || isWaxed struck then
    if weathering then
      discard <| Level.setBlock p (withPropertiesOf (Weathering.first struck.id) struck)
    let strikes := (← nextInt 3) + 3
    for _ in List.range strikes do
      let steps := (← nextInt 8) + 1
      randomWalkCleaningCopper p steps

/-! ### The tick -/

/-- `LightningBolt.getStrikePosition()`: the block just under the bolt. -/
def strikePosition (pos : Vec3) : Pos := Vec3.blockPos ⟨pos.x, pos.y - 1.0e-6, pos.z⟩

/-- `LightningBolt.spawnFire(0)`: lights a fire in the cell of the bolt, if the cell is air and
a fire can stay there, and if fire is allowed to spread. -/
def spawnFire (pos : Vec3) : M Unit := do
  let l ← get
  if Component.Fire.canSpreadFireAround l then
    let q := pos.blockPos
    if Component.Fire.canBePlacedAt l q then
      discard <| Level.setBlock q (Component.Fire.getState l q)

/-- The box in which the bolt strikes entities: 3 blocks around its position, 9 above. -/
def damageBox (pos : Vec3) : AABB :=
  ⟨pos.x - 3.0, pos.y - 3.0, pos.z - 3.0, pos.x + 3.0, pos.y + 6.0 + 3.0, pos.z + 3.0⟩

/-- An entity that the bolt with the given index would strike in a way the model does not
have: any entity in the box but a bolt. An entity whose size the model does not know counts as
being in the box. -/
def strikesEntity (l : Level) (index : ℕ) (pos : Vec3) : Bool :=
  let box := damageBox pos
  l.entities.any fun e =>
    e.index != index &&
      match e.data with
      | .lightning _ => false
      | _ =>
        match Still.boundingBox? e with
        | some b => b.intersects box
        | none => true

/-- `LightningBolt.tick()`. -/
def tick (index : ℕ) : M Unit := do
  let some e := (← get).entity? index | return
  let .lightning d := e.data | return
  let pos := e.base.pos
  let d := construct e d
  if d.life == 2 then
    -- on easy no fire is lit here
    let struck := strikePosition pos
    Component.Sensor.strike struck
    clearCopperOnLightningStrike struck
    Component.Sculk.onGameEventAt "minecraft:lightning_strike" pos
      { sourceEntity := some (.entity index) }
  let mut d := { d with life := d.life - 1 }
  if d.life < 0 then
    match d.random with
    | none =>
      -- a constructed bolt always has its generator
      Level.setOverflow
    | some r =>
      if d.flashes == 0 then
        Level.removeEntity index
        return
      let (n, r) := r.nextInt 10
      if d.life < -(n : ℤ) then
        d := { d with flashes := d.flashes - 1, life := 1, random := some (skipLong r) }
        spawnFire pos
      else d := { d with random := some r }
  Level.modifyEntity index fun e => { e with data := .lightning d }
  if d.life ≥ 0 && strikesEntity (← get) index pos then Level.setOverflow

/-- The behaviour of the entity. -/
def behaviour : EntityBehaviour := ⟨tick⟩

end Redstone.Entity.Lightning
