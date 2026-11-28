module

public import Redstone.Mechanics.Update
public import Redstone.Block.Weathering

/-!
# Copper weathering on random ticks

Java classes: `ChangeOverTimeBlock`, `WeatheringCopper`, and the `randomTick` of the classes that
implement them: `WeatheringCopperFullBlock`, `WeatheringCopperSlabBlock`,
`WeatheringCopperStairBlock`, `WeatheringCopperDoorBlock`, `WeatheringCopperTrapDoorBlock`,
`WeatheringCopperBarsBlock`, `WeatheringCopperGrateBlock`, `WeatheringCopperBulbBlock`,
`WeatheringCopperChainBlock`, `WeatheringLanternBlock`, `WeatheringLightningRodBlock`,
`WeatheringCopperChestBlock`, `WeatheringCopperGolemStatueBlock`.

A copper block that is not waxed and not fully oxidized gets random ticks. On one, with a chance
of `0.05688889`, it looks at the unwaxed copper within taxicab distance 4: if any of it is less
weathered than the block, nothing happens; otherwise the block weathers one stage with a chance
that grows with the share of copper around it that is further along
(`ChangeOverTimeBlock.getNextState`). The new block keeps the properties of the old one
(`withPropertiesOf`).

This is not a component of its own. The copper blocks belong to many components (the bulb to
`Lamp`, the door and the trapdoor to `Door`, the chest to `Container`, ...);
`Redstone.Mechanics.RandomTick` calls `randomTick` of this file for a copper block in place of
the `randomTick` of its behaviour, so that every copper block weathers by its id and no
component has to know.

The chances are compared as the game compares them, in single precision: `roundFloat` rounds an
exact fraction to the nearest `float`, so no floating-point number is used.

Left out:

* `WeatheringCopperChestBlock.randomTick` asks whether an entity has the chest open
  (`getEntitiesWithContainerOpen`, a search for players around the chest). The player of the
  `use` actions is not in the world, so the answer is always no.
* What a block does when it is replaced by its next stage is the business of its component:
  the two halves of a door or of a double chest follow each other through their `updateShape`.
-/

@[expose] public section

namespace Redstone.Component.Weathering

open Block.Weathering (WeatherState)

/-- `Enum.ordinal()` of a `WeatherState`. -/
def ordinal : WeatherState → ℕ
  | .unaffected => 0
  | .exposed => 1
  | .weathered => 2
  | .oxidized => 3

/-- The whole number nearest to `q`, the even one when two are equally near. -/
def roundHalfEven (q : ℚ) : ℤ :=
  let f := q.floor
  let r := q - f
  if r < 1 / 2 then f else if 1 / 2 < r then f + 1 else if f % 2 = 0 then f else f + 1

/-- The loop of `roundFloat`: looks for the power of two that brings `q` to `2 ^ 23` or more. -/
def roundFloatLoop (q : ℚ) : ℕ → ℕ → ℚ
  | 0, _ => q
  | fuel + 1, k =>
    if (2 : ℚ) ^ 23 ≤ q * 2 ^ k then roundHalfEven (q * 2 ^ k) / 2 ^ k
    else roundFloatLoop q fuel (k + 1)

/-- The `float` (IEEE single precision, 24 significant bits) nearest to `q`, as a fraction, for
`0 < q < 2 ^ 24` that is not below the smallest normal number: what a `float` operation with
the exact result `q` returns, and what the constant `q` written in the source denotes. -/
def roundFloat (q : ℚ) : ℚ := if q ≤ 0 then 0 else roundFloatLoop q 128 0

/-- `WeatheringCopper.getNext(state)`: the next stage of the copper block `state`, with the same
properties (`Block.withPropertiesOf`). -/
def getNext (state : Block) : Option Block := do
  let next ← Block.Weathering.next? state.id
  Block.ofProps? next fun name => state.toProps.lookup name

/-- `WeatheringCopper.getChanceModifier`. -/
def chanceModifier : WeatherState → ℚ
  | .unaffected => 3 / 4
  | _ => 1

/-- The offsets of `BlockPos.withinManhattan(origin, 4)` other than the origin itself. The order
does not matter to `getNextState`. -/
def scanOffsets : List (ℤ × ℤ × ℤ) :=
  let range : List ℤ := [-4, -3, -2, -1, 0, 1, 2, 3, 4]
  range.flatMap fun dx => range.flatMap fun dy => range.filterMap fun dz =>
    if dx.natAbs + dy.natAbs + dz.natAbs ≤ 4 ∧ (dx, dy, dz) ≠ (0, 0, 0) then some (dx, dy, dz)
    else none

/-- The ages of the weathering copper blocks around `p` (`findBlocksInManhattan(pos, 4)` without
`pos`, filtered by `isSameAgeingType`). -/
def agesAround (l : Level) (p : Pos) : List WeatherState :=
  scanOffsets.filterMap fun (dx, dy, dz) =>
    Block.Weathering.age? (l.blockAt ⟨p.x + dx, p.y + dy, p.z + dz⟩).id

/-- The chance with which a block of age `own` weathers when the copper around it has the ages
`ages`, none of them less than `own`: `chance * chance * getChanceModifier()` of
`ChangeOverTimeBlock.getNextState`, in `float` arithmetic. -/
def actualChance (own : WeatherState) (ages : List WeatherState) : ℚ :=
  let older := (ages.filter fun a => ordinal own < ordinal a).length
  let same := ages.length - older
  let chance := roundFloat ((older + 1 : ℚ) / (older + same + 1 : ℚ))
  roundFloat (roundFloat (chance * chance) * chanceModifier own)

/-- `random.nextFloat() < chance`, for a chance given exactly. -/
def nextFloatBelow (chance : ℚ) : M Bool :=
  modifyGet fun l =>
    let (n, r) := l.random.nextFloat24
    (decide ((n : ℚ) / 2 ^ 24 < chance), { l with random := r })

/-- `ChangeOverTimeBlock.getNextState(state, level, pos, random)` for a copper block of age
`own`: the state the block weathers to now, if it does. -/
def getNextState (own : WeatherState) (state : Block) (p : Pos) : M (Option Block) := do
  let ages := agesAround (← get) p
  if ages.any fun a => ordinal a < ordinal own then return none
  if ← nextFloatBelow (actualChance own ages) then return getNext state else return none

/-- `eachBlockOncePerDayChance`, the `float` written `0.05688889F`. -/
def eachBlockOncePerDayChance : ℚ := roundFloat (5688889 / 100000000)

/-- `ChangeOverTimeBlock.changeOverTime(state, level, pos, random)`. -/
def changeOverTime (own : WeatherState) (state : Block) (p : Pos) : M Unit := do
  if ← nextFloatBelow eachBlockOncePerDayChance then
    if let some weathered ← getNextState own state p then
      discard <| Level.setBlock p weathered 3

/-- `randomTick(state, level, pos, random)` of the copper classes, for the block `state` at `p`:
nothing for a block that is not copper, or that is waxed. Copper that is fully oxidized gets no
random tick in the game (`isRandomlyTicking`); here it gets one that does nothing. -/
def randomTick (state : Block) (p : Pos) : M Unit := do
  match Block.Weathering.age? state.id, Block.Weathering.next? state.id with
  | some own, some _ =>
    match state with
    -- `WeatheringCopperDoorBlock`: only the lower half weathers; the upper half follows it.
    | .weatheringCopperDoor _ s => if s.half = .lower then changeOverTime own state p
    -- `WeatheringCopperChestBlock`: not the right half of a double chest, and the block entity
    -- has to be there.
    | .weatheringCopperChest _ s =>
      if s.type ≠ .right then
        if let some (.chest _) := (← get).blockEntities p then changeOverTime own state p
    | _ => changeOverTime own state p
  | _, _ => pure ()

end Redstone.Component.Weathering
