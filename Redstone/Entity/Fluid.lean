module

public import Redstone.Mechanics.Tick
public import Redstone.Entity.Geometry

/-!
# Entities and fluids

Java classes: `EntityFluidInteraction` (`update`, `applyCurrentTo`), `Entity`
(`updateFluidInteraction`, `doWaterSplashEffect`, `getFluidInteractionBox`), `FluidState` and
`FlowingFluid` (`getOwnHeight`, `getHeight`, `getFlow`, `getAABB`).

An entity that updates its fluid interaction looks at every block its box reaches. For each
fluid it finds how deep it stands in it (`getFluidHeight`), and it adds up the directions in
which the fluid flows there. Water and lava then push the entity along the sum (`applyCurrentTo`).
An entity that has just come into water makes a splash, which draws numbers from the entity's own
generator and is a game event.

This file has what does not depend on the kind of entity: the fluid states of a level
(`Level.fluidStateAt`), their height and flow, the result of an update (`Interaction`), the push,
and the splash. The entity units call it from where the game does:

* a dropped item updates at the start (`Entity.baseTick`) and at the end of its tick, floats up
  in water and lava, and is hurt by lava (`Redstone.Entity.Item`);
* a primed TNT updates at the end of its tick (`Redstone.Entity.PrimedTnt`);
* a minecart updates after it moved (`Redstone.Entity.Minecart`);
* a falling block never updates: fluids neither push it nor slow it down.

What a fluid does to an entity that passes through it (`FluidState.entityInside`: water puts a
fire out, lava sets on fire and hurts) is in `Redstone.Entity.Touch`.

The fluids are read from the block states (`Block.fluidState`). Fluids do not flow in the model
yet (`Redstone.Mechanics.Fluid`), so what is here is right for water and lava that are at rest.

The scenarios are in `tests/scenarios/entity-fluid` (written by
`tests/palettes/entity_fluid_gen.py`). Two wait in `tests/pending/scenarios/entity-fluid`:
`cart-lava-pool`, a minecart in lava, which the minecart unit does not model, and `fuzz-cart-05`,
in which a TNT minecart explodes. Scenarios in which a fluid would have to flow (a block set
or broken next to a fluid that is not at rest) cannot pass before fluids flow in the model.

## What is left out

* Bubble columns (`BubbleColumnBlock.entityInside`): an entity that touches one sets
  `Level.overflow` (`Redstone.Entity.Touch`).
* Whether the eyes of the entity are in a fluid (`isEyeInFluid`), which none of the modelled
  entities uses.
* Rain.
* `FAST_LAVA`: lava pushes with the strength it has in the overworld.
-/

@[expose] public section

namespace Redstone

namespace FluidState

/-- `FluidState.getOwnHeight()`: a ninth of the amount, as a `float`. -/
def ownHeight (s : FluidState) : Float32 := Float32.ofNat s.amount / 9

end FluidState

namespace Block

/-- The block is in the tag `minecraft:blocks_fluid_flow` (`blocks_motion` and `all_signs`): the
tag lists the solid blocks other than cobweb and bamboo sapling, and the signs. -/
def blocksFluidFlow (b : Block) : Bool :=
  match b with
  | .standingSign .. | .wallSign .. | .ceilingHangingSign .. | .wallHangingSign .. => true
  | _ => b.attrs.solid && !b.is .cobweb && !b.is .bamboo_sapling

/-- The block is an `IceBlock` (ice or frosted ice). -/
def isIceBlock (b : Block) : Bool := b.is .ice || b.is .frosted_ice

end Block

namespace Level

/-- `FlowingFluid.getHeight(fluidState, level, pos)` as a `float`: a fluid under the same fluid
fills its block. -/
def fluidHeight (l : Level) (p : Pos) (s : FluidState) : Float32 :=
  if s.isEmpty then 0
  else if s.fluid.isSame (l.fluidStateAt (p.step .up)).fluid then 1
  else s.ownHeight

/-- `FluidState.getAABB(level, pos)` of a fluid that is not empty. -/
def fluidBox (l : Level) (p : Pos) (s : FluidState) : AABB :=
  let x := Phys.ofInt p.x
  let y := Phys.ofInt p.y
  let z := Phys.ofInt p.z
  AABB.of x y z (x + 1.0) (y + (l.fluidHeight p s).toFloat) (z + 1.0)

/-- `FlowingFluid.isSolidFace(level, pos, direction)` for a horizontal direction. -/
def isSolidFace (l : Level) (fluid : Fluid) (p : Pos) (dir : Direction) : Bool :=
  let state := l.blockAt p
  if state.fluidState.fluid.isSame fluid then false
  else if state.isIceBlock then false
  else (l.supportAttrs p).isFaceSturdy dir

end Level

namespace Entity.Fluid

/-- `Direction.Plane.HORIZONTAL`, with the step of each direction along x and z. -/
def horizontal : List (Direction × Float32 × Float32) :=
  [(.north, 0, -1), (.east, 1, 0), (.south, 0, 1), (.west, -1, 0)]

/-- `Vec3.normalize()`. -/
def normalize (a : Vec3) : Vec3 :=
  let dist := Float.sqrt (a.x * a.x + a.y * a.y + a.z * a.z)
  if dist < Phys.eps5f then .zero else ⟨a.x / dist, a.y / dist, a.z / dist⟩

/-- `Vec3.scale(s)`. -/
def scale (a : Vec3) (s : Float) : Vec3 := a.mul s s s

/-- `Vec3.length()`. -/
def length (a : Vec3) : Float := Float.sqrt (a.x * a.x + a.y * a.y + a.z * a.z)

/-- `FlowingFluid.getFlow(level, pos, fluidState)`: the direction in which the fluid at `p`
flows. Each horizontal neighbour that holds the same fluid, or none, pulls by the difference in
height; a neighbour that holds none and does not block the flow counts with the fluid below it,
which lies eight ninths lower. A falling fluid next to a solid face flows down. -/
def flow (l : Level) (p : Pos) (s : FluidState) : Vec3 :=
  let affectsFlow (n : FluidState) : Bool := n.isEmpty || n.fluid.isSame s.fluid
  let own := s.ownHeight
  let step (acc : Float × Float) (d : Direction × Float32 × Float32) : Float × Float :=
    let q := p.step d.1
    let neighbour := l.fluidStateAt q
    if affectsFlow neighbour then
      let neighbourHeight := neighbour.ownHeight
      let distance : Float32 :=
        if neighbourHeight == 0 then
          if !(l.blockAt q).blocksFluidFlow then
            let below := l.fluidStateAt (q.step .down)
            if affectsFlow below && below.ownHeight > 0 then
              own - (below.ownHeight - Float32.ofBits 0x3f638e39)
            else 0
          else 0
        else if neighbourHeight > 0 then own - neighbourHeight
        else 0
      if distance != 0 then
        (acc.1 + (d.2.1 * distance).toFloat, acc.2 + (d.2.2 * distance).toFloat)
      else acc
    else acc
  let (flowX, flowZ) := horizontal.foldl step (0.0, 0.0)
  let v : Vec3 := ⟨flowX, 0.0, flowZ⟩
  let down := s.falling && horizontal.any fun d =>
    let q := p.step d.1
    l.isSolidFace s.fluid q d.1 || l.isSolidFace s.fluid (q.step .up) d.1
  normalize (if down then (normalize v).add ⟨0.0, -6.0, 0.0⟩ else v)

/-- `EntityFluidInteraction.CurrentAccumulator`: the flow an entity gathered from one kind of
fluid. -/
structure Current where
  /-- The largest depth seen so far. -/
  height : Float := 0.0
  /-- `accumulatedCurrent`. -/
  accumulated : Vec3 := .zero
  /-- `currentCount`. -/
  count : ℕ := 0

/-- What `EntityFluidInteraction.update` leaves behind: for each fluid the height of its
surface above the feet of the entity (a `Tracker`; zero for a fluid the entity does not touch),
and for water and for lava the flow gathered. -/
structure Interaction where
  water : Float := 0.0
  flowingWater : Float := 0.0
  lava : Float := 0.0
  flowingLava : Float := 0.0
  waterCurrent : Current := {}
  lavaCurrent : Current := {}
  /-- The value `update` returns: some fluid was met. -/
  inAnyFluid : Bool := false

namespace Interaction

/-- The height of the tracker of one fluid. -/
def tracker (it : Interaction) : Redstone.Fluid → Float
  | .empty => 0.0
  | .water => it.water
  | .flowingWater => it.flowingWater
  | .lava => it.lava
  | .flowingLava => it.flowingLava

/-- Sets the height of the tracker of one fluid. -/
def setTracker (it : Interaction) (fluid : Redstone.Fluid) (h : Float) : Interaction :=
  match fluid with
  | .empty => it
  | .water => { it with water := h }
  | .flowingWater => { it with flowingWater := h }
  | .lava => { it with lava := h }
  | .flowingLava => { it with flowingLava := h }

/-- `getFluidHeight(FluidTags.WATER)`. -/
def waterHeight (it : Interaction) : Float :=
  let h := if it.water > 0.0 then it.water else 0.0
  if it.flowingWater > h then it.flowingWater else h

/-- `getFluidHeight(FluidTags.LAVA)`. -/
def lavaHeight (it : Interaction) : Float :=
  let h := if it.lava > 0.0 then it.lava else 0.0
  if it.flowingLava > h then it.flowingLava else h

/-- `isInFluid(FluidTags.WATER)`. -/
def inWater (it : Interaction) : Bool := it.waterHeight > 0.0

/-- `isInFluid(FluidTags.LAVA)`. -/
def inLava (it : Interaction) : Bool := it.lavaHeight > 0.0

end Interaction

/-- The integers from `lo` to `hi`, both included. -/
def closedRange (lo hi : ℤ) : List ℤ := (List.range (hi + 1 - lo).toNat).map fun i => lo + i

/-- `EntityFluidInteraction.update(entity, ignoreCurrent)` for an entity whose box is `bb`
(`getBoundingBox()`; the box that is searched is this one made smaller by 0.001 on every side,
`getFluidInteractionBox`). The trackers and the currents start from zero in every update. -/
def update (l : Level) (bb : AABB) (ignoreCurrent : Bool := false) : Interaction := Id.run do
  let box := bb.deflate (Phys.d 0x3f50624dd2f1a9fc)
  let entityY := bb.minY
  let mut it : Interaction := {}
  for x in closedRange (Phys.floor box.minX) (Phys.ceil box.maxX - 1) do
    for y in closedRange (Phys.floor box.minY) (Phys.ceil box.maxY - 1) do
      for z in closedRange (Phys.floor box.minZ) (Phys.ceil box.maxZ - 1) do
        let p : Pos := ⟨x, y, z⟩
        let s := l.fluidStateAt p
        if !s.isEmpty then
          let fluidTop := Phys.ofInt y + (l.fluidHeight p s).toFloat
          if !(fluidTop < box.minY) then
            let height := Phys.max (fluidTop - entityY) (it.tracker s.fluid)
            it := { it.setTracker s.fluid height with inAnyFluid := true }
            if !ignoreCurrent then
              let current := if s.fluid.isWater then it.waterCurrent else it.lavaCurrent
              let currentHeight := Phys.max height current.height
              let v := flow l p s
              let v :=
                if currentHeight < Phys.d 0x3fd999999999999a then scale v currentHeight else v
              let current : Current := ⟨currentHeight, current.accumulated.add v, current.count + 1⟩
              it := if s.fluid.isWater then { it with waterCurrent := current }
                else { it with lavaCurrent := current }
  return it

/-- `CurrentAccumulator.applyTo(entity, scale)` for an entity that is not a player: the velocity
`motion` after the push of the gathered flow. A slow entity is pushed with at least 0.0045. -/
def Current.applyTo (c : Current) (motion : Vec3) (strength : Float) : Vec3 :=
  if c.count != 0 && !(c.accumulated.lengthSqr < Phys.eps5f) then
    let impulse := scale (normalize c.accumulated) strength
    let least := Phys.d 0x3f726e978d4fdf3c
    let slow := Phys.d 0x3f689374bc6a7efa
    let impulse :=
      if motion.x.abs < slow && motion.z.abs < slow && length impulse < least then
        scale (normalize impulse) least
      else impulse
    motion.add impulse
  else motion

/-- The pushes of `Entity.updateFluidInteraction` for an entity that fluids push
(`isPushedByFluid`): water pushes with 0.014, lava with 0.0023333333333333335. -/
def Interaction.push (it : Interaction) (motion : Vec3) : Vec3 :=
  let motion :=
    if it.inWater then it.waterCurrent.applyTo motion (Phys.d 0x3f8cac083126e979) else motion
  if it.inLava then it.lavaCurrent.applyTo motion (Phys.d 0x3f631d5acb6f4651) else motion

/-- The entity's own generator after `Entity.doWaterSplashEffect`, for an entity whose width is
the `float` with the bits `width`: two numbers for the pitch of the sound, and then for each of
the `1.0F + width * 20.0F` bubbles three `double`s and for each of as many splash particles
two. -/
def splashRandom (r : JavaRandom) (width : UInt32) : JavaRandom :=
  let bound : Float32 := 1 + Float32.ofBits width * 20
  let particles := ((List.range 64).filter fun i => Float32.ofNat i < bound).length
  -- a `float` is one step of the generator, a `double` two
  (List.range (2 + particles * 10)).foldl (fun r _ => (r.next 32).2) r

end Entity.Fluid

end Redstone
