module

public import Redstone.Entity.FallingBlock

/-!
# Blocks that fall

Java classes: `FallingBlock` with `ColoredFallingBlock` and `SandBlock` (sand, red sand,
gravel), `ConcretePowderBlock`, `AnvilBlock` and `DragonEggBlock`.

When such a block is placed, or a neighbour changes, it schedules a tick. On that tick it turns
into a falling block entity if the block below is free. Concrete powder turns to concrete when
a neighbour holds water.

Not modelled: the teleporting of a dragon egg that is clicked (using one sets `Level.overflow`),
the anvil's menu, and suspicious sand and gravel (`BrushableBlock`), which fall by a mechanism of
their own.
-/

@[expose] public section

namespace Redstone.Component.FallingBlock

open Entity.FallingBlock (isFree isAnvil isConcretePowder touchesLiquid concreteOf)

/-- `getDelayAfterPlace`: 2 game ticks, 5 for the dragon egg. -/
def delayAfterPlace (b : Block) : ℕ := if b.is .dragon_egg then 5 else 2

/-- `FallingBlockEntity.fall(level, pos, state)` followed by `FallingBlock.falling(entity)`: the
block at `p` is replaced by a falling block entity. An anvil is set to hurt entities. The game
creates the entity before it removes the block and adds it afterwards; the model numbers
entities when they are added. -/
def fall (self : Block) (p : Pos) : M Unit := do
  let pos : Vec3 := ⟨Phys.ofInt p.x + 0.5, Phys.ofInt p.y, Phys.ofInt p.z + 0.5⟩
  discard <| Level.setBlock p self.fluidBlock
  let entry := ((← get).gameTime, 0)
  let data : Entities.FallingBlock :=
    if isAnvil self then
      { blockState := self, hurtEntities := true, fallDamagePerDistance := 0x40000000,
        fallDamageMax := 40, phys := { sectionEntry := entry } }
    else { blockState := self, phys := { sectionEntry := entry } }
  discard <| Level.addEntity ⟨pos, .zero, false⟩ (.fallingBlock data)

/-- `FallingBlock.tick`: the block falls if the block below is free. -/
def tick (self : Block) (p : Pos) : M Unit := do
  if isFree ((← get).blockAt (p.step .down)) && p.y ≥ -64 then fall self p

/-- The behaviour of a block that falls. -/
def behaviour (self : Block) : Behaviour :=
  { Behaviour.inert self with
    onPlace := fun p _ _ => Level.scheduleTick p self.id (delayAfterPlace self)
    updateShape := fun p _ _ _ => do
      if isConcretePowder self && touchesLiquid (← get) p then
        return (concreteOf self).getD self
      Level.scheduleTick p self.id (delayAfterPlace self)
      return self
    tick := tick self
    useWithoutItem := fun _ _ => do
      -- a dragon egg that is clicked teleports, which is not modelled
      if self.is .dragon_egg then Level.setOverflow
      return false }

end Redstone.Component.FallingBlock
