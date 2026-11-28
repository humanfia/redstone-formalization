module

public import Redstone.Block.Entity.Inventory
public import Redstone.Entity.Item

/-!
# Item stacks that leave a block

Java classes: `Containers`, `DefaultDispenseItemBehavior`, and the places where a block makes
an `ItemEntity` of its own (`JukeboxBlockEntity.popOutTheItem`, `ComposterBlock.extractProduce`,
`LecternBlock.popBook`).

What the components share when an item stack becomes an item entity: the draws from the
level's random number generator and the entity itself.

## What is left out

* An item entity holds the item and the count of its stack, and whether the stack has
  components, but not the components themselves (`Entities.Item`).
-/

@[expose] public section

namespace Redstone.ItemDrop

/-! ### The level's random number generator -/

/-- `level.getRandom().nextInt(bound)`. -/
def nextInt (bound : ℕ) : M ℕ :=
  modifyGet fun l =>
    let (v, r) := l.random.nextInt bound
    (v, { l with random := r })

/-- `level.getRandom().nextDouble()`. -/
def nextDouble : M Float :=
  modifyGet fun l =>
    let (v, r) := l.random.nextDouble53
    (Float.ofNat v / 9007199254740992.0, { l with random := r })

/-- `level.getRandom().nextFloat()`. -/
def nextFloat : M Float32 :=
  modifyGet fun l =>
    let (v, r) := l.random.nextFloat24
    (Entity.Item.toFloat32 v, { l with random := r })

/-- `RandomSource.triangle(mean, spread)`. -/
def triangle (mean spread : Float) : M Float := do
  let a ← nextDouble
  let b ← nextDouble
  return mean + spread * (a - b)

/-! ### Item entities -/

/-- `Direction.getStepX`, `getStepY` and `getStepZ`, as doubles. -/
def stepVec : Direction → Vec3
  | .west => ⟨-1, 0, 0⟩
  | .east => ⟨1, 0, 0⟩
  | .down => ⟨0, -1, 0⟩
  | .up => ⟨0, 1, 0⟩
  | .north => ⟨0, 0, -1⟩
  | .south => ⟨0, 0, 1⟩

/-- `Vec3.atCenterOf(pos).relative(direction, distance)`: also the value of
`DispenserBlock.getDispensePosition` for the distance 0.7. -/
def centerRelative (p : Pos) (d : Direction) (distance : Float) : Vec3 :=
  let n := stepVec d
  ⟨Float.ofInt p.x + 0.5 + distance * n.x, Float.ofInt p.y + 0.5 + distance * n.y,
    Float.ofInt p.z + 0.5 + distance * n.z⟩

/-- `DefaultDispenseItemBehavior.spawnItem(level, itemStack, accuracy, direction, position)`:
an item entity with the stack, thrown in the given direction. -/
def spawnItem (stack : ItemStack) (accuracy : ℕ) (d : Direction) (position : Vec3) : M Unit := do
  let y := if d.axis = .y then position.y - 0.125 else position.y - 0.15625
  let pow := (← nextDouble) * 0.1 + 0.2
  let spread := 0.0172275 * accuracy.toFloat
  let n := stepVec d
  let vx ← triangle (n.x * pow) spread
  let vy ← triangle 0.2 spread
  let vz ← triangle (n.z * pow) spread
  discard <| Entity.Item.spawnStack ⟨position.x, y, position.z⟩ ⟨vx, vy, vz⟩ stack.id stack.count
    stack.hasComponents

/-- The loop of `Containers.dropItemStack`: splits the stack into item entities of 10 to 30
items, all at the same place. `fuel` bounds the number of entities; the count of the stack is
enough. -/
def dropItemStackLoop (pos : Vec3) : ℕ → ItemStack → M Unit
  | 0, stack => if stack.isEmpty then pure () else Level.setOverflow
  | fuel + 1, stack => do
    if stack.isEmpty then return
    let n := min ((← nextInt 21) + 10) stack.count
    let vx ← triangle 0.0 0.11485000171139836
    let vy ← triangle 0.2 0.11485000171139836
    let vz ← triangle 0.0 0.11485000171139836
    discard <| Entity.Item.spawnStack pos ⟨vx, vy, vz⟩ stack.id n stack.hasComponents
    dropItemStackLoop pos fuel (stack.withCount (stack.count - n))

/-- `Containers.dropItemStack(level, x, y, z, itemStack)` at a block position. The position is
drawn even for an empty stack. -/
def dropItemStack (p : Pos) (stack : ItemStack) : M Unit := do
  let x := Float.ofInt p.x + (← nextDouble) * 0.75 + 0.125
  let y := Float.ofInt p.y + (← nextDouble) * 0.75
  let z := Float.ofInt p.z + (← nextDouble) * 0.75 + 0.125
  dropItemStackLoop ⟨x, y, z⟩ stack.count stack

/-- `Containers.dropContents(level, pos, container)`. -/
def dropContents (p : Pos) (items : Inventory) : M Unit := items.forM (dropItemStack p)

/-- `new ItemEntity(level, x, y, z, stack)`, `setDefaultPickUpDelay()` and `addFreshEntity`:
the stack lies at `pos`, with the small random velocity the constructor gives it, and cannot
be picked up for 10 ticks. -/
def spawnWithPickUpDelay (pos : Vec3) (stack : ItemStack) : M Unit := do
  if stack.isEmpty then return
  discard <| Entity.Item.spawnAtLocation pos stack.id 0 stack.count stack.hasComponents

/-- An item entity thrown out above the block at `p` (`JukeboxBlockEntity.popOutTheItem`,
`ComposterBlock.extractProduce`): at
`Vec3.atLowerCornerWithOffset(pos, 0.5, 1.01, 0.5).offsetRandomXZ(random, 0.7F)`. -/
def popOutAbove (p : Pos) (stack : ItemStack) : M Unit := do
  let offset : Float32 := Float32.ofBits 0x3f333333
  let dx := ((← nextFloat) - 0.5) * offset
  let dz := ((← nextFloat) - 0.5) * offset
  spawnWithPickUpDelay
    ⟨Float.ofInt p.x + 0.5 + dx.toFloat, Float.ofInt p.y + 1.01, Float.ofInt p.z + 0.5 + dz.toFloat⟩
    stack

end Redstone.ItemDrop
