module

public import Redstone.Mechanics.Tick
public import Redstone.Entity.PrimedTnt

/-!
# TNT

Java class: `TntBlock`.

A TNT block that receives a redstone signal, when it is placed or when a neighbour changes, is
removed and replaced by a primed TNT entity (`Redstone.Entity.PrimedTnt`) at the bottom centre
of its cell, with a fuse of 80 game ticks. Flint and steel or a fire charge used on the block
do the same. A TNT block caught in an explosion becomes a primed TNT with a fuse of 10 to 29
ticks (`TntBlock.wasExploded`, in `Redstone.Entity.Tnt.onExplosionHit`).

The game rule `tnt_explodes` is taken to be on, as it is by default.

## What is left out

* `playerWillDestroy`: an unstable TNT block is primed when a player breaks it. Players do not
  break blocks in the model, so the property `unstable` has no effect.
* The owner of the primed TNT, sounds, and the wear of the flint and steel.
-/

@[expose] public section

namespace Redstone.Component.Tnt

/-- `TntBlock.prime(level, pos, source, item)`: adds a primed TNT for the block at `p`. It
always succeeds, since TNT is allowed to explode and no adventure-mode player is involved. -/
def prime (p : Pos) : M Bool := do
  discard <| Entity.Tnt.addPrimedTnt p fun r => (80, r)
  Level.gameEvent "minecraft:prime_fuse" p
  return true

/-- The behaviour of a TNT block. -/
def behaviour (self : Block) : Behaviour :=
  match self with
  | .tnt _ =>
    { Behaviour.inert self with
      onPlace := fun p old _ => do
        if !old.is .tnt then
          if (← Level.hasNeighborSignal p) then
            if (← prime p) then discard <| Level.removeBlock p false
      neighborChanged := fun p _ _ => do
        if (← Level.hasNeighborSignal p) then
          if (← prime p) then discard <| Level.removeBlock p false
      -- A burning projectile primes the block (`Projectile.mayInteract` holds for a
      -- projectile without owner).
      onProjectileHit := fun p _ _ index => do
        let burning := ((← get).entity? index).any fun e =>
          match e.data with
          | .projectile _ d => d.fire > 0
          | _ => false
        if burning then
          if (← prime p) then discard <| Level.removeBlock p false
      useItemOn := fun p _ item => do
        if item != "minecraft:flint_and_steel" && item != "minecraft:fire_charge" then
          return false
        if (← prime p) then discard <| Level.setBlock p .AIR 11
        return true }
  | _ => .inert self

end Redstone.Component.Tnt
