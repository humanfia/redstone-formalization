module

public import Redstone.Mechanics.Tick

/-!
# Blocks that drop more than themselves

Java classes: `DropExperienceBlock`, `InfestedBlock`, `SpawnerBlock`.

What sets these classes apart from `Block` is one method, `spawnAfterBreak`, which the game
calls when a block was broken with drops (`Block.dropResources`) or destroyed by an explosion:
an ore releases experience, a spawner releases more, and an infested block releases a
silverfish. Everything else about them is the behaviour of a plain block (a spawner has a block
entity, which the model does not tick), so `behaviour` is `Behaviour.inert`.

`spawnAfterBreak` itself is not a field of `Behaviour`: it runs in the middle of
`Level.dropResources`, below the components, and what it does depends on the block alone. It is
`Level.spawnAfterBreak` in `Redstone.Mechanics.Update`, which reads what each block releases from
the generated table `Entity.Tnt.afterBreak`. That table also covers the other classes that
override the method, which belong to other components: `RedStoneOreBlock`
(`Redstone.Component.Extra`) and the sculk sensor, shrieker and catalyst
(`Redstone.Component.Sculk`).

The loot of every block is next to it: `Level.getDrops`, `Level.popResource`, and the experience
orbs of `Level.awardExperience`.

## What is left out

* The silverfish of an infested block is a mob. With the game rule `block_drops` on it appears,
  as an entity the model does not move, and `Level.overflow` is set
  (`Level.spawnInfestation`). Its spawn animation (`spawnAnim`) is a client effect.
* Enchanted tools: nothing in the model breaks a block with a tool, so the experience is never
  changed by an enchantment (`EnchantmentHelper.processBlockExperience`) and the silverfish is
  never kept in (`PREVENTS_INFESTED_SPAWNS`).
* An explosion calls `spawnAfterBreak` without experience; see `Level.getExplosionDrops`.
-/

@[expose] public section

namespace Redstone.Component.Loot

/-- The behaviour of the blocks of this component: that of a plain block. What they release
when they are broken is `Level.spawnAfterBreak`. -/
def behaviour (self : Block) : Behaviour := .inert self

end Redstone.Component.Loot
