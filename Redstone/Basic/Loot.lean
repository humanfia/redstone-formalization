module

public import Redstone.Basic.Xoroshiro

/-!
# Loot that depends on chance

What is left of a block's loot table (`LootTable`) once everything that does not depend on
chance has been decided, for a block that is broken without a tool, and how the game evaluates
it. The tables themselves are generated (`Entity.Tnt.brokenChanceLoot`); they are written in
the types of this file.

Every loot table draws from a random sequence of its own, a `Xoroshiro` generator that the
server keeps under the key of the table (`LootContext.Builder.create`,
`MinecraftServer.getRandomSequence`), in the order of `LootTable.getRandomItemsRaw`: pool by
pool, and in a pool, roll by roll, first the conditions of the entries and then the functions
of the entry that was chosen.

Only the number of stacks is computed, not the items: that number is what the level's own
generator depends on (`Block.popResource` draws three numbers for each stack).

The forms of loot table that are not expressible here are listed at
`Entity.Tnt.brokenChanceLoot`.
-/

@[expose] public section

namespace Redstone

/-- A number provider (`ContextIntProvider`). -/
inductive LootNumber
  /-- `ConstantValue`. -/
  | const (n : ℤ)
  /-- `UniformGenerator`: `Mth.nextInt(random, min, max)`. -/
  | uniform (min max : ℤ)
  /-- `BinomialDistributionGenerator`: `n` draws of `nextFloat() < p`, the probability given as
  the least `threshold` with `p ≤ threshold / 2 ^ 24`. -/
  | binomial (n threshold : ℕ)
  deriving DecidableEq, Repr

/-- A loot function (`LootItemFunction`) that acts on the count of a stack. -/
inductive LootFunction
  /-- `SetItemCountFunction`. -/
  | setCount (add : Bool) (count : LootNumber)
  /-- `ApplyBonusCount` with the formula `uniform_bonus_count` for a tool without the
  enchantment: `count + random.nextInt(1)`, which draws a number and adds zero. -/
  | uniformBonus
  /-- `ApplyBonusCount` with the formula `binomial_with_bonus_count` for a tool without the
  enchantment: `extra` draws of `nextFloat() < probability`, each success adding one. -/
  | binomialBonus (extra threshold : ℕ)
  /-- `LimitCount`. -/
  | limit (min max : Option ℤ)
  deriving DecidableEq, Repr

/-- An item entry of a pool (`LootItem`). -/
structure LootItem where
  /-- The conditions of the entry that depend on chance (`LootItemRandomChanceCondition`,
  `BonusLevelTableCondition` for a tool without the enchantment), in order: each draws
  `nextFloat()` and holds when the draw is below the probability, given as the least
  `threshold` with `p ≤ threshold / 2 ^ 24`. They are tested until one fails. -/
  chances : List ℕ
  /-- The functions of the entry, then those of its pool, then those of the table. -/
  functions : List LootFunction
  /-- `ItemStack.getMaxStackSize` of the item. -/
  maxStack : ℕ
  deriving DecidableEq, Repr

/-- A pool (`LootPool`) with a single entry: an item, or alternatives (`AlternativesEntry`). -/
structure LootPool where
  /-- The number of rolls. -/
  rolls : ℕ
  /-- The alternatives, in order: the first one whose conditions hold is the entry of the roll. -/
  items : List LootItem
  deriving DecidableEq, Repr

/-- A loot table whose result depends on chance. -/
structure ChanceLoot where
  /-- The key of the random sequence of the table, e.g. `minecraft:blocks/short_grass`. -/
  key : String
  /-- `RandomSupport.seedFromHashOf(key)`: the first eight bytes of the MD5 hash of the key. -/
  hashLo : ℕ
  /-- The second eight bytes of the MD5 hash of the key. -/
  hashHi : ℕ
  /-- The pools that are not excluded by a condition. -/
  pools : List LootPool
  deriving DecidableEq, Repr

namespace LootNumber

/-- `ContextIntProvider.getInt`. -/
def draw (r : Xoroshiro) : LootNumber → ℤ × Xoroshiro
  | const n => (n, r)
  | uniform min max =>
    if min ≥ max then (min, r)
    else
      let (v, r) := r.nextInt (max - min + 1).toNat
      (min + v, r)
  | binomial n threshold =>
    (fun (acc : ℤ × Xoroshiro) =>
      let (v, r) := acc.2.nextFloat24
      (if v < threshold then acc.1 + 1 else acc.1, r))^[n] (0, r)

end LootNumber

namespace LootFunction

/-- `LootItemFunction.apply` on a stack with the given count: the new count. -/
def apply (count : ℤ) (r : Xoroshiro) : LootFunction → ℤ × Xoroshiro
  | setCount add n =>
    let (v, r) := n.draw r
    ((if add then count else 0) + v, r)
  | uniformBonus => (count, (r.nextInt 1).2)
  | binomialBonus extra threshold =>
    let (v, r) := (LootNumber.binomial extra threshold).draw r
    (count + v, r)
  | limit min max =>
    let count := match min with | some m => Max.max count m | none => count
    (match max with | some m => Min.min count m | none => count, r)

end LootFunction

namespace LootItem

/-- Tests the conditions of the entry (`LootPoolEntryContainer.canRun`). -/
def test (r : Xoroshiro) : List ℕ → Bool × Xoroshiro
  | [] => (true, r)
  | threshold :: rest =>
    let (v, r) := r.nextFloat24
    if v < threshold then test r rest else (false, r)

/-- `LootItem.createItemStack` followed by the stack splitter of `LootTable.getRandomItems`
(`createStackSplitter`): the number of stacks the entry gives. A stack whose count is zero or
negative is empty, and is still one stack. -/
def stackCount (i : LootItem) (r : Xoroshiro) : ℕ × Xoroshiro :=
  let (count, r) := i.functions.foldl (fun acc f => f.apply acc.1 acc.2) ((1 : ℤ), r)
  (if count < i.maxStack then 1 else (count.toNat + i.maxStack - 1) / i.maxStack, r)

end LootItem

namespace LootPool

/-- `LootPool.addRandomItem`: one roll. The alternatives are tried in order
(`AlternativesEntry`); the first one whose conditions hold gives its stacks. -/
def roll (r : Xoroshiro) : List LootItem → ℕ × Xoroshiro
  | [] => (0, r)
  | i :: rest =>
    let (ok, r) := LootItem.test r i.chances
    if ok then i.stackCount r else roll r rest

/-- `LootPool.addRandomItems`: the number of stacks of all rolls. -/
def stackCount (p : LootPool) (r : Xoroshiro) : ℕ × Xoroshiro :=
  (fun (acc : ℕ × Xoroshiro) =>
    let (n, r) := roll acc.2 p.items
    (acc.1 + n, r))^[p.rolls] (0, r)

end LootPool

namespace ChanceLoot

/-- The generator of the table's random sequence when it is first used. -/
def newSequence (t : ChanceLoot) : Xoroshiro :=
  .sequence worldSeed t.hashLo t.hashHi

/-- `LootTable.getRandomItems`: the number of stacks, drawing from the table's sequence. -/
def stackCount (t : ChanceLoot) (r : Xoroshiro) : ℕ × Xoroshiro :=
  t.pools.foldl (fun acc p =>
    let (n, r) := p.stackCount acc.2
    (acc.1 + n, r)) (0, r)

end ChanceLoot

end Redstone
