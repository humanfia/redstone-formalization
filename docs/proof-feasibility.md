# Proving circuits by kernel evaluation: what was measured

Theorems about concrete circuits are proved by letting the Lean kernel run the model:
`decide +kernel` on a decidable statement about `Level.step` applied to a concrete level. This
adds no axiom (`#print axioms` shows `propext`, `Classical.choice`, `Quot.sound` at most), and it
only works if the kernel can evaluate the model in reasonable time and memory.

This file records the spike that was run before any proof was written: what was measured, what
did not work, what was changed, and the recipe that follows from it.

## Summary

* On the model as it was (`origin/main` at `7e155d75`), one game tick of a lever and a lamp is
  proved in 0.2 s. Longer runs were not usable: a 15-dust line toggled twice (8 ticks) took
  468 s and 20.7 GB, and did not finish at 16 ticks (killed at 32 GB); a 4-repeater clock failed
  at 8 ticks. Unrelated blocks in the world made it worse (not flat). Anything that removes a
  block was stuck, because `Block.fluidBlock` parsed a string.
* **Decision: the representation behind `World` and `Level.blockEntities` was replaced** by a
  canonical trie on a `Nat` key (`Redstone.Basic.PosMap`), and `Block.fluidBlock` and
  `clearWaterlogged` were made string-free. `lake test` is unchanged: 9826 of 9826 scenarios.
* With that, the cost of a run no longer depends on what else is in the world, and one long
  evaluation grows linearly in time. It still grows linearly in memory, because the kernel
  never frees its cache within one declaration (19.6 GB at 16 ticks of the dust line), and the
  clock still fails at 8 ticks when evaluated in one go.
* **The method that works is one lemma per game tick between state literals.** Each lemma is
  checked in bounded time and memory, whatever came before: 0.06 to 1.1 s per tick for the
  12-block sticky piston, the hopper pair and the repeater clock, at 1.5 GB. On this evidence
  the contingency of the plan (an abstract circuit semantics with simulation proofs) is not
  needed **for circuits without entities**.
* **What the measurements do not cover** (see "What this does not show"): the per-tick lemmas
  were checked one by one and never joined into a theorem about a run; the comparison they use
  is not in the repository; and a level with an entity in it (an item, a minecart, primed TNT, a
  projectile) can be neither evaluated nor checkpointed, because entities are computed in
  `Float`. For those the question the contingency answers is still open.
* Two things a prover must know: check the lemmas of a file **one at a time**
  (`set_option Elab.async false`), and expect **redstone dust** to be the expensive block:
  switching a 15-dust line off is 30 to 60 s and 8.9 GB for that one tick.

## How it was measured

Scratch Lean files, one per probe, each run on a compute node of the cluster
(`srun -p cpu -c 8 --mem 32G`) with `lean` directly. The nodes have no `/usr/bin/time`, so:

* **kernel time** is the profiler's cumulative `type checking` time of the file
  (`set_option profiler true`): the time the kernel spent, which for these files is the
  evaluation. It includes about 0.1 to 0.6 s for checking the definitions of the probe itself.
* **peak RSS** is `VmHWM` of the `lean` process, sampled every 0.2 s.
* Wall time is not reported: loading the `.olean` files from the cluster's file system took
  between 3 and 116 s for the same file, depending on the node's cache.

Kernel times of probes that ran while other probes ran on the same node are inflated; where a
number was measured again on a quiet node, the quiet number is given.

Every probe that passed was checked with `#print axioms`: none depends on anything but the three
standard axioms.

The circuits:

* **lever-lamp** (S1): stone, a lever on it, a lamp next to the lever; the lever is used, one
  tick runs, the lamp is lit.
* **clock**: a ring of four repeaters (delay 1) with redstone dust at the corners on a 3×3
  stone floor, started by a block of redstone that is placed for one tick. Period 8.
* **line**: a lever and 15 redstone dust in a row on stone; the lever is used before every
  fourth tick, so the line goes on at tick 1, off at tick 5, and so on.
* **idle**: the empty level.
* **piston**: a sticky piston pushing a row of 12 stone blocks (the limit), powered through a
  lever on a block behind it. The extension takes three ticks.
* **hoppers**: a hopper above a hopper, with 1 or 5 pieces of redstone in the upper one. An item
  moves every 8 ticks.
* **lever pop**: the block under a lever is destroyed; the lever breaks.

"Monolithic" means one `decide +kernel` over the whole run from the initial level, observing
the blocks of the circuit, `overflow`, the number of scheduled ticks and the game time.

## S0: primitives

Each is one `decide +kernel`. Times are from the model after the changes; on the model before
the changes all of them passed too, except `fluidBlock`.

| Probe | Kernel time | Result |
|---|---|---|
| string literal `=`, `≠`, `==` (three theorems) | 33 ms | ok |
| block entity type by `typeName` (`BlockEntity.new? .hopper`) | 15 ms | ok |
| `itemMaxStackSize "minecraft:redstone" = 64` | 400 ms | ok, but slow: a scan of about 320 item names |
| `Block` inequality, `Pos.step`, `attrs.conductor` (three theorems) | 28 ms | ok |
| `Block.fluidBlock (.plain .stone) = .AIR` | **stuck** before, 12 ms after | fixed |
| `ℚ`: `¬ (0 + 1/2 ≥ 1)`, `1/2 + 1/2 ≥ 1` | 3 ms | ok |
| `AnalogSource.roundFloat (1/3)` | 4 ms | ok |
| `Container.roundFloat (1/3)` (uses `Int.log`) | 6 ms | ok |
| `(rules.env maxDepth).block lever` signal | 3 ms | ok |

## S1 to S4: the model before the changes

| Probe | Ticks | Kernel time | Peak RSS | Result |
|---|---|---|---|---|
| S1 lever-lamp | 1 | 0.20 s | 1.1 GB | ok |
| S2 idle | 1 / 4 / 16 / 64 | 4 / 6 / 12 / 44 ms | 1.1 GB | ok, linear |
| S2 clock | 1 | 0.84 s | 1.3 GB | ok |
| S2 clock | 2 | 15.1 s (busy node) | 1.7 GB | ok |
| S2 clock | 4 | 6.8 s (busy node) | 2.1 GB | ok |
| S2 clock | 8 | 681 s | 26.2 GB | **fails**: `(kernel) deterministic timeout` |
| S2 clock | 16, 32, 64 | | | not run |
| S2 line | 1 / 2 / 4 | 13.1 / 12.2 / 12.3 s | 3.9 GB | ok (one switch-on) |
| S2 line | 8 | 468 s | 20.7 GB | ok (switch-on and switch-off) |
| S2 line | 16 | about 15 min | over 32 GB | **killed** by the memory limit of the job |
| S2 line | 32, 64 | | | not run |
| S3 line, 8 ticks, 0 unrelated stone blocks written after the circuit | 8 | 375 s | 20.7 GB | ok |
| S3 same, 200 blocks | 8 | 672 s | 28.6 GB | **fails**: `(kernel) deterministic timeout` |
| S3 1000 blocks, and the three "written before" variants | | | | not run (cancelled) |
| S4 piston, 12 blocks | 1 / 2 / 3 / 4 | 2.2 / 1.3 / 1.9 / 2.0 s | 1.5 to 1.7 GB | ok |
| S4 hoppers, 1 item | 1 / 2 | 0.66 / 0.58 s | 1.3 GB | ok |
| S4 hoppers, 5 items | 1 / 9 / 17 | 0.62 / 0.86 / 1.11 s | 1.3 to 1.5 GB | ok |
| S4 lever pop | 1 | | | **stuck** at `Block.fluidBlock` |

Decision rule of the plan: keep the representation if S2 at 64 ticks is at most 2 minutes and
S3 is flat. S2 is 468 s at 8 ticks and does not finish at 16; S3 is not flat. **The
representation was replaced.**

## Blockers found, and what was done

1. **`Block.fluidBlock` is stuck in the kernel** (`Redstone/Block/Basic.lean:75` before the
   change: `(parse? b.attrs.fluid).getD AIR`, through `String.splitOn`). It is on the path of
   `destroyBlock` and `removeBlock`, so nothing that breaks a block could be evaluated.
   Fixed: `Block.fluidState` is generated from the block dump as a match on constructors
   (`tools/gen/gen_fluid.py`, which checks for every block state that it gives the attribute
   `fluid` back), and `fluidBlock` is `fluidState.createLegacyBlock`.
   `clearWaterlogged` (`Component/Piston.lean`) and `drained?`, `holdsWater`
   (`Component/Extra.lean`) use the generated `Block.waterlogged?` and `setWaterlogged`.
2. **The world as a chain of `Function.update`** (`Redstone/World/Basic.lean:35`, and the block
   entities at `Mechanics/Update.lean:86` and `:120`): a read walks every write made before
   it. This is what S3 measures. Fixed: `World` and `Level.blockEntities` are finite maps
   (`PosMap`), a binary trie on `Pos.key p = Nat.pair (zigzag x) (Nat.pair (zigzag y) (zigzag z))`.
   The trie has no empty subtree and a world stores no air, so equal contents are equal terms:
   `World` and `PosMap` have `DecidableEq`, and extensionality is a theorem (`World.ext`,
   `PosMap.ext`). The interface (`blockAt`, `set`, `empty`, the simp lemmas) is unchanged.
3. **One long evaluation does not scale, whatever the representation.** The kernel keeps every
   intermediate result of a declaration in its cache: memory grows with the length of the run
   (about 9 GB for every time the line goes on and off), and the clock fails at 8 ticks even after the
   change. Not fixed in the model: the remedy is the proof method below.
4. **Kernel evaluations must not run side by side.** Lean elaborates the theorems of a file on
   several threads. Four per-tick lemmas of the piston took 80 s of kernel time together on a
   busy node and 5.8 s on a quiet one, against 1.9 s when checked one after the other;
   sixteen lemmas of the clock took 863 s on a busy node against 9 s. `set_option Elab.async false` at the top
   of a proof file avoids it.
5. **The block entity type was compared by name** (`Mechanics/Update.lean:270`, on every
   `setBlock` of a block with a block entity). It reduced (15 ms), but it is now compared by
   constructor (`ctorIdx`).

Measured and left as they are:

* String equality works in the kernel, at about 10 ms per comparison of two block or item
  names. `itemMaxStackSize` costs 0.4 s per call; it is called when a hopper moves an item, and
  dominates the hopper ticks. Making items an enumeration would remove it.
  (Done since, without the enumeration: see "The item table" below.)
* The other comparisons of `Attrs.fluid` with a string (`Component/Supported.lean:62`, `:67`,
  `:101`, `Component/Extra.lean:227`, `:231`, `Component/AnalogSource.lean:204`,
  `Component/Sensor/Light.lean:66`, and the entity files) are not on the path of the probes.
  They reduce; `Block.fluidState` is there to replace them.
* `Container.redstoneSignal` uses `Float32` (`Component/Container.lean`), which the kernel
  cannot evaluate. Not probed here: a comparator that reads a container is out of reach until
  that function is exact.
* A runaway evaluation ends with `(kernel) deterministic timeout` after 10 minutes or more. It
  was not tried whether a larger `maxHeartbeats` moves that limit.

## After the changes

Same probes, same circuits.

| Probe | Ticks | Kernel time | Peak RSS | Result |
|---|---|---|---|---|
| S1 lever-lamp | 1 | 0.14 s | 1.1 GB | ok |
| S2 idle | 1 / 4 / 16 / 64 | 4 / 7 / 17 / 70 ms | 1.1 GB | ok, linear |
| S2 clock | 1 / 2 / 4 | 0.56 / 4.8 / 5.9 s | 1.3 / 1.7 / 1.9 GB | ok |
| S2 clock | 8 | 658 s | 26.5 GB | **fails**: `(kernel) deterministic timeout` |
| S2 clock | 16 / 32 / 64 | 131 / 130 / 140 s | 27.6 GB | **fails** the same way |
| S2 line | 1 / 2 / 4 | 7.9 / 7.0 / 6.7 s | 3.0 GB | ok |
| S2 line | 8 | 35.8 s | 10.6 GB | ok (was 468 s, 20.7 GB) |
| S2 line | 16 | 68.6 s | 19.6 GB | ok (was killed) |
| S2 line | 32 | | over 32 GB | **killed** by the memory limit of the job |
| S2 line | 64 | | | not run |
| S3 line, 8 ticks, 0 / 200 / 1000 unrelated blocks written after | 8 | 37.4 / 36.9 / 37.8 s | 10.6 / 10.8 / 11.4 GB | ok, **flat** |
| S3 same, written before | 8 | 35.3 / 36.2 / 38.3 s | 10.6 / 10.8 / 11.4 GB | ok, **flat** |
| S4 piston, 12 blocks | 1 / 2 / 3 / 4 | 1.0 / 1.0 / 1.8 / 1.8 s | 1.5 to 1.7 GB | ok |
| S4 hoppers, 1 item | 1 / 2 | 0.61 / 0.55 s | 1.3 GB | ok |
| S4 hoppers, 5 items | 1 / 9 / 17 | 0.55 / 0.82 / 1.11 s | 1.3 to 1.5 GB | ok |
| S4 lever pop | 1 | 0.11 s | 1.2 GB | ok (was stuck) |

The monolithic method is fine for a handful of ticks of a small circuit and nothing more. It
is what `Redstone/Proof/Smoke.lean` uses (four theorems, 1.7 s of kernel time in all).

## S5: one lemma per tick

Each lemma states that one game tick, with its inputs, takes one level literal to the next:

```lean
theorem tick_k : beqL (Level.step (inputs applied to L_k)) L_{k+1} = true := by decide +kernel
```

`L_k` is a `def` whose body is the level written out as a term. `beqL` compares two levels
field by field (every field of `Level` except `entities` has `DecidableEq`; both entity lists
must be empty). Measured on a quiet node, with `Elab.async false`:

| Circuit | Lemma | Kernel time | Peak RSS |
|---|---|---|---|
| lever-lamp | the tick the lever is used; the next tick | 0.15 s for both | 1.1 GB |
| piston, 12 blocks | tick 1 (the blocks start moving) | 0.97 s | 1.5 GB |
| piston, 12 blocks | tick 2 | 0.12 s | 1.2 GB |
| piston, 12 blocks | tick 3 (the blocks arrive) | 0.72 s | 1.4 GB |
| piston, 12 blocks | tick 4 (nothing happens) | 0.06 s | 1.1 GB |
| piston, 12 blocks | the four lemmas in one file | 1.9 s | 1.5 GB |
| hoppers, 5 items | 16 lemmas, ticks 1 to 16 | 2.6 s in all, about 0.6 s for a tick in which a hopper is off cooldown | 1.4 GB |
| clock | 16 lemmas, ticks 3 to 18 | 9.0 s in all, 1.0 to 1.1 s for a tick in which a repeater switches | 1.5 GB |
| line | the tick the line goes on | 6.7 s | 3.0 GB |
| line | the tick the line goes off | 40.6 s | 8.9 GB |
| line | three ticks in which nothing happens | 0.4 s in all | 1.2 GB |
| line | 16 lemmas, ticks 1 to 16 (on, off, on, off) | 110 s in all: 7.5, 31, 9.3 and 60 s for the four switches | 8.9 GB |

The gate of the plan (the per-tick lemma of the 12-block piston within 60 s and 8 GB) is met
with a wide margin: at most 0.97 s and 1.5 GB.

Compared with the monolithic runs: the clock, which cannot be evaluated over 8 ticks at all,
costs about a second per active tick; the line over 16 ticks needs 8.9 GB instead of 19.6 GB,
and the number of ticks is not limited by memory (in one evaluation, 16 ticks fit in 32 GB and
32 do not). A failing tick is one failing lemma.

**Dust is the expensive block.** Switching 15 dust off is the worst case of the game's own wire
algorithm (every dust is recomputed many times), and it costs 30 to 60 s and 8.9 GB for that
single tick; switching it on costs 7 s. A theorem about a long dust line pays this for every
switch. Where and why the kernel spends that time was not profiled; it is the first thing to
look at when dust circuits are proved (`Redstone/Component/Dust.lean`).

## What this does not show

The numbers above are evidence that the per-tick method is affordable. They are not a theorem
about a run of several ticks, and they do not reach every kind of circuit.

* **Nothing of the per-tick method is committed.** `beqL`, the lemma that makes it useful
  (`beqL a b = true → a = b`, or equality of the fields a statement reads), the `lit%`
  elaborator and the tick lemmas themselves existed only in untracked probe files of the spike
  (`.lake/spike/`), so the S5 table cannot be reproduced from the repository.
  `Redstone/Proof/Smoke.lean` uses one evaluation per theorem, over at most 3 ticks. The
  comparison, its soundness lemma and the literal builder belong to the proof foundation
  (`Redstone/Proof`), and its first deliverable should be those together with one end-to-end
  theorem of the repeater clock, with the 16-tick clock probe (about 9 s) kept in
  `Redstone/Proof/` as a regression file.
* **The lemmas were never joined.** The spike proved isolated facts
  `beqL (step L_k) L_{k+1} = true`. It did not derive from them a statement about the run, such
  as `rules.runSchedule s L0 = L_n` or the state of a block after `n` ticks. That step needs
  the soundness lemma, and whether the kernel unfolds the large literals again while rewriting
  along the tick lemmas was not measured.
* **Levels with entities have no route yet.** `beqL` requires both entity lists to be empty:
  an `Entity` carries a `Vec3` of `Float`, `Level` has no `DecidableEq`, and the kernel cannot
  compute with `Float` at all, so a tick that moves an entity is stuck however it is stated.
  This leaves out everything that works through entities: dropped items (item sorters fed by
  item entities, droppers and dispensers that eject), minecarts, primed TNT, projectiles, and
  any block that breaks while `block_drops` is on. Circuits that only move items between
  containers are not affected. Proving the others needs either entity physics in exact
  arithmetic, as `Container.redstoneSignal` is to get, or an abstraction of the entity; neither
  was tried, so for them the contingency of the plan is not ruled out.
* **Paths that `Smoke.lean` does not guard.**
  * A comparator that reads a container goes through `Container.redstoneSignal`, which is
    `Float32`: it is stuck in the kernel today, no smoke theorem covers it, and so CI will not
    notice when it starts to work or stops again. The change that makes that function exact
    should add a smoke theorem of a comparator reading a hopper.
  * `destroyBlock` raises the game event `minecraft:block_destroy`. Without a listener only the
    list of tickers is walked and neither the name nor the position (`Float`) is forced, which
    is why the lever that loses its support is provable. A sculk sensor in the level puts the
    `Float` position on the path; this was not probed.
  * A hopper that moves an item calls `itemMaxStackSize` (a scan over item names, 0.4 s) and
    compares with `"minecraft:air"`; it reduces, and dominates the hopper ticks.
    (No longer: see "The item table" below; `Smoke.lean` now guards it.)

## The recipe

For a theorem about a concrete circuit:

1. **File.** Under `Redstone/Theorems/<Unit>/` (or `Redstone/Lemmas`, `Redstone/Contraption`,
   `Redstone/Proof`): every file there is built by `lake build` without being imported
   anywhere. Start it with

   ```lean
   import Redstone.Mechanics.Dispatch
   import Redstone.Mechanics.Input
   import Redstone.Proof.Axioms

   set_option Elab.async false
   ```

   The probes and `Redstone/Proof/Smoke.lean` are plain files, not `module`s; `decide +kernel`
   inside a `module` file was not tried.
2. **Initial level.** Write it as a term: `World.ofList [(pos, block), ...]` for the blocks,
   `PosMap.ofList [(pos, blockEntity), ...]` for the block entities, the tickers in ticking
   order, and `lightWorld` equal to `world`. Write block states with their constructors
   (`.lever ⟨.floor, .north, false⟩`), not with `Block.parse?`: parsing is string processing.
   This is a raw load, as the test harness does it; say in the theorem what is assumed.
3. **Short runs: one evaluation.** For up to a few ticks of a small circuit:

   ```lean
   theorem lever_lights_lamp :
       (rules.runSchedule [[.use ⟨0, 1, 0⟩ .up]] leverLamp).blockAt ⟨1, 1, 0⟩ = .redstoneLamp ⟨true⟩ := by
     decide +kernel

   assert_standard_axioms lever_lights_lamp
   ```

   The statement must be decidable and closed: equalities of blocks, block entities, numbers,
   lists of them, joined by `∧`. Do not bind the level with `let` inside the statement; give it
   a `def`. Always assert `overflow = false`.
4. **Longer runs: one lemma per tick.** Produce the level after each tick as a literal, and
   prove each step by a Boolean comparison:

   ```lean
   def L0 : Level := ...                       -- the initial level
   def L1 : Level := ...                       -- printed by the model, see below
   theorem tick1 : beqL (rules.stepWith [.use ⟨0, 1, 0⟩ .up] L0) L1 = true := by decide +kernel
   theorem tick2 : beqL (rules.stepWith [] L1) L2 = true := by decide +kernel
   ```

   The statement about the circuit is then read off the last literal, or follows by rewriting
   along the lemmas once the comparison is known to imply equality. That lemma, and `beqL`
   itself, belong to the proof foundation (`Redstone/Proof`) and are not in the repository
   yet; the spike used the comparison only, and did not do the rewriting. Both levels must be
   without entities.
5. **Literals.** `Level` has `Repr`, and what it prints is a term: a world prints as
   `Redstone.World.ofList [...]`, a block entity map as `Redstone.PosMap.ofList [...]`. So
   `#eval IO.println (repr (rules.stepWith inputs L0))` prints `L1`, to be pasted. Proof fields
   print as `_` (the bounds of an `IntRange`, in a repeater's delay): replace ` := _` by
   ` := by decide`. The spike did both steps with a small term elaborator that evaluates a
   closed term with compiled code and elaborates what `repr` prints:

   ```lean
   open Lean Elab Term Meta in
   elab "lit% " e:term : term <= ty => do
     let e ← elabTermEnsuringType e ty
     synthesizeSyntheticMVarsNoPostponing
     let e ← instantiateMVars e
     let str ← unsafe evalExpr String (mkConst ``String) (← mkAppM ``reprStr #[e])
     match Parser.runParserCategory (← getEnv) `term (str.replace ":= _" ":= by decide") with
     | .ok stx => elabTermEnsuringType stx ty
     | .error e => throwError e
   ```

   `def L1 : Level := lit% (rules.stepWith inputs L0)` then needs no pasting. The literal is
   not trusted: it is only the right-hand side of a lemma that the kernel checks.
6. **Budget.** Per tick-lemma, at 1.5 GB: about 0.1 s when nothing happens, 0.5 to 1 s for a
   lever, a repeater, a piston event or a hopper moving an item. For dust: 7 s to switch 15
   dust on, 30 to 60 s and 9 GB to switch it off; keep dust lines short or count on it. One
   lemma per tick, one file per circuit; files are built in parallel by Lake, lemmas within a
   file one after the other.
7. **Axioms.** End every theorem with `assert_standard_axioms name`
   (`Redstone/Proof/Axioms.lean`). It fails the build on anything beyond `propext`,
   `Classical.choice` and `Quot.sound`.

What does not work, so do not try it for ticks: plain `decide`, `rfl`, `simp` or
`with_unfolding_all` (they evaluate in the elaborator, which is far slower), and one evaluation
over tens of ticks.

## What the model must keep

`Redstone/Proof/Smoke.lean` is built by CI and proves, by evaluation: a lever lights a lamp; a
lever breaks when its support is destroyed; a sticky piston extends and moves a block; an item
moves from a hopper to the hopper below; three items do, one by one; a stack of ender pearls
fills up to sixteen and the next pearl starts a new stack. A change to the model that puts a `Float`, an opaque
or well-founded definition, or string parsing on the path of a block tick makes that file fail
or slow down. In a level without scheduled fluid ticks, with `random_tick_speed` zero and
`block_drops` off, the block path must stay free of them.

## The item table

Measured after the spike, on the model at `3e6d3c3d` and on the same model with the change
described here. `lake test` is unchanged: 9826 of 9826 scenarios.

**What was slow.** `itemMaxStackSize` was two scans, `List.contains` over the 248 names of the
items that stack to 1 and the 68 that stack to 16. The kernel has no fast strings: a string
literal unfolds to the list of its bytes, so a scan unfolds every name of the table. And it
was not only paid in the ticks in which an item moves: in the hopper pair of the probes the
average over all game ticks was 0.35 s, with the slowest tick at 0.6 to 0.7 s.

**What was changed.** The table is a binary search tree on a natural number
(`Redstone/Basic/ItemKey.lean`): `itemKey` packs the bytes of the name into one number, as
digits in base 256 below a leading 1, and the lookup compares number literals, one or two on
each of the nine levels of the tree, which the kernel does natively. `itemKey` is injective (`itemKey_injective`), so there are no
collisions to handle and no final comparison of names. The generator writes the list of names
and the tree side by side (`Redstone/Block/Generated/Items.lean`, by
`tools/gen/gen_blocks.py`), and `Redstone/Lemmas/ItemStackSize.lean` proves, for every string,
that the lookup is a scan of the list: `itemMaxStackSize id = (itemStackSizes.lookup id).getD 64`.
`ItemStack` still names its item by a `String`; no type changed.

Primitives, each one `decide +kernel`, kernel time by the profiler (a trivial `decide +kernel`
is about 3 ms):

| Probe | Before | After |
|---|---|---|
| `itemMaxStackSize "minecraft:redstone" = 64` (not in the table) | 458 ms | 4.2 ms |
| `itemMaxStackSize "minecraft:ender_pearl" = 16` | 409 ms | 3.1 ms |
| `itemMaxStackSize "minecraft:diamond_sword" = 1` | 130 ms | 3.2 ms |
| `(ItemStack.of "minecraft:redstone" 3).maxStackSize = 64` | 482 ms | 4.3 ms |
| `(ItemStack.of "minecraft:redstone" 3).isEmpty = false` | 3.0 ms | 3.0 ms |
| `isSameItemSameComponents` of two stacks of redstone | 4.6 ms | 3.8 ms |

Hopper above hopper, both pointing down, the upper one with a stack in its first slot: one
lemma per game tick between level literals, until the upper hopper is empty and for a few
ticks more. Both hoppers move items here (the upper one pushes, the lower one pulls), two
items every 8 ticks. The comparison is of `world`, `blockEntities`, `blockEntityTickers`,
`gameTime`, `overflow` and the number of scheduled ticks. The times are wall time of the lemma
commands on a compute node (4 cores, `Elab.async false`, nothing else in the job), so they
include the elaboration of the statement, a few milliseconds per lemma:

| Probe | Lemmas | Before: all, slowest | After: all, slowest |
|---|---|---|---|
| 1 piece of redstone | 16 | 5.5 s, 0.61 s | 0.95 s, 0.13 s |
| 5 pieces of redstone | 48 | 17.6 s, 0.65 s | 2.9 s, 0.12 s |
| 64 pieces of redstone | 520 | 180 s, 0.68 s | 33 s, 0.12 s |
| 16 ender pearls (a full stack of them) | 136 | 48 s, 0.76 s | 10.8 s, 0.17 s |

That is about 0.35 s per tick before and 0.06 s after, on average over all ticks. A full
stack of 64 going through a hopper is half a minute of kernel time; the number of items no longer limits a hopper theorem. Every lemma depends on the three standard axioms
only. What the remaining 60 ms of a hopper tick are spent on was not profiled.

**The emptiness test was measured and left as it is.** `ItemStack.isEmpty` compares the name
of the item with `"minecraft:air"`. That is a single comparison, and the kernel decides it on
the first byte that differs (all item names start with `minecraft:`, so on the eleventh byte
or soon after it), without unfolding the rest of the name. Comparing keys instead means computing `itemKey` of the whole
name. Over 316 stacks of different items, each seen for the first time: 582 ms with the
comparison of names (1.8 ms per stack), 859 ms with keys (2.7 ms per stack). For a stack the
kernel has met before in the same evaluation both are cached (12 ms for 300 calls, either
way). So the key would make it slower.

**What this does not change.** The model still compares item names as strings wherever it
asks whether two stacks hold the same item (`isSameItemSameComponents`), and the other tables
indexed by item names (fuels and cooking recipes, the items a dispenser treats specially) are
still lists of names. A comparison costs a few milliseconds and a scan costs about a
millisecond for every name of its list; none was on the path of these probes. `itemKey` and
`ItemTable` are there for the ones that turn out to matter. The probe files are not in the
repository (they need the level literals and the comparison of the proof foundation). The two
new hopper theorems of `Redstone/Proof/Smoke.lean` run the lookup in CI: they check its
results, and like the rest of that file they have no time limit, so a lookup that became slow
again would show as a slower build (0.25 s and 0.17 s of kernel time now), not as a failure.
