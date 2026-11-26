# Harness: scenarios on a real Minecraft 26.3 server

Runs the scenarios of `tests/FORMAT.md` on the official 26.3 dedicated server and records traces,
and writes the block dump. Environment: `tools/env.sh` (installed by `tools/mc/setup.sh`).

```
tools/record.sh <scenario.json | dir>... [-o <outdir>]   # through Slurm; this is what to use
tools/harness/run.sh record <scenario.json | dir>... [-o <outdir>]
tools/harness/run.sh dump                                 # -> $MC_REPORTS/blockdump.json
tools/fuzz.py --palette tests/palettes/lever.json --count 20 --size 5x3x5 --ticks 40 --seed 1 --out <dir>
```

`run.sh` starts a JVM with two cores and up to 2.5 GiB of heap, so run it under Slurm
(`srun -c 2 --mem 4G tools/harness/run.sh dump`; `tools/record.sh` does this for `record`). Without
`-o`, the trace of `tests/scenarios/<unit>/x.json` is written to `tests/traces/<unit>/x.trace.json`.
One invocation boots one server (about 7 s) and runs all its scenarios (about 10 ms for a small
30-tick scenario, the first ones slower while the JVM warms up). The exit status is 0 when every
scenario was recorded, 1 when some failed (they are named on stderr, the others are still
written), and 3 when the server itself failed.

Each invocation works in a fresh directory `$MC_HOME/run/<mode>.XXXXXXXX` (world, `eula.txt`,
`server.properties`, logs) and deletes it afterwards, so any number can run at the same time; the
server listens on an ephemeral port of 127.0.0.1. `HARNESS_KEEP=1` keeps the directory,
`HARNESS_VERBOSE=1` shows the server log. Compiled classes go to `$MC_HOME/harness-build`
(`build.sh`, plain `javac` against the game jar and its libraries, rebuilt when a source changes).

## How the server is driven

`rsharness.Main` does what `net.minecraft.server.Main` does (bootstrap, `server.properties`,
EULA check, new world, `MinecraftServer.spin`), but the server object is `HarnessServer`, a
subclass of the real `DedicatedServer` that overrides three protected methods:

* `tickServer`: calls `super.tickServer` — one complete vanilla server tick, with everything
  `MinecraftServer` and `ServerLevel.tick` do in their own order — and then the recorder, on the
  server thread. So the recorder acts between ticks, where a normal server handles packets and
  console commands. It applies the actions of the next tick and records a frame; it never runs
  any phase of a tick itself.
* `waitUntilNextTick`: runs the queued main-thread tasks and waits for the light engine to be
  idle, instead of sleeping until the next 50 ms boundary.
* `shouldRun`: queued tasks always run before the next tick (vanilla postpones them when the
  server is behind, which would make the result depend on timing).

This was chosen over the game-test server (`net.minecraft.gametest.Main`) because that one enables
experimental feature flags and its own structure and batch machinery, and over freezing and
stepping the tick rate manager because a frozen server still ticks in a different mode between
steps. Here every tick of the process is an ordinary tick of an ordinary dedicated server.

World: `level-type=minecraft:flat` with a single layer of air, biome `minecraft:the_void`, no
features or structures. The chunks x, z = -8 .. 15 are force-loaded (entity-ticking) once, and
the recorder waits until all of them tick blocks and entities before the first scenario. Other
`server.properties` of note: `pause-when-empty-seconds=-1` (a dedicated server without players
would stop ticking after 60 s), `max-tick-time=-1` (no watchdog), `online-mode=false`.

Scenarios run one after another at the same place, the absolute origin (0, 0, 0) (see
`tests/FORMAT.md` for why not at different places). After each one the recorder discards every
entity, sets every non-air block of the loaded region to air silently, and clears scheduled ticks
and block events; before each one it verifies that nothing is left, and aborts otherwise.

## Determinism

What is pinned at the start of each scenario is listed in `tests/FORMAT.md`. Sources of
nondeterminism found, and what was done:

* `RandomSource.create()` seeds from `System.nanoTime()` (level random, the private random of
  every entity). The level random is reseeded with 0. For the others a Java agent
  (`PatchRandomSupport`, loaded with `-javaagent`) replaces the body of
  `RandomSupport.generateUniqueSeed()` by a call to `SeedHook.next()`, which returns a
  deterministic sequence on the server thread while a scenario runs and behaves as before
  otherwise. This is the only change to game code. (The game jar is signed, so the class cannot
  be shadowed on the class path.)
* The entity id counter, `Level.randValue`, the game time and the redstone torch burn-out list
  survive from one scenario to the next: reset by reflection.
* The light engine runs on another thread: the server waits for it between ticks.
* Main-thread tasks (e.g. point-of-interest updates) are delayed depending on wall-clock time:
  they are always run between ticks.
* The attributes of a mob are saved in identity-hash order: sorted in the trace.

Not pinned: iteration orders of other identity-hash collections inside the game, should some
behaviour depend on one. Record twice and compare when in doubt (the examples, a 40-tick scenario
with hopper, chest, dropper, piston, TNT, falling sand, water, a pig and item drops, and 40 fuzzed
scenarios were byte-identical across runs and across different batches).

## Limits

* A box must lie within x, z = -96 .. 223 and y = -64 .. 319, and hold at most 16 million blocks.
* Things that leave the loaded region (x, z = -128 .. 255) reach chunks that do not tick.
* The player of `use` is not in the world; a container it opens is never closed by it.
* No players are online, so nothing that needs a nearby player happens (natural spawning,
  lightning, sounds and packets are irrelevant here).
