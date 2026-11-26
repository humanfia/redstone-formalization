package rsharness;

import com.mojang.authlib.GameProfile;
import io.netty.channel.embedded.EmbeddedChannel;
import it.unimi.dsi.fastutil.objects.ObjectLinkedOpenHashSet;
import java.lang.reflect.Field;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.UUID;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.locks.LockSupport;
import net.minecraft.SharedConstants;
import net.minecraft.commands.arguments.blocks.BlockStateParser;
import net.minecraft.core.BlockPos;
import net.minecraft.core.Direction;
import net.minecraft.core.Holder;
import net.minecraft.core.registries.BuiltInRegistries;
import net.minecraft.nbt.CompoundTag;
import net.minecraft.nbt.TagParser;
import net.minecraft.network.Connection;
import net.minecraft.network.protocol.PacketFlow;
import net.minecraft.resources.Identifier;
import net.minecraft.server.level.ClientInformation;
import net.minecraft.server.level.ServerLevel;
import net.minecraft.server.level.ServerPlayer;
import net.minecraft.server.level.ThreadedLevelLightEngine;
import net.minecraft.server.network.CommonListenerCookie;
import net.minecraft.server.network.ServerGamePacketListenerImpl;
import net.minecraft.util.ProblemReporter;
import net.minecraft.world.InteractionHand;
import net.minecraft.world.InteractionResult;
import net.minecraft.world.clock.WorldClock;
import net.minecraft.world.clock.WorldClocks;
import net.minecraft.world.entity.Entity;
import net.minecraft.world.entity.EntitySpawnReason;
import net.minecraft.world.entity.EntitySpawnRequest;
import net.minecraft.world.entity.EntityType;
import net.minecraft.world.entity.Mob;
import net.minecraft.world.item.Item;
import net.minecraft.world.item.ItemStack;
import net.minecraft.world.item.context.UseOnContext;
import net.minecraft.world.level.BlockEventData;
import net.minecraft.world.level.ChunkPos;
import net.minecraft.world.level.GameType;
import net.minecraft.world.level.Level;
import net.minecraft.world.level.block.Block;
import net.minecraft.world.level.block.Blocks;
import net.minecraft.world.level.block.RedstoneTorchBlock;
import net.minecraft.world.level.block.entity.BlockEntity;
import net.minecraft.world.level.block.state.BlockState;
import net.minecraft.world.level.block.state.properties.Property;
import net.minecraft.world.level.chunk.LevelChunk;
import net.minecraft.world.level.chunk.LevelChunkSection;
import net.minecraft.world.level.gamerules.GameRules;
import net.minecraft.world.level.levelgen.structure.BoundingBox;
import net.minecraft.world.level.material.Fluid;
import net.minecraft.world.level.saveddata.WeatherData;
import net.minecraft.world.level.storage.TagValueInput;
import net.minecraft.world.level.storage.TagValueOutput;
import net.minecraft.world.phys.BlockHitResult;
import net.minecraft.world.phys.Vec3;
import net.minecraft.world.ticks.LevelChunkTicks;
import net.minecraft.world.ticks.ScheduledTick;

/**
 * Runs on the server thread after every server tick. Sets scenarios up, applies their actions between
 * ticks, and records one frame after each tick. It never runs any part of a tick itself.
 */
final class Recorder {
   record Job(Path scenario, Path trace) {
   }

   /** The chunks kept loaded and entity-ticking for the whole run, the same for every scenario. */
   static final int REGION_MIN_CHUNK = -8;
   static final int REGION_MAX_CHUNK = 15;
   /** Scenario boxes must stay this many chunks away from the edge of the region. */
   static final int REGION_MARGIN_CHUNKS = 2;
   static final int BOX_MIN_XZ = (REGION_MIN_CHUNK + REGION_MARGIN_CHUNKS) * 16;
   static final int BOX_MAX_XZ = (REGION_MAX_CHUNK - REGION_MARGIN_CHUNKS) * 16 + 15;

   /** setBlock flags of the silent placement: UPDATE_CLIENTS | UPDATE_KNOWN_SHAPE | UPDATE_SKIP_BLOCK_ENTITY_SIDEEFFECTS | UPDATE_SKIP_ON_PLACE. */
   static final int SILENT = Block.UPDATE_CLIENTS | Block.UPDATE_KNOWN_SHAPE | Block.UPDATE_SKIP_BLOCK_ENTITY_SIDEEFFECTS | Block.UPDATE_SKIP_ON_PLACE;

   private enum Phase {
      INIT,
      WARMUP,
      IDLE,
      RUNNING
   }

   private final List<Job> jobs;
   private final Path dumpPath;
   long bootStartNanos;
   volatile boolean finished;
   volatile int exitCode;

   private Phase phase = Phase.INIT;
   private int warmupTicks;
   private int idleTicks;
   private int nextJob;
   private int failures;

   private ServerLevel level;
   private ObjectLinkedOpenHashSet<BlockEventData> blockEvents;
   private AtomicInteger entityCounter;
   private Field randValueField;
   private Map<?, ?> recentTorchToggles;
   private List<net.minecraft.world.level.block.entity.TickingBlockEntity> tickers;
   private List<net.minecraft.world.level.block.entity.TickingBlockEntity> pendingTickers;
   private final Map<BlockState, String> stateNames = new IdentityHashMap<>();

   // The scenario being run.
   private Job job;
   private Scenario scenario;
   private int tick;
   private long scenarioStartNanos;
   private StringBuilder out;
   private BlockState[] prevBlocks;
   private Map<BlockPos, String> prevBlockEntities;
   private Map<Entity, Integer> entityIndex;
   private List<Entity> entitiesByIndex;
   private ServerPlayer player;
   private int nextAction;

   private Recorder(final List<Job> jobs, final Path dumpPath) {
      this.jobs = jobs;
      this.dumpPath = dumpPath;
   }

   static Recorder forJobs(final List<Job> jobs) {
      return new Recorder(jobs, null);
   }

   static Recorder forDump(final Path path) {
      return new Recorder(List.of(), path);
   }

   // ------------------------------------------------------------------ driver

   void afterTick(final HarnessServer server) {
      if (this.finished) {
         return;
      }

      try {
         this.step(server);
      } catch (Throwable t) {
         Main.ERR.println("harness: fatal error");
         t.printStackTrace(Main.ERR);
         this.exitCode = 3;
         this.finish(server);
      }
   }

   private void finish(final HarnessServer server) {
      SeedHook.unpin();
      this.finished = true;
      // The world is thrown away, so there is no point in a clean shutdown (which would save it).
      System.out.flush();
      Main.ERR.flush();
      Runtime.getRuntime().halt(this.exitCode);
   }

   private void step(final HarnessServer server) throws Exception {
      switch (this.phase) {
         case INIT -> {
            this.init(server);
            this.phase = Phase.WARMUP;
         }
         case WARMUP -> {
            this.warmupTicks++;
            if (this.warmupTicks >= 20 && this.regionReady()) {
               this.requireCleanWorld("after boot");
               Main.ERR.printf("harness: server ready after %.1f s (%d warm-up ticks)%n", (System.nanoTime() - this.bootStartNanos) / 1e9, this.warmupTicks);
               if (this.dumpPath != null) {
                  Dump.write(this.level, this.dumpPath);
                  Main.ERR.println("harness: wrote " + this.dumpPath);
                  this.finish(server);
               } else {
                  this.phase = Phase.IDLE;
                  this.idleTicks = 2;
               }
            } else if (this.warmupTicks > 4000) {
               throw new IllegalStateException("the chunks of the region did not become ticking");
            }
         }
         case IDLE -> {
            if (this.idleTicks < 2) {
               this.idleTicks++;
            } else if (this.nextJob >= this.jobs.size()) {
               if (this.failures > 0) {
                  Main.ERR.println("harness: " + this.failures + " of " + this.jobs.size() + " scenarios failed");
                  this.exitCode = 1;
               }
               this.finish(server);
            } else {
               this.job = this.jobs.get(this.nextJob++);
               this.scenarioStartNanos = System.nanoTime();
               try {
                  this.startScenario(server);
                  if (this.scenario.ticks == 0) {
                     this.endScenario(server);
                  } else {
                     this.tick = 1;
                     this.applyActions(1);
                     this.phase = Phase.RUNNING;
                  }
               } catch (Exception e) {
                  this.failScenario(server, e);
               }
            }
         }
         case RUNNING -> {
            try {
               this.recordFrame(this.tick);
               if (this.tick == this.scenario.ticks) {
                  this.endScenario(server);
               } else {
                  this.tick++;
                  this.applyActions(this.tick);
               }
            } catch (Exception e) {
               this.failScenario(server, e);
            }
         }
      }
   }

   /** Between ticks: wait until the light engine (a separate thread in vanilla) has caught up, so that light never depends on thread timing. */
   void settle(final HarnessServer server) {
      if (this.level == null || this.finished) {
         return;
      }

      ThreadedLevelLightEngine lightEngine = this.level.getChunkSource().getLightEngine();
      for (int round = 0; round < 1000; round++) {
         CompletableFuture<?> pending = lightEngine.waitForPendingTasks(0, 0);
         long deadline = System.nanoTime() + 60_000_000_000L;
         while (!pending.isDone()) {
            lightEngine.tryScheduleUpdate();
            server.drainTasks();
            if (!pending.isDone()) {
               LockSupport.parkNanos(20_000L);
            }
            if (System.nanoTime() > deadline) {
               throw new IllegalStateException("the light engine did not finish");
            }
         }
         if (!lightEngine.hasLightWork()) {
            return;
         }
      }
      throw new IllegalStateException("the light engine did not settle");
   }

   // ------------------------------------------------------------------ boot

   @SuppressWarnings("unchecked")
   private void init(final HarnessServer server) throws Exception {
      this.level = server.overworld();
      Field f = ServerLevel.class.getDeclaredField("blockEvents");
      f.setAccessible(true);
      this.blockEvents = (ObjectLinkedOpenHashSet<BlockEventData>)f.get(this.level);
      f = ServerLevel.class.getDeclaredField("ENTITY_COUNTER");
      f.setAccessible(true);
      this.entityCounter = (AtomicInteger)f.get(null);
      this.randValueField = Level.class.getDeclaredField("randValue");
      this.randValueField.setAccessible(true);
      f = RedstoneTorchBlock.class.getDeclaredField("RECENT_TOGGLES");
      f.setAccessible(true);
      this.recentTorchToggles = (Map<?, ?>)f.get(null);

      f = Level.class.getDeclaredField("blockEntityTickers");
      f.setAccessible(true);
      this.tickers = (List<net.minecraft.world.level.block.entity.TickingBlockEntity>)f.get(this.level);
      f = Level.class.getDeclaredField("pendingBlockEntityTickers");
      f.setAccessible(true);
      this.pendingTickers = (List<net.minecraft.world.level.block.entity.TickingBlockEntity>)f.get(this.level);

      GameRules rules = server.getGameRules();
      rules.set(GameRules.ADVANCE_TIME, false, server);
      rules.set(GameRules.ADVANCE_WEATHER, false, server);
      rules.set(GameRules.RANDOM_TICK_SPEED, 0, server);
      rules.set(GameRules.SPAWN_MOBS, false, server);
      rules.set(GameRules.SPAWN_MONSTERS, false, server);
      rules.set(GameRules.SPAWN_PATROLS, false, server);
      rules.set(GameRules.SPAWN_PHANTOMS, false, server);
      rules.set(GameRules.SPAWN_WANDERING_TRADERS, false, server);
      rules.set(GameRules.SPAWN_WARDENS, false, server);

      net.minecraft.world.level.levelgen.RandomSupport.generateUniqueSeed();
      if (!PatchRandomSupport.applied) {
         throw new IllegalStateException("the RandomSupport patch is not active (is the java agent loaded?)");
      }
      if (!(this.level.getRandom() instanceof net.minecraft.world.level.levelgen.LegacyRandomSource)) {
         throw new IllegalStateException("the level random is a " + this.level.getRandom().getClass().getName() + ", not a LegacyRandomSource");
      }

      for (int cx = REGION_MIN_CHUNK; cx <= REGION_MAX_CHUNK; cx++) {
         for (int cz = REGION_MIN_CHUNK; cz <= REGION_MAX_CHUNK; cz++) {
            this.level.setChunkForced(cx, cz, true);
         }
      }
   }

   private boolean regionReady() {
      for (int cx = REGION_MIN_CHUNK; cx <= REGION_MAX_CHUNK; cx++) {
         for (int cz = REGION_MIN_CHUNK; cz <= REGION_MAX_CHUNK; cz++) {
            long key = ChunkPos.pack(cx, cz);
            if (!this.level.isPositionTickingWithEntitiesLoaded(key)
               || !this.level.shouldTickBlocksAt(key)
               || !this.level.isPositionEntityTicking(new BlockPos(cx * 16 + 8, 0, cz * 16 + 8))) {
               return false;
            }
         }
      }
      return true;
   }

   // ------------------------------------------------------------------ scenario life cycle

   private void startScenario(final HarnessServer server) throws Exception {
      this.scenario = null;
      Scenario s = Scenario.load(this.job.scenario());
      for (int i = 0; i < 3; i += 2) {
         if (s.boxMin[i] < BOX_MIN_XZ || s.boxMax[i] > BOX_MAX_XZ) {
            throw new IllegalArgumentException("the box must lie within " + BOX_MIN_XZ + ".." + BOX_MAX_XZ + " in x and z");
         }
      }
      if (s.boxMin[1] < this.level.getMinY() || s.boxMax[1] > this.level.getMaxY()) {
         throw new IllegalArgumentException("the box must lie within " + this.level.getMinY() + ".." + this.level.getMaxY() + " in y");
      }
      long volume = (long)(s.boxMax[0] - s.boxMin[0] + 1) * (s.boxMax[1] - s.boxMin[1] + 1) * (s.boxMax[2] - s.boxMin[2] + 1);
      if (volume > 16_000_000L) {
         throw new IllegalArgumentException("the box is too large");
      }

      this.scenario = s;
      this.requireCleanWorld("before scenario " + s.name);

      // Pin everything a tick could otherwise read from the past of the server.
      server.getWorldData().overworldData().setGameTime(0L);
      GameRules rules = server.getGameRules();
      rules.set(GameRules.ADVANCE_TIME, s.advanceTime, server);
      rules.set(GameRules.RANDOM_TICK_SPEED, s.randomTickSpeed, server);
      rules.set(GameRules.BLOCK_DROPS, s.blockDrops, server);
      Holder<WorldClock> clock = server.registryAccess().getOrThrow(WorldClocks.OVERWORLD);
      server.clockManager().setTotalTicks(clock, s.dayTime);
      boolean rain = !s.weather.equals("clear");
      boolean thunder = s.weather.equals("thunder");
      WeatherData weather = server.getWeatherData();
      weather.setClearWeatherTime(0);
      weather.setRainTime(0);
      weather.setThunderTime(0);
      weather.setRaining(rain);
      weather.setThundering(thunder);
      // Twice, so that the "previous" levels are equal to the current ones.
      for (int i = 0; i < 2; i++) {
         this.level.setRainLevel(rain ? 1.0F : 0.0F);
         this.level.setThunderLevel(thunder ? 1.0F : 0.0F);
      }
      this.level.getRandom().setSeed(0L);
      this.randValueField.setInt(this.level, 0);
      this.recentTorchToggles.clear();
      this.entityCounter.set(0);
      SeedHook.pin();
      this.player = this.makePlayer(server);

      this.prevBlocks = new BlockState[(int)volume];
      java.util.Arrays.fill(this.prevBlocks, Blocks.AIR.defaultBlockState());
      this.prevBlockEntities = new HashMap<>();
      this.entityIndex = new IdentityHashMap<>();
      this.entitiesByIndex = new ArrayList<>();
      this.nextAction = 0;
      this.out = new StringBuilder();
      this.out.append("{\"scenario\":").append(Json.str(s.name));
      this.out.append(",\"version\":").append(Json.str(SharedConstants.getCurrentVersion().name()));
      this.out.append(",\"frames\":[\n");

      // Silent initial placement.
      for (Scenario.Fill fill : s.fills) {
         BlockState state = this.parseState(fill.state());
         for (int x = fill.min()[0]; x <= fill.max()[0]; x++) {
            for (int y = fill.min()[1]; y <= fill.max()[1]; y++) {
               for (int z = fill.min()[2]; z <= fill.max()[2]; z++) {
                  this.placeSilently(new BlockPos(x, y, z), state);
               }
            }
         }
      }
      for (Scenario.BlockSpec spec : s.blocks) {
         BlockPos pos = new BlockPos(spec.pos()[0], spec.pos()[1], spec.pos()[2]);
         this.placeSilently(pos, this.parseState(spec.state()));
         if (spec.nbt() != null) {
            BlockEntity blockEntity = this.level.getBlockEntity(pos);
            if (blockEntity == null) {
               throw new IllegalArgumentException("nbt given for " + spec.state() + ", which has no block entity");
            }
            CompoundTag tag = TagParser.parseCompoundFully(spec.nbt());
            blockEntity.loadWithComponents(TagValueInput.create(ProblemReporter.DISCARDING, this.level.registryAccess(), tag));
         }
      }
      server.drainTasks();
      this.settle(server);
      int pendingTicks = this.level.getBlockTicks().count() + this.level.getFluidTicks().count();
      if (pendingTicks != 0 || !this.blockEvents.isEmpty()) {
         throw new IllegalStateException(
            "the silent placement scheduled something: " + pendingTicks + " ticks, " + this.blockEvents.size() + " block events"
         );
      }

      for (Scenario.EntitySpec spec : s.entities) {
         this.summon(spec);
      }
      // The level random is reseeded after the setup, so that tick 1 starts from seed 0 whatever the setup drew.
      this.level.getRandom().setSeed(0L);
      this.recordFrame(0);
   }

   private void endScenario(final HarnessServer server) throws Exception {
      this.out.append("\n]}\n");
      Path target = this.job.trace();
      Files.createDirectories(target.toAbsolutePath().getParent());
      Path tmp = target.resolveSibling(target.getFileName() + ".tmp" + ProcessHandle.current().pid());
      Files.writeString(tmp, this.out, StandardCharsets.UTF_8);
      Files.move(tmp, target, StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.ATOMIC_MOVE);
      int leaked = this.cleanup(server);
      Main.ERR.printf(
         "harness: ok %s (%d ticks, %.0f ms)%s%n",
         this.scenario.name,
         this.scenario.ticks,
         (System.nanoTime() - this.scenarioStartNanos) / 1e6,
         leaked > 0 ? "  WARNING: " + leaked + " blocks ended up outside the box" : ""
      );
      this.phase = Phase.IDLE;
      this.idleTicks = 0;
   }

   private void failScenario(final HarnessServer server, final Exception e) {
      this.failures++;
      Main.ERR.println("harness: FAILED " + this.job.scenario() + ": " + e);
      if (!(e instanceof IllegalArgumentException) && !(e instanceof com.mojang.brigadier.exceptions.CommandSyntaxException)) {
         e.printStackTrace(Main.ERR);
      }
      this.cleanup(server);
      this.phase = Phase.IDLE;
      this.idleTicks = 0;
   }

   /** Empties the world again. Returns the number of non-air blocks found outside the box of the scenario. */
   private int cleanup(final HarnessServer server) {
      SeedHook.unpin();
      this.player = null;
      for (Entity entity : this.allEntities()) {
         entity.discard();
      }

      int leaked = 0;
      BlockState air = Blocks.AIR.defaultBlockState();
      BlockPos.MutableBlockPos pos = new BlockPos.MutableBlockPos();
      int ring = REGION_MARGIN_CHUNKS;
      for (int cx = REGION_MIN_CHUNK - ring; cx <= REGION_MAX_CHUNK + ring; cx++) {
         for (int cz = REGION_MIN_CHUNK - ring; cz <= REGION_MAX_CHUNK + ring; cz++) {
            LevelChunk chunk = this.level.getChunkSource().getChunkNow(cx, cz);
            if (chunk == null) {
               continue;
            }
            LevelChunkSection[] sections = chunk.getSections();
            for (int si = 0; si < sections.length; si++) {
               if (sections[si].hasOnlyAir()) {
                  continue;
               }
               int baseY = chunk.getSectionYFromSectionIndex(si) * 16;
               for (int y = 0; y < 16; y++) {
                  for (int z = 0; z < 16; z++) {
                     for (int x = 0; x < 16; x++) {
                        if (!sections[si].getBlockState(x, y, z).isAir()) {
                           pos.set(cx * 16 + x, baseY + y, cz * 16 + z);
                           if (this.scenario == null || !this.inBox(pos)) {
                              leaked++;
                           }
                           this.level.setBlock(pos, air, SILENT);
                        }
                     }
                  }
               }
            }
            for (BlockPos stray : new ArrayList<>(chunk.getBlockEntities().keySet())) {
               chunk.removeBlockEntity(stray);
            }
         }
      }

      server.drainTasks();
      for (Entity entity : this.allEntities()) {
         entity.discard();
      }
      int far = (REGION_MAX_CHUNK - REGION_MIN_CHUNK + 1 + 2 * ring) * 16;
      BoundingBox everything = new BoundingBox(-far, this.level.getMinY(), -far, 2 * far, this.level.getMaxY(), 2 * far);
      this.level.getBlockTicks().clearArea(everything);
      this.level.getFluidTicks().clearArea(everything);
      this.blockEvents.clear();
      return leaked;
   }

   /** Refuses to go on when something of an earlier scenario (or of world generation) is still there. */
   private void requireCleanWorld(final String when) {
      int entities = this.allEntities().size();
      int ticks = this.level.getBlockTicks().count() + this.level.getFluidTicks().count();
      int events = this.blockEvents.size();
      int blocks = 0;
      int blockEntities = 0;
      for (int cx = REGION_MIN_CHUNK; cx <= REGION_MAX_CHUNK; cx++) {
         for (int cz = REGION_MIN_CHUNK; cz <= REGION_MAX_CHUNK; cz++) {
            LevelChunk chunk = this.level.getChunk(cx, cz);
            for (LevelChunkSection section : chunk.getSections()) {
               if (!section.hasOnlyAir()) {
                  blocks++;
               }
            }
            blockEntities += chunk.getBlockEntities().size();
         }
      }
      if (entities != 0 || ticks != 0 || events != 0 || blocks != 0 || blockEntities != 0) {
         throw new IllegalStateException(
            "the world is not empty " + when + ": " + entities + " entities, " + ticks + " scheduled ticks, " + events + " block events, "
               + blocks + " non-empty chunk sections, " + blockEntities + " block entities"
         );
      }
   }

   // ------------------------------------------------------------------ setup helpers

   private ServerPlayer makePlayer(final HarnessServer server) {
      GameProfile profile = new GameProfile(new UUID(0L, 1L), "harness");
      ServerPlayer mock = new ServerPlayer(server, this.level, profile, ClientInformation.createDefault()) {
         @Override
         public GameType gameMode() {
            return GameType.CREATIVE;
         }

         @Override
         public boolean isClientAuthoritative() {
            return false;
         }
      };
      GameType.CREATIVE.updatePlayerAbilities(mock.getAbilities());
      Connection connection = new Connection(PacketFlow.SERVERBOUND);
      new EmbeddedChannel(connection);
      new ServerGamePacketListenerImpl(server, connection, mock, CommonListenerCookie.createInitial(profile, false));
      return mock;
   }

   private BlockState parseState(final String text) throws Exception {
      BlockState state = BlockStateParser.parseForBlock(BuiltInRegistries.BLOCK, text, false).blockState();
      String canonical = this.stateName(state);
      if (!canonical.equals(text)) {
         throw new IllegalArgumentException("block state \"" + text + "\" must be written \"" + canonical + "\"");
      }
      return state;
   }

   String stateName(final BlockState state) {
      return this.stateNames.computeIfAbsent(state, Recorder::formatState);
   }

   static String formatState(final BlockState state) {
      StringBuilder sb = new StringBuilder(BuiltInRegistries.BLOCK.getKey(state.getBlock()).toString());
      List<Property<?>> properties = new ArrayList<>(state.getProperties());
      properties.sort(Comparator.comparing(Property::getName));
      if (!properties.isEmpty()) {
         sb.append('[');
         for (int i = 0; i < properties.size(); i++) {
            if (i > 0) {
               sb.append(',');
            }
            sb.append(properties.get(i).getName()).append('=').append(valueName(state, properties.get(i)));
         }
         sb.append(']');
      }
      return sb.toString();
   }

   private static <T extends Comparable<T>> String valueName(final BlockState state, final Property<T> property) {
      return property.getName(state.getValue(property));
   }

   private void placeSilently(final BlockPos pos, final BlockState state) {
      if (!this.level.getBlockState(pos).isAir()) {
         // An earlier write of the scenario: replace it completely (also its block entity).
         this.level.setBlock(pos, Blocks.AIR.defaultBlockState(), SILENT);
      }
      if (!state.isAir()) {
         this.level.setBlock(pos, state, SILENT);
         if (this.level.getBlockState(pos) != state) {
            throw new IllegalStateException("could not place " + this.stateName(state) + " at " + pos);
         }
      }
   }

   /** Like /summon. */
   private Entity summon(final Scenario.EntitySpec spec) throws Exception {
      Identifier id = Identifier.parse(spec.type());
      if (!BuiltInRegistries.ENTITY_TYPE.containsKey(id)) {
         throw new IllegalArgumentException("unknown entity type " + spec.type());
      }
      CompoundTag tag = spec.nbt() == null ? new CompoundTag() : TagParser.parseCompoundFully(spec.nbt());
      tag.putString("id", id.toString());
      double x = spec.pos()[0];
      double y = spec.pos()[1];
      double z = spec.pos()[2];
      Entity entity = EntityType.loadEntityRecursive(tag, this.level, new EntitySpawnRequest(EntitySpawnReason.COMMAND, false), e -> {
         e.snapTo(x, y, z, e.getYRot(), e.getXRot());
         return e;
      });
      if (entity == null) {
         throw new IllegalArgumentException("could not create entity " + spec.type());
      }
      if (spec.nbt() == null && entity instanceof Mob mob) {
         mob.finalizeSpawn(this.level, this.level.getCurrentDifficultyAt(entity.blockPosition()), EntitySpawnReason.COMMAND, null);
      }
      if (!this.level.tryAddFreshEntityWithPassengers(entity)) {
         throw new IllegalStateException("could not add entity " + spec.type());
      }
      this.registerNewEntities();
      return entity;
   }

   // ------------------------------------------------------------------ actions

   private void applyActions(final int forTick) throws Exception {
      List<Scenario.Action> actions = this.scenario.actions;
      while (this.nextAction < actions.size() && actions.get(this.nextAction).tick() == forTick) {
         Scenario.Action action = actions.get(this.nextAction++);
         BlockPos pos = action.pos() == null ? null : new BlockPos(action.pos()[0], action.pos()[1], action.pos()[2]);
         switch (action.type()) {
            case "use" -> {
               BlockHitResult hit = this.aimPlayer(pos, action.face());
               this.level.getBlockState(pos).useWithoutItem(this.level, this.player, hit);
            }
            case "use_item" -> {
               Identifier itemId = Identifier.parse(action.item());
               if (!BuiltInRegistries.ITEM.containsKey(itemId)) {
                  throw new IllegalArgumentException("unknown item " + action.item());
               }
               Item item = BuiltInRegistries.ITEM.getValue(itemId);
               BlockHitResult hit = this.aimPlayer(pos, action.face());
               InteractionHand hand = InteractionHand.MAIN_HAND;
               this.player.setItemInHand(hand, new ItemStack(item));
               // The sequence of GameTestHelper.useBlock.
               BlockState state = this.level.getBlockState(pos);
               InteractionResult result = state.useItemOn(this.player.getItemInHand(hand), this.level, this.player, hand, hit);
               if (!result.consumesAction()) {
                  if (!(result instanceof InteractionResult.TryEmptyHandInteraction)
                     || !state.useWithoutItem(this.level, this.player, hit).consumesAction()) {
                     this.player.getItemInHand(hand).useOn(new UseOnContext(this.player, hand, hit));
                  }
               }
               this.player.setItemInHand(hand, ItemStack.EMPTY);
            }
            case "set" -> this.level.setBlock(pos, this.parseState(action.state()), action.flags());
            case "destroy" -> this.level.destroyBlock(pos, action.drop());
            case "summon" -> this.summon(action.entity());
            case "kill" -> {
               if (action.entityIndex() < 0 || action.entityIndex() >= this.entitiesByIndex.size()) {
                  throw new IllegalArgumentException("kill: there is no entity with index " + action.entityIndex());
               }
               this.entitiesByIndex.get(action.entityIndex()).discard();
            }
            default -> throw new IllegalArgumentException(action.type());
         }
         this.registerNewEntities();
      }
   }

   /** Puts the player in front of the face it clicks and returns the hit (the centre of that face). */
   private BlockHitResult aimPlayer(final BlockPos pos, final String faceName) {
      Direction face = Direction.byName(faceName);
      if (face == null) {
         throw new IllegalArgumentException("unknown face " + faceName);
      }
      double cx = pos.getX() + 0.5;
      double cy = pos.getY() + 0.5;
      double cz = pos.getZ() + 0.5;
      Vec3 location = new Vec3(cx + 0.5 * face.getStepX(), cy + 0.5 * face.getStepY(), cz + 0.5 * face.getStepZ());
      if (face == Direction.UP) {
         this.player.snapTo(cx, pos.getY() + 1.0, cz, 0.0F, 90.0F);
      } else if (face == Direction.DOWN) {
         this.player.snapTo(cx, pos.getY() - 2.0, cz, 0.0F, -90.0F);
      } else {
         this.player.snapTo(cx + 2.0 * face.getStepX(), pos.getY(), cz + 2.0 * face.getStepZ(), face.getOpposite().toYRot(), 0.0F);
      }
      return new BlockHitResult(location, face, pos, false);
   }

   // ------------------------------------------------------------------ recording

   private boolean inBox(final BlockPos pos) {
      int[] min = this.scenario.boxMin;
      int[] max = this.scenario.boxMax;
      return pos.getX() >= min[0] && pos.getX() <= max[0]
         && pos.getY() >= min[1] && pos.getY() <= max[1]
         && pos.getZ() >= min[2] && pos.getZ() <= max[2];
   }

   private List<Entity> allEntities() {
      List<Entity> entities = new ArrayList<>();
      for (Entity entity : this.level.getAllEntities()) {
         if (entity != null && !entity.isRemoved()) {
            entities.add(entity);
         }
      }
      entities.sort(Comparator.comparingInt(Entity::getId));
      return entities;
   }

   /** Entities get their index in order of creation (entity ids increase with creation). */
   private void registerNewEntities() {
      for (Entity entity : this.allEntities()) {
         if (!this.entityIndex.containsKey(entity)) {
            this.entityIndex.put(entity, this.entitiesByIndex.size());
            this.entitiesByIndex.add(entity);
         }
      }
   }

   /**
    * The server writes the attribute list of a mob (and the modifiers of an attribute) in the order of an
    * identity hash map, which differs from run to run; the trace has them sorted by "id".
    */
   private static void sortById(final CompoundTag tag, final String key) {
      if (tag.get(key) instanceof net.minecraft.nbt.ListTag list) {
         List<net.minecraft.nbt.Tag> items = new ArrayList<>(list);
         for (net.minecraft.nbt.Tag item : items) {
            if (!(item instanceof CompoundTag compound) || !(compound.get("id") instanceof net.minecraft.nbt.StringTag)) {
               return;
            }
            sortById(compound, "modifiers");
         }
         items.sort(Comparator.comparing(item -> ((CompoundTag)item).getStringOr("id", "")));
         net.minecraft.nbt.ListTag sorted = new net.minecraft.nbt.ListTag();
         sorted.addAll(items);
         tag.put(key, sorted);
      }
   }

   private static final Comparator<BlockPos> XYZ = Comparator.<BlockPos>comparingInt(BlockPos::getX).thenComparingInt(BlockPos::getY).thenComparingInt(BlockPos::getZ);

   private static void pos(final StringBuilder sb, final BlockPos pos) {
      sb.append('[').append(pos.getX()).append(',').append(pos.getY()).append(',').append(pos.getZ()).append(']');
   }

   private static void key(final StringBuilder sb, final BlockPos pos) {
      sb.append('"').append(pos.getX()).append(',').append(pos.getY()).append(',').append(pos.getZ()).append('"');
   }

   private void recordFrame(final int frameTick) {
      Scenario s = this.scenario;
      StringBuilder sb = this.out;
      if (frameTick > 0) {
         sb.append(",\n");
      }
      sb.append("{\"tick\":").append(frameTick);
      sb.append(",\"gameTime\":").append(this.level.getGameTime());

      // blocks
      sb.append(",\"blocks\":{");
      boolean first = true;
      BlockPos.MutableBlockPos cursor = new BlockPos.MutableBlockPos();
      int index = 0;
      for (int x = s.boxMin[0]; x <= s.boxMax[0]; x++) {
         for (int y = s.boxMin[1]; y <= s.boxMax[1]; y++) {
            for (int z = s.boxMin[2]; z <= s.boxMax[2]; z++) {
               BlockState state = this.level.getBlockState(cursor.set(x, y, z));
               if (state != this.prevBlocks[index]) {
                  this.prevBlocks[index] = state;
                  if (!first) {
                     sb.append(',');
                  }
                  first = false;
                  key(sb, cursor);
                  sb.append(':');
                  Json.str(sb, this.stateName(state));
               }
               index++;
            }
         }
      }
      sb.append('}');

      // block entities, block ticks, fluid ticks
      TreeMap<BlockPos, String> blockEntities = new TreeMap<>(XYZ);
      List<ScheduledTick<Block>> blockTicks = new ArrayList<>();
      List<ScheduledTick<Fluid>> fluidTicks = new ArrayList<>();
      for (int cx = s.boxMin[0] >> 4; cx <= s.boxMax[0] >> 4; cx++) {
         for (int cz = s.boxMin[2] >> 4; cz <= s.boxMax[2] >> 4; cz++) {
            LevelChunk chunk = this.level.getChunk(cx, cz);
            for (Map.Entry<BlockPos, BlockEntity> entry : chunk.getBlockEntities().entrySet()) {
               BlockEntity blockEntity = entry.getValue();
               if (this.inBox(entry.getKey()) && !blockEntity.isRemoved()) {
                  String type = BuiltInRegistries.BLOCK_ENTITY_TYPE.getKey(blockEntity.getType()).toString();
                  String nbt = NbtJson.of(blockEntity.saveWithoutMetadata(this.level.registryAccess()));
                  blockEntities.put(entry.getKey().immutable(), "{\"type\":" + Json.str(type) + ",\"nbt\":" + nbt + "}");
               }
            }
            ((LevelChunkTicks<Block>)chunk.getBlockTicks()).getAll().filter(t -> this.inBox(t.pos())).forEach(blockTicks::add);
            ((LevelChunkTicks<Fluid>)chunk.getFluidTicks()).getAll().filter(t -> this.inBox(t.pos())).forEach(fluidTicks::add);
         }
      }

      TreeMap<BlockPos, String> blockEntityDelta = new TreeMap<>(XYZ);
      for (Map.Entry<BlockPos, String> entry : blockEntities.entrySet()) {
         if (!entry.getValue().equals(this.prevBlockEntities.get(entry.getKey()))) {
            blockEntityDelta.put(entry.getKey(), entry.getValue());
         }
      }
      for (BlockPos old : this.prevBlockEntities.keySet()) {
         if (!blockEntities.containsKey(old)) {
            blockEntityDelta.put(old, "null");
         }
      }
      this.prevBlockEntities = new HashMap<>(blockEntities);
      sb.append(",\"blockEntities\":{");
      first = true;
      for (Map.Entry<BlockPos, String> entry : blockEntityDelta.entrySet()) {
         if (!first) {
            sb.append(',');
         }
         first = false;
         key(sb, entry.getKey());
         sb.append(':').append(entry.getValue());
      }
      sb.append('}');

      // The order in which Level.tickBlockEntities will go through the ticking block entities.
      sb.append(",\"blockEntityTickers\":[");
      first = true;
      for (List<net.minecraft.world.level.block.entity.TickingBlockEntity> list : List.of(this.tickers, this.pendingTickers)) {
         for (net.minecraft.world.level.block.entity.TickingBlockEntity ticker : list) {
            if (!ticker.isRemoved() && this.inBox(ticker.getPos())) {
               if (!first) {
                  sb.append(',');
               }
               first = false;
               pos(sb, ticker.getPos());
            }
         }
      }
      sb.append(']');

      long gameTime = this.level.getGameTime();
      sb.append(",\"scheduled\":[");
      blockTicks.sort(ScheduledTick.DRAIN_ORDER);
      first = true;
      for (ScheduledTick<Block> t : blockTicks) {
         if (!first) {
            sb.append(',');
         }
         first = false;
         sb.append("{\"pos\":");
         pos(sb, t.pos());
         sb.append(",\"block\":").append(Json.str(BuiltInRegistries.BLOCK.getKey(t.type()).toString()));
         sb.append(",\"delay\":").append(t.triggerTick() - gameTime);
         sb.append(",\"priority\":").append(t.priority().getValue()).append('}');
      }
      sb.append(']');

      if (!fluidTicks.isEmpty()) {
         sb.append(",\"fluidTicks\":[");
         fluidTicks.sort(ScheduledTick.DRAIN_ORDER);
         first = true;
         for (ScheduledTick<Fluid> t : fluidTicks) {
            if (!first) {
               sb.append(',');
            }
            first = false;
            sb.append("{\"pos\":");
            pos(sb, t.pos());
            sb.append(",\"fluid\":").append(Json.str(BuiltInRegistries.FLUID.getKey(t.type()).toString()));
            sb.append(",\"delay\":").append(t.triggerTick() - gameTime);
            sb.append(",\"priority\":").append(t.priority().getValue()).append('}');
         }
         sb.append(']');
      }

      sb.append(",\"blockEvents\":[");
      first = true;
      for (BlockEventData event : this.blockEvents) {
         if (this.inBox(event.pos())) {
            if (!first) {
               sb.append(',');
            }
            first = false;
            sb.append("{\"pos\":");
            pos(sb, event.pos());
            sb.append(",\"block\":").append(Json.str(BuiltInRegistries.BLOCK.getKey(event.block()).toString()));
            sb.append(",\"a\":").append(event.paramA()).append(",\"b\":").append(event.paramB()).append('}');
         }
      }
      sb.append(']');

      this.registerNewEntities();
      sb.append(",\"entities\":[");
      first = true;
      for (int i = 0; i < this.entitiesByIndex.size(); i++) {
         Entity entity = this.entitiesByIndex.get(i);
         if (entity.isRemoved()) {
            continue;
         }
         if (!first) {
            sb.append(',');
         }
         first = false;
         TagValueOutput output = TagValueOutput.createWithContext(ProblemReporter.DISCARDING, this.level.registryAccess());
         entity.saveWithoutId(output);
         CompoundTag tag = output.buildResult();
         tag.remove("UUID");
         tag.remove("Pos");
         tag.remove("Motion");
         tag.remove("OnGround");
         sortById(tag, "attributes");
         Vec3 motion = entity.getDeltaMovement();
         sb.append("{\"index\":").append(i);
         sb.append(",\"type\":").append(Json.str(BuiltInRegistries.ENTITY_TYPE.getKey(entity.getType()).toString()));
         sb.append(",\"pos\":[\"").append(Json.hex(entity.getX())).append("\",\"").append(Json.hex(entity.getY())).append("\",\"").append(Json.hex(entity.getZ())).append("\"]");
         sb.append(",\"motion\":[\"").append(Json.hex(motion.x)).append("\",\"").append(Json.hex(motion.y)).append("\",\"").append(Json.hex(motion.z)).append("\"]");
         sb.append(",\"onGround\":").append(entity.onGround());
         sb.append(",\"nbt\":").append(NbtJson.of(tag)).append('}');
      }
      sb.append("]}");
   }
}
