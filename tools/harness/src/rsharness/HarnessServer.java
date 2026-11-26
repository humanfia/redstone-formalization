package rsharness;

import com.mojang.datafixers.DataFixer;
import java.util.Optional;
import java.util.function.BooleanSupplier;
import net.minecraft.CrashReport;
import net.minecraft.server.Services;
import net.minecraft.server.TickTask;
import net.minecraft.server.WorldStem;
import net.minecraft.server.dedicated.DedicatedServer;
import net.minecraft.server.dedicated.DedicatedServerSettings;
import net.minecraft.server.notifications.NotificationManager;
import net.minecraft.server.packs.repository.PackRepository;
import net.minecraft.world.level.gamerules.GameRules;
import net.minecraft.world.level.storage.LevelStorageSource;

/**
 * The vanilla dedicated server with three changes, none of which touches what a tick does:
 *  - after each {@code tickServer} (one complete vanilla server tick) the recorder runs on the server
 *    thread, between ticks, where packets and console commands are handled in a normal server;
 *  - the server does not sleep until the next 50 ms boundary, it only runs the queued main-thread
 *    tasks (all of them, independently of wall-clock time) and lets the light engine finish;
 *  - when the recorder is done the JVM exits.
 */
final class HarnessServer extends DedicatedServer {
   private final Recorder recorder;

   HarnessServer(
      final Thread serverThread,
      final LevelStorageSource.LevelStorageAccess levelStorageSource,
      final PackRepository packRepository,
      final WorldStem worldStem,
      final Optional<GameRules> gameRules,
      final DedicatedServerSettings settings,
      final DataFixer fixerUpper,
      final Services services,
      final NotificationManager notificationManager,
      final Recorder recorder
   ) {
      super(serverThread, levelStorageSource, packRepository, worldStem, gameRules, settings, fixerUpper, services, null, notificationManager);
      this.recorder = recorder;
   }

   @Override
   protected void tickServer(final BooleanSupplier haveTime) {
      super.tickServer(() -> true);
      this.recorder.afterTick(this);
   }

   @Override
   protected boolean shouldRun(final TickTask task) {
      return true;
   }

   @Override
   protected void waitUntilNextTick() {
      this.runAllTasks();
      this.recorder.settle(this);
      this.runAllTasks();
   }

   /** Runs the queued main-thread tasks; for the recorder. */
   void drainTasks() {
      this.runAllTasks();
   }

   @Override
   protected void onServerCrash(final CrashReport report) {
      super.onServerCrash(report);
      Main.ERR.println("harness: the server crashed");
      this.recorder.exitCode = 3;
   }

   @Override
   protected void onServerExit() {
      super.onServerExit();
      System.out.flush();
      Main.ERR.flush();
      Runtime.getRuntime().halt(this.recorder.finished ? this.recorder.exitCode : 3);
   }
}
