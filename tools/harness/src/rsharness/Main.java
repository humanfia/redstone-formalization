package rsharness;

import com.mojang.authlib.services.MinecraftServicesDiscoveryService;
import com.mojang.serialization.Dynamic;
import com.mojang.serialization.Lifecycle;
import java.io.File;
import java.net.Proxy;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import net.minecraft.CrashReport;
import net.minecraft.SharedConstants;
import net.minecraft.commands.Commands;
import net.minecraft.core.Registry;
import net.minecraft.core.registries.Registries;
import net.minecraft.server.Bootstrap;
import net.minecraft.server.Eula;
import net.minecraft.server.MinecraftServer;
import net.minecraft.server.Services;
import net.minecraft.server.WorldLoader;
import net.minecraft.server.WorldStem;
import net.minecraft.server.dedicated.DedicatedServerProperties;
import net.minecraft.server.dedicated.DedicatedServerSettings;
import net.minecraft.server.notifications.NotificationManager;
import net.minecraft.server.packs.repository.PackRepository;
import net.minecraft.server.packs.repository.ServerPacksSource;
import net.minecraft.util.Util;
import net.minecraft.util.datafix.DataFixers;
import net.minecraft.world.flag.FeatureFlags;
import net.minecraft.world.level.LevelSettings;
import net.minecraft.world.level.WorldDataConfiguration;
import net.minecraft.world.level.chunk.storage.RegionFileVersion;
import net.minecraft.world.level.dimension.LevelStem;
import net.minecraft.world.level.levelgen.WorldDimensions;
import net.minecraft.world.level.levelgen.WorldGenSettings;
import net.minecraft.world.level.storage.LevelDataAndDimensions;
import net.minecraft.world.level.storage.LevelStorageSource;
import net.minecraft.world.level.storage.PrimaryLevelData;

/**
 * Entry point. Does what net.minecraft.server.Main does to start a dedicated server in the current
 * directory (server.properties and eula.txt are read from it, a new world is created in it), except
 * that the server object is a {@link HarnessServer}, a DedicatedServer with a hook after every tick.
 *
 * Usage:
 *   Main dump <out.json>
 *   Main record <jobs.tsv>        (one "scenario-path<TAB>trace-path" per line)
 */
public final class Main {
   /** The real stderr; the game replaces System.err by a stream that goes to its log. */
   static final java.io.PrintStream ERR = System.err;

   public static void main(final String[] args) throws Exception {
      if (args.length < 2) {
         System.err.println("usage: Main dump <out.json> | Main record <jobs.tsv>");
         System.exit(2);
      }

      Recorder recorder;
      if (args[0].equals("dump")) {
         recorder = Recorder.forDump(Path.of(args[1]));
      } else if (args[0].equals("record")) {
         List<Recorder.Job> jobs = new ArrayList<>();
         for (String line : Files.readAllLines(Path.of(args[1]))) {
            if (!line.isBlank()) {
               String[] parts = line.split("\t");
               jobs.add(new Recorder.Job(Path.of(parts[0]), Path.of(parts[1])));
            }
         }
         recorder = Recorder.forJobs(jobs);
      } else {
         throw new IllegalArgumentException("unknown mode " + args[0]);
      }

      long start = System.nanoTime();
      SharedConstants.tryDetectVersion();
      CrashReport.preload();
      Bootstrap.bootStrap();
      Bootstrap.validate();
      Util.startTimerHackThread();
      Path settingsFile = Paths.get("server.properties");
      DedicatedServerSettings settings = new DedicatedServerSettings(settingsFile);
      settings.forceSave();
      RegionFileVersion.configure(settings.getProperties().regionFileComression);
      Eula eula = new Eula(Paths.get("eula.txt"));
      if (!eula.hasAgreedToEULA()) {
         System.err.println("harness: eula.txt in the run directory does not say eula=true");
         System.exit(2);
      }

      File universePath = new File(".");
      Services services = Services.create(MinecraftServicesDiscoveryService.create(Proxy.NO_PROXY), universePath);
      NotificationManager notificationManager = new NotificationManager();
      String levelName = settings.getProperties().levelName;
      LevelStorageSource levelStorageSource = LevelStorageSource.createDefault(universePath.toPath());
      LevelStorageSource.LevelStorageAccess access = levelStorageSource.validateAndCreateAccess(levelName);
      if (access.hasWorldData()) {
         throw new IllegalStateException("the run directory already contains a world; the harness always starts from a new one");
      }

      PackRepository packRepository = ServerPacksSource.createPackRepository(access);
      DedicatedServerProperties properties = settings.getProperties();
      WorldDataConfiguration dataConfig = new WorldDataConfiguration(properties.initialDataPackConfiguration, FeatureFlags.DEFAULT_FLAGS);
      WorldLoader.PackConfig packConfig = new WorldLoader.PackConfig(packRepository, dataConfig, false, true);
      WorldLoader.InitConfig worldLoadConfig = new WorldLoader.InitConfig(packConfig, Commands.CommandSelection.DEDICATED, properties.functionPermissions);
      WorldStem worldStem = Util.<WorldStem>blockUntilDone(
            executor -> WorldLoader.load(
               worldLoadConfig,
               context -> {
                  Registry<LevelStem> datapackDimensions = context.datapackDimensions().lookupOrThrow(Registries.LEVEL_STEM);
                  LevelSettings levelSettings = new LevelSettings(
                     properties.levelName,
                     properties.gameMode.get(),
                     new LevelSettings.DifficultySettings(properties.difficulty.get(), properties.hardcore, false),
                     false,
                     context.dataConfiguration()
                  );
                  WorldDimensions dimensions = properties.createDimensions(context.datapackWorldRegistries());
                  WorldDimensions.Complete finalDimensions = dimensions.bake(datapackDimensions);
                  Lifecycle lifecycle = finalDimensions.lifecycle().add(context.datapackWorldRegistries().allRegistriesLifecycle());
                  PrimaryLevelData levelData = new PrimaryLevelData(levelSettings, finalDimensions.specialWorldProperty(), lifecycle);
                  return new WorldLoader.DataLoadOutput<>(
                     new LevelDataAndDimensions.WorldDataAndGenSettings(levelData, new WorldGenSettings(properties.worldOptions, dimensions)),
                     finalDimensions.dimensionsRegistryAccess()
                  );
               },
               WorldStem::new,
               Util.backgroundExecutor(),
               executor
            )
         )
         .get();
      access.saveDataTag(worldStem.worldDataAndGenSettings().data());
      recorder.bootStartNanos = start;
      MinecraftServer.spin(thread -> {
         HarnessServer server = new HarnessServer(
            thread, access, packRepository, worldStem, Optional.empty(), settings, DataFixers.getDataFixer(), services, notificationManager, recorder
         );
         notificationManager.setServer(server);
         server.setPort(-1);
         return server;
      });
   }
}
