package rsharness;

import java.util.concurrent.atomic.AtomicLong;

/**
 * Replacement for {@code RandomSupport.generateUniqueSeed()} (see PatchRandomSupport).
 *
 * Outside a scenario, or on any thread but the server thread, it behaves like vanilla (a unique,
 * time-dependent seed). While a scenario is running, calls made on the server thread return a
 * deterministic sequence, so that every {@code RandomSource.create()} (the private random of each
 * new entity, for instance) is seeded the same way in every run.
 */
public final class SeedHook {
   public static final long GOLDEN_RATIO_64 = -7046029254386353131L; // 0x9E3779B97F4A7C15

   private static final AtomicLong SEED_UNIQUIFIER = new AtomicLong(8682522807148012L);
   private static volatile Thread pinnedThread;
   private static long counter;

   private SeedHook() {
   }

   /** Called from the patched RandomSupport.generateUniqueSeed(). */
   public static long next() {
      if (Thread.currentThread() == pinnedThread) {
         counter++;
         return counter * GOLDEN_RATIO_64;
      }
      return SEED_UNIQUIFIER.updateAndGet(current -> current * 1181783497276652981L) ^ System.nanoTime();
   }

   /** Start the deterministic sequence on the calling thread: the k-th call (k = 1, 2, ...) returns k * GOLDEN_RATIO_64. */
   public static void pin() {
      counter = 0L;
      pinnedThread = Thread.currentThread();
   }

   public static void unpin() {
      pinnedThread = null;
   }
}
