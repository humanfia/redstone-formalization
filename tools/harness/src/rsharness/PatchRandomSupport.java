package rsharness;

import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;
import java.lang.constant.MethodTypeDesc;
import java.lang.instrument.ClassFileTransformer;
import java.lang.instrument.Instrumentation;
import java.security.ProtectionDomain;

/**
 * Java agent (the game jar is signed, so the class cannot simply be shadowed on the class path).
 * When net.minecraft.world.level.levelgen.RandomSupport is loaded, the body of
 * {@code generateUniqueSeed()} is replaced by {@code return SeedHook.next();}. Nothing else in the
 * game is changed.
 */
public final class PatchRandomSupport {
   private static final String CLASS = "net/minecraft/world/level/levelgen/RandomSupport";
   static volatile boolean applied;

   public static void premain(final String args, final Instrumentation instrumentation) {
      instrumentation.addTransformer(new ClassFileTransformer() {
         @Override
         public byte[] transform(
            final ClassLoader loader, final String className, final Class<?> redefined, final ProtectionDomain domain, final byte[] bytes
         ) {
            if (!CLASS.equals(className)) {
               return null;
            }
            try {
               byte[] patched = patch(bytes);
               applied = true;
               return patched;
            } catch (Throwable t) {
               t.printStackTrace();
               return null;
            }
         }
      });
   }

   static byte[] patch(final byte[] original) {
      ClassFile classFile = ClassFile.of();
      ClassModel model = classFile.parse(original);
      MethodTypeDesc noArgsLong = MethodTypeDesc.of(ConstantDescs.CD_long);
      boolean[] found = new boolean[1];
      byte[] patched = classFile.transformClass(model, (builder, element) -> {
         if (element instanceof MethodModel method
            && method.methodName().equalsString("generateUniqueSeed")
            && method.methodType().equalsString("()J")) {
            found[0] = true;
            builder.withMethodBody(
               "generateUniqueSeed",
               noArgsLong,
               ClassFile.ACC_PUBLIC | ClassFile.ACC_STATIC,
               code -> code.invokestatic(ClassDesc.of("rsharness.SeedHook"), "next", noArgsLong).lreturn()
            );
         } else {
            builder.with(element);
         }
      });
      if (!found[0]) {
         throw new IllegalStateException("RandomSupport.generateUniqueSeed()J not found");
      }
      return patched;
   }
}
