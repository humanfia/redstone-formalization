import it.unimi.dsi.fastutil.doubles.DoubleList;
import java.io.PrintWriter;
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import net.minecraft.SharedConstants;
import net.minecraft.core.BlockPos;
import net.minecraft.core.Direction;
import net.minecraft.core.registries.BuiltInRegistries;
import net.minecraft.server.Bootstrap;
import net.minecraft.world.level.EmptyBlockGetter;
import net.minecraft.world.level.block.Block;
import net.minecraft.world.level.block.state.BlockBehaviour;
import net.minecraft.world.level.block.state.BlockState;
import net.minecraft.world.phys.shapes.DiscreteVoxelShape;
import net.minecraft.world.phys.shapes.Shapes;
import net.minecraft.world.phys.shapes.VoxelShape;

/**
 * Writes what the TNT model needs about blocks beyond the block dump: explosion resistance,
 * speed factor, bounce restitution and loot table of every block, whether its shape depends on
 * more than the block state, and the voxel grid of every collision shape (the grid decides how
 * an entity that overlaps a shape collides with it).
 *
 * Run by tools/gen/gen_tnt.py:  java -cp <classpath> tools/gen/TntDump.java out.json
 */
public class TntDump {
   private static String hex(final double d) {
      return String.format("\"%016x\"", Double.doubleToRawLongBits(d));
   }

   private static String hexf(final float f) {
      return String.format("\"%08x\"", Float.floatToRawIntBits(f));
   }

   public static void main(final String[] args) throws Exception {
      SharedConstants.tryDetectVersion();
      Bootstrap.bootStrap();
      Field shapeField = VoxelShape.class.getDeclaredField("shape");
      shapeField.setAccessible(true);
      Field hasCollisionField = BlockBehaviour.class.getDeclaredField("hasCollision");
      hasCollisionField.setAccessible(true);
      Map<String, Integer> grids = new LinkedHashMap<>();
      List<String> gridList = new ArrayList<>();
      StringBuilder blocks = new StringBuilder();
      boolean firstBlock = true;
      for (Block block : BuiltInRegistries.BLOCK) {
         if (!firstBlock) {
            blocks.append(",\n");
         }
         firstBlock = false;
         blocks.append("{\"id\":\"").append(BuiltInRegistries.BLOCK.getKey(block)).append("\"");
         blocks.append(",\"explosionResistance\":").append(hexf(block.getExplosionResistance()));
         blocks.append(",\"speedFactor\":").append(hexf(block.getSpeedFactor()));
         blocks.append(",\"bounceRestitution\":").append(hexf(block.getBounceRestitution()));
         blocks.append(",\"lootTable\":");
         blocks.append(block.getLootTable().map(key -> "\"" + key + "\"").orElse("null"));
         blocks.append(",\"dynamicShape\":").append(block.hasDynamicShape());
         blocks.append(",\"hasCollision\":").append(hasCollisionField.getBoolean(block));
         blocks.append(",\"states\":[");
         boolean firstState = true;
         for (BlockState state : block.getStateDefinition().getPossibleStates()) {
            VoxelShape shape = state.getCollisionShape(EmptyBlockGetter.INSTANCE, BlockPos.ZERO);
            StringBuilder g = new StringBuilder();
            g.append("{\"block\":").append(shape == Shapes.block());
            DiscreteVoxelShape discrete = (DiscreteVoxelShape)shapeField.get(shape);
            int[] sizes = new int[]{discrete.getXSize(), discrete.getYSize(), discrete.getZSize()};
            String[] names = new String[]{"xs", "ys", "zs"};
            Direction.Axis[] axes = new Direction.Axis[]{Direction.Axis.X, Direction.Axis.Y, Direction.Axis.Z};
            for (int i = 0; i < 3; i++) {
               DoubleList coords = shape.getCoords(axes[i]);
               g.append(",\"").append(names[i]).append("\":[");
               for (int k = 0; k <= sizes[i]; k++) {
                  g.append(k == 0 ? "" : ",").append(hex(coords.getDouble(k)));
               }
               g.append("]");
            }
            g.append(",\"full\":\"");
            for (int x = 0; x < sizes[0]; x++) {
               for (int y = 0; y < sizes[1]; y++) {
                  for (int z = 0; z < sizes[2]; z++) {
                     g.append(discrete.isFull(x, y, z) ? '1' : '0');
                  }
               }
            }
            g.append("\",\"boxes\":[");
            boolean[] firstBox = new boolean[]{true};
            shape.forAllBoxes((x1, y1, z1, x2, y2, z2) -> {
               g.append(firstBox[0] ? "" : ",");
               firstBox[0] = false;
               g.append("[").append(hex(x1)).append(",").append(hex(y1)).append(",").append(hex(z1)).append(",");
               g.append(hex(x2)).append(",").append(hex(y2)).append(",").append(hex(z2)).append("]");
            });
            g.append("]}");
            String key = g.toString();
            Integer index = grids.get(key);
            if (index == null) {
               index = gridList.size();
               grids.put(key, index);
               gridList.add(key);
            }
            blocks.append(firstState ? "" : ",").append(index);
            firstState = false;
         }
         blocks.append("]}");
      }
      try (PrintWriter out = new PrintWriter(args[0])) {
         out.println("{\"version\":\"" + SharedConstants.getCurrentVersion().name() + "\",");
         out.println("\"grids\":[");
         out.println(String.join(",\n", gridList));
         out.println("],\"blocks\":[");
         out.println(blocks);
         out.println("]}");
      }
      System.exit(0);
   }
}
