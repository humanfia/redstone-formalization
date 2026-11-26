import it.unimi.dsi.fastutil.doubles.DoubleList;
import java.util.Map;
import java.util.TreeMap;
import net.minecraft.SharedConstants;
import net.minecraft.core.BlockPos;
import net.minecraft.core.Direction;
import net.minecraft.server.Bootstrap;
import net.minecraft.world.level.EmptyBlockGetter;
import net.minecraft.world.level.block.Block;
import net.minecraft.world.level.block.state.BlockState;
import net.minecraft.world.phys.shapes.VoxelShape;

/**
 * Prints the voxel grid of every collision shape of the game, for tests/palettes/minecart-tables.py:
 *
 *   java -cp "$(cat $MC_HOME/harness-build/classpath)" tests/palettes/MinecartShapeGrid.java > tests/palettes/minecart-grid.txt
 *
 * A line is `boxes<TAB>x coordinates<TAB>y coordinates<TAB>z coordinates`: the boxes of the shape as
 * the block dump of the harness writes them (the key of its shape table), and the coordinates of the
 * grid planes of the shape along each axis (`VoxelShape.getCoords`), as raw `double` bits. The grid is
 * what `VoxelShape.collide` works on, and the boxes alone do not determine it. The program fails if
 * two shapes with the same boxes have different grids.
 */
public class MinecartShapeGrid {
   private static String hex(final double v) {
      return String.format("%016x", Double.doubleToRawLongBits(v));
   }

   private static String coords(final DoubleList list) {
      StringBuilder sb = new StringBuilder();
      for (int i = 0; i < list.size(); i++) {
         if (i > 0) {
            sb.append(',');
         }
         sb.append(hex(list.getDouble(i)));
      }
      return sb.toString();
   }

   public static void main(final String[] args) {
      SharedConstants.tryDetectVersion();
      Bootstrap.bootStrap();
      Map<String, String> grids = new TreeMap<>();
      for (BlockState state : Block.BLOCK_STATE_REGISTRY) {
         VoxelShape shape = state.getCollisionShape(EmptyBlockGetter.INSTANCE, BlockPos.ZERO);
         if (shape.isEmpty()) {
            continue;
         }
         StringBuilder sb = new StringBuilder("[");
         boolean[] first = {true};
         shape.forAllBoxes((x1, y1, z1, x2, y2, z2) -> {
            if (!first[0]) {
               sb.append(',');
            }
            first[0] = false;
            sb.append("[\"").append(hex(x1)).append("\",\"").append(hex(y1)).append("\",\"").append(hex(z1)).append("\",\"")
               .append(hex(x2)).append("\",\"").append(hex(y2)).append("\",\"").append(hex(z2)).append("\"]");
         });
         String key = sb.append(']').toString();
         String grid = coords(shape.getCoords(Direction.Axis.X)) + "\t" + coords(shape.getCoords(Direction.Axis.Y)) + "\t"
            + coords(shape.getCoords(Direction.Axis.Z));
         String old = grids.put(key, grid);
         if (old != null && !old.equals(grid)) {
            throw new IllegalStateException("two grids for the boxes " + key + " (" + state + ")");
         }
      }
      StringBuilder out = new StringBuilder();
      grids.forEach((key, grid) -> out.append(key).append('\t').append(grid).append('\n'));
      System.out.print(out);
   }
}
