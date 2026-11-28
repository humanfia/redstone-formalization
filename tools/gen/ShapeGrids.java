import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import net.minecraft.SharedConstants;
import net.minecraft.core.BlockPos;
import net.minecraft.core.Direction;
import net.minecraft.server.Bootstrap;
import net.minecraft.world.level.EmptyBlockGetter;
import net.minecraft.world.level.block.Block;
import net.minecraft.world.level.block.state.BlockState;
import net.minecraft.world.phys.shapes.VoxelShape;

/**
 * Writes the grid of every collision shape of the game: for each distinct list of boxes (the key
 * under which blockdump.json numbers shapes), the coordinates of the shape along x, y and z
 * ({@code VoxelShape.getCoords}). The boxes alone do not determine the grid, and the grid decides
 * how a box that overlaps the shape collides with it.
 *
 * <pre>
 *   source tools/env.sh
 *   srun -c 2 --mem 4G java -cp "$MC_GAME_JAR:$(find "$MC_LIBS" -name '*.jar' | tr '\n' ':')" \
 *       tools/gen/ShapeGrids.java "$MC_REPORTS/shapegrids.json"
 * </pre>
 *
 * Output: {@code {"grids": [{"boxes": [[...]], "coords": [[x...], [y...], [z...]]}], "conflicts": n}}
 * with doubles as 16 hex digits. {@code conflicts} counts block states whose collision shape has
 * the boxes of an earlier shape but another grid; they keep the grid seen first and are listed
 * on standard error.
 */
public final class ShapeGrids {
   private static String hex(final double v) {
      return String.format("%016x", Double.doubleToRawLongBits(v));
   }

   private static String boxes(final VoxelShape shape) {
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
      return sb.append(']').toString();
   }

   private static String coords(final VoxelShape shape) {
      StringBuilder sb = new StringBuilder("[");
      for (Direction.Axis axis : new Direction.Axis[]{Direction.Axis.X, Direction.Axis.Y, Direction.Axis.Z}) {
         sb.append(axis == Direction.Axis.X ? "[" : ",[");
         var list = shape.getCoords(axis);
         for (int i = 0; i < list.size(); i++) {
            sb.append(i > 0 ? "," : "").append('"').append(hex(list.getDouble(i))).append('"');
         }
         sb.append(']');
      }
      return sb.append(']').toString();
   }

   public static void main(final String[] args) throws Exception {
      SharedConstants.tryDetectVersion();
      Bootstrap.bootStrap();
      Map<String, String> grids = new LinkedHashMap<>();
      List<String> conflicts = new ArrayList<>();
      for (BlockState state : Block.BLOCK_STATE_REGISTRY) {
         VoxelShape shape = state.getCollisionShape(EmptyBlockGetter.INSTANCE, BlockPos.ZERO);
         if (shape.isEmpty()) {
            continue;
         }
         String key = boxes(shape);
         String value = coords(shape);
         String old = grids.putIfAbsent(key, value);
         if (old != null && !old.equals(value)) {
            conflicts.add(state.toString());
         }
      }
      StringBuilder sb = new StringBuilder("{\"grids\":[");
      boolean first = true;
      for (Map.Entry<String, String> e : grids.entrySet()) {
         sb.append(first ? "\n" : ",\n").append("{\"boxes\":").append(e.getKey()).append(",\"coords\":").append(e.getValue()).append('}');
         first = false;
      }
      sb.append("\n],\"conflicts\":").append(conflicts.size()).append("}\n");
      Files.writeString(Path.of(args[0]), sb.toString(), StandardCharsets.UTF_8);
      for (String c : conflicts) {
         System.err.println("ShapeGrids: another grid for the same boxes: " + c);
      }
      System.err.println("ShapeGrids: " + grids.size() + " shapes, " + conflicts.size() + " conflicts");
      System.exit(0);
   }
}
