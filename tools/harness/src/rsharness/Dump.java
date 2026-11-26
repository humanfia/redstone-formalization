package rsharness;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.function.Supplier;
import net.minecraft.SharedConstants;
import net.minecraft.core.BlockPos;
import net.minecraft.core.Direction;
import net.minecraft.core.registries.BuiltInRegistries;
import net.minecraft.server.level.ServerLevel;
import net.minecraft.world.entity.Entity;
import net.minecraft.world.entity.EntitySpawnReason;
import net.minecraft.world.entity.EntityType;
import net.minecraft.world.item.Item;
import net.minecraft.world.level.BlockGetter;
import net.minecraft.world.level.EmptyBlockGetter;
import net.minecraft.world.level.block.Block;
import net.minecraft.world.level.block.SupportType;
import net.minecraft.world.level.block.entity.BlockEntityType;
import net.minecraft.world.level.block.state.BlockState;
import net.minecraft.world.level.block.state.properties.BooleanProperty;
import net.minecraft.world.level.block.state.properties.IntegerProperty;
import net.minecraft.world.level.block.state.properties.Property;
import net.minecraft.world.level.material.FluidState;
import net.minecraft.world.phys.shapes.VoxelShape;

/** Writes blockdump.json (tests/FORMAT.md, "Block dump"). Position-dependent queries use an empty BlockGetter at BlockPos.ZERO. */
final class Dump {
   private static final Direction[] DIRECTIONS = {Direction.DOWN, Direction.UP, Direction.NORTH, Direction.SOUTH, Direction.WEST, Direction.EAST};
   private static final BlockGetter EMPTY = EmptyBlockGetter.INSTANCE;
   private static final BlockPos ZERO = BlockPos.ZERO;

   private final Map<String, Integer> shapeIndex = new HashMap<>();
   private final List<String> shapes = new ArrayList<>();
   private final Map<String, Integer> failures = new TreeMap<>();

   static void write(final ServerLevel level, final Path path) throws Exception {
      String json = new Dump().build(level);
      Files.createDirectories(path.toAbsolutePath().getParent());
      Path tmp = path.resolveSibling(path.getFileName() + ".tmp" + ProcessHandle.current().pid());
      Files.writeString(tmp, json, StandardCharsets.UTF_8);
      Files.move(tmp, path, StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.ATOMIC_MOVE);
   }

   private int shape(final VoxelShape shape) {
      StringBuilder sb = new StringBuilder("[");
      boolean[] first = {true};
      shape.forAllBoxes((x1, y1, z1, x2, y2, z2) -> {
         if (!first[0]) {
            sb.append(',');
         }
         first[0] = false;
         sb.append("[\"").append(Json.hex(x1)).append("\",\"").append(Json.hex(y1)).append("\",\"").append(Json.hex(z1)).append("\",\"")
            .append(Json.hex(x2)).append("\",\"").append(Json.hex(y2)).append("\",\"").append(Json.hex(z2)).append("\"]");
      });
      sb.append(']');
      String key = sb.toString();
      Integer index = this.shapeIndex.get(key);
      if (index == null) {
         index = this.shapes.size();
         this.shapes.add(key);
         this.shapeIndex.put(key, index);
      }
      return index;
   }

   /** Appends {@code ,"name":value}; an attribute whose query throws is left out and counted. */
   private void attr(final StringBuilder sb, final String name, final Supplier<Object> value) {
      Object v;
      try {
         v = value.get();
      } catch (Throwable t) {
         this.failures.merge(name, 1, Integer::sum);
         return;
      }
      if (v == null) {
         return;
      }
      if (sb.charAt(sb.length() - 1) != '{') {
         sb.append(',');
      }
      Json.str(sb, name);
      sb.append(':');
      if (v instanceof String s) {
         Json.str(sb, s);
      } else {
         sb.append(v);
      }
   }

   private static int sturdy(final BlockState state, final SupportType type) {
      int mask = 0;
      for (int i = 0; i < DIRECTIONS.length; i++) {
         if (state.isFaceSturdy(EMPTY, ZERO, DIRECTIONS[i], type)) {
            mask |= 1 << i;
         }
      }
      return mask;
   }

   private static <T extends Comparable<T>> List<String> valueNames(final Property<T> property) {
      List<String> names = new ArrayList<>();
      for (T value : property.getPossibleValues()) {
         names.add(property.getName(value));
      }
      return names;
   }

   private static <T extends Comparable<T>> int valueIndex(final BlockState state, final Property<T> property) {
      return property.getPossibleValues().indexOf(state.getValue(property));
   }

   /** The fluid of a state, as the block state it would be on its own (minecraft:water[level=0]); null when there is none. */
   private static String fluidName(final FluidState fluid) {
      return fluid.isEmpty() ? null : Recorder.formatState(fluid.createLegacyBlock());
   }

   private String build(final ServerLevel level) {
      StringBuilder blocks = new StringBuilder();
      boolean firstBlock = true;
      for (Block block : BuiltInRegistries.BLOCK) {
         blocks.append(firstBlock ? "\n" : ",\n");
         firstBlock = false;
         blocks.append("{\"id\":").append(Json.str(BuiltInRegistries.BLOCK.getKey(block).toString()));
         blocks.append(",\"classes\":[");
         for (Class<?> c = block.getClass(); c != null && c != Object.class; c = c.getSuperclass()) {
            String name = c.getName().substring(c.getName().lastIndexOf('.') + 1);
            blocks.append(c == block.getClass() ? "" : ",").append(Json.str(name));
            if (c == Block.class) {
               break;
            }
         }
         blocks.append("],\"blockEntity\":");
         String blockEntity = null;
         for (BlockEntityType<?> type : BuiltInRegistries.BLOCK_ENTITY_TYPE) {
            if (type.isValid(block.defaultBlockState())) {
               blockEntity = BuiltInRegistries.BLOCK_ENTITY_TYPE.getKey(type).toString();
               break;
            }
         }
         blocks.append(blockEntity == null ? "null" : Json.str(blockEntity));

         List<Property<?>> properties = new ArrayList<>(block.getStateDefinition().getProperties());
         blocks.append(",\"properties\":[");
         for (int i = 0; i < properties.size(); i++) {
            Property<?> property = properties.get(i);
            blocks.append(i > 0 ? "," : "").append("{\"name\":").append(Json.str(property.getName()));
            String kind = property instanceof BooleanProperty ? "bool" : property instanceof IntegerProperty ? "int" : "enum";
            blocks.append(",\"kind\":").append(Json.str(kind));
            if (kind.equals("enum")) {
               blocks.append(",\"enumClass\":").append(Json.str(property.getValueClass().getSimpleName()));
            }
            blocks.append(",\"values\":[");
            List<String> names = valueNames(property);
            for (int j = 0; j < names.size(); j++) {
               blocks.append(j > 0 ? "," : "").append(Json.str(names.get(j)));
            }
            blocks.append("]}");
         }
         blocks.append(']');

         List<BlockState> states = block.getStateDefinition().getPossibleStates();
         blocks.append(",\"default\":").append(states.indexOf(block.defaultBlockState()));
         blocks.append(",\"states\":[");
         for (int si = 0; si < states.size(); si++) {
            BlockState state = states.get(si);
            blocks.append(si > 0 ? ",\n " : "\n ").append("{\"id\":").append(Block.getId(state)).append(",\"values\":[");
            for (int i = 0; i < properties.size(); i++) {
               blocks.append(i > 0 ? "," : "").append(valueIndex(state, properties.get(i)));
            }
            blocks.append("],\"attrs\":{");
            this.attr(blocks, "air", state::isAir);
            this.attr(blocks, "conductor", () -> state.isRedstoneConductor(EMPTY, ZERO));
            this.attr(blocks, "solid", state::isSolid);
            this.attr(blocks, "solidRender", state::isSolidRender);
            this.attr(blocks, "replaceable", () -> state.canBeReplaced());
            this.attr(blocks, "signalSource", state::isSignalSource);
            this.attr(blocks, "analog", state::hasAnalogOutputSignal);
            this.attr(blocks, "randomlyTicks", state::isRandomlyTicking);
            this.attr(blocks, "hasBlockEntity", state::hasBlockEntity);
            this.attr(blocks, "push", () -> state.getPistonPushReaction().name().toLowerCase(java.util.Locale.ROOT));
            this.attr(blocks, "destroySpeed", () -> Json.hex(state.getDestroySpeed(EMPTY, ZERO)));
            this.attr(blocks, "light", state::getLightEmission);
            this.attr(blocks, "sturdyFull", () -> sturdy(state, SupportType.FULL));
            this.attr(blocks, "sturdyCenter", () -> sturdy(state, SupportType.CENTER));
            this.attr(blocks, "sturdyRigid", () -> sturdy(state, SupportType.RIGID));
            this.attr(blocks, "fluid", () -> fluidName(state.getFluidState()));
            this.attr(blocks, "collision", () -> this.shape(state.getCollisionShape(EMPTY, ZERO)));
            this.attr(blocks, "outline", () -> this.shape(state.getShape(EMPTY, ZERO)));
            this.attr(blocks, "supportShape", () -> this.shape(state.getBlockSupportShape(EMPTY, ZERO)));
            blocks.append("}}");
         }
         blocks.append("]}");
      }

      StringBuilder sb = new StringBuilder();
      sb.append("{\"version\":").append(Json.str(SharedConstants.getCurrentVersion().name()));
      sb.append(",\n\"shapes\":[");
      for (int i = 0; i < this.shapes.size(); i++) {
         sb.append(i > 0 ? ",\n" : "\n").append(this.shapes.get(i));
      }
      sb.append("],\n\"blocks\":[").append(blocks).append("],\n\"blockEntityTypes\":[");
      boolean first = true;
      for (BlockEntityType<?> type : BuiltInRegistries.BLOCK_ENTITY_TYPE) {
         sb.append(first ? "\n" : ",\n");
         first = false;
         sb.append("{\"id\":").append(Json.str(BuiltInRegistries.BLOCK_ENTITY_TYPE.getKey(type).toString())).append(",\"class\":");
         String className = null;
         for (Block block : BuiltInRegistries.BLOCK) {
            if (type.isValid(block.defaultBlockState())) {
               try {
                  var blockEntity = type.create(ZERO, block.defaultBlockState());
                  if (blockEntity != null) {
                     className = blockEntity.getClass().getSimpleName();
                     break;
                  }
               } catch (Throwable t) {
                  // try the next block
               }
            }
         }
         if (className == null) {
            this.failures.merge("blockEntityTypes.class", 1, Integer::sum);
         }
         sb.append(className == null ? "null" : Json.str(className)).append('}');
      }
      sb.append("],\n\"entityTypes\":[");
      first = true;
      for (EntityType<?> type : BuiltInRegistries.ENTITY_TYPE) {
         sb.append(first ? "\n" : ",\n");
         first = false;
         String className = null;
         try {
            Entity entity = type.create(level, EntitySpawnReason.LOAD);
            if (entity != null) {
               className = entity.getClass().getSimpleName();
               entity.discard();
            }
         } catch (Throwable t) {
            // left null
         }
         if (className == null) {
            this.failures.merge("entityTypes.class(" + BuiltInRegistries.ENTITY_TYPE.getKey(type) + ")", 1, Integer::sum);
         }
         sb.append("{\"id\":").append(Json.str(BuiltInRegistries.ENTITY_TYPE.getKey(type).toString()));
         sb.append(",\"class\":").append(className == null ? "null" : Json.str(className));
         sb.append(",\"width\":\"").append(Json.hex(type.getWidth())).append("\",\"height\":\"").append(Json.hex(type.getHeight())).append("\"}");
      }
      sb.append("],\n\"items\":[");
      first = true;
      for (Item item : BuiltInRegistries.ITEM) {
         sb.append(first ? "\n" : ",\n");
         first = false;
         sb.append("{\"id\":").append(Json.str(BuiltInRegistries.ITEM.getKey(item).toString()));
         sb.append(",\"maxStackSize\":").append(item.getDefaultMaxStackSize()).append('}');
      }
      sb.append("]}\n");
      if (this.failures.isEmpty()) {
         Main.ERR.println("harness: dump: every attribute could be computed");
      } else {
         Main.ERR.println("harness: dump: attributes that could not be computed (name=count): " + this.failures);
      }
      return sb.toString();
   }
}
