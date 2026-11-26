package rsharness;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import net.minecraft.nbt.ByteArrayTag;
import net.minecraft.nbt.ByteTag;
import net.minecraft.nbt.CompoundTag;
import net.minecraft.nbt.DoubleTag;
import net.minecraft.nbt.FloatTag;
import net.minecraft.nbt.IntArrayTag;
import net.minecraft.nbt.IntTag;
import net.minecraft.nbt.ListTag;
import net.minecraft.nbt.LongArrayTag;
import net.minecraft.nbt.LongTag;
import net.minecraft.nbt.ShortTag;
import net.minecraft.nbt.StringTag;
import net.minecraft.nbt.Tag;

/**
 * NBT as typed JSON (tests/FORMAT.md): int -> number, string -> string, list -> array, and every other
 * tag an object with one key: b, s, l (decimal string), f (8 hex digits), d (16 hex digits), B, I,
 * L (decimal strings), c (compound, keys sorted).
 */
final class NbtJson {
   private NbtJson() {
   }

   static String of(final Tag tag) {
      StringBuilder sb = new StringBuilder();
      write(sb, tag);
      return sb.toString();
   }

   static void write(final StringBuilder sb, final Tag tag) {
      switch (tag) {
         case IntTag t -> sb.append(t.value());
         case StringTag t -> Json.str(sb, t.value());
         case ByteTag t -> sb.append("{\"b\":").append(t.value()).append('}');
         case ShortTag t -> sb.append("{\"s\":").append(t.value()).append('}');
         case LongTag t -> sb.append("{\"l\":\"").append(t.value()).append("\"}");
         case FloatTag t -> sb.append("{\"f\":\"").append(Json.hex(t.value())).append("\"}");
         case DoubleTag t -> sb.append("{\"d\":\"").append(Json.hex(t.value())).append("\"}");
         case ByteArrayTag t -> {
            sb.append("{\"B\":[");
            byte[] a = t.getAsByteArray();
            for (int i = 0; i < a.length; i++) {
               sb.append(i > 0 ? "," : "").append(a[i]);
            }
            sb.append("]}");
         }
         case IntArrayTag t -> {
            sb.append("{\"I\":[");
            int[] a = t.getAsIntArray();
            for (int i = 0; i < a.length; i++) {
               sb.append(i > 0 ? "," : "").append(a[i]);
            }
            sb.append("]}");
         }
         case LongArrayTag t -> {
            sb.append("{\"L\":[");
            long[] a = t.getAsLongArray();
            for (int i = 0; i < a.length; i++) {
               sb.append(i > 0 ? "," : "").append('"').append(a[i]).append('"');
            }
            sb.append("]}");
         }
         case ListTag t -> {
            sb.append('[');
            for (int i = 0; i < t.size(); i++) {
               if (i > 0) {
                  sb.append(',');
               }
               write(sb, t.get(i));
            }
            sb.append(']');
         }
         case CompoundTag t -> {
            sb.append("{\"c\":{");
            List<String> keys = new ArrayList<>(t.keySet());
            Collections.sort(keys);
            for (int i = 0; i < keys.size(); i++) {
               if (i > 0) {
                  sb.append(',');
               }
               Json.str(sb, keys.get(i));
               sb.append(':');
               write(sb, t.get(keys.get(i)));
            }
            sb.append("}}");
         }
         default -> throw new IllegalArgumentException("unexpected NBT tag " + tag.getClass());
      }
   }
}
