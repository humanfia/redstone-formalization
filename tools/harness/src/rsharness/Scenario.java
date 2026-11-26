package rsharness;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

/** A parsed scenario file (see tests/FORMAT.md). Parsing is strict: unknown keys are errors. */
final class Scenario {
   record Fill(int[] min, int[] max, String state) {
   }

   record BlockSpec(int[] pos, String state, String nbt) {
   }

   record EntitySpec(String type, double[] pos, String nbt) {
   }

   record Action(int tick, String type, int[] pos, String face, String item, String state, int flags, boolean drop, EntitySpec entity, int entityIndex) {
   }

   String name;
   int ticks;
   int[] boxMin;
   int[] boxMax;
   long dayTime = 6000L;
   boolean advanceTime = false;
   String weather = "clear";
   int randomTickSpeed = 0;
   boolean blockDrops = false;
   final List<Fill> fills = new ArrayList<>();
   final List<BlockSpec> blocks = new ArrayList<>();
   final List<EntitySpec> entities = new ArrayList<>();
   final List<Action> actions = new ArrayList<>();

   static Scenario load(final Path path) throws Exception {
      JsonObject root = JsonParser.parseString(Files.readString(path)).getAsJsonObject();
      checkKeys(root, "scenario", Set.of("name", "ticks", "box", "settings", "fill", "blocks", "entities", "actions"));
      Scenario s = new Scenario();
      s.name = root.get("name").getAsString();
      s.ticks = root.get("ticks").getAsInt();
      if (s.ticks < 0) {
         throw new IllegalArgumentException("ticks must be >= 0");
      }

      JsonObject box = root.getAsJsonObject("box");
      checkKeys(box, "box", Set.of("min", "max"));
      s.boxMin = ints3(box.get("min"));
      s.boxMax = ints3(box.get("max"));
      for (int i = 0; i < 3; i++) {
         if (s.boxMin[i] > s.boxMax[i]) {
            throw new IllegalArgumentException("box.min must be <= box.max");
         }
      }

      if (root.has("settings")) {
         JsonObject settings = root.getAsJsonObject("settings");
         checkKeys(settings, "settings", Set.of("dayTime", "advanceTime", "weather", "randomTickSpeed", "blockDrops"));
         if (settings.has("dayTime")) {
            s.dayTime = settings.get("dayTime").getAsLong();
         }
         if (settings.has("advanceTime")) {
            s.advanceTime = settings.get("advanceTime").getAsBoolean();
         }
         if (settings.has("weather")) {
            s.weather = settings.get("weather").getAsString();
            if (!Set.of("clear", "rain", "thunder").contains(s.weather)) {
               throw new IllegalArgumentException("settings.weather must be clear, rain or thunder");
            }
         }
         if (settings.has("blockDrops")) {
            s.blockDrops = settings.get("blockDrops").getAsBoolean();
         }
         if (settings.has("randomTickSpeed")) {
            s.randomTickSpeed = settings.get("randomTickSpeed").getAsInt();
         }
      }

      for (JsonElement e : array(root, "fill")) {
         JsonObject o = e.getAsJsonObject();
         checkKeys(o, "fill entry", Set.of("min", "max", "state"));
         int[] min = ints3(o.get("min"));
         int[] max = ints3(o.get("max"));
         s.requireInBox(min, "fill.min");
         s.requireInBox(max, "fill.max");
         for (int i = 0; i < 3; i++) {
            if (min[i] > max[i]) {
               throw new IllegalArgumentException("fill.min must be <= fill.max");
            }
         }
         s.fills.add(new Fill(min, max, o.get("state").getAsString()));
      }

      for (JsonElement e : array(root, "blocks")) {
         JsonObject o = e.getAsJsonObject();
         checkKeys(o, "blocks entry", Set.of("pos", "state", "nbt"));
         int[] pos = ints3(o.get("pos"));
         s.requireInBox(pos, "blocks.pos");
         s.blocks.add(new BlockSpec(pos, o.get("state").getAsString(), o.has("nbt") ? o.get("nbt").getAsString() : null));
      }

      for (JsonElement e : array(root, "entities")) {
         s.entities.add(s.entity(e.getAsJsonObject()));
      }

      int lastTick = 1;
      for (JsonElement e : array(root, "actions")) {
         JsonObject o = e.getAsJsonObject();
         int tick = o.get("tick").getAsInt();
         String type = o.get("type").getAsString();
         if (tick < 1 || tick > s.ticks) {
            throw new IllegalArgumentException("action tick " + tick + " is outside 1.." + s.ticks);
         }
         if (tick < lastTick) {
            throw new IllegalArgumentException("actions must be listed in non-decreasing tick order");
         }
         lastTick = tick;
         int[] pos = null;
         String face = null;
         String item = null;
         String state = null;
         int flags = 3;
         boolean drop = false;
         EntitySpec entity = null;
         int entityIndex = -1;
         switch (type) {
            case "use" -> {
               checkKeys(o, "use action", Set.of("tick", "type", "pos", "face"));
               pos = ints3(o.get("pos"));
               face = o.get("face").getAsString();
            }
            case "use_item" -> {
               checkKeys(o, "use_item action", Set.of("tick", "type", "pos", "face", "item"));
               pos = ints3(o.get("pos"));
               face = o.get("face").getAsString();
               item = o.get("item").getAsString();
            }
            case "set" -> {
               checkKeys(o, "set action", Set.of("tick", "type", "pos", "state", "flags"));
               pos = ints3(o.get("pos"));
               state = o.get("state").getAsString();
               if (o.has("flags")) {
                  flags = o.get("flags").getAsInt();
               }
            }
            case "destroy" -> {
               checkKeys(o, "destroy action", Set.of("tick", "type", "pos", "drop"));
               pos = ints3(o.get("pos"));
               drop = o.has("drop") && o.get("drop").getAsBoolean();
            }
            case "summon" -> {
               checkKeys(o, "summon action", Set.of("tick", "type", "entity"));
               entity = s.entity(o.getAsJsonObject("entity"));
            }
            case "kill" -> {
               checkKeys(o, "kill action", Set.of("tick", "type", "entity"));
               entityIndex = o.get("entity").getAsInt();
            }
            default -> throw new IllegalArgumentException("unknown action type " + type);
         }
         if (pos != null) {
            s.requireInBox(pos, type + ".pos");
         }
         s.actions.add(new Action(tick, type, pos, face, item, state, flags, drop, entity, entityIndex));
      }

      return s;
   }

   private EntitySpec entity(final JsonObject o) {
      checkKeys(o, "entity", Set.of("type", "pos", "nbt"));
      JsonArray p = o.getAsJsonArray("pos");
      if (p.size() != 3) {
         throw new IllegalArgumentException("entity pos must have 3 numbers");
      }
      double[] pos = new double[]{number(p.get(0)), number(p.get(1)), number(p.get(2))};
      return new EntitySpec(o.get("type").getAsString(), pos, o.has("nbt") ? o.get("nbt").getAsString() : null);
   }

   private void requireInBox(final int[] pos, final String what) {
      for (int i = 0; i < 3; i++) {
         if (pos[i] < this.boxMin[i] || pos[i] > this.boxMax[i]) {
            throw new IllegalArgumentException(what + " " + pos[0] + "," + pos[1] + "," + pos[2] + " is outside the box");
         }
      }
   }

   private static void checkKeys(final JsonObject o, final String what, final Set<String> allowed) {
      for (String key : o.keySet()) {
         if (!allowed.contains(key)) {
            throw new IllegalArgumentException("unknown key \"" + key + "\" in " + what);
         }
      }
   }

   private static JsonArray array(final JsonObject o, final String key) {
      return o.has(key) ? o.getAsJsonArray(key) : new JsonArray();
   }

   private static int[] ints3(final JsonElement e) {
      JsonArray a = e.getAsJsonArray();
      if (a.size() != 3) {
         throw new IllegalArgumentException("expected [x, y, z]");
      }
      return new int[]{a.get(0).getAsInt(), a.get(1).getAsInt(), a.get(2).getAsInt()};
   }

   /** A JSON number, or a string of 16 hex digits giving the raw bits of a double. */
   private static double number(final JsonElement e) {
      if (e.getAsJsonPrimitive().isString()) {
         String s = e.getAsString();
         if (s.length() != 16) {
            throw new IllegalArgumentException("a hex double must have 16 hex digits: " + s);
         }
         return Double.longBitsToDouble(Long.parseUnsignedLong(s, 16));
      }
      return e.getAsDouble();
   }
}
