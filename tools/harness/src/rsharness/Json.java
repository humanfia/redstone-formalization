package rsharness;

/** Minimal JSON writing helpers (stable output, no dependencies). */
final class Json {
   private Json() {
   }

   static String str(final String s) {
      StringBuilder sb = new StringBuilder(s.length() + 2);
      str(sb, s);
      return sb.toString();
   }

   static void str(final StringBuilder sb, final String s) {
      sb.append('"');
      for (int i = 0; i < s.length(); i++) {
         char c = s.charAt(i);
         switch (c) {
            case '"' -> sb.append("\\\"");
            case '\\' -> sb.append("\\\\");
            case '\n' -> sb.append("\\n");
            case '\r' -> sb.append("\\r");
            case '\t' -> sb.append("\\t");
            default -> {
               if (c < 0x20 || c > 0x7e) {
                  sb.append(String.format("\\u%04x", (int)c));
               } else {
                  sb.append(c);
               }
            }
         }
      }
      sb.append('"');
   }

   /** 16 hex digits: the raw IEEE bits of a double. */
   static String hex(final double d) {
      return String.format("%016x", Double.doubleToRawLongBits(d));
   }

   /** 8 hex digits: the raw IEEE bits of a float. */
   static String hex(final float f) {
      return String.format("%08x", Float.floatToRawIntBits(f));
   }
}
