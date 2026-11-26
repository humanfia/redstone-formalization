# Source this file: `source tools/env.sh`.
# Locations of the Minecraft reference environment. Nothing under MC_HOME is committed.

export MC_VERSION="26.3"
export MC_HOME="${MC_HOME:-/data/$USER/redstone-formalization/mc}"
export JAVA_HOME="$MC_HOME/jdk"
export MC_SERVER_JAR="$MC_HOME/server.jar"
# The unbundled game jar and its libraries, extracted from the server bundle.
export MC_GAME_JAR="$MC_HOME/bundle/META-INF/versions/$MC_VERSION/server-$MC_VERSION.jar"
export MC_LIBS="$MC_HOME/bundle/META-INF/libraries"
# Decompiled sources, for reading only. They are Mojang's and must never be committed.
export MC_SRC="$MC_HOME/src"
export MC_REPORTS="$MC_HOME/reports"
export PATH="$JAVA_HOME/bin:$HOME/.elan/bin:$PATH"
