#!/usr/bin/env bash
# Sets up the Minecraft 26.3 reference environment under $MC_HOME:
#   jdk/        a Java 25 runtime (the version 26.3 asks for)
#   server.jar  the official 26.3 server, checked against the sha1 Mojang publishes
#   bundle/     the server bundle unpacked (game jar and libraries)
#   reports/    the data generator's reports, including every block state
#   src/        decompiled sources, for reading only
#
# Running the server later requires accepting the Minecraft EULA
# (https://aka.ms/MinecraftEULA); the recording scripts write `eula=true`.
#
# The script is idempotent: steps whose output exists are skipped.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$here/../env.sh"

SERVER_URL="https://piston-data.mojang.com/v1/objects/33680f5f2ac32864d6d7cf5e56a705fdb3e05f4c/server.jar"
SERVER_SHA1="33680f5f2ac32864d6d7cf5e56a705fdb3e05f4c"
JDK_URL="https://api.adoptium.net/v3/binary/latest/25/ga/linux/x64/jdk/hotspot/normal/eclipse"
VINEFLOWER_URL="https://repo1.maven.org/maven2/org/vineflower/vineflower/1.11.1/vineflower-1.11.1.jar"

mkdir -p "$MC_HOME"
cd "$MC_HOME"

if [ ! -x "$JAVA_HOME/bin/java" ]; then
  echo "== JDK 25"
  curl -fL --retry 3 -o jdk.tar.gz "$JDK_URL"
  mkdir -p jdk
  tar -xzf jdk.tar.gz -C jdk --strip-components=1
  rm jdk.tar.gz
fi
java -version

if [ ! -f server.jar ]; then
  echo "== server.jar"
  curl -fL --retry 3 -o server.jar.part "$SERVER_URL"
  echo "$SERVER_SHA1  server.jar.part" | sha1sum -c -
  mv server.jar.part server.jar
fi

if [ ! -f "$MC_GAME_JAR" ]; then
  echo "== unpack bundle"
  mkdir -p bundle
  (cd bundle && jar -xf ../server.jar)
fi

if [ ! -f reports/blocks.json ]; then
  echo "== data reports"
  mkdir -p datagen
  (cd datagen && java -DbundlerMainClass=net.minecraft.data.Main -jar ../server.jar --reports --output "$MC_HOME/datagen/out")
  mkdir -p reports
  cp -r datagen/out/reports/. reports/
fi

if [ ! -d src/net/minecraft ]; then
  echo "== decompile"
  [ -f vineflower.jar ] || curl -fL --retry 3 -o vineflower.jar "$VINEFLOWER_URL"
  mkdir -p src
  java -Xmx3g -jar vineflower.jar --threads=1 --only=net/minecraft "$MC_GAME_JAR" src
fi

echo "ok: $MC_HOME"
