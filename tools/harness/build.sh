#!/usr/bin/env bash
# Compiles the harness against the game jar and its libraries. Output goes to $MC_HOME/harness-build
# (never into the repository). Rebuilds only when a source file is newer than the last build.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$here/../env.sh"

out="$MC_HOME/harness-build"
stamp="$out/.stamp"
cp_file="$out/classpath"

if [ -f "$stamp" ] && [ -f "$cp_file" ] && [ -z "$(find "$here/src" "$here/build.sh" -newer "$stamp" -print -quit)" ]; then
  exit 0
fi

mkdir -p "$out"
# One build at a time; many agents may start at once.
exec 9>"$out/.lock"
flock 9
if [ -f "$stamp" ] && [ -f "$cp_file" ] && [ -z "$(find "$here/src" "$here/build.sh" -newer "$stamp" -print -quit)" ]; then
  exit 0
fi

libs="$(find "$MC_LIBS" -name '*.jar' | sort | tr '\n' ':')"
tmp="$(mktemp -d "$out/build.XXXXXX")"
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/classes"
javac -nowarn -Xlint:none -proc:none -d "$tmp/classes" -cp "$MC_GAME_JAR:$libs" $(find "$here/src" -name '*.java' | sort)
printf 'Premain-Class: rsharness.PatchRandomSupport\n' > "$tmp/manifest"
jar --create --file "$tmp/agent.jar" --manifest "$tmp/manifest" -C "$tmp/classes" rsharness/PatchRandomSupport.class

rm -rf "$out/classes" "$out/patched"
mv "$tmp/classes" "$out/classes"
mv "$tmp/agent.jar" "$out/agent.jar"
printf '%s' "$out/classes:$MC_GAME_JAR:${libs%:}" > "$cp_file"
touch "$stamp"
