#!/usr/bin/env bash
# Runs the harness on a real Minecraft server (see README.md in this directory).
#
#   run.sh dump                                      writes $MC_REPORTS/blockdump.json
#   run.sh record <scenario.json | dir>... [-o dir]  writes one <name>.trace.json per scenario
#
# Without -o, the trace of .../scenarios/<unit>/x.json goes to .../traces/<unit>/x.trace.json
# (next to the scenario if its path has no "scenarios" directory).
#
# This starts a JVM that uses two cores and up to about 3 GiB: run it through Slurm
# (tools/record.sh does). Set HARNESS_KEEP=1 to keep the run directory, HARNESS_VERBOSE=1 to see
# the server log.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$here/../env.sh"

mode="${1:-}"
[ $# -gt 0 ] && shift
case "$mode" in
  dump|record) ;;
  *) sed -n '2,12p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//' >&2; exit 2 ;;
esac

"$here/build.sh"
classpath="$(cat "$MC_HOME/harness-build/classpath")"

mkdir -p "$MC_HOME/run"
run="$(mktemp -d "$MC_HOME/run/$mode.XXXXXXXX")"
cleanup() {
  if [ -z "${HARNESS_KEEP:-}" ]; then rm -rf "$run"; else echo "harness: kept $run" >&2; fi
}
trap cleanup EXIT

if [ "$mode" = dump ]; then
  mkdir -p "$MC_REPORTS"
  args=(dump "$MC_REPORTS/blockdump.json")
else
  outdir=""
  inputs=()
  while [ $# -gt 0 ]; do
    case "$1" in
      -o) outdir="$(realpath -m "$2")"; shift 2 ;;
      *) inputs+=("$1"); shift ;;
    esac
  done
  [ ${#inputs[@]} -gt 0 ] || { echo "run.sh record: no scenarios given" >&2; exit 2; }
  : > "$run/jobs.tsv"
  for input in "${inputs[@]}"; do
    if [ -d "$input" ]; then
      mapfile -t files < <(find "$input" -type f -name '*.json' ! -name '*.trace.json' | LC_ALL=C sort)
    elif [ -f "$input" ]; then
      files=("$input")
    else
      echo "run.sh record: no such file or directory: $input" >&2; exit 2
    fi
    for file in "${files[@]}"; do
      abs="$(realpath "$file")"
      base="$(basename "$abs" .json)"
      if [ -n "$outdir" ]; then
        trace="$outdir/$base.trace.json"
      elif [[ "$abs" == */scenarios/* ]]; then
        dir="$(dirname "$abs")"
        trace="${dir%/scenarios/*}/traces/${dir##*/scenarios/}/$base.trace.json"
        [[ "$dir" == */scenarios ]] && trace="${dir%/scenarios}/traces/$base.trace.json"
      else
        trace="$(dirname "$abs")/$base.trace.json"
      fi
      printf '%s\t%s\n' "$abs" "$trace" >> "$run/jobs.tsv"
    done
  done
  [ -s "$run/jobs.tsv" ] || { echo "run.sh record: no scenarios found" >&2; exit 2; }
  args=(record "$run/jobs.tsv")
fi

# The user has agreed to the Minecraft EULA (https://aka.ms/MinecraftEULA).
echo "eula=true" > "$run/eula.txt"
cat > "$run/server.properties" <<'PROPS'
level-name=world
level-seed=0
level-type=minecraft\:flat
generator-settings={"layers"\:[{"block"\:"minecraft\:air","height"\:1}],"biome"\:"minecraft\:the_void","features"\:false,"lakes"\:false,"structure_overrides"\:[]}
generate-structures=false
server-ip=127.0.0.1
server-port=0
online-mode=false
enable-status=false
enable-query=false
enable-rcon=false
pause-when-empty-seconds=-1
max-tick-time=-1
spawn-protection=0
sync-chunk-writes=false
view-distance=2
simulation-distance=2
PROPS

cd "$run"
status=0
if [ -n "${HARNESS_VERBOSE:-}" ]; then
  java -Xmx2500m -XX:ActiveProcessorCount=2 -Djava.awt.headless=true -javaagent:"$MC_HOME/harness-build/agent.jar" -cp "$classpath" rsharness.Main "${args[@]}" < /dev/null >&2 || status=$?
else
  java -Xmx2500m -XX:ActiveProcessorCount=2 -Djava.awt.headless=true -javaagent:"$MC_HOME/harness-build/agent.jar" -cp "$classpath" rsharness.Main "${args[@]}" < /dev/null > "$run/server.log" || status=$?
  if [ "$status" -ge 2 ]; then
    echo "harness: the server failed (exit $status); end of its log:" >&2
    tail -n 60 "$run/server.log" >&2
  fi
fi
exit "$status"
