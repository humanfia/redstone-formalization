#!/usr/bin/env bash
# Records scenarios on the real server, through Slurm (site policy: anything that uses more than
# one core or 4 GiB must). Arguments are those of `harness/run.sh record`:
#
#   tools/record.sh <scenario.json | dir>... [-o <outdir>]
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
[ $# -gt 0 ] || { echo "usage: tools/record.sh <scenario.json | dir>... [-o <outdir>]" >&2; exit 2; }
exec srun --quiet -c 2 --mem 4G --job-name mc-record "$here/harness/run.sh" record "$@"
