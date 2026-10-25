#!/usr/bin/env bash
# Local independent proof replay following the official Palomar template.
set -euo pipefail
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"
python3 scripts/check-palomar.py --ready
for required_command in bwrap lake lean python3; do
  command -v "$required_command" >/dev/null || {
    echo "error: missing $required_command" >&2
    exit 1
  }
done
prefix=$(lean --print-prefix)
for bundled_tool in lake leanexport leanchecker nanoda_bin con-ron; do
  if [ ! -x "$prefix/bin/$bundled_tool" ]; then
    echo "error: selected Lean toolchain does not bundle $bundled_tool" >&2
    exit 1
  fi
done
temporary_config=$(mktemp "${TMPDIR:-/tmp}/cutoff-comparator.XXXXXX")
trap 'rm -f "$temporary_config"' EXIT
python3 - comparator.json "$temporary_config" "$prefix" <<'PY'
import json
import pathlib
import sys

source, destination, prefix = sys.argv[1:]
config = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
if "external_kernels" in config:
    raise SystemExit("external_kernels is not a submitted configuration field")
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY
lake exe cache get
lake comparator --config "$temporary_config"
