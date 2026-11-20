#!/usr/bin/env bash
# Local workaround for machines where /home is a symlink (e.g. /home -> chome/): `lake comparator`
# runs `bwrap --tmpfs /home ...`, which fails with "Can't mount on symlink destination /home".
# Usage: mkdir -p /tmp/bwrapfix && cp this-file /tmp/bwrapfix/bwrap && chmod +x /tmp/bwrapfix/bwrap
#        PATH=/tmp/bwrapfix:$PATH lake comparator --config <config>
# It hides the real home tree (resolved from $HOME) instead of /home, and re-exposes read-only the
# local packages directory that .lake/packages points to. The sandbox is otherwise unchanged.
# lake may call bwrap with an empty HOME: fall back to the passwd entry of the current user.
home_dir=${HOME:-$(getent passwd "$(id -u)" | cut -d: -f6)}
real_home=$(readlink -f "$home_dir")
[ -n "$real_home" ] || { echo "bwrap wrapper: cannot resolve the home directory" >&2; exit 1; }
packages=$(readlink -f "$(dirname "$0")/../.lake/packages" 2>/dev/null || readlink -f .lake/packages)
args=(); done=
for a in "$@"; do
  if [ "$a" = "/home" ] && [ "${args[-1]}" = "--tmpfs" ]; then args+=("$real_home")
  elif [ "$a" = "--setenv" ] && [ -z "$done" ]; then args+=(--ro-bind "$packages" "$packages" --setenv); done=1
  else args+=("$a"); fi
done
exec /usr/bin/bwrap "${args[@]}"
