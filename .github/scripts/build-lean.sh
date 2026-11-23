#!/usr/bin/env bash
set -euo pipefail

prune_finished_module_setups() {
  local build_dir setup_file relative trace_file
  for build_dir in .lake/build .lake/vendor/class-field-theory/build .lake/packages/dedekind_zeta/.lake/build; do
    [[ -d "$build_dir/ir" ]] || continue
    while IFS= read -r -d '' setup_file; do
      relative=${setup_file#"$build_dir/ir/"}
      trace_file="$build_dir/lib/lean/${relative%.setup.json}.trace"
      # Lake writes the trace after lean and any leanir process have finished.
      if [[ -f "$trace_file" && "$trace_file" -nt "$setup_file" ]]; then
        rm -f -- "$setup_file"
      fi
    done < <(find "$build_dir/ir" -type f -name '*.setup.json' -print0)
  done
}

lake --no-cache --fail-fast build "$@" &
build_pid=$!
while kill -0 "$build_pid" 2>/dev/null; do
  sleep 45
  prune_finished_module_setups
done
wait "$build_pid"
prune_finished_module_setups
