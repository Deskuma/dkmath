#!/usr/bin/env bash
# Reproducible, standalone replacement for create-dkmath-all-lean.sh.
set -euo pipefail
root="$(pwd)"
output=""
while (($#)); do
  case "$1" in
    --root) root="$2"; shift 2;;
    --output) output="$2"; shift 2;;
    -h|--help)
      echo 'Usage: create-dkmath-all-lean.sh [--root /repo/dk_math] [--output /path/all.lean.txt.gz]'; exit 0;;
    *) echo "Unknown argument: $1" >&2; exit 2;;
  esac
done
root="$(cd "$root" && pwd)"
[[ -d "$root/DkMath" && -f "$root/lakefile.toml" ]] || {
  echo 'Error: --root must be a dk_math repository with DkMath/ and lakefile.toml' >&2; exit 1;
}
if [[ -z "$output" ]]; then
  output="$root/logs/__dkmath-all.lean.txt.gz"
fi
mkdir -p "$(dirname "$output")"
output="$(cd "$(dirname "$output")" && pwd)/$(basename "$output")"
[[ "$output" == *.gz ]] || { echo 'Error: output path must end in .gz' >&2; exit 2; }
# Restrict to the intended project sources; no .lake, tests, tmp, or generated logs.
# Input is streamed to avoid a giant intermediate .txt. gzip -n avoids a timestamp.
(
  cd "$root"
  {
    if [[ -f DkMath.lean ]]; then printf '%s\n' 'DkMath.lean'; fi
    find DkMath -type f -name '*.lean' -print | LC_ALL=C sort
  } | while IFS= read -r path; do
    printf '\n%s\n%s\n%s\n' \
      '============================================================' \
      "$path" \
      '------------------------------------------------------------'
    cat -- "$path"
    printf '\n'
  done
) | gzip -n -c > "$output"
sha256sum "$output" > "$output.sha256"
echo "Wrote: $output"
ls -lh -- "$output" "$output.sha256"
echo "Uncompressed line count: $(gzip -cd "$output" | wc -l)"
