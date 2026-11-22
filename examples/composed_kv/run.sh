#!/usr/bin/env bash
set -euo pipefail

if (( $# > 1 )); then
    printf 'Usage: bash %s [recipe.json]\n' "$0" >&2
    exit 2
fi

example_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(cd -- "$example_dir/../.." && pwd)
recipe=${1:-"$example_dir/spec.json"}
output_dir="$repo_root/target/composed-kv"

# Cargo discovers examples by directory name. Stage the user's module beside
# the checked-in example so it can use the same manifest and lockfile.
target_name="composed_kv_check_$$"
stage="$repo_root/examples/$target_name"
mkdir -- "$stage"
trap 'rm -rf -- "$stage"' EXIT
python3 "$repo_root/tools/compose.py" "$recipe" --output "$stage/api.rs"
# Any recipe can be checked without looking for the default demo's methods.
printf 'pub mod api;\n\nfn main() {}\n' > "$stage/main.rs"

(
    cd -- "$repo_root"
    cargo verus verify --locked --check-toolchain --example "$target_name" -- --no-verify
)
mkdir -p -- "$output_dir"
mv -- "$stage/api.rs" "$output_dir/api.rs"
printf 'Type-checked API: %s\n' "$output_dir/api.rs"
