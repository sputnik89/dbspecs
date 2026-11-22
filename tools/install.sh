#!/usr/bin/env bash
set -euo pipefail

die() {
    printf 'error: %s\n' "$*" >&2
    exit 1
}

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
verus_version=0.2026.09.06.8dea4a2

# Asset names and checksums from the pinned Verus release.
host="$(uname -s)/$(uname -m)"
case "$host" in
    Darwin/arm64|Darwin/aarch64)
        platform=arm64-macos
        sha256=23be2e8113b50bc91729377d8ac032f658cc5187e389a319d8458f9c37b07b4a
        ;;
    Darwin/x86_64)
        platform=x86-macos
        sha256=1befa1704a412fe3cfc7af8c90d2f75dd2c4963c9737d256d970ea93aeea3b69
        ;;
    Linux/x86_64)
        platform=x86-linux
        sha256=13d01e134c0620c3b29770874707d16c33b3d227c843a489c8ceb744d43c0a16
        ;;
    *) die "no Bash-compatible binary for Verus $verus_version on $host" ;;
esac

for command in curl unzip; do
    command -v "$command" >/dev/null || die "install $command and run this script again"
done
if command -v sha256sum >/dev/null; then
    checksum=(sha256sum)
elif command -v shasum >/dev/null; then
    checksum=(shasum -a 256)
else
    die "install sha256sum or shasum and run this script again"
fi

toolchain="$repo_root/rust-toolchain.toml"
rust_channel=$(awk -F '"' '/^[[:space:]]*channel[[:space:]]*=/ { print $2; exit }' "$toolchain")
rust_profile=$(awk -F '"' '/^[[:space:]]*profile[[:space:]]*=/ { print $2; exit }' "$toolchain")
rust_components=$(awk -F '"' '/^[[:space:]]*components[[:space:]]*=/ {
    for (i = 2; i < NF; i += 2) printf "%s%s", (i == 2 ? "" : ","), $i
    exit
}' "$toolchain")
[[ -n "$rust_channel" && -n "$rust_profile" && -n "$rust_components" ]] ||
    die "could not read the Rust pins in $toolchain"

install_root="$repo_root/.tools"
verus_dir="$install_root/verus-$verus_version-$platform"
mkdir -p -- "$install_root"
scratch=$(mktemp -d "$install_root/.install.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT

download() {
    curl --proto '=https' --proto-redir '=https' --tlsv1.2 \
        --fail --location --silent --show-error --retry 3 --output "$2" "$1"
}

cargo_bin="${CARGO_HOME:-$HOME/.cargo}/bin"
cargo_path_added=false
if ! command -v rustup >/dev/null; then
    if [[ ! -x "$cargo_bin/rustup" ]]; then
        printf 'Installing Rustup\n'
        download https://sh.rustup.rs "$scratch/rustup-init.sh"
        sh "$scratch/rustup-init.sh" -y --default-toolchain none --no-modify-path
    fi
    export PATH="$cargo_bin:$PATH"
    cargo_path_added=true
fi

printf 'Installing Rust %s and its configured components\n' "$rust_channel"
rustup toolchain install "$rust_channel" --profile "$rust_profile" \
    --component "$rust_components" --no-self-update

check_bundle() {
    [[ -x "$1/verus" && -x "$1/cargo-verus" && -x "$1/z3" ]]
}

if [[ -e "$verus_dir" || -L "$verus_dir" ]]; then
    check_bundle "$verus_dir" || die "incomplete Verus bundle at $verus_dir"
else
    printf 'Downloading Verus %s for %s\n' "$verus_version" "$platform"
    archive="$scratch/verus.zip"
    release_url="https://github.com/verus-lang/verus/releases/download/release%2F$verus_version"
    download "$release_url/verus-$verus_version-$platform.zip" "$archive"
    sum=$("${checksum[@]}" "$archive")
    [[ "${sum%% *}" == "$sha256" ]] || die "checksum mismatch for the Verus archive"
    unzip -q "$archive" -d "$scratch"
    bundle="$scratch/verus-$platform"
    check_bundle "$bundle" || die "the Verus archive is missing verus, cargo-verus, or z3"
    if [[ "$platform" == *-macos ]]; then
        xattr -dr com.apple.quarantine "$bundle" 2>/dev/null || true
    fi
    mv -- "$bundle" "$verus_dir"
fi

printf 'Fetching the locked Cargo dependencies\n'
rustup run "$rust_channel" cargo fetch --locked --manifest-path "$repo_root/Cargo.toml"

version_output=$("$verus_dir/verus" --version)
[[ "$version_output" == *"Version: $verus_version"* ]] ||
    die "expected Verus $verus_version at $verus_dir"

printf '\nTo use these tools in your current shell, run:\n'
if "$cargo_path_added"; then
    printf '  export PATH=%q:%q:$PATH\n' "$verus_dir" "$cargo_bin"
else
    printf '  export PATH=%q:$PATH\n' "$verus_dir"
fi
printf '  export VERUS_Z3_PATH=%q\n' "$verus_dir/z3"
