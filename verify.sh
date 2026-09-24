#!/usr/bin/env bash
set -euo pipefail
repository_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$repository_dir/lean"
exec bash ./build.sh
