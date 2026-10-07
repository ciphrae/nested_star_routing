#!/usr/bin/env bash
# Check pair_bound with leanprover/comparator against the Mathlib-only statement in
# Comparator/Challenge.lean. Needs comparator, lean4export and landrun built for v4.33.1;
# set COMPARATOR_DIR (checkout of comparator) and COMPARATOR_LANDRUN (landrun binary).
set -euo pipefail
cd "$(dirname "$0")/.."
T=${COMPARATOR_DIR:?set COMPARATOR_DIR to a comparator checkout built for Lean v4.33.1}/.lake
export COMPARATOR_LANDRUN=${COMPARATOR_LANDRUN:?set COMPARATOR_LANDRUN to the landrun binary}
export COMPARATOR_LEAN4EXPORT=${COMPARATOR_LEAN4EXPORT:-$T/packages/lean4export/.lake/build/bin/lean4export}
exec lake env "$T/build/bin/comparator" comparator.json
