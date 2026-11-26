#!/usr/bin/env bash
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
export PATH="$HOME/.elan/bin:$HOME/Library/TinyTeX/bin/universal-darwin:$HOME/.local/bin:$PATH"
export CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-4}"
export RAYON_NUM_THREADS="${RAYON_NUM_THREADS:-4}"
export OMP_NUM_THREADS="${OMP_NUM_THREADS:-4}"
if [ -z "${PY_BIN:-}" ]; then
  if [ -x "$REPO_ROOT/.venv/bin/python3" ]; then
    PY_BIN="$REPO_ROOT/.venv/bin/python3"
  else
    PY_BIN="$(command -v python3)"
  fi
fi

echo "=== [1/6] Offline Rust builds & runs (pinned rustc 1.96.0) ==="
TMP_CARGO="$(mktemp -d)"
trap 'rm -rf "$TMP_CARGO"' EXIT
(cd "$REPO_ROOT/verifiers/rust/ub_248" && CARGO_HOME="$TMP_CARGO" cargo build --release --locked --offline && ./target/release/verify_3m_rust "$REPO_ROOT/certificates/tree_cert_3m_2480_tight.json" 2.48)
(cd "$REPO_ROOT/verifiers/rust/lb_2195" && CARGO_HOME="$TMP_CARGO" cargo build --release --locked --offline && ./target/release/verify_lb_rust "$REPO_ROOT/certificates/cert_lb_2195.json")

echo "=== [2/6] Python verifiers (fast: 2.195 LB + GH26 reeval + -O refusal) ==="
"$PY_BIN" "$REPO_ROOT/verifiers/python/verify_lb_independent.py" "$REPO_ROOT/certificates/cert_lb_2195.json"
"$PY_BIN" "$REPO_ROOT/verifiers/python/gate_a0_lb.py"
if "$PY_BIN" -O "$REPO_ROOT/verifiers/python/verify_lb_independent.py" "$REPO_ROOT/certificates/cert_lb_2195.json" >/dev/null 2>&1; then
  echo "ERROR: verify_lb_independent.py failed to refuse -O!" && exit 1
fi
if "$PY_BIN" -O "$REPO_ROOT/verifiers/python/verify_3m_independent.py" "$REPO_ROOT/certificates/tree_cert_3m_2480_tight.json" >/dev/null 2>&1; then
  echo "ERROR: verify_3m_independent.py failed to refuse -O!" && exit 1
fi
echo "Confirmed -O refusal on both Mechanism Design Python verifiers."

echo "=== [3/6] Mechanical JSON == Lean exact equality check ==="
python3 -I -O "$REPO_ROOT/scripts/check_json_lean_eq_mech.py"

echo "=== [4/6] Lean 4 + Mathlib cold build (MathForgeMechDesign, Mathlib cache preserved) ==="
(cd "$REPO_ROOT/lean_mathlib" && lake clean MathForgeMechDesign && lake build)

echo "=== [5/6] Separated negative-trap & mutation suite ==="
PY_BIN="$PY_BIN" "$PY_BIN" "$REPO_ROOT/negative_traps/run_mech_negative_traps.py"

if [ "${RUN_FULL_PY_248:-0}" = "1" ]; then
  echo "=== [6/6] Serialized solo Python mpmath.iv 2.48 UB verifier (~57 min, 8 workers) ==="
  "$PY_BIN" "$REPO_ROOT/verifiers/python/verify_3m_independent.py" "$REPO_ROOT/certificates/tree_cert_3m_2480_tight.json" --workers "${PY_248_WORKERS:-8}"
else
  echo "=== [6/6] Skipping ~57 min Python 2.48 UB run (set RUN_FULL_PY_248=1 to execute solo) ==="
fi

echo "ALL MECHANISM DESIGN CHECKS PASSED!"
