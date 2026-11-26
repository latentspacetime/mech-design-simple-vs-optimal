# Simple versus Optimal Mechanisms (`[2.195, 2.48]`) Verification and Formalization Bundle

Machine-checked certificates, offline-reproducible Rust and Python verifiers, Lean 4 + Mathlib formalization (`lean_mathlib/`, 55 exported theorems), and unified arXiv manuscript source for:

- **Upper Bound:** `REV(X) <= (62/25) * max(SREV(X), BREV(X)) = 2.48 * max(SREV(X), BREV(X))` for all `m >= 1` and independent nonnegative distributions (vs. GH26 stated `5/2 = 2.50` in `arXiv:2609.35711v3` Prop. 4.6 and derived commentary `1499/600 = 2.498333...`).
- **Deterministic Lower Bound:** `REV(X) >= DREV(X) > (439/200) * max(SREV(X), BREV(X)) = 2.195 * max(SREV(X), BREV(X))` witnessed by a finite DSIC/IR mechanism (`N_b = 2^46800`, `delta = S_A / 10^8`) under every buyer tie-breaking rule, with limiting ratio `>= 2.195136628895` (vs. GH26 stated `2026/925 = 2.190270...` and certified reevaluation `[2.190949496843, 2.190949496844]`).

## Offline Python Setup

Install pinned `mpmath==1.3.0` offline from the bundled wheelhouse:
```bash
python3 -m venv .venv
.venv/bin/pip install --no-index --find-links wheels -r requirements.lock
```

## Quick Verification

```bash
chmod +x verify_all.sh
PY_BIN=.venv/bin/python3 ./verify_all.sh
# To also execute the ~57-minute solo Python mpmath.iv 2.48 UB verifier:
RUN_FULL_PY_248=1 PY_BIN=.venv/bin/python3 ./verify_all.sh
```

## Per-Artifact Commands, Backends, and Measured Timings

| Artifact | Exact Command | Arithmetic Backend | `-O` Policy | Measured Wall Time |
| --- | --- | --- | --- | --- |
| `2.48` UB (Rust) | `cd verifiers/rust/ub_248 && cargo build --release --locked --offline && ./target/release/verify_3m_rust ../../../certificates/tree_cert_3m_2480_tight.json 2.48` | IEEE-754 outward-rounded interval, custom Taylor `exp`/`atanh` `ln`, `overflow-checks = true`, `rustc 1.96.0` | N/A | Build `~10 s`; Run `~25 s` |
| `2.48` UB (Python) | `.venv/bin/python3 verifiers/python/verify_3m_independent.py certificates/tree_cert_3m_2480_tight.json --workers 8` | Python `mpmath.iv` (`dps=35`) + exact `Fraction` | **Refuses `-O`** | `~3,410 s` (serialized solo) |
| `2.195` LB (Rust) | `cd verifiers/rust/lb_2195 && cargo build --release --locked --offline && ./target/release/verify_lb_rust ../../../certificates/cert_lb_2195.json` | Checked `i128` rationals + IEEE-754 outward-rounded interval, custom Taylor `exp`, `rustc 1.96.0` | N/A | Build `~8 s`; Run `~10.4 s` |
| `2.195` LB (Python) | `.venv/bin/python3 verifiers/python/verify_lb_independent.py certificates/cert_lb_2195.json` | Exact `Fraction` + 140-bit Kronecker integer interval + `mpmath.iv` (`dps=50`) | **Refuses `-O`** | `~70.1 s` |
| GH26 App. D baseline eval | `.venv/bin/python3 verifiers/python/gate_a0_lb.py` | `mpmath.iv` (`dps=60`) with dyadic `_mpi_` self-checks | **Refuses `-O`** | `~3 s` |
| JSON == Lean equality check | `python3 -I -O scripts/check_json_lean_eq_mech.py` | Exact `Fraction` check (`1,507` tree nodes + 8 groups) | Supported (`-I -O`) | `< 1 s` |
| Lean 4 + Mathlib (`55` thms) | `cd lean_mathlib && lake clean MathForgeMechDesign && lake build` | Lean `v4.14.0` + Mathlib `v4.14.0` (standard axioms only) | N/A | `~68 s` |
| Negative trap suite | `.venv/bin/python3 negative_traps/run_mech_negative_traps.py` | Separated Claim-Binding vs. Arithmetic traps across Rust + Python + Lean 4 | **Default (no `-O`)** | `~60 s` |
| Metadata delta verifier | `python3 scripts/verify_release_delta.py` | `render_metadata.py` + TeX Live `pdflatex` 3-pass compile | Supported | `~3 s` |

## Formalization Scope

See `FORMALIZATION_COVERAGE_LEDGER.md` and `STATEMENT_FIDELITY_LEDGER.md` for the exact theorem-by-theorem mapping between `paper/proof_body.tex` and `lean_mathlib/`.

## Updating Author Metadata Before arXiv Upload

Edit only the four literal string fields (`author`, `affiliation`, `ai_disclosure`, `repo_url`) in `paper/metadata.json` and run:
```bash
python3 scripts/verify_release_delta.py
```
