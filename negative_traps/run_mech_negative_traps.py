#!/usr/bin/env python3
"""
negative_traps/run_mech_negative_traps.py —
Unified separated negative-trap and mutation matrix for the Mechanism Design [2.195, 2.48] bundle.

Explicitly separates Claim-Binding / Schema traps from Arithmetic-Soundness traps across:
  - 2.48 UB: Rust (verify_3m_rust), Python (verify_3m_independent.py), Lean 4 (MathForgeMechDesign)
  - 2.195 LB: Rust (verify_lb_rust), Python (verify_lb_independent.py), Lean 4 (MathForgeMechDesign)
Every trap asserts BOTH non-zero exit code AND a specific expected diagnostic regex.
"""
from __future__ import annotations

import copy
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
CERT_UB = REPO / "certificates" / "tree_cert_3m_2480_tight.json"
CERT_LB = REPO / "certificates" / "cert_lb_2195.json"
PY_UB = REPO / "verifiers" / "python" / "verify_3m_independent.py"
PY_LB = REPO / "verifiers" / "python" / "verify_lb_independent.py"
RS_UB = REPO / "verifiers" / "rust" / "ub_248" / "target" / "release" / "verify_3m_rust"
RS_LB = REPO / "verifiers" / "rust" / "lb_2195" / "target" / "release" / "verify_lb_rust"
LEAN_MD = REPO / "lean_mathlib"
PY_BIN = os.environ.get("PY_BIN", sys.executable)


def run_cmd(cmd: list[str], cwd: Path | None = None, stdin_text: str | None = None) -> tuple[int, str]:
    env = os.environ.copy()
    env["PATH"] = str(Path.home() / ".elan" / "bin") + ":" + env.get("PATH", "")
    env["RAYON_NUM_THREADS"] = "4"
    p = subprocess.run(cmd, cwd=str(cwd) if cwd else None, input=stdin_text, env=env, capture_output=True, text=True)
    return p.returncode, (p.stdout + "\n" + p.stderr).strip()


def find_node(node: dict, ntype: str) -> dict | None:
    if node.get("type") == ntype:
        return node
    if node.get("type") == "split":
        for ch in node["children"]:
            r = find_node(ch, ntype)
            if r is not None:
                return r
    return None


def main() -> None:
    if not RS_UB.is_file() or not RS_LB.is_file():
        raise SystemExit(f"Missing compiled Rust release binaries ({RS_UB}, {RS_LB}). Build them first.")

    orig_ub = json.loads(CERT_UB.read_text(encoding="utf-8"))
    orig_lb = json.loads(CERT_LB.read_text(encoding="utf-8"))
    rows: list[tuple[str, str, str, str, int, str, str]] = []
    all_ok = True

    def rec(tid: str, suite: str, cls: str, desc: str, rc: int, out: str, expect_zero: bool, rx: str) -> None:
        nonlocal all_ok
        if expect_zero:
            ok = (rc == 0 and bool(re.search(rx, out, re.I)))
        else:
            ok = (rc != 0 and bool(re.search(rx, out, re.I)))
        all_ok = all_ok and ok
        lines = [l.strip() for l in out.splitlines() if l.strip() and "RUST_BACKTRACE" not in l]
        match_line = next((l for l in reversed(lines) if re.search(rx, l, re.I)), lines[-1] if lines else "")
        verdict = ("PASS" if ok else "FAIL") if expect_zero else ("REJECTED (OK)" if ok else "UNEXPECTED!")
        rows.append((tid, suite, cls, desc, rc, match_line, verdict))

    with tempfile.TemporaryDirectory(prefix="mech_traps_") as td:
        tdir = Path(td)

        # Clean Controls (Rust UB + Rust LB; Python LB verified in Tier 1)
        rc, out = run_cmd([str(RS_UB), str(CERT_UB), "2.48"])
        rec("CTRL_UB_rust", "2.48 UB", "Clean Control", "Unmodified 2.48 certificate (Rust)", rc, out, True, r"PASS.*failed=0")
        rc, out = run_cmd([str(RS_LB), str(CERT_LB)])
        rec("CTRL_LB_rust", "2.195 LB", "Clean Control", "Unmodified 2.195 certificate (Rust)", rc, out, True, r"FINAL VERDICT: PASS")

        # === 2.48 UB CLAIM-BINDING / SCHEMA TRAPS ===
        c = copy.deepcopy(orig_ub); c["target"] = 2.49
        fp = tdir / "ub_t249.json"; fp.write_text(json.dumps(c), encoding="utf-8")
        rc, out = run_cmd([PY_BIN, str(PY_UB), str(fp)])
        rec("U_CB1_target249_py", "2.48 UB", "Claim-Binding/Schema", "JSON target=2.49 rejected vs pinned 62/25 (Python)", rc, out, False, r"exceeds theorem ceiling")
        rc, out = run_cmd([str(RS_UB), str(fp), "2.48"])
        rec("U_CB1_target249_rs", "2.48 UB", "Claim-Binding/Schema", "JSON target=2.49 rejected vs pinned 62/25 (Rust)", rc, out, False, r"Certificate target.*!= expected target")

        c = copy.deepcopy(orig_ub); c["target"] = 2.47
        fp = tdir / "ub_t247.json"; fp.write_text(json.dumps(c), encoding="utf-8")
        rc, out = run_cmd([PY_BIN, str(PY_UB), str(fp)])
        rec("U_CB2_target_below_py", "2.48 UB", "Claim-Binding/Schema", "JSON target=2.47 < --expected-target 62/25 raises mismatch without silent overwrite (Py)", rc, out, False, r"refusing silent target mismatch")
        rc, out = run_cmd([str(RS_UB), str(fp), "2.48"])
        rec("U_CB2_target_below_rs", "2.48 UB", "Claim-Binding/Schema", "JSON target=2.47 < expected 2.48 raises mismatch without silent overwrite (Rust)", rc, out, False, r"refusing silent target mismatch")

        c = copy.deepcopy(orig_ub); c["ls"][0] = 0.07
        fp = tdir / "ub_badls.json"; fp.write_text(json.dumps(c), encoding="utf-8")
        rc, out = run_cmd([PY_BIN, str(PY_UB), str(fp)])
        rec("U_CB3_shifted_ls_py", "2.48 UB", "Claim-Binding/Schema", "Shifted ls[0]=0.07 rejected against pinned (3/50,7/20,9/5) (Py)", rc, out, False, r"ls mismatch")
        rc, out = run_cmd([str(RS_UB), str(fp), "2.48"])
        rec("U_CB3_shifted_ls_rs", "2.48 UB", "Claim-Binding/Schema", "Shifted ls[0]=0.07 rejected against pinned (3/50,7/20,9/5) (Rust)", rc, out, False, r"ls must equal exact rationals")

        rc, out = run_cmd([PY_BIN, "-O", str(PY_UB), str(CERT_UB)])
        rec("U_CB4_python_dash_O", "2.48 UB", "Claim-Binding/Schema", "verify_3m_independent.py refuses Python -O", rc, out, False, r"refusing to run under Python -O")

        # === 2.48 UB ARITHMETIC-SOUNDNESS TRAPS ===
        c = copy.deepcopy(orig_ub); c["target"] = 2.47
        fp = tdir / "ub_t247.json"; fp.write_text(json.dumps(c), encoding="utf-8")
        rc, out = run_cmd([str(RS_UB), str(fp), "2.47"])
        rec("U_AS1_target247_rs", "2.48 UB", "Arithmetic-Soundness", "Drive target=2.47 through JSON+CLI -> leaf numerical failure (Rust)", rc, out, False, r"RUST FAIL.*leaf #|VERIFIER FAIL")

        c = copy.deepcopy(orig_ub)
        lf = find_node(c["tree"], "leaf"); assert lf is not None
        lf["eta0"] = 1.0
        fp = tdir / "ub_baddual.json"; fp.write_text(json.dumps(c), encoding="utf-8")
        rc, out = run_cmd([str(RS_UB), str(fp), "2.48"])
        rec("U_AS2_corrupt_dual_rs", "2.48 UB", "Arithmetic-Soundness", "Corrupt leaf #1 Farkas dual eta0=1.0 -> ub > 2.48 (Rust)", rc, out, False, r"RUST FAIL.*leaf #1|VERIFIER FAIL")

        c = copy.deepcopy(orig_ub)
        c["tree"]["children"][0]["box"][1] = c["tree"]["children"][0]["box"][1] - 0.5
        fp = tdir / "ub_gap.json"; fp.write_text(json.dumps(c), encoding="utf-8")
        rc, out = run_cmd([PY_BIN, str(PY_UB), str(fp)])
        rec("U_AS3_drop_coverage_py", "2.48 UB", "Arithmetic-Soundness", "Shrink child box -> tree split coverage gap (Py)", rc, out, False, r"Split gap")
        rc, out = run_cmd([str(RS_UB), str(fp), "2.48"])
        rec("U_AS3_drop_coverage_rs", "2.48 UB", "Arithmetic-Soundness", "Shrink child box -> tree split coverage gap (Rust)", rc, out, False, r"c1\[2 \* j\] == bk\[2 \* j\]|Split gap")

        c = copy.deepcopy(orig_ub)
        dj = find_node(c["tree"], "disjoint"); assert dj is not None
        # Replace disjoint node's box & parent split? Simpler: mutate a leaf whose box intersects int(cl(L)) into type="disjoint"!
        # Specifically box [0,1]x[0,3]x[0,5/8] contains interior point (c=2 -> (1/2.06, 1/2.35, 1/3.8)).
        lf2 = find_node(c["tree"], "leaf"); assert lf2 is not None
        lf2["type"] = "disjoint"
        lf2.pop("a", None); lf2.pop("lam", None); lf2.pop("eta0", None); lf2.pop("y", None)
        fp = tdir / "ub_bad_disjoint.json"; fp.write_text(json.dumps(c), encoding="utf-8")
        rc, out = run_cmd([PY_BIN, str(PY_UB), str(fp)])
        rec("U_AS4_disjoint_interior_py", "2.48 UB", "Arithmetic-Soundness", "Mark feasible-interior box [0,1]x[0,3]x[0,5/8] as disjoint (Py)", rc, out, False, r"Invalid disjoint box")
        rc, out = run_cmd([str(RS_UB), str(fp), "2.48"])
        rec("U_AS4_disjoint_interior_rs", "2.48 UB", "Arithmetic-Soundness", "Mark feasible-interior box [0,1]x[0,3]x[0,5/8] as disjoint (Rust)", rc, out, False, r"Disjoint check failed on box")

        rc, out = run_cmd([PY_BIN, "-c",
            f"import importlib.util; from fractions import Fraction\n"
            f"spec = importlib.util.spec_from_file_location('m', {str(PY_UB)!r}); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)\n"
            f"for fr in [Fraction(1,3), Fraction(1,7), Fraction(1,10**20)]:\n"
            f"  ivv = m.f2iv(fr); assert m.mpf_tup_to_frac(ivv._mpi_[0]) <= fr <= m.mpf_tup_to_frac(ivv._mpi_[1])\n"
            f"try:\n"
            f"  m.mpf_tup_to_frac((0, 0, -456, -1)); raise RuntimeError('FAIL_NO_TRAP')\n"
            f"except SystemExit as e:\n"
            f"  assert 'Non-finite' in str(e)\n"
            f"print('ORACLE_UB_OK')\n"])
        rec("U_AS5_oracle_rounding", "2.48 UB", "Arithmetic-Soundness", "Boundary oracle: outward f2iv enclosure & non-finite trap", rc, out, True, r"ORACLE_UB_OK")

        rc, out = run_cmd(["lake", "env", "lean", "--stdin"], cwd=LEAN_MD, stdin_text=
            "import MathForgeMechDesign.UpperBoundRecipAndTree\n"
            "open MathForgeMechDesign.Cert248 MathForgeMechDesign.UpperBoundRecipAndTree\n"
            "theorem trap_247 : qToReal certTarget ≤ 247 / 100 := by unfold qToReal certTarget; norm_num\n")
        rec("U_AS6_lean_tighten_247", "2.48 UB", "Arithmetic-Soundness", "Lean Mathlib rejects tightened UB certTarget (62/25) -> 247/100", rc, out, False, r"unsolved goals|norm_num")

        rc, out = run_cmd(["lake", "env", "lean", "--stdin"], cwd=LEAN_MD, stdin_text=
            "import MathForgeMechDesign.UpperBoundRecipAndTree\n"
            "open MathForgeMechDesign.Cert248 MathForgeMechDesign.UpperBoundRecipAndTree\n"
            "theorem trap_disjoint : treeValid (CertTree.disjoint ⟨⟨0,1⟩,⟨1,1⟩,⟨0,1⟩,⟨3,1⟩,⟨0,1⟩,⟨5,8⟩⟩ none) = true := by decide\n")
        rec("U_AS7_lean_disjoint_trap", "2.48 UB", "Arithmetic-Soundness", "Lean kernel `by decide` rejects feasible-interior box marked disjoint", rc, out, False, r"tactic 'decide' proved that the proposition")

        # === 2.195 LB CLAIM-BINDING / SCHEMA TRAPS ===
        c = copy.deepcopy(orig_lb); c["groups"][0]["r_num"] = 228
        fp = tdir / "lb_badrg.json"; fp.write_text(json.dumps(c), encoding="utf-8")
        rc, out = run_cmd([PY_BIN, str(PY_LB), str(fp)])
        rec("L_CB1_perturb_rg_py", "2.195 LB", "Claim-Binding/Schema", "Perturb A1 r_num 227->228 rejected (Py)", rc, out, False, r"Raw r_g mismatch in A1")
        rc, out = run_cmd([str(RS_LB), str(fp)])
        rec("L_CB1_perturb_rg_rs", "2.195 LB", "Claim-Binding/Schema", "Perturb A1 r_num 227->228 rejected (Rust)", rc, out, False, r"Raw r_g mismatch in A1")

        rc, out = run_cmd([PY_BIN, "-O", str(PY_LB), str(CERT_LB)])
        rec("L_CB2_python_dash_O", "2.195 LB", "Claim-Binding/Schema", "verify_lb_independent.py refuses Python -O", rc, out, False, r"Refusing to run under Python -O")

        rc, out = run_cmd([PY_BIN, "-c",
            f"import sys\np = {str(PY_LB)!r}\nsrc = open(p).read()\n"
            f"src_mut = src.replace('PINNED_DEG_Z = 5013', 'PINNED_DEG_Z = 5000')\n"
            f"assert src_mut != src\nsys.argv = [p, {str(CERT_LB)!r}]\n"
            f"ns = {{'__name__': '__main__', '__file__': p}}\nexec(src_mut, ns)\n"])
        rec("L_CB3_mutate_degZ_src", "2.195 LB", "Claim-Binding/Schema", "Source-mutate PINNED_DEG_Z 5013->5000 fails K_cut check (Py)", rc, out, False, r"Pinned deg_Z mismatch")

        c = copy.deepcopy(orig_lb); c["target_num"] = 2196; c["target_den"] = 1000
        fp_t = tdir / "lb_t2196.json"; fp_t.write_text(json.dumps(c), encoding="utf-8")
        rc, out = run_cmd([PY_BIN, str(PY_LB), str(fp_t)])
        rec("L_CB4_target2196_pin_py", "2.195 LB", "Claim-Binding/Schema", "JSON target=2196/1000 rejected by raw pin guard (Py)", rc, out, False, r"Raw target mismatch")

        c = copy.deepcopy(orig_lb); c["chernoff_t_num"] = 1; c["chernoff_t_den"] = 100
        fp_c1 = tdir / "lb_badt_100.json"; fp_c1.write_text(json.dumps(c), encoding="utf-8")
        rc, out = run_cmd([PY_BIN, str(PY_LB), str(fp_c1)])
        rec("L_CB5_bad_chernoff_pin_py", "2.195 LB", "Claim-Binding/Schema", "JSON chernoff_t=1/100 rejected by raw pin guard (Py)", rc, out, False, r"Raw Chernoff t mismatch")
        rc, out = run_cmd([str(RS_LB), str(fp_c1)])
        rec("L_CB5_bad_chernoff_pin_rs", "2.195 LB", "Claim-Binding/Schema", "JSON chernoff_t=1/100 rejected by raw pin guard (Rust)", rc, out, False, r"Raw Chernoff t mismatch")

        # === 2.195 LB ARITHMETIC-SOUNDNESS TRAPS ===
        rc, out = run_cmd([PY_BIN, "-c",
            f"import sys\np = {str(PY_LB)!r}\nsrc = open(p).read()\n"
            f"src_mut = src.replace('PINNED_TARGET = Fraction(439, 200)', 'PINNED_TARGET = Fraction(2196, 1000)')\n"
            f"src_mut = src_mut.replace('target_num == 439 and target_den == 200', 'target_num == 2196 and target_den == 1000')\n"
            f"assert src_mut != src\nsys.argv = [p, {str(fp_t)!r}]\n"
            f"ns = {{'__name__': '__main__', '__file__': p}}\nexec(src_mut, ns)\n"])
        rec("L_AS1_target2196_arith_py", "2.195 LB", "Arithmetic-Soundness", "Bypass pins & drive target=2.196 (> 2.195136...) -> ratio failure (Py)", rc, out, False, r"Ratio lower bound <= target")

        rc, out = run_cmd([PY_BIN, "-c",
            f"import sys\np = {str(PY_LB)!r}\nsrc = open(p).read()\n"
            f"src_mut = src.replace('PINNED_CHERNOFF_T = Fraction(1, 10)', 'PINNED_CHERNOFF_T = Fraction(1, 100)')\n"
            f"src_mut = src_mut.replace('t_num == 1 and t_den == 10', 't_num == 1 and t_den == 100')\n"
            f"assert src_mut != src\nsys.argv = [p, {str(fp_c1)!r}]\n"
            f"ns = {{'__name__': '__main__', '__file__': p}}\nexec(src_mut, ns)\n"])
        rec("L_AS2a_chernoff_mono_py", "2.195 LB", "Arithmetic-Soundness", "Bypass pins & set t=1/100 -> fails monotonicity P0 >= 1/t (Py)", rc, out, False, r"Chernoff monotonicity requires P0 >= 1/t")

        c = copy.deepcopy(orig_lb); c["chernoff_t_num"] = 1; c["chernoff_t_den"] = 2
        fp_c2 = tdir / "lb_badt_half.json"; fp_c2.write_text(json.dumps(c), encoding="utf-8")
        rc, out = run_cmd([PY_BIN, "-c",
            f"import sys\np = {str(PY_LB)!r}\nsrc = open(p).read()\n"
            f"src_mut = src.replace('PINNED_CHERNOFF_T = Fraction(1, 10)', 'PINNED_CHERNOFF_T = Fraction(1, 2)')\n"
            f"src_mut = src_mut.replace('t_num == 1 and t_den == 10', 't_num == 1 and t_den == 2')\n"
            f"assert src_mut != src\nsys.argv = [p, {str(fp_c2)!r}]\n"
            f"ns = {{'__name__': '__main__', '__file__': p}}\nexec(src_mut, ns)\n"])
        rec("L_AS2b_chernoff_tail_py", "2.195 LB", "Arithmetic-Soundness", "Bypass pins & set t=1/2 -> fails mpmath.iv MGF tail bound (Py)", rc, out, False, r"Chernoff tail bound failed")

        rc, out = run_cmd([PY_BIN, "-c",
            f"import importlib.util; from fractions import Fraction\n"
            f"spec = importlib.util.spec_from_file_location('m', {str(PY_LB)!r}); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)\n"
            f"for fr in [Fraction(1,3), Fraction(1,7), Fraction(1, 1<<150)]:\n"
            f"  lo, hi = m.frac_to_fx(fr); assert Fraction(lo, m.SCALE_ONE) <= fr <= Fraction(hi, m.SCALE_ONE)\n"
            f"try:\n"
            f"  m.dyadic_tuple_to_frac((0, 0, -456, -1)); raise RuntimeError('FAIL_NO_TRAP')\n"
            f"except RuntimeError as e:\n"
            f"  assert 'Non-finite' in str(e)\n"
            f"print('ORACLE_LB_OK')\n"])
        rec("L_AS3_oracle_rounding", "2.195 LB", "Arithmetic-Soundness", "Boundary oracle: 140-bit frac_to_fx & inf/nan trap", rc, out, True, r"ORACLE_LB_OK")

        rc, out = run_cmd(["lake", "env", "lean", "--stdin"], cwd=LEAN_MD, stdin_text=
            "import MathForgeMechDesign.LowerBoundChebyshevAndWitness\nopen MathForgeMechDesign.LowerBoundChebyshev\n"
            "theorem trap_2196 : (2196 : ℝ) / 1000 < certRatioR := by unfold certRatioR; norm_num\n")
        rec("L_AS4_lean_tighten_2196", "2.195 LB", "Arithmetic-Soundness", "Lean Mathlib rejects tightened LB 439/200 -> 2196/1000", rc, out, False, r"unsolved goals|norm_num")

        rc, out = run_cmd(["lake", "env", "lean", "--stdin"], cwd=LEAN_MD, stdin_text=
            "import MathForgeMechDesign.LowerBoundPmf\nopen MathForgeMechDesign.LowerBoundPmf\n"
            "theorem trap_pmf_mut : (228/2000 + 207/2000 + 9/250 + 547/2000 + 179/1000 + 199/1000 + 817/2000 + 7119/2000 : ℝ) = S_A := by unfold S_A; norm_num\n")
        rec("L_AS5_lean_pmf_mut", "2.195 LB", "Arithmetic-Soundness", "Lean Mathlib rejects perturbed A1 r_num=228 vs S_A=1949/400", rc, out, False, r"unsolved goals|norm_num")

    lines = [
        "# Mechanism Design `[2.195, 2.48]` Negative Trap and Mutation Matrix",
        "",
        f"**Overall Result:** `{'ALL TRAPS REJECTED WITH EXPECTED DIAGNOSTICS + CLEAN CONTROLS & ORACLES PASSED' if all_ok else 'FAILURE DETECTED'}`",
        "",
        "| Case | Suite | Trap Class | Mutation / Check | rc | Diagnostic | Verdict |",
        "| --- | --- | --- | --- | ---: | --- | --- |",
    ]
    for tid, suite, cls, desc, rc, msg, verdict in rows:
        lines.append(f"| `{tid}` | {suite} | {cls} | {desc} | `{rc}` | `{msg.replace('|', '/')[:90]}` | **{verdict}** |")
    report = "\n".join(lines) + "\n"
    if "--write-report" in sys.argv:
        out_md = REPO / "negative_traps" / "MECH_NEGATIVE_TRAP_REPORT.md"
        out_md.write_text(report, encoding="utf-8")
    print(report)
    if not all_ok:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
