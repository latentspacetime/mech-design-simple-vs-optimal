#!/usr/bin/env python3
"""
Lean-kernel JSON-to-Lean exact equality checker for Mechanism Design certificates:
1. tree_cert_3m_2480_tight.json  <->  MathForgeMechDesign/CertTreeData248.lean
2. cert_lb_2195.json             <->  MathForgeMechDesign/LowerBoundPmf.lean

Generates bottom-up Lean 4 definitions directly from the JSON files (using parse_float=str
for exact decimal-to-Fraction parsing) and proves definitional equality (`:= rfl`) against
the compiled Lean declarations (`certTree248`, `certL1..certTarget`, `gridDen`,
`groupSizeNa`, `entryFeeTicks`, and `groupSpec 0..7`) inside Lean 4's kernel.
Exits 0 iff Lean 4's kernel accepts every equality proof.
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(f"JSON==LEAN CHECK FAILED: {msg}")


def parse_exact_frac(x) -> Fraction:
    require(not isinstance(x, bool), f"Boolean not allowed as rational: {x!r}")
    if isinstance(x, (int, str)):
        return Fraction(str(x))
    raise RuntimeError(f"JSON==LEAN CHECK FAILED: Non-exact numeric token {x!r} (expected int or str via parse_float=str)")


def parse_exact_int(x, label: str) -> int:
    require(type(x) is int, f"{label} must be exact JSON int, got {type(x).__name__}: {x!r}")
    return x


def fmt_q(fr: Fraction) -> str:
    require(fr.denominator > 0, f"Non-positive denominator in {fr}")
    return f"⟨({fr.numerator}), {fr.denominator}⟩"


def fmt_q_list(xs: list, expected_len: int | None, label: str) -> str:
    require(isinstance(xs, list), f"{label} must be a list")
    if expected_len is not None:
        require(len(xs) == expected_len, f"{label} length {len(xs)} != {expected_len}")
    else:
        require(len(xs) > 0, f"{label} must be non-empty")
    return "[" + ", ".join(fmt_q(parse_exact_frac(v)) for v in xs) + "]"


def fmt_box(box: list) -> str:
    require(isinstance(box, list) and len(box) == 6, f"Box must have 6 coordinates, got {len(box) if isinstance(box, list) else type(box)}")
    return "⟨" + ", ".join(fmt_q(parse_exact_frac(v)) for v in box) + "⟩"


def build_lean_check(tree_json: Path, lb_json: Path) -> tuple[str, int]:
    jtree = json.loads(tree_json.read_text(encoding="utf-8"), parse_float=str)
    jlb = json.loads(lb_json.read_text(encoding="utf-8"), parse_float=str)

    ls = jtree["ls"]
    require(isinstance(ls, list) and len(ls) == 3, f"Expected 3 ls entries, got {ls!r}")
    target = parse_exact_frac(jtree["target"])

    lines: list[str] = [
        "import MathForgeMechDesign.CertTreeData248",
        "import MathForgeMechDesign.LowerBoundPmf",
        "open MathForgeMechDesign.Cert248",
        "open MathForgeMechDesign.LowerBoundPmf",
        "namespace JsonLeanEqCheck",
        "set_option maxRecDepth 2000000",
        "set_option maxHeartbeats 0",
    ]

    counter = 0

    def emit_node(node: dict) -> str:
        nonlocal counter
        ntype = node.get("type")
        box_s = fmt_box(node["box"])
        if ntype == "split":
            axis = parse_exact_int(node["axis"], "split.axis")
            require(axis in (0, 1, 2), f"Invalid split axis {axis}")
            children = node["children"]
            require(isinstance(children, list) and len(children) == 2, "split must have 2 children")
            left_name = emit_node(children[0])
            right_name = emit_node(children[1])
            counter += 1
            name = f"node{counter}"
            lines.append(f"private def {name} : CertTree := CertTree.split {box_s} {axis} {left_name} {right_name}")
            return name
        if ntype == "leaf":
            a_s = fmt_q_list(node["a"], None, "leaf.a")
            lam_s = fmt_q_list(node["lam"], len(node["a"]), "leaf.lam")
            eta0_s = fmt_q(parse_exact_frac(node["eta0"]))
            y_s = fmt_q_list(node["y"], 14, "leaf.y")
            counter += 1
            name = f"node{counter}"
            lines.append(f"private def {name} : CertTree := CertTree.leaf {box_s} {a_s} {lam_s} {eta0_s} {y_s}")
            return name
        if ntype == "disjoint":
            if "farkas_y" in node and node["farkas_y"] is not None:
                fy_s = f"(some {fmt_q_list(node['farkas_y'], 14, 'disjoint.farkas_y')})"
            else:
                fy_s = "none"
            counter += 1
            name = f"node{counter}"
            lines.append(f"private def {name} : CertTree := CertTree.disjoint {box_s} {fy_s}")
            return name
        raise RuntimeError(f"JSON==LEAN CHECK FAILED: Unknown tree node type {ntype!r}")

    root_name = emit_node(jtree["tree"])

    lines.extend([
        f"example : certTree248 = {root_name} := rfl",
        f"example : certL1 = {fmt_q(parse_exact_frac(ls[0]))} := rfl",
        f"example : certL2 = {fmt_q(parse_exact_frac(ls[1]))} := rfl",
        f"example : certL3 = {fmt_q(parse_exact_frac(ls[2]))} := rfl",
        f"example : certTarget = {fmt_q(target)} := rfl",
    ])

    grid_den = parse_exact_int(jlb["grid_den"], "grid_den")
    na = parse_exact_int(jlb["Na"], "Na")
    entry_fee_ticks = parse_exact_int(jlb["entry_fee_ticks"], "entry_fee_ticks")
    groups = jlb["groups"]
    require(isinstance(groups, list) and len(groups) == 8, f"Expected 8 groups, got {len(groups) if isinstance(groups, list) else type(groups)}")

    lines.extend([
        f"example : gridDen = {grid_den} := rfl",
        f"example : groupSizeNa = {na} := rfl",
        f"example : entryFeeTicks = {entry_fee_ticks} := rfl",
    ])

    for idx, g in enumerate(groups):
        gname = g["name"]
        require(isinstance(gname, str) and gname.isascii() and '"' not in gname and "\\" not in gname, f"Invalid group name {gname!r}")
        r_num = parse_exact_int(g["r_num"], f"groups[{idx}].r_num")
        r_den = parse_exact_int(g["r_den"], f"groups[{idx}].r_den")
        k_min = parse_exact_int(g["k_min"], f"groups[{idx}].k_min")
        k_max = parse_exact_int(g["k_max"], f"groups[{idx}].k_max")
        p_tick = parse_exact_int(g["p_tick"], f"groups[{idx}].p_tick")
        lines.append(
            f'example : groupSpec {idx} = ⟨"{gname}", {r_num}, {r_den}, {k_min}, {k_max}, {p_tick}⟩ := rfl'
        )

    lines.append("end JsonLeanEqCheck")
    return "\n".join(lines) + "\n", counter


def main() -> None:
    ap = argparse.ArgumentParser(description="Lean-kernel rfl JSON == Lean certificate equality checker.")
    ap.add_argument("--lean-dir", type=Path, default=REPO / "lean_mathlib")
    ap.add_argument("--tree-json", type=Path, default=REPO / "certificates" / "tree_cert_3m_2480_tight.json")
    ap.add_argument("--lb-json", type=Path, default=REPO / "certificates" / "cert_lb_2195.json")
    args = ap.parse_args()

    lean_dir = args.lean_dir.resolve()
    require(lean_dir.is_dir(), f"Missing lean_mathlib directory: {lean_dir}")
    lean_code, n_nodes = build_lean_check(args.tree_json.resolve(), args.lb_json.resolve())

    env = os.environ.copy()
    env["PATH"] = str(Path.home() / ".elan" / "bin") + ":" + env.get("PATH", "")

    # Ensure CertTreeData248 and LowerBoundPmf oleans are fresh before checking rfl (no-op if already built).
    bld = subprocess.run(
        ["lake", "build", "MathForgeMechDesign.CertTreeData248", "MathForgeMechDesign.LowerBoundPmf"],
        cwd=str(lean_dir),
        env=env,
        capture_output=True,
        text=True,
    )
    if bld.returncode != 0:
        sys.stderr.write(bld.stdout + "\n" + bld.stderr + "\n")
        raise RuntimeError(f"JSON==LEAN CHECK FAILED: lake build failed with exit code {bld.returncode}")

    chk = subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        cwd=str(lean_dir),
        input=lean_code,
        env=env,
        capture_output=True,
        text=True,
    )
    if chk.returncode != 0:
        sys.stderr.write(chk.stdout + "\n" + chk.stderr + "\n")
        raise RuntimeError(f"JSON==LEAN CHECK FAILED: Lean kernel rfl proof rejected (exit code {chk.returncode})")

    print(
        f"[PASS] Lean-kernel rfl: tree_cert_3m_2480_tight.json == CertTreeData248.lean "
        f"(all {n_nodes} nodes, certL1..certL3, certTarget)"
    )
    print(
        "[PASS] Lean-kernel rfl: cert_lb_2195.json == LowerBoundPmf.lean "
        "(gridDen, groupSizeNa, entryFeeTicks, groupSpec 0..7)"
    )


if __name__ == "__main__":
    main()
