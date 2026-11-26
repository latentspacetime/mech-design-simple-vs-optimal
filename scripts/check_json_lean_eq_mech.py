#!/usr/bin/env python3
"""
Standalone JSON-to-Lean exact rational equality checker for Mechanism Design certificates:
1. tree_cert_3m_2480_tight.json  <->  MathForgeMechDesign/CertTreeData248.lean
2. cert_lb_2195.json             <->  MathForgeMechDesign/LowerBoundPmf.lean
Exits 0 iff every single rational parameter, node, box, leaf vector, and group entry matches exactly.
"""
import json
import re
import sys
from fractions import Fraction
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
BASE = REPO / "lean_mathlib"
TREE_JSON = REPO / "certificates" / "tree_cert_3m_2480_tight.json"
TREE_LEAN = BASE / "MathForgeMechDesign" / "CertTreeData248.lean"
LB_JSON = REPO / "certificates" / "cert_lb_2195.json"
LB_LEAN = BASE / "MathForgeMechDesign" / "LowerBoundPmf.lean"


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(f"JSON==LEAN CHECK FAILED: {msg}")


class LeanTreeParser:
    def __init__(self, text: str, helpers: dict):
        self.tokens = re.findall(
            r"CertTree\.split|CertTree\.leaf|CertTree\.disjoint|subTree_\d+|some|none|⟨|⟩|\(|\)|\[|\]|,|-?\d+",
            text,
        )
        self.pos = 0
        self.helpers = helpers

    def peek(self):
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def pop(self, expected=None):
        tok = self.tokens[self.pos]
        if expected is not None and tok != expected:
            raise ValueError(f"Expected {expected!r}, got {tok!r} at pos {self.pos}")
        self.pos += 1
        return tok

    def parse_int(self) -> int:
        if self.peek() == "(":
            self.pop("(")
            v = int(self.pop())
            self.pop(")")
            return v
        return int(self.pop())

    def parse_q(self) -> Fraction:
        self.pop("⟨")
        n = self.parse_int()
        self.pop(",")
        d = int(self.pop())
        self.pop("⟩")
        require(d > 0, f"Non-positive denominator {d}")
        return Fraction(n, d)

    def parse_q_list(self) -> list[Fraction]:
        self.pop("[")
        out = []
        if self.peek() != "]":
            out.append(self.parse_q())
            while self.peek() == ",":
                self.pop(",")
                out.append(self.parse_q())
        self.pop("]")
        return out

    def parse_box(self) -> list[Fraction]:
        self.pop("⟨")
        out = [self.parse_q()]
        for _ in range(5):
            self.pop(",")
            out.append(self.parse_q())
        self.pop("⟩")
        return out

    def parse_tree(self):
        if self.peek() == "(":
            self.pop("(")
            t = self.parse_tree()
            self.pop(")")
            return t
        tok = self.pop()
        if tok.startswith("subTree_"):
            return self.helpers[tok]
        if tok == "CertTree.split":
            box = self.parse_box()
            ax = int(self.pop())
            left = self.parse_tree()
            right = self.parse_tree()
            return {"type": "split", "box": box, "axis": ax, "children": [left, right]}
        if tok == "CertTree.leaf":
            box = self.parse_box()
            a = self.parse_q_list()
            lam = self.parse_q_list()
            eta0 = self.parse_q()
            y = self.parse_q_list()
            return {"type": "leaf", "box": box, "a": a, "lam": lam, "eta0": eta0, "y": y}
        if tok == "CertTree.disjoint":
            box = self.parse_box()
            if self.peek() == "none":
                self.pop("none")
                return {"type": "disjoint", "box": box}
            self.pop("(")
            self.pop("some")
            fy = self.parse_q_list()
            self.pop(")")
            return {"type": "disjoint", "box": box, "farkas_y": fy}
        raise ValueError(f"Unexpected token {tok!r}")


def compare_trees(jnode, lnode, path="root"):
    require(jnode["type"] == lnode["type"], f"Type mismatch at {path}")
    jbox = [Fraction(str(x)) for x in jnode["box"]]
    require(jbox == lnode["box"], f"Box mismatch at {path}: {jbox} != {lnode['box']}")
    t = jnode["type"]
    if t == "split":
        require(int(jnode["axis"]) == lnode["axis"], f"Axis mismatch at {path}")
        return (
            1
            + compare_trees(jnode["children"][0], lnode["children"][0], path + ".L")
            + compare_trees(jnode["children"][1], lnode["children"][1], path + ".R")
        )
    if t == "leaf":
        for k in ["a", "lam", "y"]:
            jv = [Fraction(str(x)) for x in jnode[k]]
            require(jv == lnode[k], f"Leaf {k} mismatch at {path}")
        require(Fraction(str(jnode["eta0"])) == lnode["eta0"], f"Leaf eta0 mismatch at {path}")
        return 1
    if t == "disjoint":
        if "farkas_y" in jnode:
            require("farkas_y" in lnode, f"Missing farkas_y at {path}")
            jfy = [Fraction(str(x)) for x in jnode["farkas_y"]]
            require(jfy == lnode["farkas_y"], f"farkas_y mismatch at {path}")
        else:
            require("farkas_y" not in lnode, f"Unexpected farkas_y at {path}")
        return 1
    raise ValueError(t)


def check_tree():
    with open(TREE_JSON) as f:
        jdata = json.load(f)
    ltext = TREE_LEAN.read_text()

    # Check scalars
    for name, expected in [
        ("certL1", Fraction(str(jdata["ls"][0]))),
        ("certL2", Fraction(str(jdata["ls"][1]))),
        ("certL3", Fraction(str(jdata["ls"][2]))),
        ("certTarget", Fraction(str(jdata["target"]))),
    ]:
        m = re.search(rf"def {name} : Q := ⟨\(?(-?\d+)\)?,\s*(\d+)⟩", ltext)
        require(m is not None, f"Missing {name} in Lean file")
        got = Fraction(int(m.group(1)), int(m.group(2)))
        require(got == expected, f"{name} mismatch: {got} != {expected}")

    # Parse helper subtrees in order
    helpers = {}
    for m in re.finditer(r"def (subTree_\d+) : CertTree :=\s*(.+?)(?=\n(?:def |end ))", ltext, re.S):
        name, body = m.group(1), m.group(2)
        p = LeanTreeParser(body, helpers)
        helpers[name] = p.parse_tree()
        require(p.pos == len(p.tokens), f"Unparsed tokens in {name}")

    mroot = re.search(r"def certTree248 : CertTree :=\s*(.+?)(?=\nend )", ltext, re.S)
    require(mroot is not None, "Missing certTree248")
    proot = LeanTreeParser(mroot.group(1), helpers)
    ltree = proot.parse_tree()
    require(proot.pos == len(proot.tokens), "Unparsed tokens in certTree248")

    n_nodes = compare_trees(jdata["tree"], ltree)
    print(f"[PASS] tree_cert_3m_2480_tight.json == CertTreeData248.lean (exact rational match across all {n_nodes} nodes, ls, target)")


def check_lb():
    require(LB_LEAN.exists(), f"Missing {LB_LEAN}")
    with open(LB_JSON) as f:
        jdata = json.load(f)
    ltext = LB_LEAN.read_text()
    for name, val in [
        ("gridDen", jdata["grid_den"]),
        ("groupSizeNa", jdata["Na"]),
        ("entryFeeTicks", jdata["entry_fee_ticks"]),
    ]:
        m = re.search(rf"def {name} : ℕ := (\d+)", ltext)
        require(m is not None and int(m.group(1)) == val, f"{name} mismatch")

    rows = re.findall(r'⟨"(A\d+)",\s*(\d+),\s*(\d+),\s*(\d+),\s*(\d+),\s*(\d+)⟩', ltext)
    require(len(rows) == len(jdata["groups"]) == 8, f"Expected 8 groups, found {len(rows)}")
    for idx, (g, row) in enumerate(zip(jdata["groups"], rows)):
        exp = (g["name"], g["r_num"], g["r_den"], g["k_min"], g["k_max"], g["p_tick"])
        got = (row[0], int(row[1]), int(row[2]), int(row[3]), int(row[4]), int(row[5]))
        require(got == exp, f"Group {idx} mismatch: {got} != {exp}")
    print("[PASS] cert_lb_2195.json == LowerBoundPmf.lean (exact match on D, Na, F_ticks, and all 8 groups)")


if __name__ == "__main__":
    check_tree()
    check_lb()
