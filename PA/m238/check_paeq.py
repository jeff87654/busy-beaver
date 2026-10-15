#!/usr/bin/env python3
"""Static source checks for the pinned PAeq endpoint.

python3 check_paeq.py --source-only   # static checks, explicitly no kernel check

Native compilation must use the common PA/m238/check.py after integration.
This helper cannot launch a compiler, acquire a native lock, or fall back to
another build mechanism.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys


HERE = Path(__file__).resolve().parent
VENDOR = HERE / "vendor" / "undecidability"
PIN = "70dfc56f33a6e4835281044e68aa68279989047e"
OWN = [HERE / "coq/arith/PAeq238.v", HERE / "coq/arith/CheckPAeq238.v"]
EXPECTED_CLOSED = 11
REQ = re.compile(
    r"(?:From\s+([\w.]+)\s+)?Require\s+(?:Import\s+|Export\s+)?(.*?)\.(?:\s|$)",
    re.S,
)


def strip_comments(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1
            i += 2
        elif text.startswith("*)", i) and depth:
            depth -= 1
            i += 2
        else:
            if not depth:
                out.append(text[i])
            i += 1
    if depth:
        raise ValueError("unclosed Coq comment")
    return "".join(out)


def dependency_order(top, roots):
    seen, active, order = set(), set(), []

    def resolve(prefix, name):
        full = f"{prefix}.{name}" if prefix else name
        parts = full.split(".")
        if parts[0] not in roots:
            return None  # standard library
        candidate = roots[parts[0]].joinpath(*parts[1:]).with_suffix(".v")
        if not candidate.exists():
            # Upstream also uses imports such as `...PSL Require Import
            # Tactics`, whose source is PSL/Tactics/Tactics.v.
            tail = "/" + "/".join(name.split("."))
            base = roots[parts[0]].joinpath(*prefix.split(".")[1:]) if prefix else roots[parts[0]]
            candidates = sorted(
                file for file in base.rglob(name.split(".")[-1] + ".v")
                if file.with_suffix("").as_posix().endswith(tail)
            )
            if len(candidates) != 1:
                raise ValueError(f"unresolved or ambiguous dependency {full}")
            candidate = candidates[0]
        return candidate

    def visit(file):
        if file in seen:
            return
        if file in active:
            raise ValueError(f"dependency cycle at {file}")
        active.add(file)
        for prefix, names in REQ.findall(strip_comments(file.read_text())):
            for name in names.split():
                dependency = resolve(prefix, name)
                if dependency is not None:
                    visit(dependency)
        active.remove(file)
        seen.add(file)
        order.append(file)

    visit(top)
    return order


def source_checks():
    manifest = json.loads((VENDOR / "MANIFEST.json").read_text())
    if manifest["commit"] != PIN or manifest["license"] != "MPL-2.0":
        raise ValueError("wrong vendor pin or license")
    paths = set()
    for entry in manifest["files"]:
        relative = Path(entry["path"])
        if relative.is_absolute() or ".." in relative.parts or relative in paths:
            raise ValueError("unsafe or duplicate manifest path")
        paths.add(relative)
        data = (VENDOR / relative).read_bytes()
        blob = b"blob " + str(len(data)).encode() + b"\0" + data
        if hashlib.sha256(data).hexdigest() != entry["sha256"]:
            raise ValueError(f"SHA256 mismatch: {relative}")
        if hashlib.sha1(blob).hexdigest() != entry["git_blob_sha1"]:
            raise ValueError(f"Git blob mismatch: {relative}")
    actual = {file.relative_to(VENDOR) for file in VENDOR.rglob("*.v")} | {Path("LICENSE")}
    if paths != actual:
        raise ValueError("vendor files differ from manifest")
    for file in OWN:
        text = strip_comments(file.read_text())
        if re.search(r"\b(?:Admitted|admit|Axiom|Parameter)\b", text):
            raise ValueError(f"unfinished proof or assumption: {file.relative_to(HERE)}")
    roots = {"Undecidability": VENDOR / "theories", "P238": HERE / "coq"}
    order = dependency_order(OWN[1], roots)
    closure = {file.relative_to(VENDOR) for file in order if VENDOR in file.parents}
    # The integrated manifest also covers signature extensions used by the
    # compact calculus. Hash all manifest files, then require coverage of the
    # arithmetic endpoint's dependency closure without forbidding that union.
    inventory = paths - {Path("LICENSE")}
    if not closure <= inventory:
        raise ValueError("vendor manifest omits endpoint dependencies")
    reports = re.findall(r"\bPrint\s+Assumptions\b", strip_comments(OWN[1].read_text()))
    if len(reports) != EXPECTED_CLOSED:
        raise ValueError("unexpected number of assumption reports")
    print(
        f"SOURCE CHECK PASS: {len(closure)} endpoint library sources; "
        f"{len(inventory)} pinned vendor sources verified; original proof scan clean"
    )
    return order


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-only", action="store_true")
    args = parser.parse_args()
    try:
        source_checks()
        if args.source_only:
            print("KERNEL CHECK NOT RUN (--source-only)")
            return 0
        print(
            "KERNEL CHECK NOT RUN: use the common PA/m238/check.py after integration",
            file=sys.stderr,
        )
        return 2
    except (OSError, ValueError, KeyError) as error:
        print(f"CHECK FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
