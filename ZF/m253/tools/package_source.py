#!/usr/bin/env python3
"""Package committed ZF253 sources after the canonical kernel check succeeds.

--plan only selects and hashes sources. Creating a ZIP additionally requires
--verified-commit to equal the selected repository's complete HEAD hash. This
records the caller's completed verification; this tool never invokes Coq and
cannot establish that verification itself. No archive is made implicitly.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tempfile
import zipfile

sys.dont_write_bytecode = True
if sys.flags.optimize:
    raise RuntimeError("Run with assertions enabled, not python -O")

HERE = Path(__file__).resolve().parents[1]
PREFIX = "ZF/m253/"
EXTRA = (
    "ZF/m254/check.py", "ZF/m254/machine/zfc_254.tm", "ZF/m254/README.md",
    "ZF/generator/LICENSE.wade",
    "ZF/stdzf/README.md", "ZF/stdzf_r3/README.md",
    "ZF/stdzf_r3/vendor/undecidability/README.md",
    "ZF/stdzf_r3/vendor/undecidability/LICENSE",
    "ZF/stdzf_r3/vendor/busycoq/README.md",
    "ZF/stdzf_r3/vendor/busycoq/LICENSE",
    "ZF/stdzf_r3/vendor/busycoq/LICENSE-LibTactics",
)
DEPENDENCY_PREFIXES = (
    "ZF/m254/coq/tm/", "ZF/m254/coq/prog/", "ZF/m254/coq/logic/",
    "ZF/m254/coq/settheory/", "ZF/m254/coq/e2e/", "ZF/stdzf/coq/",
    "ZF/stdzf_r3/regcon/", "ZF/stdzf_r3/zfc/",
    "ZF/stdzf_r3/vendor/undecidability/theories/",
    "ZF/stdzf_r3/vendor/busycoq/",
)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def git(repository, *arguments, input=None):
    result = subprocess.run(["git", "--no-optional-locks", "-C", str(repository),
                             *arguments], input=input, capture_output=True, timeout=45)
    if result.returncode:
        raise RuntimeError(result.stderr.decode("utf-8", errors="replace").strip())
    return result.stdout


def canonical_source(path):
    if not path.startswith(PREFIX):
        return False
    part = path[len(PREFIX):]
    return (part in ("README.md", "check.py", ".gitignore", "LICENSE", "NOTICE")
            or part == "machine/zfc_253.tm"
            or (part.startswith("coq/") and part.endswith(".v"))
            or (part.startswith("tools/") and part.endswith(".py")))


def tree(repository, revision):
    entries = {}
    for item in git(repository, "ls-tree", "-r", "-z", revision).split(b"\0"):
        if not item:
            continue
        description, raw_path = item.split(b"\t", 1)
        mode, kind, object_id = description.decode("ascii").split()
        path = raw_path.decode("utf-8")
        if str(PurePosixPath(path)) != path or ".." in PurePosixPath(path).parts:
            raise RuntimeError(f"unsafe repository path: {path!r}")
        entries[path] = (mode, kind, object_id)
    return entries


def blobs(repository, entries, selected):
    """Read only the explicit selected Git blobs, in one bounded subprocess."""
    request = "".join(entries[path][2] + "\n" for path in selected).encode("ascii")
    stream = io.BytesIO(git(repository, "cat-file", "--batch", input=request))
    result = {}
    for path in selected:
        mode, kind, expected_id = entries[path]
        if mode not in ("100644", "100755") or kind != "blob":
            raise RuntimeError(f"source must be a regular tracked file: {path} ({mode}/{kind})")
        object_id, actual_kind, raw_size = stream.readline().decode("ascii").split()
        if (object_id, actual_kind) != (expected_id, "blob"):
            raise RuntimeError(f"Git blob identity mismatch: {path}")
        data = stream.read(int(raw_size))
        if len(data) != int(raw_size) or stream.read(1) != b"\n":
            raise RuntimeError(f"truncated Git blob: {path}")
        source = repository / path
        if source.is_symlink() or not source.is_file() or source.read_bytes() != data:
            raise RuntimeError(f"working source differs from committed bytes: {path}")
        result[path] = data
    if stream.read(1):
        raise RuntimeError("unexpected trailing Git blob data")
    return result


def select(repository):
    head = git(repository, "rev-parse", "--verify", "HEAD^{commit}").decode("ascii").strip()
    entries = tree(repository, head)
    checker_path = repository / PREFIX / "check.py"
    if checker_path.read_bytes() != git(repository, "show", f"{head}:{PREFIX}check.py"):
        raise RuntimeError("canonical checker must match committed HEAD before packaging")
    spec = importlib.util.spec_from_file_location("m253_package_check", checker_path)
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    if not hasattr(checker, "AUDIT"):
        raise RuntimeError("canonical checker must require Audit253.v")
    # Includes the exact literal/generator checks and forbidden-escape scan;
    # this invokes Python only and makes no claim of kernel acceptance.
    closure = checker.source_checks()
    modules = []
    dependency_files = set()
    for source in closure:
        path = source.relative_to(repository).as_posix()
        if not canonical_source(path) and not (
                path.endswith(".v") and path.startswith(DEPENDENCY_PREFIXES)):
            raise RuntimeError(f"dependency outside the explicit package roots: {path}")
        dependency_files.add(path)
        modules.append({"module": checker.logical_name(source), "path": path})
    canonical = {path for path in entries if canonical_source(path)}
    # Refuse to silently omit an uncommitted canonical source, even if it is
    # not currently imported by the final audit.
    for source in (repository / PREFIX).rglob("*"):
        path = source.relative_to(repository).as_posix()
        if canonical_source(path) and source.is_file() and path not in canonical:
            raise RuntimeError(f"uncommitted canonical source: {path}")
    selected = sorted(canonical | dependency_files | set(EXTRA))
    missing = set(selected) - entries.keys()
    if missing:
        raise RuntimeError("required sources/notices are uncommitted or absent: " + ", ".join(sorted(missing)))
    data = blobs(repository, entries, selected)
    manifest = {
        "format": "zf253-source-package-v1",
        "source_commit": head,
        "target": "M253E.Audit253",
        "coq_version": "8.20.1",
        "verification": "Caller must complete ZF/m253/check.py at source_commit before ZIP creation; packaging does not invoke Coq.",
        "machine_sha256": checker.GEN.CANDIDATE_SHA256,
        "baseline_sha256": checker.GEN.BASE_SHA256,
        "dependency_order": modules,
        "load_path_directories": sorted({directory.relative_to(repository).as_posix()
                                         for directories in checker.ROOTS.values()
                                         for directory in directories}),
        "required_notices_and_support": list(EXTRA),
        "files": [{"path": path, "bytes": len(data[path]), "sha256": sha256(data[path]),
                   "mode": entries[path][0]} for path in selected],
        "reproduce": "python3 -I -B ZF/m253/check.py --coqc coqc",
        "excluded": ["Coq build products", "optimization reports", "PA", "Git metadata", "installed compiler"],
    }
    return head, entries, data, manifest


def manifest_bytes(manifest):
    return (json.dumps(manifest, ensure_ascii=False, sort_keys=True, indent=2) + "\n").encode("utf-8")


def write_archive(output, entries, data, manifest):
    """Write sorted entries with fixed timestamps/modes and no zlib dependency."""
    if output.exists():
        raise RuntimeError(f"refusing to replace an existing archive: {output}")
    output.parent.mkdir(parents=True, exist_ok=True)
    descriptor, name = tempfile.mkstemp(prefix=".zf253-source-", suffix=".zip", dir=output.parent)
    temporary = Path(name)
    try:
        with os.fdopen(descriptor, "w+b") as handle:
            with zipfile.ZipFile(handle, "w", compression=zipfile.ZIP_STORED) as archive:
                content = dict(data)
                content["MANIFEST.json"] = manifest_bytes(manifest)
                # Preserve even an unused load-path root as an empty directory
                # so the unchanged checker emits no missing-directory warning.
                directories = {path.rstrip("/") + "/" for path in manifest["load_path_directories"]}
                for path in sorted(set(content) | directories):
                    info = zipfile.ZipInfo(path, date_time=(1980, 1, 1, 0, 0, 0))
                    info.create_system = 3
                    mode = 0o040755 if path in directories else (int(entries[path][0], 8) if path in entries else 0o100644)
                    info.external_attr = mode << 16
                    if path in directories:
                        info.external_attr |= 0x10
                    archive.writestr(info, b"" if path in directories else content[path])
            handle.flush()
            os.fsync(handle.fileno())
        # Hard linking is an atomic create-without-replacement on the same
        # filesystem, unlike rename after a separate existence check.
        os.link(temporary, output)
    finally:
        temporary.unlink(missing_ok=True)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", type=Path, default=HERE.parents[1], help="repository root (default: this checkout)")
    parser.add_argument("--plan", action="store_true", help="select/hash sources only; do not create a ZIP")
    parser.add_argument("--output", type=Path, help="new ZIP path; existing files are never replaced")
    parser.add_argument("--verified-commit", help="complete HEAD commit whose canonical check has already passed")
    args = parser.parse_args(argv)
    if args.plan == bool(args.output):
        parser.error("choose exactly one of --plan or --output")
    if args.output and (not args.verified_commit or not re.fullmatch(r"[0-9a-f]{40}", args.verified_commit)):
        parser.error("ZIP creation requires the complete --verified-commit hash after canonical verification")
    repository = args.repository.resolve()
    head, entries, data, manifest = select(repository)
    if args.verified_commit and args.verified_commit != head:
        raise RuntimeError(f"verified commit differs from current HEAD: {args.verified_commit} != {head}")
    manifest_hash = sha256(manifest_bytes(manifest))
    print(f"SOURCE PACKAGE PLAN: {len(data)} files, {len(manifest['dependency_order'])} Coq modules, commit {head}")
    print(f"MANIFEST.json SHA256 {manifest_hash}")
    if args.plan:
        print("\n".join(sorted(data)))
        print("PLAN ONLY: no ZIP created; no Coq verification performed")
        return 0
    output = args.output.resolve()
    try:
        output.relative_to(repository)
    except ValueError:
        pass
    else:
        raise RuntimeError("write deliverable ZIP outside the source repository")
    if git(repository, "rev-parse", "HEAD").decode("ascii").strip() != head:
        raise RuntimeError("repository HEAD changed during package selection")
    write_archive(output, entries, data, manifest)
    print(f"SOURCE ZIP {output}")
    print(f"ZIP SHA256 {sha256(output.read_bytes())}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (AssertionError, OSError, RuntimeError, subprocess.TimeoutExpired, ValueError) as error:
        print(f"PACKAGE FAIL: {error}", file=sys.stderr)
        raise SystemExit(1)
