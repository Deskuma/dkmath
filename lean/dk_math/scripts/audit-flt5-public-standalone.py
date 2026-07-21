#!/usr/bin/env python3
"""Audit fixed FLT5 standalone statements and trust against production."""

from __future__ import annotations

import argparse
import hashlib
import re
import shutil
import subprocess
import sys
from pathlib import Path


REPOSITORY = "Deskuma/dkmath"
BRANCH = "feature/FLT35-essence-260722-v0"
TOOLCHAIN = "leanprover/lean4:v4.29.0"
ARTIFACT = Path("DkMath/FLT/docs/StandAlone/FLT5#StandAlone-v0.lean.txt")
ARTIFACT_SHA256 = "400935756c2468577582e6e9b87db2e5a2194a127855e3eb9bea312ff79b8dbd"
BASIC = Path("DkMath/FLT/Five/Basic.lean")
MAIN = Path("DkMath/FLT/Five/Main.lean")
QUADRATIC = Path("DkMathTest/FLT/QuadraticEssence.lean")
TEMP_ROOT = Path("/tmp/dkmath-flt5-audit-v429")

DECLARATIONS = (
    ("def", "Fermat5Equation", BASIC),
    ("abbrev", "FLT5Target", MAIN),
    ("theorem", "flt5Target", MAIN),
    ("theorem", "fermatFive_no_positive_solution", MAIN),
)
ENDPOINTS = (
    "DkMath.FLT.Five.flt5Target",
    "DkMath.FLT.Five.fermatFive_no_positive_solution",
)
CHECKS = (
    "DkMath.FLT.Five.Fermat5Equation",
    "DkMath.FLT.Five.flt5Target",
    "DkMath.FLT.Five.fermatFive_no_positive_solution",
)
QUADRATIC_NAMES = (
    "DkMath.NumberTheory.TraceOneQuadratic.traceOne_norm_mul",
    "DkMath.NumberTheory.TraceOneQuadratic.four_mul_traceOneNorm_eq_discriminant",
    "DkMath.FLT.S0_nat_eq_traceOneNorm_negOne",
    "DkMath.FLT.GN_three_sub_eq_traceOneNorm_negOne",
    "DkMath.FLT.Five.goldenNorm_eq_traceOneNorm_one",
    "DkMath.FLT.Five.GN5_eq_traceOneNorm_squareLink",
)


class AuditFailure(Exception):
    def __init__(self, result: str, message: str):
        super().__init__(message)
        self.result = result


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def run(root: Path, args: list[str]) -> tuple[int, str]:
    completed = subprocess.run(
        args,
        cwd=root,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    return completed.returncode, completed.stdout.replace("\r\n", "\n")


def find_assignment(text: str, start: int) -> int:
    """Find `:=` outside strings and nested comments."""
    index = start
    depth = 0
    in_string = False
    while index + 1 < len(text):
        pair = text[index : index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                index += 2
                continue
            if pair == "-/":
                depth -= 1
                index += 2
                continue
            index += 1
            continue
        if in_string:
            if text[index] == "\\":
                index += 2
                continue
            if text[index] == '"':
                in_string = False
            index += 1
            continue
        if pair == "/-":
            depth = 1
            index += 2
            continue
        if pair == "--":
            newline = text.find("\n", index + 2)
            index = len(text) if newline == -1 else newline + 1
            continue
        if text[index] == '"':
            in_string = True
            index += 1
            continue
        if pair == ":=":
            return index
        index += 1
    raise AuditFailure("FAIL_STATEMENT_MISMATCH", "declaration assignment delimiter not found")


def extract_statement(text: str, kind: str, name: str) -> str:
    start_match = re.search(rf"(?m)^{re.escape(kind)}\s+{re.escape(name)}\b", text)
    if not start_match:
        raise AuditFailure("FAIL_STATEMENT_MISMATCH", f"missing declaration: {kind} {name}")
    assignment = find_assignment(text, start_match.start())
    if kind == "theorem":
        return text[start_match.start() : assignment].rstrip()
    next_decl = re.search(
        r"(?m)^\s*$\n(?=(?:/--|/-!|(?:private\s+)?(?:def|abbrev|theorem|lemma|structure|inductive)\s))",
        text[assignment + 2 :],
    )
    if not next_decl:
        raise AuditFailure("FAIL_STATEMENT_MISMATCH", f"end of declaration not found: {name}")
    end = assignment + 2 + next_decl.start()
    return text[start_match.start() : end].rstrip()


def normalize_source(text: str) -> str:
    """Collapse ordinary whitespace outside comments and strings."""
    output: list[str] = []
    index = 0
    depth = 0
    in_string = False
    pending_space = False
    while index < len(text):
        pair = text[index : index + 2]
        char = text[index]
        if depth:
            output.append(char)
            if pair == "/-":
                output.append("-")
                depth += 1
                index += 2
                continue
            if pair == "-/":
                output.append("/")
                depth -= 1
                index += 2
                continue
            index += 1
            continue
        if in_string:
            output.append(char)
            if char == "\\" and index + 1 < len(text):
                output.append(text[index + 1])
                index += 2
                continue
            if char == '"':
                in_string = False
            index += 1
            continue
        if pair == "/-":
            if pending_space and output:
                output.append(" ")
            pending_space = False
            output.extend(("/", "-"))
            depth = 1
            index += 2
            continue
        if char == '"':
            if pending_space and output:
                output.append(" ")
            pending_space = False
            output.append(char)
            in_string = True
            index += 1
            continue
        if char.isspace():
            pending_space = True
            index += 1
            continue
        if pending_space and output:
            output.append(" ")
        pending_space = False
        output.append(char)
        index += 1
    return "".join(output).strip()


def audit_commands() -> str:
    lines: list[str] = []
    for name in CHECKS:
        marker = name.rsplit(".", 1)[-1]
        lines.extend(
            (
                f'#eval IO.println "F35_CHECK_BEGIN:{marker}"',
                f"#check @{name}",
                f'#eval IO.println "F35_CHECK_END:{marker}"',
            )
        )
    for name in ENDPOINTS:
        marker = name.rsplit(".", 1)[-1]
        lines.extend(
            (
                f'#eval IO.println "F35_AXIOM_BEGIN:{marker}"',
                f"#print axioms {name}",
                f'#eval IO.println "F35_AXIOM_END:{marker}"',
            )
        )
    lines.append(
        """
example (x y z : ℕ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ¬ DkMath.FLT.Five.Fermat5Equation x y z :=
  DkMath.FLT.Five.fermatFive_no_positive_solution x y z hx hy hz
""".strip()
    )
    return "\n".join(lines) + "\n"


def marker_block(output: str, category: str, marker: str) -> str:
    begin = f"F35_{category}_BEGIN:{marker}"
    end = f"F35_{category}_END:{marker}"
    start = output.find(begin)
    finish = output.find(end, start + len(begin))
    if start == -1 or finish == -1:
        raise AuditFailure("FAIL_BUILD", f"missing output markers: {category} {marker}")
    return output[start + len(begin) : finish].strip()


def normalize_lean_output(text: str) -> str:
    text = re.sub(r"(?m)^(?:info: )?[^\n:]+\.lean:\d+:\d+:\s*", "", text)
    return re.sub(r"\s+", " ", text).strip()


def axiom_set(block: str, name: str) -> tuple[str, ...]:
    match = re.search(r"depends on axioms:\s*\[(.*?)\]", block, re.DOTALL)
    if match:
        return tuple(sorted(item.strip() for item in match.group(1).split(",") if item.strip()))
    if "does not depend on any axioms" in block:
        return ()
    raise AuditFailure("FAIL_TRUST_BOUNDARY", f"cannot parse axiom report for {name}: {block}")


def strip_comments_and_strings(text: str) -> str:
    output: list[str] = []
    index = 0
    depth = 0
    in_string = False
    while index < len(text):
        pair = text[index : index + 2]
        char = text[index]
        if depth:
            if pair == "/-":
                depth += 1
                index += 2
            elif pair == "-/":
                depth -= 1
                index += 2
            else:
                index += 1
            continue
        if in_string:
            if char == "\\":
                index += 2
            elif char == '"':
                in_string = False
                index += 1
            else:
                index += 1
            continue
        if pair == "/-":
            depth = 1
            output.append(" ")
            index += 2
        elif pair == "--":
            newline = text.find("\n", index + 2)
            output.append("\n")
            index = len(text) if newline == -1 else newline + 1
        elif char == '"':
            in_string = True
            output.append(" ")
            index += 1
        else:
            output.append(char)
            index += 1
    return "".join(output)


def ensure_trustworthy(axioms: tuple[str, ...], name: str) -> None:
    bad = [axiom for axiom in axioms if "sorryAx" in axiom or axiom.startswith("DkMath.")]
    if bad:
        raise AuditFailure("FAIL_TRUST_BOUNDARY", f"unsafe axioms for {name}: {bad}")


def perform(root: Path) -> str:
    artifact_bytes = (root / ARTIFACT).read_bytes()
    artifact_hash = sha256_bytes(artifact_bytes)
    if artifact_hash != ARTIFACT_SHA256:
        raise AuditFailure("FAIL_ENVIRONMENT", f"artifact SHA-256 mismatch: {artifact_hash}")

    version_status, version_output = run(root, ["lake", "env", "lean", "--version"])
    version_output = version_output.strip()
    if version_status != 0 or "version 4.29.0" not in version_output:
        raise AuditFailure("FAIL_ENVIRONMENT", f"unexpected Lean version: {version_output}")

    public_texts = {
        BASIC: (root / BASIC).read_text(encoding="utf-8"),
        MAIN: (root / MAIN).read_text(encoding="utf-8"),
    }
    standalone_text = artifact_bytes.decode("utf-8")
    hashes: dict[str, tuple[str, str]] = {}
    comparisons: dict[str, bool] = {}
    for kind, name, source in DECLARATIONS:
        public = normalize_source(extract_statement(public_texts[source], kind, name))
        standalone = normalize_source(extract_statement(standalone_text, kind, name))
        public_hash = sha256_bytes(public.encode("utf-8"))
        standalone_hash = sha256_bytes(standalone.encode("utf-8"))
        hashes[name] = (public_hash, standalone_hash)
        comparisons[name] = public == standalone
        if public != standalone:
            raise AuditFailure("FAIL_STATEMENT_MISMATCH", f"statement mismatch: {name}")

    if TEMP_ROOT.exists():
        shutil.rmtree(TEMP_ROOT)
    TEMP_ROOT.mkdir(parents=True)
    public_audit = TEMP_ROOT / "public-audit.lean"
    standalone_audit = TEMP_ROOT / "standalone-audit.lean"
    public_audit.write_text("import DkMath.FLT.Five.Main\n\n" + audit_commands(), encoding="utf-8")
    standalone_audit.write_bytes(artifact_bytes + b"\n" + audit_commands().encode("utf-8"))

    public_status, public_output = run(root, ["lake", "env", "lean", str(public_audit)])
    standalone_status, standalone_output = run(root, ["lake", "env", "lean", str(standalone_audit)])
    if public_status != 0 or standalone_status != 0:
        raise AuditFailure(
            "FAIL_BUILD",
            f"Lean audit failure: public={public_status}, standalone={standalone_status}",
        )

    type_results: dict[str, tuple[str, str, bool]] = {}
    for name in CHECKS:
        marker = name.rsplit(".", 1)[-1]
        public_type = normalize_lean_output(marker_block(public_output, "CHECK", marker))
        standalone_type = normalize_lean_output(marker_block(standalone_output, "CHECK", marker))
        equal = public_type == standalone_type
        type_results[name] = (public_type, standalone_type, equal)
        if not equal:
            raise AuditFailure("FAIL_TYPE_OUTPUT_MISMATCH", f"type output mismatch: {name}")

    endpoint_axioms: dict[str, tuple[tuple[str, ...], tuple[str, ...]]] = {}
    for name in ENDPOINTS:
        marker = name.rsplit(".", 1)[-1]
        public_axioms = axiom_set(marker_block(public_output, "AXIOM", marker), name)
        standalone_axioms = axiom_set(marker_block(standalone_output, "AXIOM", marker), name)
        ensure_trustworthy(public_axioms, name)
        ensure_trustworthy(standalone_axioms, name)
        if public_axioms != standalone_axioms:
            raise AuditFailure("FAIL_AXIOM_MISMATCH", f"axiom mismatch: {name}")
        endpoint_axioms[name] = (public_axioms, standalone_axioms)

    active_tokens: dict[str, list[str]] = {}
    for label, text in (
        (str(BASIC), public_texts[BASIC]),
        (str(MAIN), public_texts[MAIN]),
        (str(ARTIFACT), standalone_text),
    ):
        executable = strip_comments_and_strings(text)
        found = sorted({token for token in ("native_decide", "admit", "sorry") if re.search(rf"\b{token}\b", executable)})
        active_tokens[label] = found
        if found:
            raise AuditFailure("FAIL_TRUST_BOUNDARY", f"active unsafe tokens in {label}: {found}")

    quadratic_status, quadratic_output = run(root, ["lake", "env", "lean", str(QUADRATIC)])
    if quadratic_status != 0:
        raise AuditFailure("FAIL_BUILD", f"quadratic audit failed: {quadratic_status}")
    quadratic_axioms: dict[str, tuple[str, ...]] = {}
    for name in QUADRATIC_NAMES:
        match = re.search(
            rf"'{re.escape(name)}'\s+depends on axioms:\s*\[(.*?)\]",
            quadratic_output,
            re.DOTALL,
        )
        if not match:
            raise AuditFailure("FAIL_TRUST_BOUNDARY", f"missing quadratic axiom report: {name}")
        axioms = tuple(sorted(item.strip() for item in match.group(1).split(",") if item.strip()))
        ensure_trustworthy(axioms, name)
        quadratic_axioms[name] = axioms

    lines = [
        "checkpoint: F35-008A",
        f"repository: {REPOSITORY}",
        f"branch: {BRANCH}",
        f"lean_toolchain: {TOOLCHAIN}",
        f"lean_version_output: {version_output}",
        f"artifact: {ARTIFACT}",
        f"artifact_sha256: {artifact_hash}",
        "",
        "[normalized declaration hashes]",
    ]
    for _, name, _ in DECLARATIONS:
        public_hash, standalone_hash = hashes[name]
        lines.append(f"{name}: public={public_hash} standalone={standalone_hash}")
        lines.append(f"{name}: statement_equal={str(comparisons[name]).lower()}")
    lines.extend(("", "[public Lean audit]", f"command: lake env lean {public_audit}", f"exit_status: {public_status}", public_output.rstrip()))
    lines.extend(("", "[standalone Lean audit]", f"command: lake env lean {standalone_audit}", f"exit_status: {standalone_status}", standalone_output.rstrip()))
    lines.extend(("", "[normalized #check comparisons]"))
    for name in CHECKS:
        public_type, standalone_type, equal = type_results[name]
        lines.append(f"{name}: equal={str(equal).lower()}")
        lines.append(f"{name}: public={public_type}")
        lines.append(f"{name}: standalone={standalone_type}")
    lines.extend(("", "[endpoint axiom sets]"))
    for name in ENDPOINTS:
        public_axioms, standalone_axioms = endpoint_axioms[name]
        lines.append(f"{name}: public={list(public_axioms)}")
        lines.append(f"{name}: standalone={list(standalone_axioms)}")
        lines.append(f"{name}: equal=true")
    lines.extend(("", "[active token audit]"))
    for label, found in active_tokens.items():
        lines.append(f"{label}: active_tokens={found}")
    lines.extend(("", "[quadratic essence audit]", f"command: lake env lean {QUADRATIC}", f"exit_status: {quadratic_status}", quadratic_output.rstrip(), "", "[quadratic essence axiom sets]"))
    for name in QUADRATIC_NAMES:
        lines.append(f"{name}: {list(quadratic_axioms[name])}")
    lines.extend(("", "final result: PASS", ""))
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true", help="run without saving a log")
    mode.add_argument("--log", type=Path, help="run and save the deterministic audit log")
    args = parser.parse_args()
    try:
        root = Path(__file__).resolve().parent.parent
        log = perform(root)
        if args.log is not None:
            output = args.log if args.log.is_absolute() else root / args.log
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(log, encoding="utf-8", newline="\n")
            print(f"log: {output}")
        print("final result: PASS")
        return 0
    except (OSError, UnicodeError, AuditFailure) as error:
        result = error.result if isinstance(error, AuditFailure) else "FAIL_BUILD"
        print(f"final result: {result}", file=sys.stderr)
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
