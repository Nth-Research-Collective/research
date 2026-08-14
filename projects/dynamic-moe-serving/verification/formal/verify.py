"""Formal verification backends.

The novelty gate accepts two kinds of evidence:
1. a deterministically verified construction beating a published record
2. a machine-checked proof accepted by a backend here

Contract: `check(statement, proof_path)` either verifies end to end and
returns an evidence dict, or raises FormalVerificationError. There is no
"probably fine" return value.
"""
from __future__ import annotations

import hashlib
import re
import shutil
import subprocess
import tempfile
from collections.abc import Collection
from pathlib import Path

_ELAN_BIN = Path.home() / ".elan" / "bin" / "lean"


class FormalVerificationError(Exception):
    """The claim remains UNVERIFIED."""


def _find_lean() -> str:
    lean = shutil.which("lean") or (str(_ELAN_BIN) if _ELAN_BIN.exists() else None)
    if lean is None:
        raise FormalVerificationError(
            "Lean not installed (expected on PATH or in ~/.elan/bin). "
            "Install: curl -sSf https://elan.lean-lang.org/elan-init.sh | sh"
        )
    return lean


class LeanBackend:
    """Checks standalone Lean 4 proof files with the core toolchain.

    A proof passes only if ALL hold:
    1. the claimed statement appears verbatim in the file — a compiling
       file proving something else is worthless;
    2. the source declares no escape hatches (sorry / axiom / constant /
       admit / native_decide, which trusts the compiler);
    3. Lean accepts the exact source with no `sorry` warnings;
    4. Lean reports no transitive axioms outside the explicit allowlist.

    Statement matching is textual, so the DIRECTOR must read the theorem
    statement and confirm it formalizes the mathematical claim — Lean
    guarantees the proof is airtight, not that the statement means what
    you wanted. Files in, or importing modules from, formal/lean_project run
    through that pinned Lake project; standalone files use core Lean directly.
    """

    available = True
    _FORBIDDEN = re.compile(
        r"\b(sorry|admit|native_decide)\b|^\s*(?:axiom|constant)\b", re.M
    )
    _DECLARATION = re.compile(r"\b(?:theorem|lemma)\s+([A-Za-z_][\w.']*)")
    _NAMESPACE = re.compile(r"^\s*namespace\s+([A-Za-z_][\w.']*)\s*$", re.M)
    _END_NAMESPACE = re.compile(r"^\s*end\s+([A-Za-z_][\w.']*)\s*$", re.M)
    _IMPORT = re.compile(r"^\s*import\s+(.+?)\s*$", re.M)
    _AXIOM_REPORT = re.compile(r"depends on axioms:\s*\[([^]]*)\]", re.S)
    _DEFAULT_ALLOWED_AXIOMS = frozenset(
        {"propext", "Classical.choice", "Quot.sound"}
    )

    @classmethod
    def _declaration_name(cls, statement: str, src: str) -> str:
        match = cls._DECLARATION.search(statement)
        if not match:
            raise FormalVerificationError(
                "claimed statement must name a Lean theorem or lemma"
            )
        name = match.group(1)
        if "." in name:
            return name

        statement_at = src.find(statement.strip())
        prefix = src[:statement_at] if statement_at >= 0 else src
        namespaces: list[str] = []
        events = [
            (m.start(), "open", m.group(1)) for m in cls._NAMESPACE.finditer(prefix)
        ] + [
            (m.start(), "close", m.group(1))
            for m in cls._END_NAMESPACE.finditer(prefix)
        ]
        for _, event, namespace in sorted(events):
            if event == "open":
                namespaces.append(namespace)
            elif namespace in namespaces:
                while namespaces:
                    closed = namespaces.pop()
                    if closed == namespace:
                        break
        return ".".join([*namespaces, name])

    @classmethod
    def _parse_axioms(cls, output: str) -> list[str]:
        match = cls._AXIOM_REPORT.search(output)
        if match:
            return sorted(
                axiom.strip() for axiom in match.group(1).split(",") if axiom.strip()
            )
        if "does not depend on any axioms" in output:
            return []
        raise FormalVerificationError(
            "Lean accepted the proof but did not return a readable transitive axiom report"
        )

    def _compile_and_audit_axioms(
        self, src: str, path: Path, declaration: str, *, project_env: bool
    ) -> tuple[list[str], str]:
        audit_path: Path | None = None
        try:
            with tempfile.NamedTemporaryFile(
                mode="w",
                encoding="utf-8",
                suffix=".lean",
                prefix="beyond_axiom_audit_",
                dir=path.parent,
                delete=False,
            ) as audit:
                audit.write(src)
                audit.write(f"\n\n#print axioms {declaration}\n")
                audit_path = Path(audit.name)

            if project_env:
                project = Path(__file__).parent / "lean_project"
                lake = Path(_find_lean()).parent / "lake"
                cmd, cwd = [str(lake), "env", "lean", str(audit_path.resolve())], project
            else:
                cmd, cwd = [_find_lean(), str(audit_path.resolve())], None
            proc = subprocess.run(
                cmd, cwd=cwd, capture_output=True, text=True, timeout=600
            )
            output = proc.stdout + proc.stderr
            if proc.returncode != 0:
                raise FormalVerificationError(
                    "Lean rejected the proof during dependency audit:\n"
                    f"{output.strip()}"
                )
            return self._parse_axioms(output), output
        finally:
            if audit_path is not None:
                audit_path.unlink(missing_ok=True)

    def check(
        self,
        statement: str,
        proof_path: str,
        *,
        allowed_axioms: Collection[str] = _DEFAULT_ALLOWED_AXIOMS,
    ) -> dict:
        path = Path(proof_path)
        if not path.exists():
            raise FormalVerificationError(f"no such proof file: {path}")
        src = path.read_text()

        if statement.strip() not in src:
            raise FormalVerificationError(
                "claimed statement does not appear in the proof file; "
                "refusing to verify a different theorem"
            )
        hit = self._FORBIDDEN.search(src)
        if hit:
            raise FormalVerificationError(f"escape hatch in source: {hit.group().strip()!r}")

        declaration = self._declaration_name(statement, src)
        project = Path(__file__).parent / "lean_project"
        uses_project_env = (
            project in path.resolve().parents
            or "import Mathlib" in src
            or "import LeanProject" in src
        )
        axioms, output = self._compile_and_audit_axioms(
            src, path, declaration, project_env=uses_project_env
        )
        if "sorry" in output:
            raise FormalVerificationError(f"proof compiles but uses sorry:\n{output.strip()}")

        unexpected_axioms = sorted(set(axioms) - set(allowed_axioms))
        if unexpected_axioms:
            raise FormalVerificationError(
                "unexpected transitive axioms: " + ", ".join(unexpected_axioms)
            )

        version = subprocess.run(
            [_find_lean(), "--version"], capture_output=True, text=True
        ).stdout.strip()
        return {
            "backend": "lean",
            "lean_version": version,
            "proof_file": str(path),
            "proof_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "statement": statement.strip(),
            "statement_sha256": hashlib.sha256(
                statement.strip().encode("utf-8")
            ).hexdigest(),
            "declaration": declaration,
            "imports": self._IMPORT.findall(src),
            "axioms": axioms,
            "allowed_axioms": sorted(allowed_axioms),
        }
