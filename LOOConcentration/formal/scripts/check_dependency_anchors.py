#!/usr/bin/env python3
"""Check immutable LOOConcentration anchor files and their elaborated Lean declarations."""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path


PROJECT = Path(__file__).resolve().parents[1]
REPO = PROJECT.parents[1]
MANIFEST = PROJECT / "dependency-anchors.json"
PAPER_URL = "https://arxiv.org/abs/2211.02478"
PRINT_START = re.compile(r"(?m)^(?:(?:@\[reducible\] )?def|theorem) LOOConcentration\.[^\n]+")
DECL_START = re.compile(r"(?m)^(?:abbrev|def|noncomputable def|theorem) ")


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def declaration_bytes(data: bytes) -> bytes:
    text = data.decode("utf-8")
    starts = list(DECL_START.finditer(text))
    if len(starts) != 1:
        raise ValueError(f"expected one declaration, found {len(starts)}")
    end = text.find("\n\nend LOOConcentration", starts[0].start())
    if end < 0:
        raise ValueError("missing end LOOConcentration after declaration")
    return (text[starts[0].start() : end] + "\n").encode("utf-8")


def abi_blocks(output: str) -> dict[str, bytes]:
    starts = list(PRINT_START.finditer(output))
    blocks = {}
    for index, match in enumerate(starts):
        end = starts[index + 1].start() if index + 1 < len(starts) else len(output)
        name = re.search(r"LOOConcentration\.[A-Za-z0-9_]+", match.group()).group()
        blocks[name] = output[match.start() : end].encode("utf-8")
    return blocks


def main() -> int:
    manifest = json.loads(MANIFEST.read_text())
    anchors = manifest["anchors"]
    paths = [entry["path"] for entry in anchors]
    exports = [entry["export"] for entry in anchors]
    ids = [entry["id"] for entry in anchors]
    if len(paths) != len(set(paths)) or len(exports) != len(set(exports)) or len(ids) != len(set(ids)):
        print("duplicate frozen path, export, or ID", file=sys.stderr)
        return 1
    frozen_files = {
        str(path.relative_to(REPO)) for path in (PROJECT / "LOOConcentration" / "Frozen").rglob("*.lean")
    }
    if frozen_files != set(paths):
        print(f"manifest/file mismatch: {sorted(frozen_files ^ set(paths))}", file=sys.stderr)
        return 1
    anchor_imports = [
        entry["path"].removeprefix("LOOConcentration/formal/").removesuffix(".lean").replace("/", ".")
        for entry in anchors
    ]
    draft_imports = [module for module, entry in zip(anchor_imports, anchors)
                     if entry["state"] == "DRAFT_SORRY"]
    root_text = (PROJECT / "LOOConcentrationRevision.lean").read_text()
    for module in draft_imports:
        if re.search(rf"(?m)^import {re.escape(module)}$", root_text):
            print(f"draft anchor imported by production root: {module}", file=sys.stderr)
            return 1
    with tempfile.TemporaryDirectory(prefix="looconcentration-frozen-abi-") as directory:
        probe = Path(directory) / "PrintABI.lean"
        probe.write_text(
            ""
            + "".join(f"import {module}\n" for module in anchor_imports)
            + "set_option pp.all true\n"
            + "".join(f"#print {entry['export']}\n" for entry in anchors)
        )
        result = subprocess.run(
            ["lake", "env", "lean", str(probe)],
            cwd=PROJECT,
            text=True,
            capture_output=True,
            check=False,
        )
    if result.returncode:
        print(result.stderr or result.stdout, file=sys.stderr)
        return result.returncode
    blocks = abi_blocks(result.stdout)
    errors = []
    for entry in anchors:
        source = entry["source"]
        if (source.get("url") != PAPER_URL or
                source.get("audit_basis") != "historical_source_not_in_repository" or
                not re.fullmatch(r"[0-9a-f]{64}", source.get("historical_sha256", "")) or
                not source.get("historical_locator") or
                "path" in source):
            errors.append(f"{entry['id']}: invalid paper reference")
        path = REPO / entry["path"]
        data = path.read_bytes()
        command = declaration_bytes(data)
        has_sorry = re.search(rb"\bsorry\b", command) is not None
        if entry["state"] == "DRAFT_SORRY":
            if not (entry.get("quarantine") is True and
                    entry.get("draft_body_policy") == "exact_by_sorry" and
                    command.endswith(b":= by\n  sorry\n")):
                errors.append(f"{entry['id']}: invalid draft body or quarantine")
        elif has_sorry:
            errors.append(f"{entry['id']}: unauthorized sorry")
        checks = {
            "file_sha256": digest(data),
            "declaration_sha256": digest(command),
            "abi_sha256": digest(blocks[entry["export"]]),
        }
        for field, actual in checks.items():
            expected = entry[field]
            if actual != expected:
                errors.append(f"{entry['id']}: {field} mismatch")
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Checked {len(anchors)} frozen anchors: files, commands, and ABI match.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
