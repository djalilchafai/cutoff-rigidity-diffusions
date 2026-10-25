#!/usr/bin/env python3
"""Conservative local checks; not a substitute for Palomar's verifier."""
import argparse
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
EXCLUDED = {".git", ".lake", ".agents", ".codex", ".aws"}


def code_only(text):
    """Blank comments and strings, preserving positions and line breaks."""
    out = list(text)
    i = 0
    while i < len(text):
        start = i
        if text.startswith("--", i):
            stop = text.find("\n", i)
            i = len(text) if stop < 0 else stop
        elif text.startswith("/-", i):
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError("unterminated block comment")
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            i += 1
            continue
        for j in range(start, min(i, len(out))):
            if out[j] not in "\r\n":
                out[j] = " "
    return "".join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ready", action="store_true", help="also require submission scaffolding")
    args = parser.parse_args()
    errors = []
    source_count = 0
    for path in ROOT.rglob("*.lean"):
        relative = path.relative_to(ROOT)
        if any(part in EXCLUDED for part in relative.parts):
            continue
        if path.is_symlink():
            errors.append(f"{relative}: Lean source symlink is not permitted")
            continue
        source_count += 1
        try:
            raw = path.read_text(encoding="utf-8")
            code = code_only(raw)
        except (OSError, UnicodeError, ValueError) as error:
            errors.append(f"{relative}: {error}")
            continue
        lines = len(raw.splitlines())
        if lines > 10000:
            errors.append(f"{relative}: {lines} lines exceeds 10000")
        if path.name != "lakefile.lean" and not re.match(r"\s*module\b", code):
            errors.append(f"{relative}: missing initial module header")
        if relative == pathlib.Path("Challenge.lean"):
            if lines > 1000 or len(raw.encode("utf-8")) > 100 * 1024:
                errors.append("Challenge.lean: exceeds statement surface limit")
            # Deliberate statement holes are allowed only in Challenge.
            forbidden = r"\b(?:axiom|native_decide|sorryAx|ofReduceBool)\b"
        else:
            forbidden = r"\b(?:sorry|admit|axiom|native_decide|sorryAx|ofReduceBool)\b"
        for match in re.finditer(forbidden, code):
            line = raw.count("\n", 0, match.start()) + 1
            errors.append(f"{relative}:{line}: unsupported proof token {match.group()}")
    if not source_count:
        errors.append("no Lean source files found")
    if args.ready:
        for required in ("lean-toolchain", "lake-manifest.json", "Challenge.lean", "Solution.lean"):
            if not (ROOT / required).is_file():
                errors.append(f"missing {required}")
        if sum((ROOT / name).is_file() for name in ("lakefile.lean", "lakefile.toml")) != 1:
            errors.append("exactly one Lakefile is required")
        try:
            config = json.loads((ROOT / "comparator.json").read_text())
            if not config.get("theorem_names"):
                errors.append("Comparator has no advertised theorems")
            if set(config.get("permitted_axioms", [])) - {"propext", "Classical.choice", "Quot.sound"}:
                errors.append("Comparator permits nonstandard axioms")
            if "external_kernels" in config:
                errors.append("external_kernels is not a submitted configuration field")
        except (OSError, ValueError) as error:
            errors.append(f"comparator.json: {error}")
        try:
            import yaml
            metadata = yaml.safe_load((ROOT / "formalization.yaml").read_text())
            project = metadata.get("project", {})
            for field in ("authors", "responsible_maintainers", "license"):
                if not project.get(field):
                    errors.append(f"formalization.yaml: project.{field} is unassigned")
            license_files = [p for p in ROOT.iterdir() if re.fullmatch(
                r"(?:LICENSE|LICENCE|COPYING|UNLICENSE|OFL)(?:\.(?:md|markdown|txt))?",
                p.name, re.IGNORECASE)]
            if len(license_files) != 1:
                errors.append("exactly one root licence file is required")
        except (ImportError, OSError, ValueError) as error:
            errors.append(f"metadata check: {error}")
    for error in errors:
        print(f"ERROR: {error}", file=sys.stderr)
    if errors:
        return 1
    print(f"Local source checks passed for {source_count} Lean files; official verification remains required.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
