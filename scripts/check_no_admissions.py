#!/usr/bin/env python3
"""Reject proof admissions in project Lean sources (not dependency sources).

This lexical guard complements, rather than replaces, Lean and #print axioms.
Nested comments and string literals are skipped.
"""
from pathlib import Path
import re
import sys


def code_only(text: str) -> str:
    result = []
    i = depth = 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                result.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            i += 2
            result.append(" ")
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
            result.append(" ")
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    result.append("\n" if text[i] == "\n" else " ")
                    i += 1
            result.append(" ")
        else:
            result.append(text[i])
            i += 1
    return "".join(result)


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    paths = sorted((root / "NPTEnt").rglob("*.lean"))
    paths += [root / "NPTEnt.lean"]
    failed = False
    for path in paths:
        for match in re.finditer(r"\b(?:sorry|admit|axiom)\b", code_only(path.read_text())):
            print(f"{path}: forbidden token {match.group()}")
            failed = True
    if not failed:
        print(f"Admission scan passed ({len(paths)} project Lean files).")
    return int(failed)


if __name__ == "__main__":
    sys.exit(main())
