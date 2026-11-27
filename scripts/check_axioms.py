#!/usr/bin/env python3
"""Run the Lean milestone audit and reject nonstandard transitive axioms."""
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def check_output(output: str) -> None:
    entries = re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
    if not entries:
        raise ValueError("No axiom audit entries found; refusing an empty audit")
    for entry in entries:
        names = {name.strip() for name in entry.split(",") if name.strip()}
        unexpected = names - ALLOWED
        if unexpected:
            raise ValueError(f"Nonstandard axiom dependencies: {sorted(unexpected)}")


def main() -> int:
    run = subprocess.run(["lake", "env", "lean", "scripts/AxiomAudit.lean"],
                         cwd=ROOT, text=True, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT)
    print(run.stdout, end="")
    if run.returncode:
        return run.returncode
    try:
        check_output(run.stdout)
    except ValueError as exc:
        print(exc, file=sys.stderr)
        return 1
    print("Axiom audit passed: only standard foundational axioms.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
