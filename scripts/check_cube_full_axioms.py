"""Require an explicit axiom report for each exported cube-full result."""

from pathlib import Path
import re
import sys

THEOREMS = (
    "CubeFull.isCubeFull_iff_primeFactors",
    "CubeFull.no_consecutive",
    "CubeFull.refutesBoundedExistence",
)
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: python3 scripts/check_cube_full_axioms.py LOG")
    log = Path(sys.argv[1]).read_text(encoding="utf-8")
    for theorem in THEOREMS:
        name = re.escape(theorem)
        match = re.search(rf"'{name}'\s+depends on axioms:\s*\[([^\]]*)\]", log)
        if match is None:
            if re.search(rf"'{name}'\s+does not depend on any axioms", log):
                axioms = set()
            else:
                raise SystemExit(f"Missing axiom report for {theorem}")
        else:
            axioms = {item.strip() for item in match.group(1).split(",") if item.strip()}
        if unexpected := axioms - ALLOWED:
            raise SystemExit(f"Unexpected axioms for {theorem}: {sorted(unexpected)}")
        print(f"{theorem}: axiom audit passed: {sorted(axioms)}")


if __name__ == "__main__":
    main()
