"""Fail unless Lean reports only the three standard axioms for the final theorem."""

from pathlib import Path
import re
import sys


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: python3 scripts/check_axioms.py axioms.log")
    text = Path(sys.argv[1]).read_text(encoding="utf-8")
    pattern = (
        r"'SixVertex\.edge_color_avoidance'\s+depends on axioms:\s*\[([^\]]*)\]"
    )
    match = re.search(pattern, text)
    if match is None:
        raise SystemExit("Missing final theorem axiom report; refusing to infer success.")
    axioms = {item.strip() for item in match.group(1).split(",") if item.strip()}
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    unexpected = axioms - allowed
    if unexpected:
        raise SystemExit(f"Unexpected axioms: {sorted(unexpected)}")
    print(f"Final theorem axiom audit passed: {sorted(axioms)}")


if __name__ == "__main__":
    main()
