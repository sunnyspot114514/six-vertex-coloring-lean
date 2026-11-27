#!/usr/bin/env python3
"""Flatten the checked modules into the upstream's one-file submission."""
from pathlib import Path
import argparse

MODULES = ("Core", "Cycle", "TokenAllocation", "Checker", "Projection", "Finite", "Main")


def assemble(source: Path, destination: Path) -> None:
    imports: list[str] = []
    bodies: list[str] = []
    for name in MODULES:
        lines = (source / f"{name}.lean").read_text().splitlines()
        body: list[str] = []
        for line in lines:
            if line.startswith("import "):
                if not line.startswith("import A245211.") and line not in imports:
                    imports.append(line)
            else:
                body.append(line)
        bodies.append("\n".join(body).strip())
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text("\n".join(imports) + "\n\n" + "\n\n".join(bodies) + "\n")
    print(f"Assembled {destination}: {destination.stat().st_size} bytes")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    assemble(args.source, args.output)
