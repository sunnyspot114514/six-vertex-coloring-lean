#!/usr/bin/env python3
"""Flatten the checked modules into the upstream's one-file submission."""
from pathlib import Path
import argparse
import re

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
        text = "\n".join(body).strip()
        options = re.findall(r"(?m)^set_option (\S+) (\d+)\s*$", text)
        text = re.sub(r"(?m)^set_option \S+ \d+\s*\n", "", text)
        if options:
            # The upstream gate permits scoped options only. Keep each module's
            # settings on its proof declarations, leaving definitions unchanged.
            prefix = "".join(f"set_option {key} {value} in\n" for key, value in options)
            text = text.replace("/--", "/-")
            text = re.sub(r"(?m)^((?:@\[[^\n]*\]\s*)?(?:private\s+)?(?:theorem|lemma)\b)",
                          lambda match: prefix + match.group(1), text)
        bodies.append(text)
    required_import = "import OMAReductions.R_OeisA245211_conjecture_R2"
    imports.remove(required_import)
    imports.insert(0, required_import)
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text("\n".join(imports) + "\n\n" + "\n\n".join(bodies) + "\n")
    print(f"Assembled {destination}: {destination.stat().st_size} bytes")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    assemble(args.source, args.output)
