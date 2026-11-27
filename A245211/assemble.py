#!/usr/bin/env python3
"""Flatten the checked modules into the upstream's one-file submission."""
from pathlib import Path
import argparse
import re

MODULES = ("Core", "Cycle", "TokenAllocation", "Checker", "Projection", "Finite", "Main")


def kernel_proof_definitions(text: str) -> set[str]:
    """Find proof-valued definitions that retain the module's proof options."""
    declarations = list(re.finditer(
        r"(?m)^(?:private\s+)?(theorem|lemma|abbrev|def)\s+([^\s(:]+)", text))
    result: set[str] = set()
    for index, declaration in enumerate(declarations):
        end = declarations[index + 1].start() if index + 1 < len(declarations) else len(text)
        body = text[declaration.start():end].partition(":=")[2]
        if declaration[1] == "def" and re.match(r"\s*by\s+decide\s+\+kernel(?:\s|$)", body):
            result.add(declaration[2])
    return result


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
            # settings on its proofs, including synchronous kernel certificates.
            prefix = "".join(f"set_option {key} {value} in\n" for key, value in options)
            text = text.replace("/--", "/-")
            proof_definitions = kernel_proof_definitions(text)

            def scope_options(match: re.Match[str]) -> str:
                if match[2] == "def" and match[3] not in proof_definitions:
                    return match[0]
                return prefix + match[0]

            text = re.sub(
                r"(?m)^((?:@\[[^\n]*\]\s*)?(?:private\s+)?)(theorem|lemma|def)\b"
                r"(?:[ \t]+([A-Za-z_][A-Za-z0-9_'.]*))?", scope_options, text)
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
