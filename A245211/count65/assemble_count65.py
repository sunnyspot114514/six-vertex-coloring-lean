#!/usr/bin/env python3
"""Assemble the genuine count-65 proof; does not compile or publish it."""

from pathlib import Path
import importlib.util
import re


ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parent
MODULES = ("Core", "Cycle", "TokenAllocation", "Checker", "Projection")


def assemble() -> Path:
    spec = importlib.util.spec_from_file_location("a245211_assemble", SOURCE / "assemble.py")
    assert spec is not None and spec.loader is not None
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    imports: list[str] = []
    bodies: list[str] = []
    inputs = [SOURCE / f"{name}.lean" for name in MODULES] + [ROOT / "Count65Main.lean"]
    for path in inputs:
        body: list[str] = []
        for line in path.read_text().splitlines():
            if line.startswith("import "):
                if not line.startswith("import A245211.") and line not in imports:
                    imports.append(line)
            else:
                body.append(line)
        text = "\n".join(body).strip()
        options = re.findall(r"(?m)^set_option (\S+) (\d+)\s*$", text)
        text = re.sub(r"(?m)^set_option \S+ \d+\s*\n", "", text)
        if options:
            prefix = "".join(f"set_option {key} {value} in\n" for key, value in options)
            text = text.replace("/--", "/-")
            proof_definitions = helper.kernel_proof_definitions(text)

            def scope_options(match: re.Match[str]) -> str:
                if match[2] == "def" and match[3] not in proof_definitions:
                    return match[0]
                return prefix + match[0]

            text = re.sub(
                r"(?m)^((?:@\[[^\n]*\]\s*)?(?:private\s+)?)(theorem|lemma|def)\b"
                r"(?:[ \t]+([A-Za-z_][A-Za-z0-9_'.]*))?", scope_options, text)
        bodies.append(text)
    parent_import = "import OMAReductions.R_OeisA245211_conjecture_R2"
    assert parent_import in imports
    imports.remove(parent_import)
    imports.insert(0, "import OMAReductions.R_OeisA245211_conjecture_R2_H3_R1")
    bodies.append(
        "theorem OMA.solution : OMA.R_OeisA245211_conjecture_R2_H3_R1.H1 := by\n"
        "  exact A245211New.squarefree_no_fixed_count65"
    )
    destination = ROOT / "proofs/OeisA245211.conjecture.R2.H3.R1.H1.lean"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text("\n".join(imports) + "\n\n" + "\n\n".join(bodies) + "\n")
    print(f"Assembled {destination}: {destination.stat().st_size} bytes")
    return destination


if __name__ == "__main__":
    assemble()
