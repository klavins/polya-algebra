"""The prose budgets of STYLE.md, measured on a section's .lean file without extracting: each
problem's @preamble and @description together at most 27 lines of 55 characters, each concept's
prose at most 400 characters.

    python3 scripts/check_budgets_lean.py PolyaAlgebra/GroupTheory/Prerequisites.lean [--all]"""

import re
import sys

from check_budgets import lines


def blocks(text):
    for m in re.finditer(r"/-[-!]\s*\n?(@(?:problem|concept)\b.*?)-/", text, re.S):
        yield m.group(1)


def main():
    text = open(sys.argv[1]).read()
    show_all = "--all" in sys.argv
    for b in blocks(text):
        head = re.match(r"@(problem|concept)\s+(\S+)", b)
        kind, slug = head.group(1), head.group(2)
        if kind == "concept":
            prose = "\n".join(l for l in b.splitlines() if not l.startswith("@")).strip()
            if len(prose) > 400 or show_all:
                print(f"concept {len(prose):4d}  {slug}")
        else:
            pre = re.search(r"@preamble\n(.*?)(?=\n@description)", b, re.S)
            desc = re.search(r"@description\n(.*)", b, re.S)
            n = lines(((pre.group(1) if pre else "").strip() + "\n\n" + (desc.group(1) if desc else "").strip()))
            if n > 27 or show_all:
                print(f"problem {n:4d}  {slug}")


if __name__ == "__main__":
    main()
