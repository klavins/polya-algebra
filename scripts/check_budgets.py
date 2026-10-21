"""The prose budgets of STYLE.md, measured over a bundle: a problem's preamble and description
together at most 27 lines of 55 characters, a concept description at most 400 characters.

    uv run --with pyyaml python scripts/check_budgets.py grouptheory [--all]

Prints the problems and concepts over budget; with --all, every problem's count."""

import sys
import textwrap


def lines(prose, w=55):
    n, fence = 0, False
    for ln in prose.split("\n"):
        if ln.strip().startswith("```"):
            fence = not fence
            n += 1
            continue
        if fence or not ln.strip():
            n += 1
            continue
        n += len(textwrap.wrap(ln, w)) or 1
    return n


def main():
    from problem_files import load_bundle

    subj, probs = load_bundle(sys.argv[1])
    show_all = "--all" in sys.argv
    for c in subj["concepts"]:
        n = len(c["description"].strip())
        if n > 400 or show_all:
            print(f"concept {n:4d}  {c['slug']}")
    for p in probs:
        n = lines((p.get("statement") or "").strip() + "\n\n" + (p.get("description") or "").strip())
        if n > 27 or n < 17 or show_all:
            print(f"problem {n:4d}  {p['slug']}")


if __name__ == "__main__":
    main()
