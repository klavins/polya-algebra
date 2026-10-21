"""Build a student's view of a Polya bundle: prose, concepts and starting code only.

usage: python make_view.py BUNDLE_DIR OUT_DIR

Writes OUT_DIR/subject.md and OUT_DIR/problems/NNN-slug.md in lesson order. The reference
solutions, specs and Lean preambles (which carry earlier references) are left out.
"""
import sys
from pathlib import Path

import yaml

bundle, out = Path(sys.argv[1]), Path(sys.argv[2])
subject = yaml.safe_load((bundle / "subject.yaml").read_text())
concepts = {c["slug"]: c for c in subject.get("concepts", [])}
problems = sorted((yaml.safe_load(p.read_text()) for p in (bundle / "problems").glob("*.yaml")),
                  key=lambda p: p["seq"])

(out / "problems").mkdir(parents=True, exist_ok=True)
index = [f"# {subject['title']}", "", subject.get("description", ""), "", "## Problems, in order", ""]
seen: set[str] = set()
for n, p in enumerate(problems, 1):
    name = f"{n:03d}-{p['slug']}.md"
    lines = [f"# {p['title']}  (problem {n}, slug `{p['slug']}`)", ""]
    for c in p.get("concepts") or []:
        cc = concepts.get(c, {})
        tag = "NEW CONCEPT" if c not in seen else "Concept"
        lines += [f"**{tag}: {cc.get('title', c)}** (`{c}`, {cc.get('kind', '')})", ""]
        if c not in seen:
            lines += [cc.get("description", ""), ""]
            index.append(f"- **New concept: {cc.get('title', c)}** — {cc.get('description', '')}")
        seen.add(c)
    if p.get("statement"):
        lines += ["## Preamble", "", p["statement"].strip(), ""]
    lines += ["## Problem", "", (p.get("description") or "").strip(), "",
              "## Starting code", "", "```lean", p["stub"].rstrip(), "```", ""]
    (out / "problems" / name).write_text("\n".join(lines))
    index.append(f"- {n:03d} `{p['slug']}` — {p['title']}")
(out / "subject.md").write_text("\n".join(index) + "\n")
print(f"{len(problems)} problems -> {out}")
