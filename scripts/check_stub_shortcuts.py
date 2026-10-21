"""A theorem the student is asked to prove should not close by `inferInstance`, or by a single
Mathlib lemma that uses nothing of the subject: the exercise then becomes a search, and the
student never meets the argument (Profinite Spaces review, 2026-10-14: `tychonoff` closed by
`inferInstance`, `profinite_compact_hausdorff` by `Function.Surjective.compactSpace`).

    uv run --with pyyaml python scripts/check_stub_shortcuts.py grouptheory [--only SLUG ...]

Each theorem of each stub is tried, one at a time and with the others left as `sorry`, with
`inferInstance` and with `exact?`. A shortcut is reported unless it names a declaration of the
problem's context or one from the stub itself, which is the subject's own work being used.
A problem where the shortcut is intended (a hand-over that asks the student to call Mathlib)
is listed in scripts/stub_shortcuts_ok.txt and skipped."""

import os
import re
import sys

from problem_files import ROOT, compile_source, is_theorem, load_bundle, problem_source, run_all, split_decls

OK_FILE = os.path.join(ROOT, "scripts", "stub_shortcuts_ok.txt")


def allowed():
    if not os.path.exists(OK_FILE):
        return set()
    return {l.split("#")[0].strip() for l in open(OK_FILE) if l.split("#")[0].strip()}


def context_names(prob):
    names = set(re.findall(r"^(?:@\[.*\]\s*)?(?:noncomputable\s+)?(?:theorem|lemma|def|instance|structure|class|abbrev)\s+([\w.']+)",
                           prob.get("preamble", ""), re.M))
    names |= {n.split(".")[-1] for n in names}
    names |= set(prob.get("stub_names") or [])
    names |= {n.split(".")[-1] for n in prob.get("stub_names") or []}
    return names


def try_decl(job):
    subj, prob, i = job
    stub = split_decls(prob["stub"])
    d = stub[i]
    # the other declarations are the reference's, so that no `sorry` definition makes a theorem
    # about it trivial; the reference splits into the stub's declarations plus its specs
    ref = [r for r in split_decls(prob["reference"]) if not r.lstrip().startswith(("/--", "example"))]
    decls = ref if len(ref) == len(stub) else stub
    m = re.search(r":=\s*sorry\s*$", d)
    if not m:
        return None
    head = d[:m.start()]
    name = re.search(r"(?:theorem|lemma|instance)\s+([\w.']+)", d)
    name = name.group(1) if name else None
    ns = prob.get("namespace") or ""
    # instance search: the term it builds names the subject's declarations by their full names
    if name:
        new = decls[:i] + [head + ":= inferInstance"] + decls[i + 1:]
        out = compile_source(problem_source(subj, prob, stub="\n\n".join(new),
                                            tail=f"set_option pp.explicit true in\nset_option pp.fullNames true in\n#print {name}"))
        if not re.search(r": error", out) and ":=" in out:
            typ, val = out.split(":=", 1)
            ids = lambda t: set(re.findall(r"[A-Za-z_][\w.']*", t))
            used = sorted(ids(val) - ids(typ) - {"inferInstance", "fun", "u", "v", "w"})
            if not any(ns and c.startswith(ns + ".") for c in used):
                return prob["slug"], name, "inferInstance, through " + ", ".join(used[:4])
    # one lemma: exact? names it, and the subject's own lemmas appear under their short names
    new = decls[:i] + [head + ":= by\n  exact?"] + decls[i + 1:]
    out = compile_source(problem_source(subj, prob, stub="\n\n".join(new)))
    if re.search(r": error", out):
        return None
    ctx = context_names(prob)
    for f in re.findall(r"Try this:\s*\n?\s*(?:\[apply\]\s*)?(exact [^\n]*)", out):
        if not (set(re.findall(r"[\w.']+", f)) & ctx):
            return prob["slug"], name or f"decl {i}", f.strip()
    return None

def main():
    args = sys.argv[1:]
    subject = args[0]
    only = set(args[args.index("--only") + 1:]) if "--only" in args else None
    subj, probs = load_bundle(subject)
    ok = allowed()
    jobs = []
    for p in probs:
        if (only and p["slug"] not in only) or p["slug"] in ok:
            continue
        for i, d in enumerate(split_decls(p["stub"])):
            if is_theorem(d):
                jobs.append((subj, p, i))
    for r in run_all(jobs, try_decl):
        if r:
            print(f"{r[0]}: {r[1]} closes by `{r[2]}`")


if __name__ == "__main__":
    main()
