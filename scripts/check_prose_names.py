"""Every name a problem's preamble or description writes in backticks must exist where the student
is: in the problem's context, in the part of Mathlib the subject imports, or in the stub itself.
A name the prose offers that the context does not hold sends the student after a lemma they
cannot use (Profinite Spaces review, 2026-10-14: `pi_coarsest`, `inverseLimit.t2Space`,
`IsProfinite.t2Space`, `isProfinite_iff`).

    uv run --with pyyaml python scripts/check_prose_names.py grouptheory [--only SLUG ...]

Prints, for each problem, the backticked names that do not resolve; prints nothing for a clean
problem. Variables and hypotheses of the stub, tactics and keywords are skipped."""

import os
import re
import sys

from problem_files import ROOT, compile_source, load_bundle, problem_source, run_all

OK_FILE = os.path.join(ROOT, "scripts", "prose_names_ok.txt")


def allowed():
    """`slug: name, name` lines: names a problem's prose writes on purpose though the context lacks
    them, such as a name of General Topology or the field of a structure the stub fills in."""
    ok = {}
    if os.path.exists(OK_FILE):
        for line in open(OK_FILE):
            line = line.split("#")[0].strip()
            if ":" in line:
                slug, names = line.split(":", 1)
                ok.setdefault(slug.strip(), set()).update(n.strip() for n in names.split(","))
    return ok

IDENT = re.compile(r"^@?[A-Za-z_][\w.'!?]*$")
SKIP = set("""
    by fun let have show from at with do then else if this where in
    intro intros rintro obtain exact apply refine rw rwa simp simp_all constructor cases rcases
    induction ext funext classical choose use exists trivial rfl decide omega grind norm_num
    linarith positivity contrapose push by_contra by_cases unfold change calc congr specialize
    letI haveI inferInstance infer_instance sorry aesop tauto exfalso left right split
    noncomputable def theorem lemma instance structure class abbrev example namespace open
    universe variable section end extends deriving Type Prop Sort True False
    """.split())


def candidates(prob):
    text = (prob.get("statement") or "") + "\n" + (prob.get("description") or "")
    stub_words = set(re.findall(r"[\w']+", prob["stub"]))
    out = []
    for span in re.findall(r"`([^`\n]+)`", text):
        span = span.strip()
        if not IDENT.match(span) or "ᶜ" in span:
            continue
        name = span.lstrip("@")
        head = name.split(".")[0]
        if name in SKIP or head in SKIP or len(head) <= 1:
            continue
        if re.fullmatch(r"h[\w'₀-₉]*", head) and head not in ("hom",):
            continue  # a hypothesis the student names
        if head in stub_words and head[0].islower() and "_" not in head and len(head) <= 3:
            continue  # a variable of the stub
        if name not in out:
            out.append(name)
    return out


def check(job):
    subj, prob = job
    names = candidates(prob)
    if not names:
        return prob["slug"], []
    stub_lines = prob["stub"].count("\n") + 1
    checks = "\n".join(f"#check @{n}" for n in names)
    src = problem_source(subj, prob, tail=checks)
    out = compile_source(src)
    # map each failing #check line back to its name
    lines = src.splitlines()
    bad = []
    for m in re.finditer(r"<problem>:(\d+):\d+: error[^:]*: (.*)", out):
        ln = int(m.group(1))
        line = lines[ln - 1] if ln - 1 < len(lines) else ""
        if line.startswith("#check @"):
            n = line[len("#check @"):]
            if n not in bad:
                bad.append(n)
    # an error anywhere else means the file itself failed: a stub whose body is the answer (an
    # inductive's constructors) cannot compile the names that use it, so try the reference, and
    # say so only when that fails too
    other = [m.group(0) for m in re.finditer(r"<problem>:(\d+):\d+: error.*", out)
             if not lines[int(m.group(1)) - 1].startswith("#check @")]
    if other and prob.get("reference"):
        return check_with(subj, prob, names, stub=prob["reference"])
    return prob["slug"], bad + [f"(file error) {o}" for o in other[:2]]


def check_with(subj, prob, names, stub):
    checks = "\n".join(f"#check @{n}" for n in names)
    src = problem_source(subj, prob, stub=stub, tail=checks)
    out = compile_source(src)
    lines = src.splitlines()
    bad = []
    for m in re.finditer(r"<problem>:(\d+):\d+: error[^:]*: (.*)", out):
        ln = int(m.group(1))
        line = lines[ln - 1] if ln - 1 < len(lines) else ""
        if line.startswith("#check @"):
            n = line[len("#check @"):]
            if n not in bad:
                bad.append(n)
    other = [m.group(0) for m in re.finditer(r"<problem>:(\d+):\d+: error.*", out)
             if not lines[int(m.group(1)) - 1].startswith("#check @")]
    return prob["slug"], bad + [f"(file error) {o}" for o in other[:2]]


def main():
    args = sys.argv[1:]
    subject = args[0]
    only = set(args[args.index("--only") + 1:]) if "--only" in args else None
    subj, probs = load_bundle(subject)
    jobs = [(subj, p) for p in probs if not only or p["slug"] in only]
    ok = allowed()
    for slug, bad in run_all(jobs, check):
        bad = [b for b in bad if b not in ok.get(slug, set())]
        if bad:
            print(f"{slug}: " + ", ".join(bad))


if __name__ == "__main__":
    main()
