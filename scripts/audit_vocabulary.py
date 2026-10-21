"""Vocabulary audit: does each solution use only what the course has taught by that point?

    uv run --with pyyaml python scripts/audit_vocabulary.py SUBJECT \
        --prior ../polya-basic/.lake/polya/bundles/settheory [--prior ...] \
        [--solutions NAME=DIR ...] [--out DIR]

A `--prior` is a subject's slug in this project or the path of a bundle directory, so that the
prior subjects of another repository (polya-basic's, extracted there) count as the baseline.

The vocabulary of a problem is
  * the baseline: names written in backticks in the prior subjects' prose, and the tactics and
    Mathlib names their reference proofs use (what a student who finished them has worked with);
  * the problem's context: every declaration above the stub, and every name the stub writes;
  * the subject's prose so far: every name in backticks in the concept descriptions, preambles
    and descriptions of this problem and every earlier one.

Each solution (the reference, and any directory of agent solutions laid out as DIR/<slug>/*.lean,
the newest file taken) is read token by token. A token that names a global constant or a tactic
and is not in the vocabulary is reported. Names reached by dot notation on a local (`hU.mono`)
are reported by their last component unless some vocabulary name ends in it.

Writes DIR/audit.csv (one row per problem and solution) and DIR/audit_summary.md (the most
frequent untaught items, with the problems that need them). See AUDIT.md."""

import argparse
import collections
import csv
import glob
import json
import os
import re
import sys

from problem_files import ROOT, compile_source, load_bundle, run_all

TACTICS = set("""
    intro intros rintro exact exacts apply refine refine' rw rwa rewrite erw nth_rewrite rfl constructor
    cases rcases obtain use exists existsi have haveI letI let show change calc simp simp_all simpa
    dsimp norm_num linarith nlinarith positivity omega ring ring_nf field_simp by_contra by_contra!
    by_cases exfalso left right ext funext trivial assumption contradiction absurd push_neg push
    contrapose contrapose! specialize choose choose! induction unfold delta classical decide
    native_decide aesop tauto grind gcongr congr congrArg convert subst symm trans first try repeat
    all_goals any_goals iterate split_ifs split infer_instance inferInstance exact_mod_cast norm_cast
    push_cast lift set generalize revert clear rename_i next case nomatch fin_cases interval_cases
    filter_upwards beta_reduce whnf apply_fun nontriviality on_goal swap rotate_left rotate_right
    and_intros constructorm casesm rcases' wlog bound fun_prop continuity measurability""".split())
SYNTAX = set("""fun by at with do then else if this where in from for match return mut let have show
    Type Prop Sort True False true false theorem lemma def instance example noncomputable structure
    namespace open section end variable universe private protected deriving extends sorry
    _ u v w x y z""".split())
IDENT = re.compile(r"(?<![\w.'])([A-Za-z_][\w']*(?:\.[\w']+)*)")


def strip_comments(code):
    code = re.sub(r"/-.*?-/", " ", code, flags=re.S)
    return re.sub(r"--[^\n]*", " ", code)


def tokens(code):
    code = strip_comments(code)
    code = re.sub(r'"[^"\n]*"', " ", code)
    return [m.group(1) for m in IDENT.finditer(code)]


def prose_tokens(text):
    out = set()
    for span in re.findall(r"`([^`\n]+)`", text or ""):
        out.update(tokens(span))
    return out


def declared_names(lean):
    names = set()
    for m in re.finditer(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|protected\s+|private\s+)*"
                         r"(?:theorem|lemma|def|instance|structure|class|abbrev|inductive)\s+([\w.']+)",
                         lean, re.M):
        names.add(m.group(1))
    for m in re.finditer(r"^\s{2}(\w+)\s*(?:⦃|\{|\(|:)", lean, re.M):  # structure and class fields
        names.add(m.group(1))
    return names


def with_suffixes(names):
    out = set(names)
    for n in names:
        parts = n.split(".")
        for i in range(1, len(parts)):
            out.add(".".join(parts[i:]))
    return out


def baseline(prior):
    words = set()
    for subject in prior:
        _, probs = load_bundle(subject)
        for p in probs:
            words |= prose_tokens(p.get("statement")) | prose_tokens(p.get("description"))
            words |= {t for t in tokens(p.get("reference") or "")}
    return words


def latest_solution(d):
    files = sorted(glob.glob(os.path.join(d, "*.lean")), key=os.path.getmtime)
    return open(files[-1]).read() if files else None


def resolve(job):
    """Which of these tokens are global constants in the problem's context?"""
    subj, prob, toks = job
    if not toks:
        return prob["slug"], set()
    imports = "\n".join("import " + m for m in subj["environment"]["modules"])
    ns = prob.get("namespace")
    stub = prob["stub"]
    checks = "\n".join(f"#check @{t}" for t in sorted(toks))
    body = f"namespace {ns}\n{stub}\n{checks}\nend {ns}\n" if ns else f"{stub}\n{checks}\n"
    src = f"{imports}\n{prob.get('preamble', '')}\n{body}"
    out = compile_source(src)
    lines = src.splitlines()
    bad = set()
    for m in re.finditer(r"<problem>:(\d+):\d+: error", out):
        line = lines[int(m.group(1)) - 1]
        if line.startswith("#check @"):
            bad.add(line[len("#check @"):])
    return prob["slug"], set(toks) - bad


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("subject")
    ap.add_argument("--prior", action="append", default=[])
    ap.add_argument("--solutions", action="append", default=[], help="NAME=DIR")
    ap.add_argument("--out", default=os.path.join(ROOT, "audit"))
    ap.add_argument("--vocab-only", action="store_true",
                    help="write DIR/vocab/<slug>.json (each problem's vocabulary) and stop")
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    subj, probs = load_bundle(a.subject)
    base = baseline(a.prior)
    concept_text = {c["slug"]: c["description"] for c in subj["concepts"]}

    if a.vocab_only:
        os.makedirs(os.path.join(a.out, "vocab"), exist_ok=True)
        taught = set(base)
        for p in probs:
            taught |= prose_tokens(p.get("statement")) | prose_tokens(p.get("description"))
            for c in p.get("concepts", []):
                taught |= prose_tokens(concept_text.get(c))
            vocab = with_suffixes(taught | declared_names(p.get("preamble", ""))
                                  | set(p.get("stub_names") or []) | set(tokens(p["stub"])))
            shown = sorted(t for t in taught if t in TACTICS or re.search(r"[._A-Z]", t))
            json.dump({"vocab": sorted(vocab), "shown": shown},
                      open(os.path.join(a.out, "vocab", p["slug"] + ".json"), "w"))
        return

    sols = {}  # (slug, name) -> code
    for p in probs:
        sols[(p["slug"], "reference")] = re.sub(r"/-- @spec -/.*?(?=\n\n|\Z)", "", p.get("reference") or "", flags=re.S)
    for spec in a.solutions:
        name, d = spec.split("=", 1)
        for p in probs:
            code = latest_solution(os.path.join(d, p["slug"]))
            if code:
                sols[(p["slug"], name)] = code

    # candidate global names per problem: every non-syntax, non-tactic token whose head is not local-looking
    cands = collections.defaultdict(set)
    for (slug, _), code in sols.items():
        for t in tokens(code):
            if t in SYNTAX or t in TACTICS or re.fullmatch(r"[a-zA-Z][₀-₉']*|h\w*|ih\w*", t.split(".")[0]):
                continue
            cands[slug].add(t)
    jobs = [(subj, p, cands[p["slug"]]) for p in probs]
    globals_ = dict(run_all(jobs, resolve, workers=6))

    rows, freq, where = [], collections.Counter(), collections.defaultdict(set)
    taught = set(base)
    for p in probs:
        taught |= prose_tokens(p.get("statement")) | prose_tokens(p.get("description"))
        for c in p.get("concepts", []):
            taught |= prose_tokens(concept_text.get(c))
        vocab = with_suffixes(taught | declared_names(p.get("preamble", "")) | set(p.get("stub_names") or [])
                              | set(tokens(p["stub"])))
        for name in ["reference"] + [s.split("=")[0] for s in a.solutions]:
            code = sols.get((p["slug"], name))
            if code is None:
                continue
            missing = set()
            for t in tokens(code):
                head = t.split(".")[0]
                if t in TACTICS:
                    if t not in vocab:
                        missing.add(t)
                elif t in globals_.get(p["slug"], set()):
                    if t not in vocab and t.split(".")[-1] not in vocab:
                        missing.add(t)
                elif "." in t and re.fullmatch(r"[a-z]\w*|h\w*", head):
                    field = t.split(".")[-1]
                    if not field.isdigit() and field not in vocab:
                        missing.add("." + field)
            rows.append({"seq": p["seq"], "slug": p["slug"], "solution": name,
                         "untaught": " ".join(sorted(missing)), "count": len(missing)})
            for m in missing:
                freq[(name, m)] += 1
                where[(name, m)].add(p["slug"])

    with open(os.path.join(a.out, "audit.csv"), "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)
    names = ["reference"] + [s.split("=")[0] for s in a.solutions]
    with open(os.path.join(a.out, "audit_summary.md"), "w") as fh:
        for n in names:
            sub = [r for r in rows if r["solution"] == n]
            fh.write(f"## {n}: {sum(1 for r in sub if r['count'])} of {len(sub)} solutions use something untaught\n\n")
            for (nm, item), k in sorted(((k, v) for k, v in freq.items() if k[0] == n), key=lambda kv: -kv[1]):
                fh.write(f"- `{item}` ({k}): {', '.join(sorted(where[(nm, item)])[:8])}\n")
            fh.write("\n")
    print(open(os.path.join(a.out, "audit_summary.md")).read()[:6000])


if __name__ == "__main__":
    main()
