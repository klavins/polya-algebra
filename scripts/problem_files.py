"""Shared helpers for the bundle checks: load a subject's bundle and write, for one problem, the
Lean file a student starts from (imports, the context, the stub in its namespace), with each
`sorry` of a theorem optionally replaced, and compile it under the project's options.

Run the checks with `uv run --with pyyaml python scripts/<check>.py SUBJECT`."""

import concurrent.futures
import glob
import os
import re
import subprocess
import tempfile

import yaml

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# the [leanOptions] of lakefile.toml, which `lake env lean` does not apply by itself
LEAN_OPTIONS = [
    "-Dpp.unicode.fun=true",
    "-DrelaxedAutoImplicit=false",
    "-Dweak.linter.mathlibStandardSet=true",
    "-DmaxSynthPendingDepth=3",
]


def load_bundle(subject):
    """A subject's bundle: by slug under this project's .lake/polya/bundles/, or by the path of a
    bundle directory (another repository's, for a prior subject)."""
    base = subject if os.path.isdir(subject) else os.path.join(ROOT, ".lake", "polya", "bundles", subject)
    subj = yaml.safe_load(open(os.path.join(base, "subject.yaml")))
    probs = [yaml.safe_load(open(f)) for f in glob.glob(os.path.join(base, "problems", "*.yaml"))]
    return subj, sorted(probs, key=lambda p: p["seq"])


def split_decls(stub):
    """The stub's declarations, each a string, in order."""
    starts = re.compile(r"^(@\[.*\]\s*)?(noncomputable\s+)?(theorem|lemma|def|instance|structure|class|abbrev|example)\b")
    decls, cur = [], []
    for line in stub.splitlines():
        if starts.match(line) and cur:
            decls.append("\n".join(cur).rstrip())
            cur = []
        cur.append(line)
    if cur:
        decls.append("\n".join(cur).rstrip())
    return [d for d in decls if d.strip()]


def is_theorem(decl):
    return re.match(r"^(@\[.*\]\s*)?(theorem|lemma|instance)\b", decl.strip()) is not None


def problem_source(subj, prob, stub=None, tail=""):
    imports = "\n".join("import " + m for m in subj["environment"]["modules"])
    ns = prob.get("namespace")
    body = stub if stub is not None else prob["stub"]
    if ns:
        body = f"namespace {ns}\n\n{body}\n\n{tail}\nend {ns}\n"
    else:
        body = f"{body}\n\n{tail}\n"
    return f"{imports}\n{prob.get('preamble', '')}\n{body}"


def compile_source(src, timeout=600):
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, dir=tempfile.gettempdir()) as f:
        f.write(src)
        path = f.name
    try:
        r = subprocess.run(["lake", "env", "lean", *LEAN_OPTIONS, path], cwd=ROOT,
                           capture_output=True, text=True, timeout=timeout)
        out = (r.stdout + r.stderr).replace(path, "<problem>")
    except subprocess.TimeoutExpired:
        out = "<problem>:0:0: error: timed out"
    finally:
        os.unlink(path)
    return out


def run_all(jobs, fn, workers=4):
    with concurrent.futures.ThreadPoolExecutor(workers) as ex:
        return list(ex.map(fn, jobs))
