"""Grade a student's solution the way Polya does, without showing the reference or spec.

usage: python check.py SLUG SOLUTION.lean

SOLUTION.lean holds the student's region: the starting code with every `sorry` replaced
(keep any given declarations from the starting code). Prints PASS, or FAIL with the
student-facing reason and diagnostics.
"""
import os
import sys
from pathlib import Path

import yaml

REPO = Path(os.environ.get("POLYA_REPO", "/Users/ericklavins/Code/polya/polya-algebra"))
BUNDLE = Path(os.environ.get("POLYA_BUNDLE", str(REPO / ".lake/polya/bundles/grouptheory")))
sys.path.insert(0, str(REPO / ".lake/packages/polya-publisher"))
from polya.check import service  # noqa: E402

slug, solution = sys.argv[1], Path(sys.argv[2]).read_text()
p = yaml.safe_load((BUNDLE / "problems" / f"{slug}.yaml").read_text())
env = yaml.safe_load((BUNDLE / "subject.yaml").read_text())["environment"]
v = service.check(header=service.import_header(env["modules"]), preamble=p["preamble"],
                  text=solution, spec=p["spec"], stub_names=p.get("stub_names") or [],
                  env=REPO, kind=p.get("kind", "theorem"),
                  givens=service.given_names(p["stub"]), namespace=p.get("namespace", ""))
if v.passed:
    print(f"PASS ({v.elapsed_s:.1f}s)")
else:
    print(f"FAIL: {v.reason}")
    if v.diagnostics:
        print(v.diagnostics)
    for f in v.spec_failures:
        print(f"spec not met: {f.statement}\n  {f.error}")
