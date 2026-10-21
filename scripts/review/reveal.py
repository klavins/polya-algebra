"""Show the author's reference solution for one problem. Use ONLY after your own
solution PASSes check.py, or after you have given up (say so in your report).

usage: python reveal.py SLUG"""
import os, sys
from pathlib import Path
import yaml
REPO = Path(os.environ.get("POLYA_REPO", "/Users/ericklavins/Code/polya/polya-algebra"))
p = yaml.safe_load((REPO / ".lake/polya/bundles/grouptheory/problems" / f"{sys.argv[1]}.yaml").read_text())
print(p["reference"])
