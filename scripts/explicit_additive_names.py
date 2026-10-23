"""Write the additive name into every bare `@[to_additive]` mark of a section file, from the
pairs `scripts/additive_names.lean` prints (`multiplicative additive`, one per line, on stdin).

    lake env lean scripts/additive_names.lean | python3 scripts/explicit_additive_names.py FILE…

The closure of the publisher finds a declaration by the names written in the source, so a copy
that a later problem cites must have its name written there: `@[to_additive add_left_cancel]`.
The name is written in full below the subject's namespace (`AddSubgroup.add_mem`), as
`to_additive` reads a dotted name."""
import re
import sys

pairs = {}
for line in sys.stdin:
    parts = line.split()
    if len(parts) == 2 and parts[0].startswith("GroupTheory."):
        pairs[parts[0].removeprefix("GroupTheory.")] = parts[1].removeprefix("GroupTheory.")

DECL = re.compile(r"@\[to_additive\]\n((?:/--.*?-/\n)?(?:open [^\n]* in\n)?(?:noncomputable )?"
                  r"(?:theorem|instance|def|abbrev|lemma) ([^\s{(\[:]+))", re.S)
for path in sys.argv[1:]:
    src = open(path).read()
    missing = []

    def name(m):
        mul = m.group(2)
        add = pairs.get(mul)
        if add is None:
            missing.append(mul)
            return m.group(0)
        return f"@[to_additive {add}]\n{m.group(1)}"

    src = DECL.sub(name, src)
    open(path, "w").write(src)
    print(path, "unnamed:", missing or "none")
