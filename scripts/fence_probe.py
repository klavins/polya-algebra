"""The fence probe of STYLE.md: compile a scratch file that imports only the fence, nothing of
this repository, and ask for two lists of names. The names the subject teaches (`Group` first)
must be UNKNOWN; the tools it uses must be KNOWN; and a few instances must be absent or present.
Run it before adding an import, with the candidate module as an argument. The test is per
subject, since the publisher checks every problem under the union of all sections' imports.

    python3 scripts/fence_probe.py                          # the fence of STYLE.md
    python3 scripts/fence_probe.py Mathlib.Data.Fin.Basic   # the fence plus a candidate module
    python3 scripts/fence_probe.py --verbose                # and Lean's own output

Prints one line per name that fails its test, and `fence ok` when none does."""

import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

FENCE = [
    "Mathlib.Data.Fintype.Card",
    "Mathlib.Data.Fintype.EquivFin",
    "Mathlib.Logic.Equiv.Fin.Basic",
    "Mathlib.Logic.Equiv.Defs",
    "Mathlib.Data.Set.Basic",
    "Mathlib.Data.Setoid.Basic",
    "Mathlib.Algebra.Quotient",
    "Mathlib.Order.Notation",
    "Mathlib.Data.Nat.Find",
    "Mathlib.Data.Int.Init",
]

# what the subject teaches: every one of these must be an unknown identifier under the fence
UNKNOWN = """
    Group CommGroup Monoid Semigroup MonoidHom MulEquiv Subgroup Subgroup.center Subgroup.closure
    Subgroup.zpowers Subgroup.Normal Subgroup.index IsCyclic orderOf Nat.Prime Multiplicative ZMod
    DihedralGroup QuaternionGroup MulAction MulAction.orbit MulAction.stabilizer ConjAct IsPGroup
    QuotientGroup.mk QuotientGroup.leftRel Finset.sum Fintype.card_prod
    mul_assoc one_mul mul_one inv_mul_cancel mul_inv_cancel inv_mul_cancel_left mul_inv_cancel_left
    mul_inv_cancel_right inv_mul_cancel_right mul_eq_left mul_eq_right left_inv_eq_right_inv
    inv_eq_of_mul_eq_one_right inv_inv inv_one inv_injective mul_inv_rev mul_left_cancel
    mul_right_cancel mul_left_cancel_iff mul_right_cancel_iff eq_inv_mul_iff_mul_eq Group.ofLeftAxioms
    Fintype.exists_ne_map_eq_of_card_lt Finset.card_product finRotate
    ZMod.ext ZMod.val_add ZMod.val_mul ZMod.val_one ZMod.val_inv card_zmod mul_comm mul_left_comm
    mul_right_comm prod_mul_def DihedralGroup.r DihedralGroup.equivProd card_dihedral
    Equiv.Perm.permGroup Prod.instGroup
""".split()

# the tools: every one of these must be known under the fence
KNOWN = """
    Fintype Fintype.card Fintype.card_congr Fintype.card_le_of_injective Fintype.card_fin
    Fintype.card_pos Fintype.ofSurjective Fintype.ofEquiv Fintype.equivFin Fintype.card_subtype_le
    Fintype.decidableForallFintype Fintype.decidableExistsFintype Finite.injective_iff_surjective
    Finset Finset.univ Finset.induction_on Finset.card_union_of_disjoint Finset.filter
    finProdFinEquiv finTwoEquiv Quotient.fintype
    Equiv Equiv.Perm Equiv.ext Equiv.ofBijective Equiv.prodCongr Equiv.sigmaFiberEquiv
    Equiv.bijective Equiv.symm_apply_apply Equiv.apply_symm_apply Equiv.refl Equiv.trans Equiv.symm
    Set Set.ext Set.range Set.mem_range Set.mem_image Set.image_union Set.image_eq_range
    Set.mem_setOf_eq Set.mem_union Set.univ Set.image_univ Subtype.val_injective Subtype.ext
    Setoid Setoid.ker Quotient Quotient.sound Quotient.exact Quotient.eq Quotient.ind
    Quotient.inductionOn₂ Quotient.lift Quotient.lift₂ Quotient.out Quotient.out_eq
    Quotient.mk_surjective Quotient.lift_mk
    HasQuotient Top Bot Min Max
    Nat.find Nat.find_spec Nat.find_min' Nat.find_eq_iff Nat.find_min
    Int.induction_on Int.add_assoc Int.zero_add Int.add_zero Int.add_left_neg Int.add_right_neg
    Int.negSucc_eq Int.emod Int.toNat Int.emod_nonneg Int.emod_lt_of_pos Int.emod_emod_of_dvd
    Inv Pow SMul NeZero Nat.pos_of_neZero
    Nat.mod_lt Nat.mod_eq_of_lt Nat.mod_add_mod Nat.add_mod_mod Nat.add_mod Nat.mod_self
    Nat.sub_add_cancel Nat.mod_add_div Nat.pow_dvd_pow Nat.mod_mod Nat.mod_two_eq_zero_or_one
    Nat.gcd Nat.gcd_dvd_left Nat.dvd_gcd Nat.Coprime Nat.coprime_iff_gcd_eq_one
    Nat.Coprime.dvd_of_dvd_mul_left Nat.Coprime.dvd_of_dvd_mul_right Nat.Coprime.pow_left
    Nat.Coprime.eq_one_of_dvd Nat.decidableBallLT
    Fin Fin.ext Fin.ext_iff Fin.isLt Fin.is_lt Fin.mk
    Function.Injective Function.Surjective Function.Bijective Function.Injective.comp
    Function.LeftInverse.injective Function.Injective.of_comp Equivalence
    Nat.lt_irrefl Nat.le_antisymm Classical.choice
    Nat.add_assoc Nat.zero_add Nat.add_zero Nat.add_comm Nat.le_of_lt Nat.add_sub_of_le Int.add_comm
    Prod.mul_def OfNat
""".split()

# instances: `#synth` lines that must fail (`-`) or succeed (`+`)
SYNTH = [
    "- Inv ℤ",
    "- Inv (Equiv.Perm (Fin 3))",
    "- Fintype (Fin 3 × Bool)",
    "- Fintype (Equiv.Perm (Fin 3))",
    "- Mul (Equiv.Perm (Fin 3))",
    "- Inv (Fin 3 × Bool)",
    "- Fintype (Fin 2 × Fin 3)",
    "+ One ℤ",
    "+ Fintype (Fin 4)",
    "+ Fintype Bool",
    "+ DecidableEq (Equiv.Perm (Fin 3))",
    "+ Decidable (∀ x : Fin 4, x + x + x + x = 0)",
    "+ Mul (ℕ × ℕ)",
]


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    verbose = "--verbose" in sys.argv
    lines = [f"import {m}" for m in FENCE + args] + [""]
    tests = []  # (kind, name): kind in unknown/known/absent/present
    for n in UNKNOWN:
        lines.append(f"#check @{n}")
        tests.append(("unknown", n))
    for n in KNOWN:
        lines.append(f"#check @{n}")
        tests.append(("known", n))
    for s in SYNTH:
        lines.append(f"#synth {s[2:]}")
        tests.append(("absent" if s[0] == "-" else "present", s[2:]))
    first = len(FENCE) + len(args) + 2  # 1-based line of the first test (the imports, a blank line)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write("\n".join(lines) + "\n")
        path = f.name
    try:
        r = subprocess.run(["lake", "env", "lean", path], cwd=ROOT, capture_output=True, text=True)
        out = r.stdout + r.stderr
    finally:
        os.unlink(path)
    errs = {int(m.group(1)) for m in re.finditer(re.escape(path) + r":(\d+):\d+: error", out)}
    bad = 0
    for i, (kind, name) in enumerate(tests):
        failed = (first + i) in errs
        if kind == "unknown" and not failed:
            print(f"KNOWN but must be unknown: {name}"); bad += 1
        elif kind == "known" and failed:
            print(f"unknown but must be known: {name}"); bad += 1
        elif kind == "absent" and not failed:
            print(f"instance FOUND but must be absent: {name}"); bad += 1
        elif kind == "present" and failed:
            print(f"instance absent but must be present: {name}"); bad += 1
    if verbose:
        print(out)
    if bad == 0:
        print("fence ok")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
