# Style for PolyaAlgebra subjects

The house rules are the `polya-author` skill's; this file records what is particular to this
repository, and it wins where the two differ. It was seeded from `polya-topology/STYLE.md` on
2026-10-21, before the first section of Group Theory, with every rule the Profinite Spaces
build learned on a finished section (`BEST_PRACTICES.md` in `polya-publisher`, Step 3) stated
here up front. The plan is `plans/GROUP_THEORY_PLAN.md`; what the student knows on arrival is
`plans/STUDENT_BACKGROUND.md`.

## The fence: a student builds what a subject teaches

A section's imports are the whole of the library a student may use in it, and one rule sets
them: **a student builds what the subject teaches, so the fence excludes the Mathlib modules
that hold it.** Group Theory teaches groups themselves, so its fence keeps out
`Mathlib.Algebra.Group.Defs` and every module that imports it, which is nearly every module
that touches algebra. Under the fence the name `Group` must be an unknown identifier, and with
it `Monoid`, `MonoidHom`, `Subgroup`, `ZMod`, `DihedralGroup`, `orderOf`, `MulAction` and the
rest of Mathlib's group theory. What the fence supplies is the language the subject is written
in: sets, functions and equivalences, finite types and their cardinalities, setoids and
quotients, `Nat.find`, induction on `ℤ`, and the notation classes `Inv`, `Pow` and `SMul`,
which carry no algebra. Core Lean supplies the arithmetic: `ℤ`, `%`, `Nat.gcd`, `Nat.Coprime`,
`omega` and `decide`.

The fence of `GroupTheory/Prerequisites.lean`, and of every later section of the subject:

```lean
import Mathlib.Data.Fintype.Card        -- Finset, Fintype, Fintype.card and its lemmas; decide over a finite type
import Mathlib.Data.Fintype.EquivFin    -- Fintype.equivFin
import Mathlib.Logic.Equiv.Fin.Basic    -- finProdFinEquiv
import Mathlib.Logic.Equiv.Defs         -- Equiv, Equiv.Perm
import Mathlib.Data.Set.Basic           -- Set, {x | p x}, f '' S, Set.range, ↥S
import Mathlib.Data.Setoid.Basic        -- Setoid; Quotient.sound, exact, inductionOn, lift
import Mathlib.Algebra.Quotient         -- the ⧸ notation (HasQuotient)
import Mathlib.Order.Notation           -- ⊤, ⊥, ⊓, ⊔ as classes
import Mathlib.Data.Nat.Find            -- Nat.find
import Mathlib.Data.Int.Init            -- Int.induction_on
```

**Before adding an import, run the probe:** `python3 scripts/fence_probe.py Mathlib.Some.Module`
compiles a scratch file that imports the fence and the candidate, nothing of this repository,
and asks for `Group` and the other names the subject defines, which must be unknown, and for
the tools, which must be known. Modules known to carry `Group`, and so refused:
`Mathlib.Data.Fintype.Prod`, `…Pi`, `…Sigma`, `…Sum`, `…Perm` (`Fintype.card_prod`,
`Fintype (α × β)`, `Fintype (Equiv.Perm α)`), `Mathlib.Data.Finset.Prod`,
`Mathlib.Algebra.BigOperators.*` (`Finset.sum`), `Mathlib.Data.Nat.Prime.*` and
`Mathlib.Data.Nat.GCD.Basic` (`Nat.Prime`), `Mathlib.Tactic.Ring`, `…Linarith`, `…NormNum`,
and everything under `Mathlib.Algebra.Group.*`, `Mathlib.GroupTheory.*` and `Mathlib.Data.ZMod.*`.
What the fence therefore lacks, and what stands in: products are counted by labelling through
`finProdFinEquiv`, not by `Fintype.card_prod`; the class equation is counted by blocks with
`Finset.induction_on` and `Finset.card_union_of_disjoint`, not by a sum; primes are the
student's; `Fintype (α × β)` and `Fintype (Equiv.Perm X)` are built where needed; the
arithmetic is `omega` and `decide`. `Quotient.fintype` is in the fence, so a quotient of a
finite type is finite under `open Classical` with nothing to build.

Two things follow from the rule being about what is taught, not about Mathlib.

- **The test is per subject, not per section.** The publisher builds one check environment for
  a subject, from the union of the root's and every section's imports, and checks every problem
  under it, so a module any section imports reaches every section. A name any section defines
  must be unknown under the union of the subject's imports, and a module that carries what an
  earlier section built cannot be added by a later one. When such a module gets in, every spec
  that states the shared name fails as `Ambiguous term`, because the check compiles it at the
  root with the subject's namespace opened, where the student's declaration and Mathlib's are
  both in scope (Profinite Spaces §7, 2026-10-10).
- **A module comes whole.** Mathlib's lemmas *about* what is imported are tools, not answers:
  `Fintype.card_congr`, `Quotient.sound` and `Nat.find_spec` are as fair here as
  `Set.Finite.induction_on` is in General Topology. What the student may not take from the
  fence is the thing the subject exists to build.

## Every new structure is the student's to define

Every algebraic notion this repository introduces is defined by the student, as a problem with
a `@spec`, before anything is proved about it: `Group` and `CommGroup`, the examples (`ZMod n`,
the symmetric and dihedral groups, the product), powers and `orderOf`, `Subgroup`, `closure`
and `zpowers`, `IsCyclic`, homomorphisms and isomorphisms, kernels and images, cosets, the
coset relation, `G ⧸ H`, `index`, `Nat.Prime`, `Subgroup.Normal`, the quotient group,
`MulAction`, orbits, stabilizers, `ConjAct`, `IsPGroup`. The owner's decision of 2026-10-21:
"The student should redefine as much as possible, including Group and Homomorphism. … the
Mathlib way of defining a group from One, Magma, etc. is a Mathlib API choice not a
pedagogical one." If a draft's first problem about a new notion is a theorem, the draft is
wrong (the Profinite Spaces lesson of 2026-10-06, recorded in `polya-topology/STYLE.md`).

The Prerequisites section is the one exception: it takes Mathlib's `Set`, `Equiv`, `Setoid`,
`Quotient` and `Fintype` as given, because they are the language the subject is written in,
not what it teaches.

There is no hand-over to Mathlib's `Group`, since it is outside the fence; the hand-over is the
first problem of the first later subject that imports Mathlib's algebra. What there is instead
is the **vocabulary rule** below: the student's definitions carry Mathlib's names, so that the
hand-over, when it comes, is cheap.

A **structure definition problem carries a `/-- @spec -/` naming its fields**, since the
generated shape check is nearly vacuous, and so does every `where`-bodied `def` and every
`Quotient.lift`. A class definition's spec binds it as an instance, `example (G : Type)
[Group G] …`.

## The running examples

Eight groups carry Group Theory, each defined in its second or third section from the
student's `Group` class, `ℕ` with `%`, `ℤ`, `Equiv` and `Bool`, and each returned to in later
sections: the trivial group `Unit`; `Bool` under `xor`; `ℤ` under addition; the student's
`ZMod n`, a structure holding `val : ℕ` with `val < n` and the operation `(a + b) % n`, owing
nothing to Mathlib's `ZMod` but the name; the symmetric groups `Equiv.Perm (Fin n)`; the
dihedral groups, an inductive over `ZMod n` with constructors `r` and `sr` and a four-line
table, Mathlib's shape; the Klein four-group as `DihedralGroup 2`; and the product `G × H`.
The rule for every concept after the examples: **its last problem, or its first after the
definition, instantiates the concept in the smallest running example that shows the
phenomenon**, with a numeric check where there is one, closed by `decide` when `n` is fixed.
A concept for which none of the eight shows anything takes the example the literature uses,
named in the plan's table. The student never needs a group that is not on this list.

No multiplication table is proved by hand. A small fact about a running example is one
`decide`; a concrete instance whose proof is a case analysis the student types is not worth a
problem (the skill's rule 7).

## Notation and names

**The group operation has its own symbol.** The class is `class Group (G : Type) extends Inv G`
with fields `mul` and `one`, the notations `a ∗ b` (`infixl:70`, typed `\ast`) and `𝟙` (typed
`\b1`), and the five equations of Milne's Definition 1.1. The reason is the examples: a group
is a set with *some* operation, and `ℤ` under addition, `ZMod n` under addition modulo `n`,
`Sₙ` under composition and `Dₙ` under its table are instances of one class, each with `a ∗ b`
meaning that group's operation, `(3 : ℤ) ∗ 4 = 7` by `rfl`. Mathlib's `*` and `1` cannot carry
this (`Mul ℤ` is multiplication, `One ℤ` the integer `1`); Mathlib keeps a second additive
hierarchy and the wrapper `Multiplicative` to avoid it, an API choice the owner has ruled out
(the plan's Decision 4). The prose says once, in the section that defines the class, that
Mathlib writes `a * b` and `1`.

**Names follow Mathlib** all the same, so that the arrival at Mathlib's algebra changes the
imports and not the vocabulary: `mul_assoc`, `one_mul`, `mul_one`, `inv_mul_cancel`,
`mul_inv_cancel`, `mul_left_cancel`, `mul_inv_rev`, `inv_inv`, `pow_succ`, `zpow_add`,
`orderOf_dvd_iff_pow_eq_one`; `Subgroup` with `carrier`, `one_mem'`, `mul_mem'`, `inv_mem'`;
`MulAction` with `one_smul`, `mul_smul`; `DihedralGroup` with `r` and `sr`;
`Subgroup.card_subgroup_dvd_card`, `QuotientGroup.quotientKerEquivRange`,
`MulAction.orbitEquivQuotientStabilizer`. Where Mathlib's shape is awkward for a beginner (its
`Subgroup` extends `Submonoid` and goes through `SetLike`; its `orderOf` goes through
`Function.minimalPeriod`; its `ZMod n` is a ring and `ℤ` at `n = 0`), the student's is the
textbook's shape under Mathlib's name, and the prose says once, at the definition, how
Mathlib's differs. A divergence is deliberate and recorded, in the problem that introduces it
and in the plan.

**`[NeZero n]`** carries the hypothesis `n ≠ 0` wherever `ZMod n`, `Fin n` or a residue needs
it, as Mathlib does; `Nat.pos_of_neZero n` reads it back as `0 < n`. The Prerequisites section
introduces it, on `residue`.

**Cardinality is `Fintype.card`** with a `[Fintype G]` hypothesis, since `Nat.card` is outside
the fence; a quotient gets its `Fintype` through `Quotient.fintype` under `open Classical in`,
and the prose at Lagrange's theorem says that Mathlib states it with `Nat.card`.

## One Mathlib idea at a time

**Never a Mathlib idea and a hard mathematical idea in one problem.** The owner's rule, and
the one the Profinite Spaces student review found broken most often. It is enforced in three
places.

1. **The Prerequisites section front-loads the Lean.** Every Mathlib or Lean device the
   subject uses and `polya-basic` did not teach is introduced there, on mathematics the student
   already has: Mathlib's `Set` and a set as a type, `Function.Injective`, `Equiv` and
   `Equiv.Perm`, `Fin n`, `where`-bodied definitions, `Fintype` and `Fintype.card` and `decide`
   over a finite type, counting by labelling, `ℤ` and `cases` on it, `%` and its lemmas,
   `Nat.find`, `Nat.Coprime`, `Equivalence` and `Setoid` (both core Lean's), `Quotient` with `sound`, `exact`,
   `lift` and `inductionOn`, `NeZero`, `open Classical in`. When a later section defines
   cosets, the quotient type is old.
2. **A device that cannot be separated from its mathematics is taught in a problem of its own,
   just before the problem that needs it**, and the plan names each: a class with its own
   notation (§2, the definition of `Group` itself); recursion for powers and `Int.induction_on`
   (§4); a `Membership` instance and the coercion of a subgroup to a type (§5); `CoeFun` for
   homomorphisms (§6); a `HasQuotient` instance (§7); `Quotient.lift₂` (§9); `extends SMul` and
   a type synonym with a copied instance (§11); `Finset.induction_on` (§12). A definition
   problem may carry the one Lean fact its shape needs, said in the description, and nothing
   more.
3. **Every section is checked against the rule before it is committed**, and the student
   review after each section asks the question verbatim: does any problem teach a new piece of
   mathematics and an unfamiliar piece of Mathlib at once?

A Lean device the mathematics does not reveal (`classical`, `show`, `(p := …)`, `haveI`, `‹_›`,
`@`) is motivated in prose once, at first use, and never explained again.

## Prose

A **concept description is at most 400 characters**: what the concept is, in a sentence, and
why the subject needs it. Nothing a problem already says, no worked example, no Lean, no
forward reference. The concept column is read beside the problems, not instead of them.

**A preamble opens with why the problem is here**, then the mathematics, then the notation the
student will write, introduced with "we write". It names the earlier subjects by their titles
("as Set Theory proved", "The Natural Numbers wrote the property in Lean's form"), never "we
built" or "our definition", since the reader does not share the author's history. A claim that
an earlier argument carries over must be true of its helpers: a lemma that was a problem in
`polya-basic` is not a Mathlib name, so say that the argument holds and name the Mathlib
lemmas that stand in for them. A preamble carries no Lean internals the student does not act
on, no aphorisms about method, no forward references, and no second telling of the concept.

**Show a background definition; do not describe it.** When a preamble brings in a type, class
or def of Lean's core or Mathlib that the problem builds or takes apart (`Equiv`, `Fintype`,
`Equivalence`, `Setoid`, `Int`, `Function.Injective`), put Lean's own definition in a fenced
`lean` block, trimmed to what the problem uses, and compile every such block in a scratch
namespace before publishing. Show it once, in the problem that first needs it.

**A description states the exercise as a textbook would**: the problem in English, ending
with what to do, "Show that …", "Define `f`, which …". Never a proof outline, never the
witness, never the order of steps, never "rewrite with X then Y". After the statement, and only
at first appearance, it may list Mathlib names or tactics the student has not met, as options
("Mathlib provides `X` and `Y`, which you may find useful"); a Lean gotcha the mathematics
cannot reveal; and, at a concrete type's first use, the instance Mathlib provides. In the
Prerequisites section, which introduces Mathlib's own library, the lists are longer, never
steps.

**A context fact the student did not prove in an exercise is introduced where it is used.**
A problem's context holds every declaration its reference depends on. When the reference uses a
theorem of an earlier section, the preamble or the description names it as available and says
where it comes from and what it says: "The context holds `mod_add_mod_eq_add_mod`, a theorem of
this subject's first section, which says …". Say where by position ("the first section", "the
previous section"), never by a title that sounds like a library. Naming the fact is not a proof
route: say that it is there and what it says, not where in the proof it goes. A helper list
that omits a needed context fact is worse than no list. Never name in prose a declaration the
context does not hold as if the student could use it.

**Mathlib only where the student can use it.** Student prose mentions Mathlib only to point at a
definition or theorem the student can use at that point. It never describes Mathlib's version of
something the subject keeps out or defines itself ("Mathlib's `Group` is built from `Mul`,
`One` and `Inv`", "as Mathlib does", "Mathlib's `ZMod` is a ring"), except in the one sentence
at a definition that records a deliberate divergence of shape. A thing that is not available is
"not available in this subject".

**Words the student has.** Subject, section, concept, problem, student. "Fence" is this file's
word for a section's imports; the prose says "the part of Mathlib this subject imports". No
author-to-agent asides ("not of Mathlib", "the plan says").

**Titles name the object**, in Title Case, using its standard or eponymous name when it has
one: "Lagrange's Theorem", "The Dihedral Groups", "The Class Equation". A definition's title
names the thing, a theorem's states the fact.

**Each term is defined in prose where it is first used, in one sense**, and the terminology
survey of `BEST_PRACTICES.md` 4f is run once per subject: *coset*, *index*, *order* (of a group,
of an element), *class*, *orbit*, *conjugate* are the ones to watch.

A problem's `@preamble` and `@description` together get **about 22 lines of 55 characters**,
17 to 27, the room the problem page has. Measure with `python3 scripts/check_budgets_lean.py
<file>` before extraction and `scripts/check_budgets.py` after. Cut first: forward references,
morals about method, a second telling of the concept, Lean mechanics met before. A problem
honestly over the budget is two problems.

## Binders

Bind a variable implicitly wherever that makes the proofs downstream read better, and let the
call sites decide it. A fact used **backwards** (rewritten into a goal, matched by `exact` or
`apply`, `.mp`/`.mpr` taken) has its variables fixed by the statement it lands in, so naming
them is noise: `mul_left_cancel h`, `e.symm_apply_apply`. A fact used **forwards** (applied to
a chosen witness, instantiated into a `have`) has to be given its arguments: `mul_assoc a b c`,
`pow_add a m n`, `Nat.find_min' h hm`. Look at every use in the subject; if none passes the
argument, make it implicit. A declaration nothing uses yet keeps explicit binders until
something does. For a structure's fields this matters most, since the reference is the context
every later problem compiles against: say in the description which fields are implicit.

## Specs

A spec must accept every *correct* encoding, not just the reference's: both binder styles (`by
apply M.symm`), both orientations of an `↔` (`by simp [M.eq_zero]`), and a conjunction in
either order. Do not use `first | exact … | exact …`: the unused branches raise
`linter.unusedTactic`, and warnings become errors under publish. Before publishing a structure,
compile its spec against variants of every field shape plus one wrong definition, which must
still fail; the scratch battery of 2026-10-21 is the pattern (`boolEquivFinTwo` built with
`⟨…⟩`, with `where`, as `finTwoEquiv.symm`, and swapped; `modSetoid` with the relation
reversed, as `Setoid.ker`, as `⟨…⟩`, and with `a = b` and `True` for the relation).

**A relation stated through a `Setoid` is checked through `change`.** Mathlib's `Setoid` applies
through `Setoid.r`, and `simp` and `grind` never rewrite there, so a spec cannot normalize a
student's orientation that way. What works: `constructor`, and in each direction `intro h`,
then `change _ = _ at h` or `change _ = _`, which exposes the equation up to definitional
unfolding, then `grind`, which closes it in either orientation. Test against the swapped
orientation, Mathlib's `Setoid.ker`, and a wrong definition.

**A `Quotient.lift` is checked by `rfl` on a representative**: `(residue n (Quotient.mk _ a)).val
= a % n := rfl` accepts the reference, an eta-expanded version, and `Fin.ofNat`, and rejects a
constant.

**A definition with a numeric value is checked by `decide`**: `boolEquivFinTwo false = 0 ∧
boolEquivFinTwo true = 1 := by decide`, `rot3 0 = 1 ∧ rot3 1 = 2 ∧ rot3 2 = 0 := by decide`.

## Proofs

No proof runs past fifteen lines; a structure definition counts one proof per field. When one
would, the way out is a lemma of its own, given its own problem and taught before the problem
that needs it. Reference proofs are the proof a student should write: tactic style, one step
per line, one goal per bullet, no packed `refine` with inline lambdas, `show` only where it
does not change the goal (the linter refuses it otherwise; `change` is the tactic that does),
and automation (`omega`, `decide`, `grind`) closing a goal, never replacing the argument. A
reference proof that uses something the course has not taught is a bug (the vocabulary audit
finds them); a Lean idiom met for the first time in a hard problem is the friction the student
review looks for.

Long prose lines in doc comments raise `linter.style.longLine` under `lake env lean`; they are
expected, as in `polya-topology`, and are not errors.

**The checker's context is the reference's closure.** A problem's context holds only the
earlier declarations its reference uses, so a student's correct proof through an earlier
theorem the reference did not use fails with `Unknown identifier` (the Naturals review's
finding, `BEST_PRACTICES.md` Part II). The policy is the owner's: fix it in the content. Where
the prose points at an earlier result ("by the two theorems of the previous concept"), the
reference uses it, and the description says the context holds it; otherwise the prose does not
invite it. Section 1 did this for `equiv_bijective` and `residue_bijective` after its review.

## Learned building §1 (2026-10-21)

- `omega` reads `Int.negSucc n` as `-(n + 1)` but treats `Int.ofNat n` and `↑n` as different
  atoms; a goal showing `Int.ofNat n` that holds by definition is closed by `rfl`. The prose
  says so where `cases` on `ℤ` is taught.
- `Setoid` and `Quotient` are core Lean's (`Setoid` is a `class`), and Lean prints
  `Quotient.mk s a` as `⟦a⟧` and `s a b` as `a ≈ b` whether or not `s` is an instance; a goal
  `a ≈ b` unfolds to the relation, which `exact` sees through. `Quotient.inductionOn`'s one
  case is named `h`; `induction q using Quotient.ind` has no usable case name.
- `Int.induction_on`'s cases are `zero`, `succ`, `pred`.
- A `decide` proof of a `Function.LeftInverse` field works directly; `Fintype.decidableForallFintype`
  is in the fence, so `∀ x : Fin 4, …` and equations in `Equiv.Perm (Fin 3)` are `decide`'s.
- A lemma named in the prose as usable "from here on" closes the problem it is named in, and
  the check accepts it; say "in later problems" instead.
- A one-name shortcut found by `check_stub_shortcuts.py` is replaced by the fact one step
  beyond (`int_cases`: a difference of naturals, not "a natural or its negative").
- The linter refuses a `show` that changes the goal (`linter.style.show`); references write
  the term (`(congrArg g ha).trans hb`) or `rw [Function.comp_apply, …]` instead, and the
  `rw`/`∘` gotcha is said in the prose at first use.
- Reviewers found the double teaching the author did not see in four problems of twenty-one;
  the warm-ups they proposed were each one line of Lean. Run the review after every section.

## Checks over a bundle

`scripts/` holds the mechanical checks, run after `lake exe polya extract grouptheory`:

- `python3 scripts/fence_probe.py [MODULE]` — the fence test above, before any import changes.
- `python3 scripts/check_budgets_lean.py PolyaAlgebra/GroupTheory/<File>.lean [--all]` — the
  prose budgets on a section file; `uv run --with pyyaml python scripts/check_budgets.py
  grouptheory` over the bundle.
- `uv run --with pyyaml python scripts/check_prose_names.py grouptheory` — every name the prose
  writes in backticks exists in the problem's context or in Mathlib; exceptions, with reasons,
  in `scripts/prose_names_ok.txt`.
- `uv run --with pyyaml python scripts/check_stub_shortcuts.py grouptheory` — each theorem of
  each stub tried with instance search and `exact?`; a warm-up that proves a Mathlib fact by hand
  before naming it is intended, and listed in `scripts/stub_shortcuts_ok.txt` with the reason.
- `uv run --with pyyaml python scripts/audit_vocabulary.py grouptheory --prior
  ../polya-basic/.lake/polya/bundles/<subject> …` (one `--prior` per subject of polya-basic,
  extracted there) — the vocabulary audit of `AUDIT.md` in `polya-topology`: does each
  reference proof use only what the course has taught by that point? The baseline is
  `polya-basic`'s five subjects. Section 1 passed it on 2026-10-21 with 0 of 21.

**The student review after each section** uses `scripts/review/`: `make_view.py BUNDLE OUT`
renders the bundle answer-free (concepts, preambles, descriptions, starting code), `check.py
SLUG FILE.lean` grades an answer with the publisher's own checker in the problem's real context
(run it with `.lake/packages/polya-publisher/.venv/bin/python`), `reveal.py SLUG` prints the
reference, and `PROMPT.md` is the reviewers' brief, with `{REPO}` and `{REVIEW_DIR}` to fill in
and `{CONCEPT}`, `{FIRST}`, `{LAST}`, `{NUM}` per concept. One agent per concept, at most three
at a time, each compiling only through `check.py`; a copy of `plans/STUDENT_BACKGROUND.md` goes
in the review directory, since the reviewers may not read `plans/`. The brief asks the rule's
question verbatim.

## Sources

The subjects follow published treatments for their selection and order of results, and name
them in `@reference` lines. Group Theory follows J. S. Milne's *Group Theory* notes, which are
CC BY-NC-SA 4.0 and so a syllabus only: the prose, the Lean and the problems are written here,
and no sentence, example or exercise is taken from them. Subjects carry CC BY 4.0, the
repository's default, and the text of it is the `LICENSE` file in each subject's directory.
