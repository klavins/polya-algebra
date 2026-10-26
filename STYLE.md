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
quotients, `Nat.find`, induction on `ℤ`, and the notation classes `Mul`, `One`, `Inv`, `Pow` and `SMul`,
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
a `@spec`, before anything is proved about it: `Group` and `CommGroup` with their additive twins
`AddGroup` and `AddCommGroup`, the examples (`ZMod n`, the symmetric and dihedral groups, the
product), powers and multiples, `orderOf`, `Subgroup` and `AddSubgroup`, `closure`
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
`ZMod n`, `abbrev ZMod (n : ℕ) := Fin n` (Mathlib's own definition for positive `n`; since
2026-10-23, replacing a structure of the student's), with the operation `(a + b) % n`; the symmetric groups `Equiv.Perm (Fin n)`; the
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

**The group operation is `*`, the neutral element `1`, the inverse `a⁻¹`: Mathlib's symbols; an
additive group writes `+`, `0` and `-a`.** The class is `class Group (G : Type u)` with the data
fields `mul`, `one` and `inv` and the five equations of Milne's Definition 1.1; the symbols reach
it through the instances `Group.toMul`, `Group.toOne` and `Group.toInv` of the notation classes
`Mul`, `One` and `Inv`, the targets of a problem of their own (`group_notation`). A type that
already carries `*` or `1` with another meaning cannot be a multiplicative group, and `ℤ` carries
both, so the plus-like examples are the student's `AddGroup`, the same class under additive
names (`add`, `zero`, `neg`; `add_assoc`, `zero_add`, `add_zero`, `neg_add_cancel`,
`add_neg_cancel`), with `AddGroup.toAdd`, `AddGroup.toZero` and `AddGroup.toNeg`: `AddGroup ℤ`
from the integers' own operations and the five core laws, `AddGroup (ZMod n)` from the student's
laws of addition modulo `n`, and `AddGroup Bool` with `xor`, `true + true = false` and
`0 = false`. Because the instance's `+` is the type's own, every law reaches `3 + x` as written,
and `omega` and `decide` work on it unchanged. `Unit`, `Sₙ`, `Dₙ` (table `r (i + j)`,
`sr (j + -i)`), products and subgroups are multiplicative; a product of additive groups is
additive. (The plan's Decision 4, taken 2026-10-23 after the wrapper `Multiplicative` of
2026-10-22 proved cumbersome in the examples.)

**Every general definition and theorem carries `@[to_additive NAME]`**, which makes its additive
copy: `mul_left_cancel` gives `add_left_cancel`, `g ^ n` gives the multiple `n • a`, `orderOf`
gives `addOrderOf`, `Subgroup.zpowers` gives `AddSubgroup.zmultiples`. Write the name out, in
full below `GroupTheory` (`@[to_additive AddSubgroup.add_mem]`): the publisher's closure finds a
declaration only by a name the source writes, and Lean's own translation is sometimes not
Mathlib's (`mul_inv_rev` would be `add_neg_rev`, Mathlib's `neg_add_rev`; `orderOf_eq_one_iff`
would be `addOrderOf_eq_zero_iff`, reading the number `1` as the identity). Each section file
sets `set_option linter.translateGenerateName false` after `namespace GroupTheory`, so that a
written name equal to the generated one is not a warning. `lake env lean
scripts/additive_names.lean` prints every pair Lean holds, and `scripts/explicit_additive_names.py`
writes them into bare marks; run both after adding marks, and compare the pairs before and after.
`to_additive` cannot make a class or a structure, nor a definition by recursion (the copy's
equation lemmas do not match), so **each such notion has an additive twin the student writes**
as a short problem right after the original: `AddGroup`, `AddCommGroup` (inside `comm_group`),
`AddGroup.nsmul` with `SMul ℕ A`, `AddGroup.zsmul` with `SMul ℤ A`, `AddSubgroup`; after the
problem block, one line per pair, `attribute [to_additive existing AddGroup] Group`, with the
twin named in the brackets so that the closure pulls it wherever the line replays. Instances
carry names (`Prod.instGroup`, `Subgroup.instMembership`), since a mark on an anonymous
instance cannot be written. A map from a multiplicative group to an additive one has no class,
and the subject avoids it: the parity maps go to `Equiv.Perm (Fin 2)`.

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
   notation (§2, the definition of `Group` itself), the additive class and the mark
   `@[to_additive]` (§2, `add_group` and `to_additive`, the mark used at once through its copy on
   `ℤ`); recursion for powers and `Int.induction_on` (§4), and the multiple `n • a` (§4, `nsmul`); a `Membership` instance for the student's structure (§5; the coercion of a subgroup
   to a type is §1's `↥S`, written `H.carrier`, since a coercion instance never reaches a later
   context, **Learned building §5**); a named application for homomorphisms (§6, for the same
   reason); a `HasQuotient` instance (§7); `Quotient.lift₂` (§9); `extends SMul` and
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

**Identities: a worked example for the first of a kind, a chain for the subtle ones, nothing
for the rest** (the owner, 2026-10-23, after Algebra.lean of the LeanPIMS26 course, narrowed the
same day after the blind review of Group Theory). A student meets an identity such as
`a⁻¹ * (a * b) = b` as too obvious to prove and has no idea how to begin, so **the first identity
of a new kind** is proved in front of them: a `@given` whose proof is a `calc` chain, one law per
step, shown in the preamble as well (and so in the starting code), then the same steps as one
`rw`, then the pattern in a sentence (regroup, cancel, tidy up); the exercise is its mirror image
(`first_identity`). **A genuinely subtle identity**, one whose route is not the pattern, gives the
chain of expressions in the preamble, `b = b * 1 = b * (a * c) = b * a * c = 1 * c = c`, and
leaves the law behind each step to the student (`neutral_unique`, `inverse_unique`,
`mul_inv_rev`): the expressions are given, the reasons are the exercise. This is the one place the
rule against giving the steps yields. **The mirror image of a worked identity, the second identity
of a kind, and the routine ones get no chain** (`cancel_adjacent`, `mul_left_cancel` after
`neutral_unique`, `mul_right_cancel`): the preamble says the idea and stops. Outside a worked
example no preamble names the tactics of the proof, a case split or a witness, or lists the laws
in the order of the steps ("regroup so that `b` meets `b⁻¹`, and then `a` meets `a⁻¹`" is such
a list); the mathematics stays. The worked firsts of later sections are the first identity of residues (`ZMod.zero_add`,
one rewrite per line with the goal each leaves in a comment) and the first induction on powers
(`one_pow`, a `calc` step). A worked example whose prose outgrows the page splits the problem
rather than the example (`zmod_neg_laws`, `one_pow`, `zpow_zero_one`, `pow_mod_order_of`). Later
sections do the same for their first identity of a new kind (cosets, homomorphisms).

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

## Learned building §2 (2026-10-21)

- **A `class … extends …` is not shape-checked**: the publisher hands the student the head with
  an empty body and skips the field check (`checkspec._lift_structure`), so the student's class
  carries `inv` as a plain field and the `Inv G` instance is a `@given`. (§3's `CommGroup` extends
  `Group` all the same, with an authored spec as the whole check; see below. Since 2026-10-22 the
  `Mul G`, `One G` and `Inv G` instances are the targets of `group_notation`, so a student writes
  them.) The same holds for a
  structure with binder-style fields `(a : G)` before the colon: write fields as `name : type`.
- **A notation command cannot sit inside a problem block** (the extractor refuses it as a
  target). It goes after the block with a docstring, as polya-basic writes `''`, and is
  replayed wherever the name it abbreviates is pulled; the declarations that use it are
  `@given`s of the next problem block that needs them, and the class's own spec is stated with
  the raw fields (`Group.mul (Group.mul a b) c`).
- **A class spec in the form `have h := @Group.law G _ a` then `grind`** accepts a field stated
  with explicit or implicit binders and in either orientation (`a = mul a one` for `mul_one`),
  and still rejects a wrong equation; `by apply Group.law` rejected the reversed orientation,
  which the §2 reviewer found to be the natural transcription of a chain `1 * a = a = a * 1`.
  So the preamble states each law once, one orientation each, and the description gives the
  naming rule (`one_mul` for `1 * a = a`).
- **An instance target has no mechanical check**; its `@spec` is a `decide` on the values that
  pin the operation (`true * true = false ∧ … ∧ (1 : Bool) = false`), which rejects another
  group on the same type (`Bool` under `==`) and accepts every spelling of the intended one.
- **A hypothesis named like a theorem of the subject pulls that theorem**: the closure's token
  scan resolved a binder `one_mul` to `GroupTheory.one_mul` and dragged the group layer into a
  context that needed none of it (a "did not verify at once" warning). Theorems about a bare
  operation name their data `op`, `e`, `inv` and their laws `assoc`, `e_op`, `inv_op`.
- `omega` sees through a field defined as `(· + ·)` once the elements are introduced, so the
  `ℤ` instance's laws close by the five core names or by `intro; omega`; `(3 : ℤ) * 4 = 7`,
  `(3 : ℤ)⁻¹ = -3` and an `↔` whose sides compute to the same thing close by `rfl` or `decide`.
- `Fintype.card Bool = 2` closes by `decide`, and `decide` proves every law of `Bool` under
  `xor` and of `Unit`.
- **The reviewers' commonest finding was a context gap, not double teaching**: a preamble that
  says "by cancellation on the left" while the reference goes another way, so that
  `mul_left_cancel` is an unknown identifier in the check. Either the reference uses the route
  the prose names (so the closure carries it) or the description says the context does not
  hold it. A problem on a running example whose prose mentions a theorem of the example's
  instance (`int_mul_eq_add`) must use it in the reference too.
- A preamble that gives the steps in order ("write `b` as `b * 1`, replace that `1` by
  `a * c`, and reassociate") makes the exercise a transcription; three were cut to the idea.
  A title must be true as a statement: "Self-Inverse Elements Commute" is false of two
  elements; "A Group of Self-Inverse Elements is Commutative" is the theorem.
- A hypothesis drawn by `intro` from `Function.Injective (fun a => a⁻¹)` or from
  `Function.Bijective (fun x => a * x)` shows the function applied, `(fun a => a⁻¹) a`; `exact`
  sees through it and `rw` does not, the `∘` gotcha of §1 again, said where it recurs.

## Learned building §3 (2026-10-21)

- **`show` is linted.** `linter.style.show` is in Mathlib's standard set, which the lakefile
  turns on, so a `show` that changes the goal is a warning under `lake build` and the check,
  and an error under publish; `lake env lean` on a scratch file does not apply the lakefile's
  options, so a scratch compile must `set_option linter.mathlibStandardSet true` to see what
  the build sees. A reference restates a goal with `change` or, better, avoids the need: the
  value of a structure built inline, `⟨(a.val + b.val) % n, _⟩`, is invisible to `rw` in a
  law's goal ("motive is not type correct" when it tries), so an operation on a structure is
  a `def` of its own with a `rfl` equation for its value (`ZMod.add` with `ZMod.val_add`), and
  the laws are `apply ZMod.ext` then `rw` with those equations and the arithmetic lemmas.
- **A shared auxiliary proof pulls an unrelated definition into a context.** Lean abstracts
  the proofs inside a definition into `_proof_n` constants and reuses one whose statement and
  term match within the module, so the first definition in a section that needs the instance
  `NeZero 2` mints `_proof_1 : NeZero (1 + 1)` and every later definition needing it depends
  on that constant in the build's graph. The closure maps the constant to its parent and pulls
  the whole definition, without the parent's own context (`zmodTwoEquivBool` with its
  `decide`, into `dihedral_fintype`), and the extract reports "preamble closure: no progress".
  Theorems do not abstract their proofs, so only definitions and instances share. Keep the
  numerals of a fixed modulus out of a definition that an unrelated later definition should
  not drag along (`a.val = 1` and `⟨1, by decide⟩` instead of `(1 : ZMod 2)`), or make the
  first such definition one that every later context holds anyway.
- **A `class … extends …` can be a problem after all**: the student receives the head with an
  empty body (the publisher skips the field check), the description names the one field to
  add, and the authored spec (`have h := @CommGroup.mul_comm G _ a b` then `grind`) is the
  check, accepting both binder styles and both orientations. An instance of it is built with
  `where` and the new field alone; Lean fills `toGroup` by instance search.
- **A spec may use only what the reference uses**: a `simp [DihedralGroup.mul, mul_comm]` spec
  that would accept the table in either orientation failed at extract, since the reference
  needs no `CommGroup (ZMod n)` instance and the context has none. The table's spec is `rfl`
  in the orientation the description dictates. `simp` with an argument it does not use is a
  linter warning, so a spec never lists a lemma only some encodings need.
- **A `/-- @spec -/` cannot be followed by `open … in`** (a doc comment must precede a
  declaration): a spec that needs a constructor writes `DihedralGroup.r 1`; a theorem in a
  block may carry `open DihedralGroup in`, and the stub keeps the line. Inside a declaration
  named `DihedralGroup.mul` or `DihedralGroup.equivProd` the namespace is open by itself, so
  `r i` resolves without it; a theorem named `DihedralGroup.mul_assoc` would shadow the
  subject's `mul_assoc` in its own body, so the associativity theorem is `dihedral_mul_assoc`.
- **`Prod.mul_def` exists under the fence** (Mathlib's notation layer, for `*`), so the
  product's equation is `prod_mul_def`; the fence probe lists `Prod.mul_def` as known.
- **Extra credit lives in a last section.** By the syllabus rule every concept declared before
  the goal is on its path, so extra credit placed in the middle of the subject becomes
  recommended the moment the goal moves past it. `FewerAxioms.lean`, imported last by the
  root, holds what nothing builds on, and each section's goal move leaves it after the goal.
- `Fin 2` literal patterns work in a `match`, `| (0, k) => … | (1, k) => …`, and Lean sees that
  no third case is possible; `cases a <;> cases b <;> cases c` with `·` bullets afterwards
  keeps an eight-case proof at nine lines, the unnamed variables reached with `_`.
- `decide` reaches `D₄` and `D₂` through a `Fintype` built by `Fintype.ofEquiv` from
  `Fin (2 * n)`; the whole section compiles in six seconds.
- `check_prose_names.py` compiles the stub, and an inductive's stub has no constructors, so a
  prose name that uses one fails to compile; the script now retries with the reference.
- **The reviewers' findings, in order of frequency**: a prose promise the context cannot keep
  ("by `decide`" on a type whose `Fintype` or `Group` instance the reference never uses, "of
  order six" with no instance to count by), fixed by making the promise an exercise whose
  reference pulls the instance; a preamble handing over a witness, the steps in order or a
  tactic script, cut to the idea or to the reason the obvious route fails; a term-mode shape
  never met (`exact congrArg r (by rw …)`) over variables `<;>` left unnamed, replaced by
  `rfl` equations given in the context and `rw`; and prose that read the table in written
  order against the subject's own convention that in `f * g` the right factor acts first.
  Say the first error a student meets (`decide` on a goal with a free variable) before the
  deeper reason; say the direction a Mathlib function runs (`Fintype.ofEquiv` takes the
  equivalence out of the finite type) the first time `.symm` is needed; and say once that a
  bare `rw [mul_comm]` turns the first product it finds and `rw [mul_comm a b]` names one.

## Learned building §4 (2026-10-21)

- **The power instance carries `@[default_instance high]`**, as Mathlib's `Monoid.Pow` does, and
  for the same reason. A numeral exponent, `(3 : ℤ) ^ 2`, is elaborated through the default
  instances alone, and core's `instPowNat` (through `NatPow ℤ`, Lean's own `3 ^ 2 = 9`) is one;
  a plain `instance : Pow G ℕ` is never consulted for it, so `(3 : ℤ) ^ 2 = 6` fails by `decide`
  while `(1 : ℤ) ^ k = k` with `k : ℕ` compiles, since an ordinary search prefers the instance
  declared last. A generic `instance : NatPow G` loses both ways: at equal priority a concrete
  key (`NatPow ℤ`) beats a star key (`NatPow ?G`) whatever the declaration order. The mark rides
  into the stub, so the student fills the body and the prose says in one sentence what the mark
  is for. A negative numeral exponent needs its type, `g ^ (-3 : ℤ)`.
- **A statement that does not use `Fintype.card` takes `[Finite G]`**: `linter.unusedFintypeInType`
  refuses `[Fintype G]` in a theorem whose type never mentions it, and a warning is an error under
  publish. `Finite.exists_equiv_fin G : ∃ n, Nonempty (G ≃ Fin n)` gives the bijection for a
  pigeonhole argument, and a later `[Fintype G]` context finds `Finite G` by itself, so
  `orderOf_pos` under `[Finite G]` serves everywhere.
- **`Nat.find` in a statement or a proof needs `open Classical in` on that theorem**, as on the
  definition: `Nat.find_spec h` as a term fails to synthesize `DecidablePred` even when the goal
  already holds the instance. A `/-- @spec -/` cannot carry `open … in`, so its proof opens with
  the tactic `classical`, which supplies the same instance. The two cases of a definition by
  `if h : c then … else …` are exposed by `unfold` and picked by core's `dif_pos h` and
  `dif_neg h`; `orderOf_of_isOfFinOrder : orderOf g = Nat.find h` and its negative companion are
  the equations later proofs rewrite with, so that `by_cases h : IsOfFinOrder g` opens every
  proof about the order and the `if` is never unfolded again.
- **`change` restates a goal up to definitional unfolding where `show` is linted**: the integer
  equations `Int.ofNat k + 1 = Int.ofNat (k + 1)`, `Int.negSucc 0 + 1 = 0`,
  `Int.negSucc (j + 1) + 1 = Int.negSucc j`, `-(Int.ofNat (k + 1)) = Int.negSucc k` and
  `-(Int.negSucc k) = Int.ofNat (k + 1)` all hold by `rfl`, and `change (g ^ (j + 1))⁻¹ = (g ^
  (j + 1 + 1))⁻¹ * g` puts a `zpow` goal into the form the laws rewrite. A `cases` on an integer
  opens into a `cases` on the natural number inside it.
- **`Int.induction_on` is Mathlib's `induction_eliminator` for `ℤ`**, so a plain `induction n
  with | zero | succ k ih | pred k ih` uses it with no `using`; the goals read `↑k + 1` and
  `-↑k - 1`.
- **`g ^ 2` is `(1 * g) * g` by definition, not `g * g`**: an `exact mul_inv_cancel (sr i)`
  against `sr i ^ 2 = 1` needs `rw [pow_succ, pow_one]` first. `cases h` on `h : sr i = 1`
  closes a goal, since `1` unfolds to the other constructor `r 1`.
- **`not_imp` is ambiguous under the fence** (`_root_.not_imp` and `Classical.not_imp`); the
  reference writes `Classical.not_imp`.
- **Slugs are snake_case**: the extractor refuses `@problem orderOf` ("needs a slug").
- **The fence probe passes `-DmaxErrors=10000` to `lean`**: once the UNKNOWN list has more than
  a hundred names Lean stops at its default limit, every later `#synth` test goes unrun, and the
  probe reports instances FOUND that were never tried. `set_option maxErrors` in the file does
  not take effect.
- **The reviewers' findings, in order of frequency**: a context gap behind a prose promise
  (`pow_zero` promised in `npow` and absent from `int_pow`, whose reference closed the zero case
  by `rfl`; `s3_pow_check` absent from `is_of_fin_order`), fixed by routing the reference through
  the promised fact; a Lean device arriving in the concept's hardest problem (`change` in
  `zpow_add_one`, `induction` on `ℤ` in `zpow_add`), fixed by teaching it one problem earlier on
  a trivial fact (`zpow_neg`, the new `one_zpow`), as §4's `one_pow` taught induction on `ℕ`; a
  preamble handing over the case split, the lemma per case or the proof in words; a reference
  over the fifteen-line rule (`orderOf_dvd_iff_pow_eq_one`, split under Mathlib's
  `orderOf_dvd_of_pow_eq_one`); a title promising a theorem the problem did not prove ("The
  Elements of Order One and Two" with no `orderOf_eq_two_iff`), fixed by adding the theorem and
  making the running example its instance; and the first error a student meets left unsaid
  (`decide` on `orderOf` itself, a numeral in a `change` taking the goal's type). A concept whose every
  problem passes by transcription is a concept whose preambles do the student's work (the
  fourth reviewer's finding on the finite-group problems): cut each to the idea and the one Lean
  fact the mathematics does not reveal, and split a device (`Finite.exists_equiv_fin` with
  `Nonempty`, a function built on the spot) from the theorem it serves. A numeric check that
  restates the theorem invites `exact theorem _`, which here failed on `Finite (ZMod 6)` not
  being in the context; state the check as the theorem evaluated (`2⁻¹ = 4 ∧ 2 ^ (orderOf 2 -
  1) = 4`). The review found no double teaching in `natural_powers` or `order_of_element`, and
  all but one problem passed on the reviewers' first attempt.
- **The closure misses an anonymous instance and the repair pulls it**: seven problems of §4
  (`int_pow`, `is_of_fin_order` and the five that open the order's definition) report "did not
  verify at once: repair added instance", the `Pow G ℕ` instance (`instPowNatOfGroup`) not
  reaching the context in the first round although the reference's term names it, as §2's
  `Inv G` instance did not; the bundle holds the repaired preamble.

## Learned building §5 (2026-10-21)

- **A coercion instance never reaches a later problem's context.** Elaboration unfolds a
  `CoeSort` or `CoeFun` instance on the spot, so no compiled term names it, the build's graph
  carries no dependency on it, and the repair loop (which answers `failed to synthesize` and
  `unknown identifier`) never sees the `type expected` it leaves behind: a problem-owned
  `instance : CoeSort (Subgroup G) (Type u)` failed the next problem's statement `(a : H)` at the
  first extract, exactly as polya-topology's given one did (Profinite Spaces §8). The rule is
  theirs: spell the type out. **A subgroup as a type is `H.carrier`**, the set as a type of the
  first section, through Mathlib's own `Set` coercion, which is in every context; the group
  instance is `Group H.carrier`, the count `Fintype.card H.carrier`, and the prose says once that
  Mathlib writes `↥H`. §6's homomorphisms must apply through a named function, not a `CoeFun`
  instance, for the same reason.
- **A coercion equation must coerce both factors**: `((a * b : H.carrier) : G) = a * b` elaborates
  the right side as a product in `H.carrier` coerced afterwards, so it is `↑(a * b) = ↑(a * b)` and
  a wrong instance passes it. Write `(a : G) * (b : G)`; the spec battery caught it.
- **`by decide` proves a structure field with implicit binders directly**: a tactic block is never
  given implicit lambdas, so the goal of `mul_mem' := by decide` is the whole
  `∀ {a b : ZMod 6}, a ∈ {0, 2, 4} → …`, which `Fintype.decidableForallFintype` decides, and
  membership in a set literal `{0, 2, 4}` is decidable under the fence. A membership in a `def`
  such as `zmodSixEvens` is not: rewrite with its `mem_` equation first, and state a later
  `decide` over the set or the disjunction.
- **A carrier written as `Set.range f` hands `intro ⟨k, hk⟩` a beta-redex**, `hk : (fun k => g ^ k) k
  = a`, which `rw` cannot use; `zpowers` has carrier `{x | ∃ k : ℤ, g ^ k = x}` instead, and the
  rotations keep `Set.range r` because `r` is a constructor, not a lambda.
- **`decide` cannot see inside a `def` subgroup** (`failed to synthesize Decidable`): after
  `apply Subgroup.ext`, `simp only [mem_center_iff, mem_bot]` rewrites `x ∈ center G` and
  `x ∈ ⊥` under the `∀`, and `decide` runs through `D₃` and `D₄`; `intro x`, `rw`, `revert x`
  would do the same, but `revert` is a tactic the student has not met and `simp only` is.
- `Membership.mem` takes the collection first, `⟨fun H x => x ∈ H.carrier⟩`; a slug is snake_case,
  so the problem for `sInf` is `s_inf`; a binder a proof uses only implicitly is `_`
  (`fun _ hx _ hH => hH hx`), or the unused-variable linter fires; `Int.dvd_zero`, `Int.dvd_add`
  and `Int.dvd_neg` make `nℤ` three one-liners, and `omega` decides `2 ∣ x ∧ 3 ∣ x ↔ 6 ∣ x`.
- The `Membership` instance, the `Top`, `Bot`, `LE`, `Min` and `InfSet` instances and the
  `Group H.carrier` instance all reached later contexts without a repair: a compiled term names
  each of them.
- **An equation stated "for later proofs to rewrite with" must be used by a later reference**, or
  it is not in the later context: the `mem_` equations of `zpowers` and `closure` were stated and
  never used, so `rw [Subgroup.mem_zpowers_iff]`, the move every earlier problem had trained,
  failed in four problems. Route the next references through the equation (`mem_closure :=
  Subgroup.mem_sInf` carries the previous problem's equation along too).
- **The reviewers' findings, in order of frequency**: a context gap behind a trained habit or a
  concept promise (the `mem_` equations above; the `LE` instance absent from `inf` while the
  concept description promised a greatest lower bound; a numeral instance absent from
  `rotations`), fixed by routing references through the equations and stating the promised facts
  (`inf_le_left`, `inf_le_right`, `le_inf`); preambles handing over the witness, the lemma per step
  or the tactic script, in ten problems, cut to the idea, two reviewers finding every problem of
  their concept passed by transcription; a tactic the student had not met (`revert`) arriving in
  new mathematics, replaced by `simp only`; `⊢` in an `at` clause in a reference; the first error
  unsaid; a background class described rather than shown (`Min`, `InfSet`); a promise no exercise
  kept (the centre as a measure of non-commutativity, the empty family), each fixed by a theorem
  (`d4_center_ne_top`, `mem_sInf_pair`). No double teaching was found in any concept, and every
  problem passed on the reviewers' first attempt.

## Learned refactoring to Mathlib's symbols (2026-10-22)

The wrapper `Multiplicative` this section describes was replaced on 2026-10-23 by the student's
`AddGroup` (**Learned refactoring to additive groups**); its findings on `Prod.instMul`, the
numeral `0` of `ZMod n`, `@[default_instance high]` and the reviewers stand.


- **A law of the wrapped instance is the core law applied to the unwrapped elements**:
  `mul_assoc a b c := Int.add_assoc (toAdd a) (toAdd b) (toAdd c)` is accepted as it stands,
  since `ofAdd` and `toAdd` are the identity under `def Multiplicative (α : Type u) := α`, and
  the same term proves the same law for `Multiplicative (ZMod n)` from `ZMod.add_assoc`. The
  reverse direction is as cheap: `inv_inv (ofAdd a)` proves `-(-a) = a` on `ZMod n` by `exact`,
  which is how the dihedral table gets its residue arithmetic without a second proof.
- **The wrapper is opaque to `omega`, `decide` is not**: `ofAdd 3 * ofAdd 4 = ofAdd 7` holds by
  `rfl` and by `decide` (with `DecidableEq (Multiplicative α)` by `inferInstanceAs`), but
  `omega` sees no integers until `ofAdd_add`, `ofAdd_neg`, read right to left, and `ofAdd_inj`
  have turned the statement into one about `ℤ`; `rw [h]` on `x = ofAdd 4` leaves
  `ofAdd 3 * ofAdd 4 = ofAdd 7` for an explicit `rfl`, since `rw`'s closing `rfl` is reducible
  only. A `change` restates a wrapped goal in the form a lemma about values reads
  (`zmod_cyclic`).
- **The copy carries nothing across by itself**: `DecidableEq`, `Fintype` (`Fintype
  (Multiplicative α)` by `inferInstanceAs`, with `Fintype.card_multiplicative` by `rfl`) and a
  `Fintype` for a product of copies (`Fintype.ofEquiv` from `Fin 6`) are each supplied once;
  numerals are deliberately not, so `(3 : Multiplicative ℤ)` is an error and the two ones cannot
  be confused. An equivalence `Fin 6 ≃ ZMod 2 × ZMod 3` is accepted at the type
  `Fin 6 ≃ Multiplicative (ZMod 2) × Multiplicative (ZMod 3)` by definitional unfolding.
- **`Prod.instMul` of the fence wins the elaboration of `*` on `G × H`**, and the student's
  `Group (G × H)` with a componentwise `mul` is definitionally the same instance, so `rw
  [mul_assoc]`, `mul_assoc a b c` and `rfl` all accept it; nothing to do but know it.
- **The numeral `0` of `ZMod n` has value `0 % n`**, not `0`, so the additive laws take
  `ZMod.val_zero : (0 : ZMod n).val = 0 % n` as a given and `Nat.zero_mod` after it; the old
  trick of building the neutral element as `⟨0, _⟩` is gone, since `1 = ofAdd 0` must be the
  numeral.
- **`@[default_instance high]` on `Pow G ℕ` is still needed**: a numeral exponent as in
  `rot3 ^ 3` is read through the default instances alone, whatever the base type.
- **`Bool`'s `1` is `false`** under the group instance, legal because the fence gives `Bool` no
  `One`, and said in a sentence at `bool_xor_group`; `(1 : Bool) = false` is `rfl`.
- **The extract needs a publisher newer than v0.6.0.** Its repair pulled an instance only of
  the class Lean names, and Lean names `HMul`, `HPow`, `OfNat` and `Decidable` for a missing
  `*`, `^`, `1` and `decide`, while the author declares `Mul`, `Pow`, `One` and `DecidableEq`:
  ten problems failed, every one a spec or a pulled law using `*` or `1` on a type whose
  derived instance had not been pulled. The fix (`closure._feeders_of`, `_rank`,
  `_pull_for_binders` in polya-publisher, with a test) makes the repair accept the feeding
  class and pull the binder's concrete instance (`Group Bool` for `[Group G] : Mul G`). Until
  the owner releases it and the lakefile's `rev` moves, `lake exe polya extract` runs v0.6.0
  and fails those ten; the `polya` shim over the sibling checkout passes, 108 problems.
- **The reviewers' findings after the refactor**, one agent per changed concept: a description
  that promises a check ("check that `ofAdd 3 * ofAdd 4 = ofAdd 7`") must have a theorem in the
  stub, since the spec is invisible to the student, and the prose must carry the ascription
  `(3 : ℤ)` without which numerals default to `ℕ`; an `↔` that holds "by definition" closes by
  `Iff.rfl`, not `rfl`, and the prose says so; a theorem with no explicit element, `inv_one`,
  applied through the wrapper needs its group named, `inv_one (G := Multiplicative (ZMod n))`,
  a device said where it bites; a preamble that prints an instance body or the first of three
  parallel answers makes a transcription, so the pattern is shown on an earlier type (`Add
  Vec3`) instead; a reference that closes a case by `exact congrArg r (…)` is a term shape the
  student does not find, where `rw` with the table's equation and the law is, and the context
  list then names the equations; a prose claim about an earlier concept ("the product concept
  named `ZMod 2 × ZMod 2` the Klein four-group") must be true of an earlier problem.
- **The §2 refactor touched 35 of 79 problems** and added four (`group_notation`,
  `multiplicative`, `zmod_add_laws`, `zmod_add_rearrange`); every file compiled on the first
  attempt after the block replacements, the budgets needing six trims of a line or two.

## Learned refactoring to additive groups (2026-10-23)

- **A student `AddGroup ℤ` reaches the integers' own `+`.** With `add a b := a + b`, `zero := 0`,
  `neg a := -a`, the generic `AddGroup.toAdd`, declared later than `Int.instAdd`, wins the
  elaboration of `3 + x` inside the subject, and the two are equal at instance transparency, so
  `rw [zero_add]` on `(0 : ℤ) + 3 = 3`, `add_left_cancel h` on `h : 3 + x = 3 + 4`, `omega` and
  `decide` all work; so on `ZMod n` with its `OfNat` numerals, and `-(2 : ZMod 6)` by `decide`.
  Under the fence alone `ℤ` has `SMul ℕ ℤ` (core's `Lean.Grind.NatModule.nsmul`) and `SMul ℤ ℤ`
  (`instSMulOfMul`); inside the subject the student's `AddGroup.toSMul` and `AddGroup.toZSMul`
  win the same way, with the same values (the fence probe records it).
- **`to_additive` on the student's declarations**: it needs every multiplicative name in a
  statement or proof to have a translation, so the class, its notation instances and each
  structure are paired by hand first, and every theorem a marked proof uses must carry its own
  mark; a theorem with no group in it (`injective_of_left_inverse`) is used as it stands. It
  cannot translate a definition without a value (a class or structure: "cannot translate
  `Group` because it has no value") nor a recursive `def` ("do not generate the same number of
  equation lemmas"), which is why the twins are the student's. `open Classical in` goes above
  the mark, `@[to_additive]` directly above the declaration; `@[to_additive X,
  default_instance high]` does not carry the default mark to the copy, and the `SMul` instances
  need none (`3 • (2 : ℤ) = 6` elaborates).
- **The definitions of powers take the exponent first** (`Group.npow n g`, Mathlib's `npowRec`
  order), so that the twin `AddGroup.nsmul n a` matches `SMul.smul`'s order and the pairing needs
  no `reorder`; the `Pow` instance swaps the arguments.
- **A mark needs its twin to exist**, so a theorem about a new definition cannot sit in the
  definition's own problem when the twin comes after it: `pow_zero` and `pow_succ` moved from
  `npow` into `pow_one`, `zpow_natCast` and `zpow_negSucc` from `zpow` into `zpow_neg`.
- **The publisher's closure needed to know the marks.** Extracting with the pinned v0.6.1 failed
  44 of 110 problems in two ways: a context held a marked theorem without the line pairing
  `Group` with `AddGroup` ("`to_additive` cannot translate `Group`"), because the line names only
  `Group`; and a problem citing a copy (`neg_add_rev`, `zero_nsmul`) found no source declaration
  of that name. The change prepared for the owner, in `polya/closure.py`: a declaration under
  `@[to_additive NAME]` is indexed under `NAME` too, and the name in a `[to_additive existing
  NAME]` bracket counts as a mention of the attribute line, so that replaying it pulls the twin.
  With it the subject extracts with 110 problems and 0 errors, and the publisher's suite passes.
- A concrete example of an abstract notion with no additive meaning is replaced, not translated:
  the centre of an additive group is the whole group, so `center (Multiplicative ℤ) = ⊤` became
  `center (DihedralGroup 2) = ⊤`.
- **The refactor touched 26 of 108 problems' statements** and every general theorem's mark;
  removed `multiplicative`, `multiplicative_fintype` and `zmod_add_rearrange`, and added
  `add_group`, `to_additive`, `nsmul`, `zsmul` and `add_subgroup`: 110 problems. Every section
  compiled at its first build after the edits; the budgets needed nine trims.

## Learned simplifying ZMod (2026-10-23)

- **`ZMod n` is `Fin n`** by an `abbrev`, the owner's choice after finding the structure "a lot of
  book-keeping for very little payoff": numerals, `+`, `-`, `DecidableEq`, `Fintype` and the
  count (`Fintype.card_fin`) come with `Fin`, and §1 already taught its arithmetic. Lean's
  `Fin` negation and numerals are by definition the remainders the structure had,
  `(-a).val = (n - a.val) % n` and `(0 : Fin n).val = 0 % n` by `rfl`, so every proof carried
  over with `Fin.ext` for `ZMod.ext` and `isLt` for `val_lt`. Only `ZMod.val_zero` needs
  `[NeZero n]`.
- **The fiddly remainder laws are given** (`ZMod.add_assoc`, `ZMod.neg_add_cancel`), the owner's
  choice; `ZMod.zero_add` is the worked example and the student proves `add_zero`, `add_comm`
  and `add_neg_cancel`, the last from commutativity and the given law with no arithmetic. The
  fence has no `Fin.add_comm`, `Fin.add_assoc` or `Fin.neg_add_cancel`, but core has
  `Fin.add_zero` and `Fin.zero_add`, which the shortcut check finds; and `omega` cannot reason
  about `% n` for a variable `n`, so the laws keep their `Nat.mod_add_mod` proofs.
- **`Fin 6 ≃ ZMod 2 × ZMod 3` is `finProdFinEquiv` turned round**, but Lean does not unify `Fin 6`
  with `Fin (?m * ?n)`: the factors are named, `(finProdFinEquiv (m := 2) (n := 3)).symm`. The
  dihedral labelling passes residues across as they are, `r i ↦ (0, i)`.
- Seven problems became four: `zmod` (the `abbrev`, the value equations, the count and a
  numeral), `zmod_add_laws`, `zmod_group`, `zmod_two_equiv_bool`; `zmod_add_neg`,
  `zmod_neg_laws` and `zmod_fintype` are gone. 112 problems.

**The blind review of 2026-10-23** (one simulated student per concept, from the bundle, through
`scripts/review/`), applied section by section:

- **Prose that handed over the proof** was the commonest finding, in 14 of 25 reports: chains
  given for the second identity of a kind, preambles naming tactics, witnesses and case splits.
  The owner's rule since: a chain only for the first identity of a kind and for a subtle one
  ("Identities" above).
- **A context is the reference's closure**, so an instance the reference never touched was absent
  for the student: `AddGroup (ZMod n)` in the products, `AddGroup ℤ` in the extra credit. Fixed
  in the content, by references and checks that go through the student's instances, never
  through Mathlib's `Prod.instAdd` that happens to agree.
- **An additive copy is enforced only off a finite type**: `decide` proves a statement about
  `Bool` or `ZMod 6` without the copy, so the checks that demand one are on ℤ
  (`int_add_three_bijective`, `int_center`, `int_zsmul_one`) or need a general `n`.
- Double teaching removed by warm-ups (`quotient_mk_surjective`, `to_fin_mod`,
  `exists_injective_fin`, `to_fin_or_zero`, `order_of_sr`, `eq_of_coe_eq`); `pigeonhole` moved
  to §1. 127 problems.

## Learned reviewing the prose (2026-10-26)

A full review of every concept, preamble and description, section by section, each section
then re-read by a fresh reviewer. What it settled:

- **Student prose says "additive version"**, never "copy", "mark" or "spelling": the line
  `@[to_additive n]` is named as a line the first time the student meets it (`first_identity`)
  and explained in `to_additive`. "Copy" and "mark" stay this file's words.
- **No prose leans on what the student cannot see.** The `attribute [to_additive existing …]`
  lines sit outside every problem; the prose says only that Lean is told the two correspond.
- **A long expression goes on its own line**: an equation, iff or signature of more than about
  20 characters is a fenced `lean` block, never backticks in a sentence; a lemma's statement
  is shown as `theorem name … : …`, checked against `#check`.
- **No concept description carries Lean**, Prerequisites included; no description of
  Mathlib's version of what the student proves ("Mathlib's `pow_add`" becomes "`pow_add`").
- **The common giveaway is the lemma for each goal**: a context list in proof order, or a
  preamble that pairs each field with the fact that closes it. Name the facts; never the
  pairing, the witness or the case split.
- **The subject description states the current goal**, not the plan's eventual one, and
  lists only what is built.

## Learned building §6 (2026-10-26)

- **A structure's name says what it is, even where Mathlib's does not** (the owner, 2026-10-26):
  the homomorphism is `GroupHom` and the isomorphism `GroupIso`, with the twins `AddGroupHom`
  and `AddGroupIso`, since Mathlib's `MonoidHom` and `MulEquiv` name structures the subject never
  defines; the notations `→*`, `→+`, `≃*`, `≃+` and the field and theorem names (`map_mul'`,
  `map_one`, `ker`, `symm`) stay Mathlib's. The plan's **Decisions** 3 has the reasoning.
- **A homomorphism applies as `f.toFun x`**, the field itself, as polya-topology's `Homeomorph`
  does, with no `CoeFun` instance (§5); the prose says once that Mathlib writes `f a`. An isomorphism `extends G ≃ H`, so `e.toFun`, `e.invFun`,
  `e.left_inv` and `e.right_inv` are reached directly; the spec of each structure is
  `have h := @GroupHom.map_mul' G H _ _ f a b; grind`, which accepts both binder styles and both
  orientations, and a kernel's membership spec is `change _ = _ at h; grind`.
- **A notation is replayed only for a pulled item that names its declaration.** `zmodTwoIsoBool`
  reuses the auxiliary proof `zmodSixToTwo._proof_2 : NeZero (1 + 1)`, so the closure pulls
  `zmodSixToTwo` into its context (the shared-proof lesson of §3); its text named `→+`, not
  `AddGroupHom`, and the context failed with `unexpected token '+'`. The fix inside the project
  is to write the type of a definition whose proofs others may share as the structure's name,
  `AddGroupHom (ZMod 6) (ZMod 2)`; the root fix, replaying a notation when a pulled item's text
  contains its symbol, is the publisher's, and waits on the owner.
- **Inside a declaration named `Group.x`, `mul_one` is the class field `Group.mul_one`**, whose
  binders differ, and `rw [mul_one]` fails; the Cayley homomorphism is `cayley`, outside the
  `Group` namespace.
- **A homomorphism into `Equiv.Perm G` has no additive version**: the permutations of an
  additive group form a multiplicative group, and `@[to_additive]` refuses. `cayley` carries no
  mark, and the prose says why.
- **`decide` cannot decide a case with free variables** (`Expected type must not contain free
  variables`): the orientation's reflection-by-reflection case is `swap2 * swap2 = 1` under
  `sr i * sr j`, given as `swap2_mul_self` and used by `exact`.
- **No `Fintype` on a product or on `Equiv.Perm (Fin 3)` under the fence**: a statement over
  `ZMod 2 × ZMod 2` ranges over `x y : ZMod 2` instead, and `D₃ ≃* S₃` is an injective
  homomorphism with the count of `S₃` said in prose.
- **The vocabulary audit reads fenced blocks.** Since the prose review moved signatures into
  `lean` blocks, the audit's inline-backtick reading flagged 20 references whose names were
  taught in a block; `scripts/audit_vocabulary.py` now counts the names in fenced blocks too,
  and the subject passes with 0 of 149.
- **A spec over a structure that extends `Equiv` tries `exact` before `grind`**: a student may
  write the law through the coercion, `toEquiv (a * b) = toEquiv a * toEquiv b`, which is
  `toFun` only by definition, and `grind` rejects it; `first | exact h | exact h.symm | grind`
  accepts that form, both binder styles and both orientations.
- **The reviewers' findings, in order of frequency**: a step that holds only by definition,
  unsaid (`a ^ Int.ofNat n`, a projection's law, `e.toGroupHom`'s function, `Equiv.mulLeft`'s
  values), where the trained `rw` fails; a device used before the problem that shows it (a value
  of an extending structure); a notion defined and never used (the image); a preamble pairing
  each goal with its closer. Every problem passed, and no double teaching was found.

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
  `polya-basic`'s five subjects, and names in backticks and in fenced `lean` blocks count as taught.
  Section 1 passed it on 2026-10-21 with 0 of 21, the six sections on 2026-10-26 with 0 of 149.

**The student review after each section** uses `scripts/review/`: `make_view.py BUNDLE OUT`
renders the bundle answer-free (concepts, preambles, descriptions, starting code), `check.py
SLUG FILE.lean` grades an answer with the publisher's own checker in the problem's real context
(run it with `.lake/packages/polya-publisher/.venv/bin/python`), `reveal.py SLUG` prints the
reference, and `PROMPT.md` is the reviewers' brief, with `{REPO}`, `{REVIEW_DIR}` and
`{SECTION_BLURB}` (two or three sentences: what the sections before taught, what this one is
for, and the one or two Lean devices its plan entry says are new) to fill in, and `{CONCEPT}`,
`{FIRST}`, `{LAST}`, `{NUM}` per concept. The review directory lives outside the repository
(the session's scratchpad), since the brief forbids reading `.lake/`, and each agent is handed
the path of its filled-in brief and told to follow it. One agent per concept, at most three
at a time, each compiling only through `check.py`; a copy of `plans/STUDENT_BACKGROUND.md` goes
in the review directory, since the reviewers may not read `plans/`. The brief asks the rule's
question verbatim.

## Sources

The subjects follow published treatments for their selection and order of results, and name
them in `@reference` lines. Group Theory follows J. S. Milne's *Group Theory* notes, which are
CC BY-NC-SA 4.0 and so a syllabus only: the prose, the Lean and the problems are written here,
and no sentence, example or exercise is taken from them. Subjects carry CC BY 4.0, the
repository's default, and the text of it is the `LICENSE` file in each subject's directory.
