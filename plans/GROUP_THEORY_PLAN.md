# Plan for a subject on group theory

Draft, 2026-10-21, revised four times the same day: first on the owner's decision that **the
student defines everything, the group axioms and homomorphisms included**, as General
Topology's student built topology and Naturals' student built the natural numbers, so the fence
is free of Mathlib's `Group`; then on the owner's call for **a fixed set of running examples,
as basic as possible, met in an early section and returned to in every concept** (see **The
running examples**); then on the owner's two points that **`ZMod n` is defined with `%` and
owes nothing to Mathlib's `ZMod`**, and that **`ℤ` itself is an example**, which together
settle how the group operation is written (see **Decisions**, 4); then on the owner's call for
**a Prerequisites section** that introduces, on mathematics the student already has, every
Mathlib and Lean device the subject uses, so that **no problem introduces a Mathlib idea and a
hard mathematical idea at once** (see **Design points**, the rule, and §1); and on 2026-10-22
on the owner's two points that **the symbols could be Mathlib's `*` and `1` through `Mul` and
`One` instances, as `⁻¹` is through `Inv`**, which a probe answered (**Decisions**, 4, reopened),
and that **the notation is introduced in a problem of its own** (**Decisions**, 9, and §2's
**Fix**); and, the same day, on the owner's decision for **Mathlib's symbols**: `*`, `1` and
`⁻¹` through `Mul`, `One` and `Inv` instances, the additive examples through the student's
`Multiplicative`, and §2–§5 refactored to them at once (**Design points**, the symbols;
**Decisions**, 4; each section's **As refactored**); and on 2026-10-23 on the owner's finding,
after working the examples, that the wrapper is "super cumbersome": **the additive examples are
the student's `AddGroup`, and every general theorem carries `@[to_additive]`**, with `Bool` under
`xor` additive and the parity maps into `Equiv.Perm (Fin 2)` (**Spelling** under **The
sections**; **Decisions**, 4; each section's second **As refactored**). Proposed, not decided:
the open questions are under **Decisions**, each with a recommendation.

Slug `grouptheory`, title *Group Theory*, modules under `PolyaAlgebra/GroupTheory/`, the first
subject of this repository and the first algebra subject in the library. Two subjects follow it
(see **What comes after**): *Permutation Groups* and *The Sylow Theorems*.

## What the subject is

A group is a set with an associative operation, a neutral element and inverses. The student
first meets, in Lean, the mathematics a first course assumes (sets, bijections, equivalence
relations and their classes, finite sets and counting, the integers and remainders), then writes
the definition of a group, meets the handful of groups every course lives on, and builds, in
order, what a first course builds on them: powers and the order of an element, subgroups,
homomorphisms, cosets and Lagrange's theorem, cyclic groups and groups of prime order, normal
subgroups and quotients, the isomorphism theorems, and group actions with the counting they make
possible, the orbit–stabilizer theorem and the class equation. Its goal is the first structural
theorem those tools prove: *every group of order `p²` is commutative*, through the theorem that
a `p`-group has a nontrivial centre.

The subject is the first chapter of a first graduate course, as Milne's notes present it, with
the first half of the chapter on actions. It is finite group theory from the third section on,
with `ℤ` as the one infinite example: cardinalities are counted, and small facts about the
examples are checked by `decide`.

## Why it belongs here

- **Nothing in the library does algebra yet.** `polya-basic` ends with the natural numbers built
  from zero and successor (`naturals`, unfinished at divisibility) and a programming subject that
  teaches structures, classes and instances. A student who has finished it can read a `class`,
  write an `instance`, define a function by recursion and prove its laws by induction, and has
  never seen a group.
- **It builds groups the way the library builds everything**: by the student, from the axioms,
  under Mathlib's names, so that a later subject that imports Mathlib's algebra changes the
  imports and not the vocabulary (see **Design points**). Mathlib's own `Group` is a class at
  the bottom of a hierarchy (`Semigroup`, `Monoid`, `DivInvMonoid`, …) that exists for the
  library's sake; the student's is Milne's definition and nothing else.
- **Every later algebra subject needs it**: permutation groups, Sylow theory, rings and fields,
  Galois theory, representation theory, and the profinite groups that `polya-topology`'s
  *Profinite Spaces* names and never defines.

## Who the student is

The student has finished the five subjects of `polya-basic` (surveyed 2026-10-21):

| knows | from |
|---|---|
| terms, types, functions, implicit arguments, definitional equality | Getting Started |
| propositions as types, the connectives, quantifiers, classical logic; predicates and relations as `α → Prop` and `α → α → Prop`; equality | Logic |
| sets as predicates on a type, `⊆`, `∪`, `∩`, families, products, image and preimage — in the subject's own `Set`, with a hand-written `Membership` class, not Mathlib's | Set Theory |
| recursion, inductive types, `structure`, `class` and `instance`, coercions, lists, trees | Programming in Lean |
| `MyNat` from zero and `succ`, an `Add MyNat` instance over a recursive `add`, induction, strong induction, `simp` sets, `calc`, truncated subtraction, multiplication, divisibility; the subject's own `Function.Injective` | The Natural Numbers |
| tactics: `intro`, `exact`, `apply`, `rw`, `simp`, `cases`, `rcases`, `obtain`, `induction`, `constructor`, `omega`, `decide`, `calc` | throughout |

The student has **not** met, in Lean: Mathlib's `Set` (the same shape as Set Theory's, under
other lemma names) and the coercion of a set to a type; `Function.Injective`, `Surjective` and
`Bijective` as Mathlib spells them; `Equiv`; equivalence relations as `Equivalence` and
`Setoid`, and quotients; `Finset`, `Fintype`, `Fintype.card` and `decide` over a finite type;
`Fin n`; the integers as a type with theorems; `%` beyond one use in Logic, `Nat.find`,
`Nat.gcd` and `Nat.Coprime`; `ring`, `linarith` or `norm_num` (`ring` appears once, in
Programming's extra credit). The mathematics behind all of these the student has, or can be
given in a sentence; §1 is where each gets its Lean (see **Design points**, the rule).

## The source

J. S. Milne, *Group Theory*, v4.01 (November 2025), <https://www.jmilne.org/math/CourseNotes/GT.pdf>,
139 pages, published under **CC BY-NC-SA 4.0**. The NonCommercial clause makes it a syllabus and
not an input: the subjects of this repository carry CC BY, which an adaptation of NC-SA text may
not, so the notes supply the selection and order of the results and nothing else. Every sentence
of prose, every statement and every problem is written here; the subject cites the notes with a
`@reference` line, as a mathematician cites. A copy sits in `refs/GT.pdf`, untracked.

The results the subject takes, with Milne's numbers and the section that proves each:

| Milne | Result | Section here |
|---|---|---|
| p. 5, Notation; the background the notes assume | sets, families, bijections, equivalence relations and `[∗]`, `|S|`, `m ∣ n`, `ℤ` | §1 |
| 1.1, 1.2 (a)–(e), 1.10 | the axioms and their first consequences: uniqueness of the neutral element and of inverses, the inverse of a product, cancellation; one-sided axioms suffice | §2 |
| 1.3–1.6, 1.16, 1.17 | the examples: `ℤ` and `ℤ/nℤ`, the symmetric groups, the product `G × H`, commutative groups, the cyclic and dihedral groups | §2, §3 |
| p. 8–9 | `aⁿ` for `n ∈ ℕ` and `n ∈ ℤ`, the laws of exponents; the order of an element; `aⁿ = e ⟺ m ∣ n` | §4 |
| 1.11–1.16 | subgroups and the subgroup criterion; the centre; intersections; the subgroup generated by a set; cyclic groups; the subgroups `nℤ` | §5 |
| 1.20–1.23, p. 20 | homomorphisms preserve `e`, inverses and powers; isomorphisms; injective iff the kernel is trivial; Cayley's theorem | §6 |
| 1.24–1.26, 1.29 | cosets, the partition they form, the index; Lagrange's theorem | §7 |
| 1.16, 1.27, 1.28, 1.31, Ex. 1-5 | `⟨g⟩` has `order(g)` elements; the order of an element divides the order of the group; `g^{|G|} = e`; groups of prime order are cyclic; `(G : K) = (G : H)(H : K)` | §8 |
| 1.32–1.37, 1.41–1.44, 1.49 | normal subgroups, their characterizations and examples; `HN`; kernels are normal; the quotient group and its universal property; `ℤ/mℤ` as a quotient; `D₄/⟨r²⟩` | §9 |
| 1.45–1.48, 1.50, 1.51, eq. (13) | the homomorphism theorem; the isomorphism theorem; the correspondence theorem; internal direct products; `Cₘ × Cₙ ≈ Cₘₙ` for coprime `m, n` | §10 |
| 4.1–4.6, 4.10 | actions, orbits, stabilizers, transitive and faithful actions, conjugation | §11 |
| 4.7–4.8, 4.11–4.12, 4.16, 4.18, 4.19, Lemma 5.1 | orbit–stabilizer; the class equation; a `p`-group has nontrivial centre; groups of order `p²` are commutative | §12, the goal |

Milne's chapter 1 also classifies finitely generated commutative groups (1.53–1.58), treats
characters (1.59–1.63) and proves 1.64 on the order of `ab`; chapter 4 goes on to permutation
groups, primitive actions and the Todd–Coxeter algorithm; chapters 2, 3, 5, 6 and 7 are free
groups, automorphisms and extensions, Sylow, series, and representations. See **What is left
out**.

## The running examples

Eight groups carry the subject. Each is defined in §2 or §3, with nothing but the student's
`Group` class, `ℕ` with `%`, `ℤ`, `Equiv` and `Bool`, and each comes back in later sections as
the case that shows what a concept is for. The rule for every concept after §3: **its last
problem, or its first after the definition, instantiates the concept in the smallest running
example that shows the phenomenon**, with a numeric check where there is one, closed by `decide`
when `n` is fixed. A concept for which none of the eight shows anything takes the example the
literature uses, named in the table below. The student never needs a group that is not on this
list.

| example | what it is in Lean | why it is here |
|---|---|---|
| the trivial group | `Unit` | the first instance; the subgroup `⊥`; the quotient `G ⧸ ⊤` |
| the group of order two | `Bool` under `xor`, an additive group with `true + true = false` and `0 = false` | the third instance, closed by `decide`; addition modulo two; `ZMod 2 ≃+ Bool` is the first isomorphism; the parity maps go to `Equiv.Perm (Fin 2)` instead, which is multiplicative |
| the integers | `ℤ`, the student's `AddGroup ℤ` with the integers' own `+`, `0`, `-` (Milne 1.3, `C∞`) | the infinite example: an element of infinite order, so that `addOrderOf (1 : ℤ) = 0` means something; the subgroups `nℤ = zmultiples n`; cosets of `2ℤ` are the evens and the odds; `ℤ ⧸ nℤ ≃+ ZMod n` (1.44 a); the one group whose subgroups and quotients the student can list completely |
| the integers mod `n` | `ZMod n`, `abbrev ZMod (n : ℕ) := Fin n` (Mathlib's own definition for positive `n`; a structure of the student's until 2026-10-23), with `+` and `-` as `(a + b) % n` and `(n - a) % n`, and `AddGroup (ZMod n)` from its laws (Milne 1.3, `Cₙ`; nothing of Mathlib's `ZMod` but its additive reading) | the commutative finite example; every cyclic group; subgroups `⟨d⟩` for `d ∣ n`; the reduction `ZMod 6 →* ZMod 2`; quotients `ZMod 6 ⧸ ⟨3⟩`; `ZMod 2 × ZMod 3 ≃* ZMod 6`; groups of prime order; `ZMod p × ZMod p` and `ZMod (p²)` at the goal |
| the symmetric groups | `Equiv.Perm (Fin n)`, the student's instance (Milne 1.4, `Sₙ`); `S₃` with its rotation `r` and reflection `s` written out | the first non-commutative group; the smallest, `S₃`, with `r * s ≠ s * r` by `decide`; Cayley's theorem; the tautological action on `Fin n` |
| the dihedral groups | the student's `DihedralGroup n`, an inductive with constructors `r i` and `sr i` over `ZMod n` and a four-line multiplication table (Milne 1.17, `Dₙ`; Mathlib's shape) | the geometric example, the symmetries of the `n`-gon: order `2n`; `⟨r⟩` normal of index two, `⟨s⟩` not normal (1.36 b); `D₄`'s centre `{1, r²}`, its classes, its quotient by `⟨r²⟩` (1.49); a `p`-group with nontrivial centre; `D₃ ≃* S₃`; the action on the vertices with orbit–stabilizer `n · 2 = 2n` |
| the Klein four-group | `DihedralGroup 2`, which Milne calls `V₄` or `D₂`, isomorphic to `ZMod 2 × ZMod 2` | order 4 without an element of order 4 (1.30); not isomorphic to `ZMod 4`; every subgroup normal; `D₄ ⧸ ⟨r²⟩ ≃* V₄` |
| the product | `G × H`, the student's instance (1.5) | the projections as homomorphisms; the internal direct product; `ZMod 2 × ZMod 3 ≃* ZMod 6` (Milne eq. 13) |

Extra credit, once, in §9: the quaternion group `Q₈` (Milne 1.18, Exercise 1-1) as a second
inductive over `ZMod 4`, the non-commutative group all of whose subgroups are normal, and the
other group of order 8 with centre of order 2.

How each concept returns to them, section by section (the problem count in parentheses is
inside the section's budget, not added to it):

| concept | example problem | shows |
|---|---|---|
| §2 `group_axioms` | `Unit`; `AddGroup ℤ` with the integers' own operations; `Bool` under `xor` by `decide` | an instance is an operation that passes the axioms, whatever the operation is |
| §2 `consequences` | in `Bool`, every element is its own negative; `x + 5 + -5 + -x = 0` in `ℤ` by an additive copy | a consequence read off, in either spelling |
| §2 `cancellation` | in `S₃`, `r * s = r * x → x = s` is not a computation but a law | cancellation needs no table |
| §3 all | the definitions themselves | — |
| §4 `natural_powers` | `r ^ 3 = 1` and `s ^ 2 = 1` in `S₃`; `k • 1 = k` in `ℤ` | powers computed; a power in an additive group is a multiple |
| §4 `order_of_element` | `addOrderOf 2 = 3` in `ZMod 6`; `orderOf (sr i) = 2` in `Dₙ`; `addOrderOf 1 = 0` in the integers | the three cases: a divisor, an involution, infinite |
| §5 `subgroups` | the rotations `{r i}` of `Dₙ`; `⟨2⟩ = {0, 2, 4}` in `ZMod 6`; `nℤ` in `ℤ` | the criterion applied |
| §5 `centre` | `center D₃ = ⊥` by `decide`; `center D₄ = {1, r 2}`; `center V₄ = ⊤` | three sizes of centre |
| §5 `generated_subgroups` | `closure {r 1, sr 0} = ⊤` in `Dₙ`; `IsAddCyclic ℤ` and `IsAddCyclic (ZMod n)`, generated by `1`; `zmultiples n = nℤ` | generators; the integers are cyclic |
| §6 `homomorphisms` | reduction `ZMod 6 →+ ZMod 2`; reduction `ℤ →+ ZMod n`, `k ↦ k % n`; orientation `Dₙ →* Equiv.Perm (Fin 2)` (`r i ↦ 1`, `sr i ↦` the swap); `Prod.fst` | the standard maps |
| §6 `isomorphisms` | `ZMod 2 ≃+ Bool`; `DihedralGroup 3 ≃* Equiv.Perm (Fin 3)` by `decide`; `V₄` is not isomorphic to `ZMod 4` (as additive groups, `ZMod 2 × ZMod 2` against `ZMod 4`) | sameness and difference of groups |
| §6 `kernels_and_images` | the kernel of reduction is `⟨2⟩`, of `ℤ →* ZMod n` is `nℤ`, of orientation the rotations | kernels computed |
| §6 `cayley` | `S₃` inside `Equiv.Perm S₃` as prose; the left-multiplication permutation of `ZMod 3` written out | the theorem seen once |
| §7 `cosets` | the cosets of `2ℤ` in `ℤ`; the two cosets of the rotations in `D₃`; the three left cosets of `⟨s⟩` in `D₃`, and `r⟨s⟩ ≠ ⟨s⟩r` | cosets as residues and as rows of the table; left is not right |
| §7 `lagrange` | `D₃` has no subgroup of order 4; the subgroups of `ZMod 6` have orders `1, 2, 3, 6` | the theorem used |
| §8 `cyclic_subgroups` | `zpowers (r 1)` in `Dₙ` has `n` elements | the count |
| §8 `prime_order` | `ZMod p`, and every group of order `p` is isomorphic to it (prose, until §10) | the only group of order `p` |
| §9 `normal_subgroups` | the rotations in `Dₙ` (index two); `⟨s⟩` in `D₃`; every subgroup of `V₄` and of `ℤ` | normal and not |
| §9 `quotient_groups` | `ℤ ⧸ nℤ` has `n` elements (Milne 1.44 a); `ZMod 6 ⧸ ⟨3⟩`; `D₄ ⧸ ⟨r 2⟩`, Milne 1.49 | quotients computed |
| §10 `first_isomorphism_theorem` | `ℤ ⧸ nℤ ≃+ ZMod n` from the reduction; `ZMod 6 ⧸ ⟨2⟩ ≃+ ZMod 2`; `Dₙ ⧸ rotations ≃* Equiv.Perm (Fin 2)` | the theorem as a calculation |
| §10 `correspondence_theorem` | the subgroups of `D₄` above `⟨r 2⟩` against those of `V₄` (Milne 1.49's two lattices); the subgroups of `ℤ` above `6ℤ` against those of `ZMod 6` | the bijection drawn |
| §10 `direct_products` | `ZMod 2 × ZMod 3 ≃* ZMod 6`, and `ZMod 2 × ZMod 2 ≄ ZMod 4` | coprime orders |
| §11 `actions` | `Sₙ` on `Fin n`; `Dₙ` on the vertices `Fin n`; `ZMod n` on `Fin n` by rotation; `G` on itself | actions from the examples |
| §11 `orbits`, `stabilizers` | `Dₙ` on the vertices: one orbit, stabilizer of a vertex of order 2 | transitive, with a stabilizer |
| §11 `conjugation` | the five classes of `D₄` by `decide`; `S₃`'s three classes | classes computed |
| §12 `orbit_stabilizer` | `n · 2 = 2n` for `Dₙ` on the vertices | the count checked |
| §12 `block_counting` | `Bool` acting on `Fin n` by `i ↦ -i`: the fixed points of an involution have the parity of the set (the literature's example, Zagier's) | Lemma 5.1 at `p = 2` |
| §12 `class_equation` | `8 = 1 + 1 + 2 + 2 + 2` for `D₄`; its centre `{1, r 2}` | the theorem on the running `p`-group |
| §12 `prime_square` | `ZMod p × ZMod p` and `ZMod (p ^ 2)` are the two cases; `D₄` and `Q₈` of order `8 = 2³` are not commutative, so `p²` is sharp | the goal bounded on both sides |

Where Milne's own example is not basic, the table replaces it: lines in `ℝ²` as cosets (1.24)
by the cosets of `2ℤ` and of `⟨s⟩` in `D₃`; `GL₂(ℚ)` and its conjugate subgroup (1.33) by `⟨s⟩`
in `D₃` (1.36 b); `ℝ²/L` (1.44 b) by `ZMod 6 ⧸ ⟨3⟩`; `det` and `SLₙ` (p. 21) by the orientation
map of `Dₙ`. Fermat's little theorem, the textbook corollary of Lagrange, needs the
multiplicative group of units mod `p`, which is a ring's to supply, and is prose.

The mechanics were checked on 2026-10-21 under the fence, with a class of the shape **Decisions**
4 recommends: `ℤ` is an instance with `(3 : ℤ) ∗ 4 = 7`, `(3 : ℤ)⁻¹ = -3` and `(𝟙 : ℤ) = 0` all
by `rfl`, and `(3 : ℤ) * 4 = 12` untouched; `ZMod n` as a structure over `ℕ` with `%` has each
of its five laws as a one-line proof from `Nat.mod_add_mod`, `Nat.add_mod_mod`,
`Nat.mod_eq_of_lt`, `Nat.sub_add_cancel` and `Nat.mod_self`, and `decide` settles
`∀ a b : ZMod 6, a ∗ b = b ∗ a` once its `Fintype` instance comes from `Fin n` by
`Fintype.ofEquiv`; `decide` settles equations in `Equiv.Perm (Fin n)` (`DecidableEq` is in
`Mathlib.Data.Fintype.Card`) and quantified statements over `Fin 4` and over `Bool`; the
symmetric group's instance has `rfl` proofs; associativity of the dihedral table closes by
`cases` and `omega` for fixed `n` and by the `ZMod n` laws in general. On 2026-10-22 the
mechanics were checked again for Mathlib's symbols and the wrapper (`scripts/wrapper_probe.lean`), and §2–§5 were refactored to them; on 2026-10-23 for the student's `AddGroup` and `@[to_additive]` (`scripts/addgroup_probe.lean`, `scripts/addgroup_order_probe.lean`), and §2–§5 were refactored again. There is no
`Fintype (Equiv.Perm (Fin n))` and no `Fintype (α × β)` in the fence, so counts are done on
`DihedralGroup n` and `ZMod n`, whose `Fintype` instances the student builds from `Fin (2 * n)`
and `Fin n`, and `D₃` stands in for `S₃` wherever an order is counted.

## Design points

- **Never a Mathlib idea and a hard mathematical idea in one problem.** The owner's rule, and
  the one Profinite Spaces' student review found broken most often ("a problem must not teach a
  new piece of mathematics and an unfamiliar piece of Mathlib at once", `BEST_PRACTICES.md`
  4b). This plan enforces it in three places:
  1. **§1, Prerequisites, front-loads the Lean.** Every Mathlib or Lean device the subject uses
     and `polya-basic` did not teach is introduced there, on mathematics the student already
     has or can be told in a sentence: Mathlib's `Set` and sets as types, injective and
     bijective functions, `Equiv`, relations and `Equivalence`, `Setoid` and `Quotient`,
     `Fintype` and `Fintype.card` and `decide` over a finite type, `Fin n`, `ℤ` as a type, `%`,
     `Nat.find`, `Nat.gcd` and `Nat.Coprime`. When §7 defines cosets, the quotient type is old;
     when §12 counts orbits, `Fintype.card` is old.
  2. **A device that cannot be separated from its mathematics is taught in a problem of its
     own, just before the problem that needs it**, and the plan names each: a class (§2, the
     definition of `Group` itself, on which nothing else is new), then the three notation
     instances (§2, `group_notation`), then the additive class (§2, `add_group`), then the mark
     `@[to_additive]` (§2, `to_additive`, on a theorem whose copy is used at once); the multiple
     `n • a` (§4, `nsmul`, after the power it copies); recursion
     for powers (§4, Naturals' pattern) and `Int.induction_on` for `zpow_add` (§4); a `Membership`
     instance for the student's structure (§5; the coercion of a subgroup to a type turned out
     to be §1's `↥S`, since a coercion instance never reaches a later context); a named
     application for the student's homomorphisms (§6, for the same reason); a `HasQuotient` instance for `G ⧸ H` (§7);
     `Quotient.lift₂` for the quotient group (§9); `extends SMul` (§11); a type synonym with a
     copied instance (§11, `ConjAct`, said there with `inferInstanceAs`); `Finset.induction_on` (§12). A definition problem may
     carry the one Lean fact its shape needs, said in the description as the skill allows ("a
     Lean gotcha the mathematics cannot reveal"), and nothing more.
  3. **Every section is checked against the rule** before it is committed (**Building a
     section**, step 5), and the student review after each section asks the question
     verbatim, as Appendix G of `BEST_PRACTICES.md` does.
- **The fence rule is `polya-topology`'s**: a student builds what the subject teaches, so the
  fence keeps out the Mathlib modules that hold it. This subject teaches groups themselves, so
  the fence keeps out `Mathlib.Algebra.Group.Defs` and every module that imports it, which is
  nearly every module that touches algebra (see **The fence**). What the fence supplies is
  finite types and their cardinalities, equivalences, sets, setoids and quotients, the `⧸`, `⊤`
  and `⊥` notations, `Nat.find`, induction on `ℤ`, and the notation classes `Inv`, `Pow` and
  `SMul`, which are core's or Mathlib's notation layer and carry no algebra. Core Lean supplies
  the arithmetic: `ℤ` with `Int.add_assoc` and its kin, `%` with `Nat.mod_lt`, `Nat.mod_add_mod`
  and `Nat.mod_eq_of_lt`, `Nat.gcd`, `Nat.Coprime` and its lemmas, `Nat.mod_add_div`,
  `Nat.pow_dvd_pow`, `omega` and `decide`.
- **The student defines everything**: `Group` and `AddGroup`, `CommGroup` and `AddCommGroup`, the eight examples, powers and multiples,
  `orderOf`, `Subgroup` and `AddSubgroup`, `Subgroup.closure`, `Subgroup.zpowers`, `IsCyclic`, homomorphisms and
  isomorphisms, kernels and images, cosets, the coset relation, `G ⧸ H`, `Subgroup.index`,
  `Nat.Prime`, `Subgroup.Normal`, the quotient group, `MulAction`, orbits, stabilizers,
  `ConjAct`, `IsPGroup`. Each is a problem with a `@spec`, before anything is proved about it, as
  STYLE.md's **Every new topology is the student's to define** asks; if a draft's first problem
  about a new notion is a theorem, the draft is wrong. §1 is the exception: it takes Mathlib's
  `Set`, `Equiv`, `Setoid`, `Quotient` and `Fintype` as given, because they are the language the
  subject is written in, not what it teaches.
- **Mathlib's hierarchy does not appear.** The student's class is Milne's Definition 1.1: an
  operation, a neutral element, inverses, and the five equations G1–G3, in one declaration. No
  `Semigroup`, `Monoid` or `DivInvMonoid`: those are Mathlib's organisation of its library, not
  a way of teaching what a group is. The prose says once, in §2, that Mathlib reaches the same
  class by a tower of smaller ones, and never mentions the tower again.
- **The symbols are Mathlib's: `a * b`, `1`, `a⁻¹`, and `a + b`, `0`, `-a` for an addition**
  (the owner, 2026-10-22 for the first, reversing the 2026-10-21 choice of `∗` and `𝟙`;
  2026-10-23 for the second, replacing the wrapper `Multiplicative`; **Decisions**, 4, holds the
  designs and the probes). The symbols reach the student's classes through instances of the
  notation classes, the targets of problems of their own (`group_notation`, `add_group`), so
  that the student sees how a symbol reaches a type; Mathlib's own classes extend the same
  notation classes. `ℤ` carries `*` and `1` with their arithmetic meaning, so it cannot be a
  multiplicative group; it is an additive one, with its own `+`, and so are `ZMod n` and `Bool`
  under `xor`, which is how a first course writes them. Every general definition and theorem
  carries `@[to_additive NAME]`, so each is proved once and holds in both spellings; the student
  meets the mark in §2 and writes the additive twin of each class and structure as a short
  problem. The handoff is Mathlib's own design: Mathlib has `AddGroup`, `AddSubgroup`,
  `addOrderOf`, `zmultiples` and `to_additive` under these names, and its integers and `ZMod n`
  are additive groups. The lemma names are Mathlib's as before. (**Decisions**, 4 and 9.)
- **Identities are shown before they are asked** (2026-10-23): the first identity of a new kind
  is worked in front of the student as a `calc` chain with the law of each step, the exercise
  is its mirror image, and a subtle identity's preamble gives the chain of expressions with the
  laws left to the student (`STYLE.md`, **Identities**). §4's laws of exponents and §7's coset
  identities follow it.
- **Names follow Mathlib** all the same, so that the arrival at Mathlib's algebra changes the
  imports and not the vocabulary: the lemmas are `mul_assoc`, `one_mul`, `inv_mul_cancel`,
  `mul_left_cancel`, `mul_inv_rev`, `inv_inv`, `pow_succ`, `zpow_add`,
  `orderOf_dvd_iff_pow_eq_one`; the structures are `Subgroup` with `carrier`, `one_mem'`,
  `mul_mem'`, `inv_mem'`, `MulAction` with `one_smul`, `mul_smul`, `DihedralGroup` with `r` and
  `sr`; the theorems are `Subgroup.card_subgroup_dvd_card`,
  `QuotientGroup.quotientKerEquivRange`, `MulAction.orbitEquivQuotientStabilizer`. Where
  Mathlib's shape is awkward for a beginner (its `Subgroup` extends `Submonoid` and goes through
  `SetLike`; its `orderOf` goes through `Function.minimalPeriod`; its `ZMod n` is a ring and
  `ℤ` at `n = 0`), the student's is the textbook's shape under Mathlib's name, and the prose
  says once, at the definition, how Mathlib's differs. The name of the homomorphism structure is
  an open decision (**Decisions**, 3).
- **Cardinality is `Fintype.card`** with a `[Fintype G]` hypothesis; a quotient type gets its
  `Fintype` through `Fintype.ofSurjective` under `open Classical`. Mathlib's group theory states
  Lagrange with `Nat.card`, which is beyond the fence; the prose notes the difference once.
- **Counting is done by bijection, never by sums or products.** `Fintype.card_prod` and
  `Finset.sum` live in modules that carry `Group`. Lagrange's count goes through a chain of
  equivalences ending in `Fin (index * card H)` (see §7), and the class equation's congruence is
  proved by induction over the finite set of orbits with `Finset.card_union_of_disjoint`
  (see §12). Both are honest mathematics, counting by labelling and counting by blocks, and each
  is a problem; the first is rehearsed in §1 on `Fin m × Fin n`.
- **Arithmetic stays within core Lean**: `omega`, `decide`, `Nat.mod_add_div`, `Nat.Coprime`.
  `ring`, `linarith` and `norm_num` are not in the fence, because their modules carry `Group`,
  and the student has not met them anyway.
- **No multiplication table is proved by hand.** Groups of small order (Milne pp. 12, 15) are
  prose, except the running examples, whose small facts `decide` checks. The skill's rule 7
  applies: a case analysis the student types out teaches tedium; one `decide` does not.

## The fence

Checked on 2026-10-21 against Mathlib `v4.31.0`, the pinned revision, by compiling scratch files
that import candidate modules and nothing of this repository, and asking for `Group` (which must
be unknown) and the tools (which must be known). Nearly every module that touches algebra fails
the first test. What was probed:

| module | `Group` | useful contents |
|---|---|---|
| `Mathlib.Data.Fintype.Card` | free | `Finset`, `Fintype`, `Fintype.card`, `card_congr`, `card_of_bijective`, `card_le_of_injective`, `card_fin`, `card_pos`, `card_subtype_le`, `ofSurjective`, `ofEquiv`, `ofList`, `Subtype.fintype`, `decidableEqEquivFintype`, `decidableForallFintype`, `Finset.card_union_of_disjoint`, `Finset.induction_on`, `Finset.filter`, `Finite.injective_iff_surjective`, `Equiv.prodCongr`, `Equiv.sigmaFiberEquiv` |
| `Mathlib.Data.Fintype.EquivFin` | free | `Fintype.equivFin : α ≃ Fin (card α)` |
| `Mathlib.Logic.Equiv.Fin.Basic` | free | `finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)` |
| `Mathlib.Logic.Equiv.Defs`, `…Basic`, `…Prod` | free | `Equiv`, `Equiv.Perm`, `Equiv.ext`, `ofBijective`, `prodCongr` |
| `Mathlib.Data.Fin.Basic` | free | `Fin.ext_iff`, `Fin.val_add`, `Fin.val_neg` (not needed now that `ZMod n` is built on `ℕ` and `%`; available) |
| `Mathlib.Data.Set.Basic`, `Mathlib.Data.Set.Finite.Basic` | free | `Set`, `{x ∣ p x}`, `f '' S`, `Set.range`, `Set.ext`, `↥S` |
| `Mathlib.Data.Setoid.Basic` | free | `Setoid`; `Quotient.sound`, `exact`, `ind`, `lift`, `lift₂`, `out` |
| `Mathlib.Algebra.Quotient` | free | `HasQuotient`, the `⧸` notation |
| `Mathlib.Order.Notation` | free | `Top`, `Bot`, `Min`, `Max` |
| `Mathlib.Data.Nat.Find` | free | `Nat.find`, `Nat.find_spec`, `Nat.find_min'` |
| `Mathlib.Data.Int.Init`, `Mathlib.Data.Int.Basic` | free | `Int.induction_on` |
| `Mathlib.Data.Nat.Notation`, `Mathlib.Logic.Function.Basic`, `Mathlib.Order.Basic`, `Mathlib.Algebra.Notation.Defs`, `Mathlib.Algebra.Notation.Prod` | free | notation; `Prod.instMul` |
| `Mathlib.Data.Finset.Prod`, `Mathlib.Data.Fintype.Prod`, `…Pi`, `…Sigma`, `…Sum`, `…Pigeonhole`, `…Perm` | **carries it** | `Finset.card_product`, `Fintype.card_prod`, `exists_ne_map_eq_of_card_lt`, `Fintype (Equiv.Perm α)` (`Quotient.fintype` turned out to be in `Mathlib.Data.Fintype.Card`, 2026-10-21) |
| `Mathlib.Algebra.BigOperators.Group.Finset.Basic` | **carries it** | `Finset.sum`, `Finset.prod` |
| `Mathlib.Data.Nat.Prime.Defs`, `Mathlib.Data.Nat.GCD.Basic`, `Mathlib.Data.Int.GCD` | **carries it** | `Nat.Prime` |
| `Mathlib.Tactic.Ring`, `…Linarith`, `…NormNum` | **carries it** | the tactics |
| `Mathlib.Algebra.Group.*`, `Mathlib.GroupTheory.*`, `Mathlib.Data.ZMod.*` | **carries it** | everything the subject defines, `ZMod` and `DihedralGroup` included |

The fence, as of this draft:

```lean
import Mathlib.Data.Fintype.Card        -- Finset, Fintype, Fintype.card and its lemmas; Finset.induction_on; decide on Perm
import Mathlib.Data.Fintype.EquivFin    -- Fintype.equivFin
import Mathlib.Logic.Equiv.Fin.Basic    -- finProdFinEquiv
import Mathlib.Logic.Equiv.Defs         -- Equiv, Equiv.Perm, Equiv.ofBijective
import Mathlib.Data.Set.Basic           -- Set, {x | p x}, f '' S, Set.range, ↥S
import Mathlib.Data.Setoid.Basic        -- Setoid; Quotient.sound, exact, ind, lift, lift₂, out
import Mathlib.Algebra.Quotient         -- the ⧸ notation (HasQuotient)
import Mathlib.Order.Notation           -- ⊤, ⊥, ⊓, ⊔ as classes
import Mathlib.Data.Nat.Find            -- Nat.find
import Mathlib.Data.Int.Init            -- Int.induction_on
```

Under the union of these (compiled 2026-10-21): `Group`, `Monoid`, `MonoidHom`, `IsCyclic`,
`Nat.Prime`, `Multiplicative`, `AddGroup`, `AddSubgroup`, `ZMod`, `DihedralGroup`, and with them every name of Mathlib's
group theory, are unknown; so are the symbols `∗` and `𝟙` (Mathlib uses them only as scoped
notation in modules outside the fence) and the instances `Inv ℤ` and `Inv (Equiv.Perm X)`, so
the student's class may extend `Inv` for `⁻¹` without a collision. Known and verified:
everything in the table's "free" rows; `Inv`, `SMul`, `Pow`, `Prod.instMul`, `NeZero`; core's
`Int.add_assoc`, `Int.zero_add`, `Int.add_zero`, `Nat.mod_lt`, `Nat.mod_eq_of_lt`,
`Nat.mod_add_mod`, `Nat.add_mod_mod`, `Nat.mod_self`, `Nat.sub_add_cancel`, `Nat.Coprime`,
`Nat.Coprime.dvd_of_dvd_mul_left`, `dvd_of_dvd_mul_right`, `pow_left`, `eq_one_of_dvd`,
`Nat.coprime_iff_gcd_eq_one`, `Nat.gcd_dvd_left`, `Nat.dvd_gcd`, `Nat.mod_add_div`,
`Nat.pow_dvd_pow`; `decide` on `Bool`, on `Fin 4`, on `ZMod 6` and on equations in
`Equiv.Perm (Fin 3)`. There is no `Fintype (Equiv.Perm (Fin n))` and no `Fintype (α × β)`, so
those are the student's where needed. `One ℤ` exists (`One.ofOfNat1`), as `Mul ℤ` does, which is why
the integers enter the subject as an additive group (their `+`, `0` and `-` are the student's `AddGroup ℤ`'s, and the fence's `SMul ℕ ℤ` and `SMul ℤ ℤ` lose to the student's `•`, declared later, with the same values). `scripts/notation_probe.lean` (2026-10-22) is the probe
behind Decision 4's reopening: `Mul G` and `One G` instances derived from the student's `Group`,
the instance `Group ℤ` under addition, and what `3 * 4`, `1`, `one_mul` and a second `⁻¹` then
do; run it with `lake env lean scripts/notation_probe.lean` and read the expected outcome in the
comment on each line. `scripts/wrapper_probe.lean` (the same day) is the second probe, the
alternative design compiled: `Multiplicative ℤ` as the student writes it, `ZMod n` under `*`
with its numerals, the product diamond, and which example types carry `Mul` or `One`.

What the Group-free fence costs, and what replaces it:

| lost | replaced by |
|---|---|
| `Fintype.card_prod`, `Fintype (α × β)` | counting by labelling: `G ≃ (G ⧸ H) × H`, then `Equiv.prodCongr` of two `Fintype.equivFin`, then `finProdFinEquiv`, then `Fintype.card_congr` and `Fintype.card_fin` (§7, rehearsed in §1); `V₄` counted as `DihedralGroup 2` |
| `Finset.sum`, the class equation as a sum | block counting by `Finset.induction_on` and `Finset.card_union_of_disjoint` (§12) |
| `Quotient.fintype` | not lost after all: it is in the fence, and `Fintype (G ⧸ H)` is instance search under `open Classical in` (§1 teaches it; §7 uses it) |
| pigeonhole, `Fintype.exists_ne_map_eq_of_card_lt` | the contrapositive of `Fintype.card_le_of_injective` (§1, used in §4) |
| `Nat.Prime` | the student's `Nat.Prime`, Milne's definition, with coprimality from core's `Nat.Coprime` (§8); Euclid's lemma dropped by the owner, 2026-10-27, as nothing uses it |
| `ZMod n`, `DihedralGroup n`, `Group (G × H)`, `Group (Equiv.Perm X)` | the student's (§3), as the owner wants |
| `AddGroup ℤ`, `to_additive`'s copies | the student's `AddGroup` and its twins; `Mathlib.Tactic.ToAdditive` is in the fence, so the mark works on the student's declarations |
| `Fintype (Equiv.Perm (Fin n))` | not needed: orders are counted on `DihedralGroup n` and `ZMod n`, whose `Fintype` the student builds; `Sₙ`'s order `n!` is prose |
| `ring`, `linarith`, `norm_num` | `omega`, `decide`, `Nat.mod_add_div`, `pow_add`, `pow_mul` |

The test is per subject, not per section: the publisher checks every problem under the union
of all sections' imports, so a module that one section wants must leave `Group` unknown. Before
adding an import, compile the probe again with it. The probe script and its table go into
`scripts/` before §1.

## The sections

Sized as Profinite Spaces was: four or five concepts and sixteen to eighteen problems per
section, every reference proof under fifteen lines, one section per session. Concept slugs are
provisional. Each section gets an **As built** note when it exists.

**Spelling, from 2026-10-23.** The group operation is `*`, the neutral element `1`, the inverse
`a⁻¹`, through the `Mul`, `One` and `Inv` instances of §2 (`Group.toMul`, `Group.toOne`,
`Group.toInv`). A group whose operation is an addition is the student's `AddGroup`, written
`+`, `0`, `-a` through `Add`, `Zero` and `Neg` (`AddGroup.toAdd`, …): `ℤ`, `ZMod n` and `Bool`
under `xor` (`true + true = false`, `0 = false`) are additive groups as they stand, so `3 + x`
in `ℤ` is a sum in the group, `omega` and `decide` apply, and `{0, 2, 4}` is a subset of
`ZMod 6`. `Unit`, `Sₙ`, `Dₙ` (table `r (i + j)`, `sr (j + -i)`), products and subgroups are
multiplicative. **Every general definition and theorem carries `@[to_additive NAME]`**, which
makes its additive copy under Mathlib's name (`mul_left_cancel` → `add_left_cancel`, `g ^ n` →
`n • a`, `orderOf` → `addOrderOf`, `Subgroup` → `AddSubgroup`, `zpowers` → `zmultiples`,
`IsCyclic` → `IsAddCyclic`); the name is always written out, for the publisher's closure, and
each section file sets `linter.translateGenerateName false` so that a written name equal to the
generated one is not a warning. `to_additive` cannot make a class or a structure, or a recursive
definition whose equations it would have to regenerate: each such notion has an **additive twin
the student writes as a short problem right after the original** (`add_group`, the `AddCommGroup`
half of `comm_group`, `nsmul`, `zsmul`, `add_subgroup`), followed outside the block by lines
`attribute [to_additive existing AddGroup] Group` pairing the two, one declaration per line. For
§6–§12 this means: `GroupHom` gets the twin `AddGroupHom` (`A →+ B`) and `GroupIso` the twin
`AddGroupIso` (`≃+`) (**Decisions** 3); `Subgroup.Normal` its `AddSubgroup.Normal`; the quotient group `G ⧸ N` its
additive quotient `A ⧸ N` for an additive subgroup (`QuotientAddGroup`), so that `ℤ ⧸ nℤ` and
`ZMod 6 ⧸ ⟨3⟩` are additive quotients; `MulAction` its `AddAction` only if `ZMod n` acting on
`Fin n` stays (it can be dropped: `Dₙ` on the vertices shows the same). A map from a
multiplicative group to an additive one is the one awkward case, and the parity maps avoid it
by landing in `Equiv.Perm (Fin 2)`, the symmetric group on two points, multiplicative: the
orientation `Dₙ →* Equiv.Perm (Fin 2)` (rotations to `1`, reflections to the swap) in §6, §9's
universal property and §10's `Dₙ ⧸ rotations ≃* Equiv.Perm (Fin 2)`; §12's involution acting on
`Fin n` is an action of `Equiv.Perm (Fin 2)` too. `ZMod 2 ≃+ Bool` joins two additive groups.
The entries of §6–§12 below, written before that date, say `ℤ`, `ZMod n`, `∗` and `𝟙` for
short, and `Bool` for the parity target: read `+`, `0`, `-` and the additive twins for `ℤ`,
`ZMod n` and `Bool`, `*` for `∗`, `1` for `𝟙`, and `Equiv.Perm (Fin 2)` for the target of a
parity map. A session building a section writes its Lean in this spelling and may rewrite its
entry to match (`STYLE.md`, **Notation and names**). The spelling of 2026-10-22, the wrapper
`Multiplicative`, is recorded under **Decisions**, 4.

### §1. Prerequisites

Milne p. 5 and the background his notes assume. No group appears. Each concept is a piece of
mathematics the student has, or can be told in a sentence, and its problems are where the Lean
for it is learned: Mathlib's names for Set Theory's sets, bijections as `Equiv`, equivalence
relations and their classes as `Setoid` and `Quotient`, counting with `Fintype`, and the
integers and remainders. Every later section leans on this one and introduces Lean only where
the mathematics cannot be separated from it (**Design points**, the rule). The problems re-prove
facts the student knows, so that the only new thing in each is the Lean; where a Mathlib lemma
closes a statement in one name, the problem asks for the fact one step beyond it.

- `mathlib_sets`: Mathlib's `Set α` is Set Theory's `Set` under other names: `Set.ext`,
  `{x | p x}` and `Set.mem_setOf_eq`, `f '' S`, `Set.range f`, and a set as a type, `↥S`, whose
  elements are pairs of a point and a proof; problems: `f '' (S ∪ T) = f '' S ∪ f '' T` again
  (Set Theory proved it for its own `Set`), `Set.range f = f '' Set.univ`, and a function
  `↥S → α` from a set to its type. (3)
- `functions`: `Function.Injective`, `Surjective` and `Bijective` as Mathlib spells them
  (Naturals wrote its own `Function.Injective`); the composition of injective maps is injective,
  of surjective maps surjective; a left inverse makes a map injective. (3)
- `bijections`: an `Equiv` `α ≃ β` is a pair of inverse functions with the two proofs, applied
  through a coercion (`e x`, Mathlib's `CoeFun`), compared by `Equiv.ext`, with `refl`, `symm`,
  `trans` and `ofBijective`; `Equiv.Perm α` is `α ≃ α`; problems: `Bool ≃ Fin 2` written out,
  `(e.trans f).symm = f.symm.trans e.symm`, a permutation of `Fin 3` written out and two of its
  values checked by `decide`. (3)
- `relations`: a relation is `α → α → Prop` (Logic's `relations`); reflexive, symmetric and
  transitive, bundled as `Equivalence r` (core) and as `Setoid α` with `a ≈ b`; problems: "same
  remainder mod `n`" on `ℕ` is an equivalence; "same image under `f`" is an equivalence, for any
  `f : α → β`; a `Setoid` instance for the first. (3)
- `equivalence_classes`: the classes of an equivalence relation partition the set (prose, with
  Milne's `[∗]`); `Quotient s` as the type of classes, `⟦a⟧`, `Quotient.sound` and
  `Quotient.exact` (`⟦a⟧ = ⟦b⟧ ↔ a ≈ b`), `Quotient.ind` (to prove something of every class,
  prove it of every `⟦a⟧`), `Quotient.lift` (a function constant on classes descends to the
  classes), `Quotient.out` with `open Classical` (choosing a representative is a choice, and the
  function is `noncomputable`); problems: the classes of "same remainder mod `n`" map to `Fin n`
  by `Quotient.lift`, injectively; `Quotient.mk` is onto; a quotient of a finite type is finite,
  `Fintype.ofSurjective`. (4)
- `finite_types`: `Fintype α` as a list of all the elements, `Finset.univ`, `Fintype.card α`;
  `Fin n` and `Fintype.card_fin`; `decide` over a finite type (`∀ x : Fin 4, …`); a bijection
  preserves cardinality (`Fintype.card_congr`), an injection does not increase it
  (`Fintype.card_le_of_injective`), so a map `Fin (n + 1) → Fin n` has two inputs with one
  output (pigeonhole, the contrapositive) and an injective self-map of a finite type is onto
  (`Finite.injective_iff_surjective`); counting by labelling: `Fintype.equivFin` and
  `finProdFinEquiv`, so that `α ≃ Fin m × Fin n` gives `Fintype.card α = m * n`, the shape of
  Lagrange's count. (4)
- `integers_and_remainders`: `ℤ` as a type: literals, `Int.ofNat` and `Int.negSucc` by cases,
  `omega` on `ℤ`, `Int.add_assoc` and its kin; `%` on `ℕ`: `Nat.mod_lt`, `Nat.mod_eq_of_lt`,
  `Nat.mod_add_mod`, `Nat.mod_add_div`; the least natural number with a property, `Nat.find`,
  with `Nat.find_spec` and `Nat.find_min'`; `Nat.gcd` and `Nat.Coprime`,
  `Nat.Coprime.dvd_of_dvd_mul_left`; problems: `(a + b) % n = ((a % n) + (b % n)) % n`;
  `Nat.find` of `∃ k, 0 < k ∧ 12 % k = 0 ∧ 18 % k = 0`'s complement, or simply the least
  positive multiple of 3 above 10, by `decide`; `Nat.Coprime 4 9` and a use of
  `dvd_of_dvd_mul_left`. (3)

Budget: 23, which is over; the section is honest at 18–20 if `functions` folds into
`mathlib_sets` and `finite_types` loses the pigeonhole problem to §4, where it is used. It is
the one section whose problems are allowed to be one Mathlib name long, since naming the lemma
is the point; the stub-shortcut check is run on it anyway, and a problem it flags is replaced by
the fact one step beyond the lemma.

**As built (2026-10-21).** `PolyaAlgebra/GroupTheory/Prerequisites.lean`: 24 problems over
7 concepts, in this order, each concept's problems after its slug: `mathlib_sets`
(`image_union`, `restrict_mem_image`, `image_eq_range`); `functions` (`composites`,
`one_sided_inverses`, two theorems each); `bijections` (`not_equiv`, `bool_equiv_fin_two`,
`equiv_bijective`, `rot3`); `finite_types` (`fin_four_add_neg` with `card_fin_four`,
`card_of_equiv_prod`, `bijective_of_injective` under `[Finite α]`); `integers_and_remainders`
(`int_cases`, now "every integer is a difference of two naturals", since `Int.eq_nat_or_neg`
closed the planned statement in one name; `mod_add_mod` with the warm-up `mod_mod_of_pos`;
`find_least` with `find_sqrt_fifty`, which uses `Nat.find_eq_iff`; `coprime`); `relations`
(`ker_equivalence`, `same_parity` on `ℤ` with a witness, `mod_setoid`); `equivalence_classes`
(`quotient_eq_iff_mod`, `to_fin`, `residue`, `residue_bijective`, `card_quotient_le` under
`open Classical in`), with `@goal` on the last concept. The order puts the integers before the
relations, so that `%` and `Nat.mod_lt` precede `modSetoid` and `residue`. The pigeonhole
problem went to §4 as planned; `functions` kept two problems rather than folding. Extraction:
24 problems, 0 errors; the budgets, prose-name, stub-shortcut and vocabulary checks are clean
(0 of 24 references use anything untaught, against polya-basic's five bundles); every
definition's spec was compiled against correct variants and a wrong one.

The student review (one blind agent per concept, from the answer-free bundle, three at a time,
`scripts/review/`) ran the same day and changed the draft in these ways, each a rule for the
sections to come: four warm-ups split a second Lean device out of a problem
(`restrict_mem_image` for a set as a type, `not_equiv` for `Equiv`/`where`/`decide`, `to_fin`
for `NeZero` and the `Fin` constructor, `mod_mod_of_pos` for `Nat.mod_lt`); two references were
rewritten to use the earlier theorem the prose pointed to, since the checker's context holds
only what the reference uses (`equiv_bijective` through `injective_of_left_inverse`,
`residue_bijective` through `quotient_eq_iff_mod`), and the descriptions say the context holds
them; three preambles that handed over a proof or a witness were trimmed to the idea; `Setoid`
is core Lean's and a `class`, and Lean prints `⟦a⟧` and `a ≈ b` whatever the setoid, which the
prose now says; `omega` does not identify `Int.ofNat n` with `↑n`, which the prose now says;
"you may use them from here on" became "in later problems", since the named lemma closed the
problem in one token; `same_difference` on pairs became `same_parity`, a witness-carrying
relation of the shape cosets and orbits will have; the `Finite` class is shown, not described.
Six pages are under the 17-line floor and say what they need; none is over 27.

### §2. Groups

Milne 1.1–1.3, 1.10. The student writes the definition, meets three instances, and proves what
follows from the axioms. The Lean that is new here is the class with its own notation, and
nothing else: `Unit`, `Bool`, `ℤ`, `decide` and `Fintype.card` are §1's.

- `group_axioms`: `class Group (G : Type) extends Inv G` with fields `mul` and `one`, the
  notations `a ∗ b` and `𝟙`, and the five equations of G1–G3, `mul_assoc`, `one_mul`,
  `mul_one`, `inv_mul_cancel`, `mul_inv_cancel` (the shape is **Decisions** 4); the prose says
  that the operation is whatever the group's is, and that Mathlib writes it `*`; the trivial
  group `Unit`; `Bool` under `xor` as the group of order two, closed by `decide`; `ℤ` under
  addition (Milne 1.3), where `𝟙` is `0` and `a⁻¹` is `-a` by `rfl`. (5)
- `consequences`: Milne 1.2 (a)–(d) under Mathlib's names: the neutral element is the only
  solution of `x ∗ x = x`; an element with a left inverse and a right inverse has them equal;
  `inv_inv`; `inv_one`; `mul_inv_rev`; `mul_eq_one_comm`; in `Bool` every element is its own
  inverse. (6)
- `cancellation`: `mul_left_cancel`, `mul_right_cancel` and their `↔` forms (1.2 e); solving
  `a ∗ x = b`; left multiplication by `a` is a bijection (prepares Cayley). (3)
- `finite_groups`: the order of a group is `Fintype.card G`; in a finite group left
  multiplication is onto (`Finite.injective_iff_surjective`, §1); Exercise 1-8, a nonempty
  finite set with an associative cancellative operation is a group, as extra credit. (2)

Budget: 16. Aside 1.10, the one-sided axioms, is a problem of `consequences` or extra credit: a
`def Group.ofLeftAxioms` from `mul_assoc`, `one_mul` and `inv_mul_cancel` alone, Mathlib's name.

Notes from §1 (2026-10-21): the `ℤ` instance's description names the five core laws it needs,
`Int.add_assoc`, `Int.zero_add`, `Int.add_zero`, `Int.add_left_neg : -a + a = 0` and
`Int.add_right_neg : a + -a = 0`, as options; §1 taught `ℤ`'s constructors and `omega` but
deliberately not these names. `consequences` must prove `inv_one`, which §3's dihedral
instance needs for `one_mul`. The `Bool` instance under `xor` closes every law by `decide`.

**As built (2026-10-21).** `PolyaAlgebra/GroupTheory/Groups.lean`: 17 problems over 4
concepts, in this order: `group_axioms` (`group`, the class, with an authored spec that
accepts both binder styles; `unit_group`; `bool_xor_group`, with `card_bool`; `int_add_group`,
with `int_mul_eq_add`, `int_one_eq_zero` and `int_inv_eq_neg`, the three `rfl` theorems later
sections rewrite with); `consequences` (`cancel_adjacent`, the four adjacent cancellations;
`neutral_unique`, `mul_eq_left`, `mul_eq_right` and `eq_one_of_left_neutral`; `inverse_unique`,
`left_inv_eq_right_inv` and `inv_eq_of_mul_eq_one_right`; `inv_inv`, with `inv_one` and
`inv_injective` through §1's `injective_of_left_inverse`; `mul_inv_rev`; `self_inverse_comm`,
`Bool` by `decide`, the general theorem `mul_comm_of_inv_eq_self`, and `Bool` again from it);
`cancellation` (`mul_left_cancel` and `mul_right_cancel` with their `↔` forms;
`solve_equation`, `eq_inv_mul_iff_mul_eq` through `mul_left_cancel` and
`(3 : ℤ) ∗ x = 7 ↔ x = 4` through `int_mul_eq_add` and `omega`; `Group.mulLeft_bijective`,
Mathlib's name, with `bool_mul_true` by `decide`), with the `@goal`; and `one_sided_axioms`
(Aside 1.10: `op_inv_of_left_axioms` and `op_e_of_left_axioms` on a bare operation, then
`Group.ofLeftAxioms` as an `abbrev`, then `intGroupLeft : Group ℤ` from three laws of
addition, the concept's running example), after the goal as extra credit. Extraction: 41
problems, 0 errors; the budgets, prose-name, stub-shortcut and vocabulary checks are clean
(0 of 41). The two problems that mention the class's field names in a `where` body
(`Group.ofLeftAxioms` and what is built from it) pull the five restated laws into their context
through the token scan and need a second round for the `Inv` instance; the extract says so as a
warning, and the check passes.

The student review (one blind agent per concept, `scripts/review/`, the brief with a
`{SECTION_BLURB}`) ran the same day: every problem of the four concepts passed on the
reviewers' first or second attempt, no double teaching was found outside the declared exception
(the class itself), and the draft changed in these ways: the laws are stated one orientation
each with the naming rule (`one_mul` for `𝟙 ∗ a = a`), and the class spec accepts either
orientation through `grind`, since the natural transcription of a chain `𝟙 ∗ a = a = a ∗ 𝟙`
is `a = mul a one`; `class Inv` is shown and the notation lines named at `unit_group`; the claim
that `omega` sees through `∗` is confined to the inside of the instance; three preambles that
gave the steps in order were cut to the idea; `inverse_unique` says the cancellations are not
in its context, and `solve_equation`'s references go through `mul_left_cancel` and
`int_mul_eq_add` so that the routes the prose invites are in the context; a false title ("Self-
Inverse Elements Commute") became "A Group of Self-Inverse Elements is Commutative";
`eq_one_of_left_neutral` and `bool_mul_true` were added; the `rw`-does-not-see-through-`fun`
gotcha is said at `inv_inv` and `Group.mulLeft_bijective`.

Three departures from the entry above, each forced by the tooling or the fence. (1) **The class
does not `extends Inv G`**: the publisher skips the field check of a structure that extends
another and hands the student an empty body, so `inv` is a third data field and the `Inv G`
instance is a `@given` of `unit_group`, the first problem whose spec writes `⁻¹`; the five
laws restated under the notation (`mul_assoc : a ∗ b ∗ c = a ∗ (b ∗ c)`, …) are `@given`s of
`cancel_adjacent`, the first problem that rewrites with them, since a notation command cannot
sit inside a problem block and the class's own spec is therefore stated with `Group.mul`.
(2) **`finite_groups` is not a concept**: left multiplication is onto in every group, so a
finiteness hypothesis on it is pointless, and the order of a group is defined in prose at
`bool_xor_group` with `card_bool`; Exercise 1-8 is not built, and the one-sided axioms took the
two remaining problems. (3) **The cancellation example is `ℤ`**, not `S₃`, whose instance is
§3's; §3 should add `r ∗ s = r ∗ x → x = s` there if it has room.

**As refactored (2026-10-22).** To Mathlib's symbols, by the owner's decision of that day
(Decision 4): `group` keeps its class and loses its notation paragraph; `group_notation` is new,
its targets the instances `Mul G`, `One G` and `Inv G` with a `rfl` spec pinning the three
symbols to the fields; `unit_group` loses the `Inv` given; `bool_xor_group` says that the group's
`1` on `Bool` is `false`; `multiplicative` is new, the student's `def Multiplicative (α : Type u)
:= α` with `ofAdd`, `toAdd`, `toAdd_ofAdd`, `ofAdd_toAdd`, `ofAdd_inj` and a `DecidableEq`
instance given by `inferInstanceAs`; `int_add_group` is `Group (Multiplicative ℤ)` from the five
core laws applied to `toAdd`, with the six equations `ofAdd_add`, `ofAdd_zero`, `ofAdd_neg`,
`toAdd_mul`, `toAdd_one`, `toAdd_inv` replacing `int_mul_eq_add`, `int_one_eq_zero` and
`int_inv_eq_neg`; `int_solve` reads `ofAdd 3 * x = ofAdd 7 ↔ x = ofAdd 4`, through
`eq_inv_mul_iff_mul_eq` and the equations read right to left; every other problem changed symbol
only. 16 problems over 4 concepts; the one-sided axioms stay in Extra Credit with `intGroupLeft :
Group (Multiplicative ℤ)`. The record of the earlier design is Decision 4 and
`scripts/notation_probe.lean`. The student review of `group_axioms` after the refactor (one blind
agent, `scripts/review/`, same day) solved all six problems, five at the first attempt, found no
double teaching, and changed four things: `int_add_group` gained the theorem
`int_three_mul_four` its description promised (a spec is invisible to the student) with the
ascription `ofAdd (3 : ℤ)` in the prose; `multiplicative` says the equivalence closes by
`Iff.rfl`; `bool_xor_group` argues `a * a = a → a = 1` by multiplying with `a⁻¹`, not by a
cancellation not yet proved; `group_notation` shows the pattern on `Add Vec3` instead of
printing the first answer. The extract of the refactored subject needed a publisher fix
(`STYLE.md`, **Learned refactoring**): 108 problems, 0 errors through the patched checkout,
pending the owner's release and the lakefile's repin.

**As refactored (2026-10-23).** To additive groups, by the owner's decision of that day
(Decision 4): `group_notation` names its instances `Group.toMul`, `Group.toOne` and
`Group.toInv`; `multiplicative` is gone, and `add_group` is new, the class `AddGroup` with `add`,
`zero`, `neg` and the five additive laws, the instances `AddGroup.toAdd`, `AddGroup.toZero` and
`AddGroup.toNeg`, and four `attribute [to_additive existing …]` lines after the block pairing
`Group` and its instances with them; `int_add_group` is `AddGroup ℤ` from the integers' own
operations and the five core laws, with no equations to state; `bool_xor_group` moves after it
and is `AddGroup Bool`, `true + true = false`, `0 = false`; `cancel_adjacent` says that every
theorem from there on carries a mark; `to_additive` is new, the mark explained on
`mul_mul_inv_mul_inv_cancel` and used at once through its copy on `x + 5 + -5 + -x = 0` in `ℤ`;
every general theorem carries `@[to_additive NAME]` with Mathlib's additive name (`mul_inv_rev`
named by hand `neg_add_rev`, Lean's own translation being `add_neg_rev`); `self_inverse_comm`
proves `bool_neg_self` and `bool_add_comm` through `add_comm_of_neg_eq_self`; `int_solve` is `3 +
x = 7 ↔ x = 4` through `eq_neg_add_iff_add_eq`; `bool_true_add` checks that adding `true` is
`!`. 17 problems over 4 concepts. In Extra Credit `Group.ofLeftAxioms` carries its mark and
`intGroupLeft : AddGroup ℤ` is built by `AddGroup.ofLeftAxioms`, `intGroupLeft_add` checking `3 +
4 = 7`; the subgroup criterion carries marks, its copy `AddSubgroup.ofSub`.

**Revised (2026-10-23), identities.** On the owner's point that a student sees the first group
identities as obvious and has no idea how to prove them (the model being Algebra.lean of the
LeanPIMS26 course), `first_identity` is new and comes first in `consequences`: why an identity
needs proving, `inv_mul_cancel_left` worked as a given `calc` chain with the law of each step,
the same as one `rw`, and the mirror `mul_inv_cancel_left` as the exercise; `cancel_adjacent`
keeps the two right-hand forms; `neutral_unique`, `inverse_unique`, `mul_inv_rev` and
`mul_left_cancel` give the chain of expressions, the laws left to the student (`STYLE.md`,
**Identities**). 18 problems over 4 concepts.

The same day the rule was carried through §3–§5 and Extra Credit: in §3, `zmod_add_laws` works
`ZMod.zero_add` as a given, one rewrite per line with the goal each leaves, the student proving
`add_zero`, `add_comm` and `add_assoc`, and the new `zmod_neg_laws` takes the two cancellation
laws with the chain of values `((n - a.val) % n + a.val) % n = … = 0 % n`; `comm_rearrange` and
`dihedral_mul_assoc` give chains (21 problems over 5 concepts). In §4, `pow_one` keeps the
definition's equations and `g ^ 1 = g`; the new `one_pow` works `1 ^ n = 1` as an induction with
a `calc` step and asks for `pow_succ'` (its reference a `calc` too); the new `zpow_zero_one`
separates the `change` device from the sign law, which `zpow_neg` keeps with a chain per case;
the new `pow_mod_order_of` takes `pow_mod_orderOf` and its chain out of
`order_of_dvd_iff_pow_eq_one`; `pow_add`, `zpow_add_one`, `zpow_add`, `finite_order_of_finite`
and `inv_eq_pow` give their chains (26 problems over 4 concepts). In §5, `center` gives the
chains of its two closure proofs; in Extra Credit, `left_axioms_laws` gives the whole chain in
the notation `*`, `1`, `⁻¹`, the left laws only. 115 problems.

**Revised (2026-10-23), `ZMod n`.** On the owner's finding that the structure was "a lot of
book-keeping for very little payoff", `ZMod n` is `abbrev ZMod (n : ℕ) := Fin n`, Mathlib's own
definition for positive `n`, and the remainder laws whose arithmetic is fiddly
(`ZMod.add_assoc`, `ZMod.neg_add_cancel`) are given. `zmod` defines the `abbrev`, shows Lean's
`Fin` addition, negation and numerals, and proves the value equations, the count and a numeral;
`zmod_add_laws` works `ZMod.zero_add` and asks for `add_zero`, `add_comm` and `add_neg_cancel`;
`zmod_group` and `zmod_two_equiv_bool` stand; `zmod_add_neg`, `zmod_neg_laws` and `zmod_fintype`
are gone. `prod_fintype`'s labelling is `finProdFinEquiv` turned round, and the dihedral
labelling passes residues as they are. §3 has 18 problems over 5 concepts; the subject 112.

### §3. Examples

Milne 1.3–1.6, 1.16, 1.17. The finite groups the subject lives on, each a definition problem
with a spec, each with one or two facts checked by `decide`. The Lean that is new here is one
thing per concept, and each is a definition's own shape: a structure with a proof field, an
instance on `Equiv.Perm`, an inductive with a multiplication table.

- `integers_mod_n`: the student's `structure ZMod (n : ℕ) where val : ℕ; val_lt : val < n`,
  its `Group` instance for `n ≥ 1` with `a ∗ b = (a + b) % n`, `𝟙 = 0` and `a⁻¹ = (n - a) % n`,
  the five laws each a line from §1's `%` lemmas and `Nat.sub_add_cancel` (checked); nothing of
  Mathlib's `ZMod` is used, and the prose says only that Mathlib has a type of the same name
  that is also a ring; the `Fintype` instance from `Fin n` (§1's `Fintype.ofEquiv`) and
  `Fintype.card (ZMod n) = n`; `ZMod 2 ≃ Bool` as a bijection (the isomorphism waits for §6).
  (5)
- `symmetric_groups`: the student's `instance : Group (Equiv.Perm X)` with `f ∗ g = g.trans f`,
  so that `(f ∗ g) x = f (g x)` as Mathlib has it, every law by `rfl` or `Equiv.ext`; `Sₙ` is
  `Equiv.Perm (Fin n)`, and `S₃`'s rotation `r : i ↦ i + 1` and reflection `s : i ↦ -i` written
  out as `Equiv`s; `r ∗ s ≠ s ∗ r` by `decide`, the first non-commutative group. (3)
- `dihedral_groups`: `inductive DihedralGroup (n : ℕ) | r (i : ZMod n) | sr (i : ZMod n)`,
  Mathlib's shape, read as the rotations and the reflections of the `n`-gon; the four-line
  multiplication table `r i ∗ r j = r (i ∗ j)`, `r i ∗ sr j = sr (j ∗ i⁻¹)`,
  `sr i ∗ r j = sr (i ∗ j)`, `sr i ∗ sr j = r (j ∗ i⁻¹)`, in `ZMod n`'s own operation (the
  warm-up on reading a table: `sr 0 ∗ r 1 ∗ sr 0 = (r 1)⁻¹` in `D₄` by `decide`); the `Group`
  instance, associativity by cases and the `ZMod n` laws; the `Fintype` instance from
  `Fin (2 * n)` and `Fintype.card (DihedralGroup n) = 2 * n`; `V₄` is `DihedralGroup 2`. (5)
- `product_groups`: the student's `instance : Group (G × H)` (1.5); `CommGroup` with `mul_comm`
  (1.6), with `ℤ`, `ZMod n` and `G × H` of commutative groups as instances and `S₃` as the
  non-instance; commuting elements and the commutator `a ∗ b ∗ a⁻¹ ∗ b⁻¹`. (4)

Budget: 17. Hazards: `ZMod n` is a group only for `n ≥ 1`; `[NeZero n]`, core's class, carries
the hypothesis and the prose says once what it means, or the instance is on `ZMod (n + 1)`;
settled when §3 is built. `DihedralGroup n`'s `Fintype` needs a bijection with `Fin (2 * n)`
through `finProdFinEquiv`, a small problem of its own.

**As built (2026-10-21).** `PolyaAlgebra/GroupTheory/Examples.lean`: 19 problems over 5
concepts, in this order: `integers_mod_n` (`zmod`, the structure with `deriving DecidableEq`
and the `OfNat (ZMod n) k` instance in one problem; `zmod_add_neg`, `ZMod.add` and `ZMod.neg`
with the two `rfl` equations `ZMod.val_add` and `ZMod.val_neg`; `zmod_group`, the instance
with `ZMod.ext` as a given, the three `rfl` theorems `ZMod.val_mul`, `ZMod.val_one` and
`ZMod.val_inv`, and `3 ∗ 4 = 2` in `ZMod 5` by `decide`; `zmod_fintype`, `finEquivZMod` with
the `Fintype` instance, `card_zmod`, and every element of `ZMod 6` having an inverse by
`decide`;
`zmod_two_equiv_bool`, with `decide` showing the bijection carries the one table to the
other); `symmetric_groups` (`perm_group`, `f ∗ g = g.trans f` with `Equiv.ext` for the
cancellations; `reflect3`, `i ↦ -i` with `reflect3 ∗ reflect3 = 𝟙` and `rot3`'s cube restated in the
group's symbols; `s3_not_comm`, the `≠` by `decide`, the rule `reflect3 ∗ rot3 = rot3⁻¹ ∗
reflect3`, and the cancellation example §2 could not do, `rot3 ∗ x = rot3 ∗ reflect3 → x =
reflect3`); `commutative_groups` (`comm_group`, `class CommGroup extends Group` with the
`have`-then-`grind` spec; `comm_instances`, `ℤ`, `ZMod n` and `Bool`, with `mul_comm` restated as a
given; `comm_rearrange`, `mul_left_comm` and `mul_right_comm`, which the dihedral table
needs); `product_groups` (`prod_group`, the instance with `prod_mul_def` and `(1, 2) ∗ (1, 2)
= (0, 1)` in `ZMod 2 × ZMod 3`; `prod_fintype`, `Fin 6 ≃ ZMod 2 × ZMod 3` through
`Equiv.prodCongr` and `finProdFinEquiv`, its `Fintype` instance and the count `6`;
`prod_comm_group`, with the commutativity of `ZMod 2 × ZMod 3` by `decide` over its pairs); `dihedral_groups` (`dihedral_mul`, the
inductive and the table in one problem with `sr 0 ∗ r 1 ∗ sr 0 = r 3` in `D₄`;
`dihedral_mul_assoc`, the four table equations as `rfl` givens, then the eight cases by
`cases a <;> cases b <;> cases c <;> simp only [the four]` and one `rw` each;
`dihedral_group`, the instance with `d4_not_comm`; `dihedral_fintype`, `DihedralGroup.equivProd`
into `Fin 2 × Fin n` with the `Fintype` instance through `finProdFinEquiv` and `card_dihedral`
from §1's `card_of_equiv_prod`; `klein_four`, every element of `D₂` self-inverse by `decide`,
the `CommGroup (DihedralGroup 2)` instance from §2's `mul_comm_of_inv_eq_self`, and `1` not
self-inverse in `ZMod 4` by `decide`), with the `@goal`. The order puts `commutative_groups` before `product_groups` and `dihedral_groups`,
since the table's associativity rearranges products in `ZMod n`; the entry's `product_groups`
split into two concepts, and the commutator was dropped for the budget. Extraction: 60
problems, 0 errors; budgets, prose names, stub shortcuts and the vocabulary audit (0 of 59)
clean; every spec was compiled against variants (both binder styles and both orientations of
`mul_comm`, the dihedral table in the other orientation, `finEquivZMod` as an anonymous
constructor, `equivProd` with an `if` inverse) and a wrong definition each.

The student review (one blind agent per concept, `scripts/review/`, the brief with the
section's blurb) ran the same day: every problem of the five concepts passed on the
reviewers' first or second attempt, and no double teaching was found except the one the
reviewer of `dihedral_mul_assoc` flagged, since fixed. The draft changed in these ways:
`dihedral_mul`'s prose read the table in written order, against §3's own convention that in
`f ∗ g` the right factor acts first, and now reads it the other way, with `sr i` glossed as `s`
after the rotation `r i`; `dihedral_mul_assoc` no longer hands over `exact congrArg r (by rw
…)`, a term-mode shape the student had never met over unnamed residues, and the four table
equations are givens the proof rewrites with after `simp only` unfolds them; four preambles
that handed over a witness, a proof in order or a tactic script (`zmod_add_neg`'s
constructor, `zmod_group`'s steps, `comm_instances`'s route, `prod_group`'s two `rw`s) were
cut to the idea or the reason; `zmod_group` now says to build the neutral element as
`⟨0, _⟩` and why the numeral `0` strands `one_mul`; the prose named facts the context did
not hold (`Bool` and `Unit` commutative "by `decide`" in `comm_instances`, `decide` over
`ZMod 6` in `zmod_fintype`, "of order six" in `prod_comm_group` with no `Fintype` on a
product), and each became an exercise whose reference pulls the instance: `CommGroup Bool`,
`zmod_six_has_inv`, and the new problem `prod_fintype` with `zmod_two_three_comm` by
`decide` over the thirty-six pairs; numeric checks were added where a running example had
none (`3 ∗ 4 = 2` in `ZMod 5`, `rot3`'s cube in the group's symbols, `reflect3 ∗ rot3 =
rot3⁻¹ ∗ reflect3`, `1` not self-inverse in `ZMod 4`); `s3_not_comm` says the first error a
student meets (`decide` refuses a goal with a free variable) before the missing list of
permutations; the `.symm` direction of `Fintype.ofEquiv`, the bare `rw [mul_comm]` trap, and
`rw [mul_comm a b]` naming its product are said at first use; `ZMod.ext` is given with
`subst h`, the taught form, not `cases h`; two concept descriptions lost forward references
and the undefined letters `r`, `s`, and `n!`; and `ZMod 2 × ZMod 2` and `D₂`, both called
the Klein four-group, are connected in `klein_four`'s preamble. The reviewers' commonest
finding was again a context gap behind a prose promise, not double teaching.

Five departures from the entry, each forced by the tooling or the fence. (1) **`ZMod n`'s
laws go through named operations**: Mathlib's `linter.style.show`, in the lakefile's standard
set, refuses a `show` that changes the goal, and `rw` cannot see through the constructor
`⟨(a.val + b.val) % n, _⟩` an inline `mul` leaves in a law's goal; so `ZMod.add` and `ZMod.neg`
are definitions of their own with `rfl` equations for their values, and each law is `apply
ZMod.ext` then `rw` with them and the `%` lemmas. (2) **The `OfNat` instance is the
structure's problem**, not a problem of its own, to stay within eighteen. (3) **The table's
spec is `rfl`** in the orientation the description states: a `simp [DihedralGroup.mul,
mul_comm]` spec, which accepts the other orientation, needs the `CommGroup (ZMod n)`
instance, which the reference does not use and the context therefore lacks. (4) **A shared
auxiliary proof pulls an unrelated definition into a context.** Lean deduplicates the
abstracted proofs of definitions within a module: the first definition needing the instance
`NeZero 2` mints `_proof_1 : NeZero (1 + 1)`, and every later definition needing it reuses that
constant, so the build's dependency graph says `DihedralGroup.equivProd` uses
`zmodTwoEquivBool._proof_1`, and the closure pulled `zmodTwoEquivBool` into the contexts of
`dihedral_fintype` and `klein_four` without its own dependencies, where its `decide` failed
("preamble closure: no progress"). The fix in the content: `zmodTwoEquivBool` tests `a.val = 1`
and builds `⟨1, by decide⟩`, using no numeral of `ZMod 2`, so the first definition that needs
`NeZero 2` is `equivProd` itself, which every later `D₂` context holds anyway. The rule, in
`STYLE.md`: two definitions of a section that need the same `NeZero k` instance share a proof
constant, and the later one's context will hold the earlier one. (5) **`one_sided_axioms`
moved to a section of its own, `ExtraCredit.lean`, imported last by the root**: by the
syllabus rule every concept declared before the goal is on its path, so once the goal moved
from `cancellation` to `dihedral_groups` the one-sided axioms would have been recommended;
in a last section they stay after the goal as it moves, and the extract still lists them as
extra credit. Slugs are unchanged. `Prod.mul_def` exists under the fence (for `*`), so the
product's equation is `prod_mul_def`; `check_prose_names.py` now falls back to the reference
when the stub cannot compile (an inductive's stub has no constructors).

**As refactored (2026-10-22).** `ZMod n` is additive: `zmod_add_neg` supplies `Add (ZMod n)` and
`Neg (ZMod n)` with `ZMod.val_add : (a + b).val = …` and `ZMod.val_neg`; `zmod_add_laws` is new,
the six laws `ZMod.add_assoc`, `ZMod.zero_add`, `ZMod.add_zero`, `ZMod.neg_add_cancel`,
`ZMod.add_neg_cancel`, `ZMod.add_comm`, with `ZMod.ext` and `ZMod.val_zero : (0 : ZMod n).val =
0 % n` as givens; `zmod_group` is `Group (Multiplicative (ZMod n))` from those laws applied to
`toAdd`, with `ZMod.ofAdd_add` and its five companions and `zmod_five_check`; `zmod_fintype`
keeps `finEquivZMod`, `Fintype (ZMod n)` and `card_zmod`, and the new `multiplicative_fintype`
(a split the review asked for) carries the generic `Fintype (Multiplicative α)` across by
`inferInstanceAs`, with `Fintype.card_multiplicative`, `card_mul_zmod` and `zmod_six_has_inv`; `zmodTwoEquivBool_mul` became `zmodTwoEquivBool_add`, `e (a + b) = e a * e
b`; `comm_instances` builds `CommGroup (Multiplicative ℤ)`, `CommGroup (Multiplicative (ZMod n))`
and `CommGroup Bool`; `zmod_add_rearrange` is new, `ZMod.neg_neg`, `ZMod.neg_zero`,
`ZMod.neg_add_rev`, `ZMod.add_left_comm` and `ZMod.add_right_comm` each as a group theorem
applied to `ofAdd a` by `exact`; the product example is `Multiplicative (ZMod 2) × Multiplicative
(ZMod 3)`; the dihedral table is Mathlib's, `r (i + j)`, `sr (j + -i)`, `sr (i + j)`, `r (j +
-i)`, its associativity proved from the five residue facts, the instance with `one := r 0` and
`inv (r i) = r (-i)`; `zmod_four_one_inv` is about `ofAdd 1`. 22 problems over 5 concepts. The
student review of `integers_mod_n`, `commutative_groups` and `dihedral_groups` after the refactor
(three blind agents, same day) solved every problem, all but two at the first attempt, found no
double teaching, and changed: `zmod_add_laws` names its lemmas without their statements or a
`simp only` fragment; `zmod_fintype` is split, `multiplicative_fintype` carrying the copy's
`Fintype`; `zmod_two_equiv_bool` takes the numerals; `zmod_add_rearrange` explains
`inv_one (G := …)` and drops a forward reference; `comm_instances` no longer prints an instance
body; `comm_group` says why `*` is in scope inside the class; `comm_rearrange`'s `rw` example
uses other letters; `dihedral_group` proves its laws by `rw` with the table's equations, which
its description now names, as does `dihedral_mul_assoc` for `ZMod.add_assoc`; `klein_four`
states on its own that `ZMod 2 × ZMod 2` is the Klein four-group, and says "unlike D₄".

**As refactored (2026-10-23).** `zmod_group` is `AddGroup (ZMod n)` from the laws of
`zmod_add_laws`, with `zmod_neg_neg` and `zmod_neg_add_rev` showing two copies of §2's theorems
at work on residues; `multiplicative_fintype` and `zmod_add_rearrange` are gone (the copy needs
no count of its own, and `neg_neg`, `neg_zero`, `neg_add_rev`, `add_left_comm`, `add_right_comm`
are the copies of §2's and `comm_rearrange`'s theorems); `zmodTwoEquivBool_add` reads `e (a + b)
= e a + e b`; `comm_group` defines `CommGroup` and its twin `AddCommGroup` with `add_comm`, the
line `attribute [to_additive existing AddCommGroup] CommGroup` after it; `comm_instances` builds
`CommGroup Unit`, `AddCommGroup ℤ`, `AddCommGroup (ZMod n)` and `AddCommGroup Bool`, with
`mul_comm` given under its mark; `prod_group` and `prod_comm_group` name their instances
`Prod.instGroup` and `Prod.instCommGroup` under marks, so that `ZMod 2 × ZMod 3` is an additive
group with `(1, 2) + (1, 2) = (0, 1)`; `prod_fintype` counts `ZMod 2 × ZMod 3`; the dihedral
proofs rewrite with the additive copies (`add_assoc`, `neg_add_rev`, `neg_neg`, `zero_add`, …)
in place of the residue facts; `zmod_four_neg_one : -(1 : ZMod 4) ≠ 1`. 20 problems over 5
concepts.

### §4. Powers and the Order of an Element

Milne pp. 8–9. The Lean that is new here: a recursive definition of a power (Naturals' pattern)
and `Int.induction_on`, each in the problem that needs it.

- `natural_powers`: `Group.npow g : ℕ → G` by recursion, `instance : Pow G ℕ`, as Naturals
  defined `add` and its instance; `pow_zero`, `pow_succ`, `pow_add`, `pow_mul`, `pow_one`,
  `one_pow`; `r ^ 3 = 𝟙` and `s ^ 2 = 𝟙` in `S₃` by `decide`; `(1 : ℤ) ^ k = k`, a power in `ℤ`
  being a multiple. (5)
- `integer_powers`: `zpow` by cases on `ℤ` (§1's `Int.ofNat` and `Int.negSucc`) and
  `instance : Pow G ℤ`; `zpow_natCast`, `zpow_neg`, `zpow_add_one`, then `zpow_add` and
  `zpow_mul` by `Int.induction_on`, introduced here. (5)
- `order_of_element`: `orderOf g` as the least `n > 0` with `g ^ n = 𝟙` through §1's
  `Nat.find` under `open Classical`, and `0` when there is none, Mathlib's convention;
  `pow_orderOf_eq_one`; `orderOf_dvd_iff_pow_eq_one` by division with remainder
  (`Nat.mod_add_div`); `orderOf_eq_one_iff`; `orderOf (2 : ZMod 6) = 3`, `orderOf (sr i) = 2`
  in `Dₙ`, and `orderOf (1 : ℤ) = 0`. (5)
- `orders_in_finite_groups`: some positive power of `g` is `𝟙` in a finite group, by §1's
  pigeonhole on `n ↦ g ^ n` over `Fin (card G + 1)`, so `orderOf_pos`;
  `g⁻¹ = g ^ (orderOf g - 1)`; `zpow_mod_orderOf`. (3)

Budget: 18. Hazard: `zpow_add` is the first proof with cases on `ℤ`; write it first, in a
scratch file, and let its length decide whether `integer_powers` is four problems or six.

**As built (2026-10-21).** `PolyaAlgebra/GroupTheory/Powers.lean`: 21 problems over 4
concepts, in this order: `natural_powers` (`npow`, `Group.npow` by recursion with the
`Pow G ℕ` instance under `@[default_instance high]`, `pow_zero` and `pow_succ` by `rfl`, and
`rot3 ^ 3 = 𝟙 ∧ reflect3 ^ 2 = 𝟙` by `decide`; `pow_one` with `one_pow` and `pow_succ'`;
`pow_add` with `pow_mul`, the two laws in one block; `int_pow`, `(3 : ℤ) ^ 2 = 6` by `decide`
and `(1 : ℤ) ^ k = k` by induction and `omega`); `integer_powers` (`zpow`, `Group.zpow` by
cases on `ℤ` with the `Pow G ℤ` instance, `zpow_natCast` and `zpow_negSucc` by `rfl`, and
`(2 : ℤ) ^ (-3 : ℤ) = -6`; `zpow_neg` with `zpow_zero`, `zpow_one`, the tactic `change` taught
on them, and `rot3 ^ (-1 : ℤ) = rot3 ∗ rot3` by `decide`; `zpow_add_one` with `zpow_sub_one`,
the hazard, ten lines by `cases` and `change`; `one_zpow`, the warm-up where `induction` on
`ℤ` is taught; `zpow_add` with `zpow_sub`); `order_of_element` (`is_of_fin_order`, the
student's `IsOfFinOrder`, Mathlib's name and statement, with `rot3` of finite order through
`s3_pow_check` and `1 : ℤ` not; `order_of`, the definition by `if h : IsOfFinOrder g then
Nat.find h else 0` under `open Classical in` as a `noncomputable def`, with a two-example spec;
`order_of_cases`, the two equations `orderOf_of_isOfFinOrder` and `orderOf_of_not_isOfFinOrder`
by `dif_pos` and `dif_neg`, and `orderOf (1 : ℤ) = 0`; `pow_order_of_eq_one` with
`orderOf_le_of_pow_eq_one` and `orderOf_pos_iff`; `order_of_eq_iff`, Mathlib's
characterization, with `orderOf (2 : ZMod 6) = 3` by `decide` through it;
`order_of_dvd_iff_pow_eq_one` with `pow_mod_orderOf` and `orderOf_dvd_of_pow_eq_one`;
`order_of_eq_one_iff` with `orderOf_one`; `order_of_eq_two_iff` with `orderOf (sr i) = 2` in
`Dₙ` as its instance); and `orders_in_finite_groups` (`pigeonhole`,
`Fintype.exists_ne_map_eq_of_card_lt` from `Fintype.card_le_of_injective` through `not_forall`
and `Classical.not_imp`, the injective case closed by `omega`; `exists_pow_eq_of_finite`, two
powers coincide, under `[Finite G]` through `Finite.exists_equiv_fin` and the pigeonhole on
`Fin (n + 1) → Fin n`; `finite_order_of_finite`, `pow_sub_eq_one_of_pow_eq`,
`isOfFinOrder_of_finite` and `orderOf_pos`; `inv_eq_pow`, `inv_eq_pow_orderOf_sub_one` and
`2⁻¹ = 4 ∧ 2 ^ (orderOf 2 - 1) = 4` in `ZMod 6`), with the `@goal`.
Extraction: 81 problems, 0 errors; budgets, prose names, stub shortcuts and the vocabulary
audit (0 of 81) clean; every spec was compiled against variants (`Nat.succ` and `match`
spellings of the recursion, `.ofNat` patterns, `n > 0` and `n ≥ 1` for the order's condition,
`dite` for the `if`) and a wrong definition each; `links.yaml` carries `naturals/addition` and
`naturals/induction → grouptheory/natural_powers`.

The student review (one blind agent per concept, `scripts/review/`, the brief with the
section's blurb) ran the same day: every problem of the four concepts passed on the reviewers'
first attempt but one (`zpow_add_one`, on the second, after a bare `rw [pow_succ']` turned the
wrong power), and the draft changed in these ways. Two problems were added where a reviewer
flagged double teaching: `one_zpow`, so that `induction` on `ℤ` is learned on `𝟙 ^ n = 𝟙`
before the law of exponents, as §4's `one_pow` taught it on `ℕ`, and the tactic `change` moved
from the hazard `zpow_add_one` to `zpow_neg`, where the mathematics is nil, with the gotcha
that a numeral in the restatement takes the goal's type unless ascribed (`g ^ (1 : ℕ)`);
`order_of_eq_two_iff`, the general fact behind "every reflection has order `2`", so that the
dihedral example instantiates a theorem, and with it the `g ^ 2 = 𝟙 ∗ g ∗ g` gotcha said where
it bites. Three context gaps were fixed in the content: `int_one_pow`'s zero case now goes
through `pow_zero` and `int_one_eq_zero`, which the prose had promised; `rot3_isOfFinOrder`
uses `s3_pow_check`, the student's own proof; `pow_add`'s description names its context.
`orderOf_dvd_iff_pow_eq_one`'s sixteen-line direction became `orderOf_dvd_of_pow_eq_one`,
Mathlib's name, and `pow_mod_orderOf` restates `g ^ n` alone before rewriting, since
`Nat.mod_add_div` backwards replaces every `n`. Preambles that handed over a case split, the
lemma per case or the proof in words were cut to the idea (`zpow_neg`, `zpow_add_one`,
`int_pow`, `order_of_eq_iff`, `order_of_dvd_iff_pow_eq_one`, `order_of_eq_one_iff`); the
`order_of` definition is now shown on the first section's example rather than handed over;
`Pow` is shown as a class and the recursive call inside `npow` is named; forward references
left the concept descriptions and `pow_one`; `by_cases` is said to be new; the first error a
student meets (`decide` on `orderOf` itself) is said before the route around it; and titles
were made to state the fact or name the thing. The fourth reviewer solved its three problems by transcription, which it
read as the preambles doing the student's work, and flagged the finiteness theorem for double
teaching (`Finite.exists_equiv_fin`, `Nonempty` and a function built on the spot, arriving with
the first proof in which finiteness enters): the device became `exists_pow_eq_of_finite`, a
problem of its own, and `isOfFinOrder_of_finite` keeps the mathematics; the pigeonhole's
description no longer hands over the case split, its preamble no longer claims that §1 named
`Fintype.card_le_of_injective`, and `omega` closes the injective case; `inv_eq_pow` names
`pow_orderOf_eq_one`, which its proof needs, and its check is `2⁻¹ = 4 ∧ 2 ^ (orderOf 2 - 1)
= 4`, which no one-liner closes and which shows the number. No double teaching was found in
`natural_powers` or `order_of_element`.

Six departures from the entry, each forced by the tooling, the fence or the review. (1) **The
power instance is marked `@[default_instance high]`**, Mathlib's own device for `Monoid.Pow`: a
numeral exponent `(3 : ℤ) ^ 2` is elaborated through default instances alone, where core's
`instPowNat` over `NatPow ℤ` wins and gives `9`; the mark rides into the stub and the prose says
what it is for (`STYLE.md`, **Learned building §4**). (2) **The finite-group theorems take
`[Finite G]`**, since `linter.unusedFintypeInType` refuses a `[Fintype G]` a statement never
uses; the pigeonhole runs on `Fin (n + 1) → Fin n` through `Finite.exists_equiv_fin`, the form
§1 had planned, and `orderOf_pos` under `[Finite G]` serves every later `[Fintype G]` context.
(3) **`zpow_mul` is not built** and `pow_add` and `pow_mul` share a block; `zpow_sub` came free
with `zpow_add`, and `one_zpow` was added by the review. (4) **`IsOfFinOrder` is a problem of
its own** before `orderOf`, Mathlib's own split, so that the definition by `if h : IsOfFinOrder
g` carries one Lean fact and the examples of finite and infinite order precede the order
itself; the two `dif` equations are a problem of their own after it, so that no later proof
unfolds the definition. (5) **`zpow_mod_orderOf` and `g⁻¹ = g ^ (orderOf g - 1)` became one**:
the inverse as a power, checked on `2` in `ZMod 6`; the integer-exponent form waits for the
section that needs it. (6) **Twenty-one problems, not eighteen**: the three the review added (`one_zpow`,
`order_of_eq_two_iff`, `exists_pow_eq_of_finite`) are each a warm-up or a general fact that
the one-idea rule asks for, and the budget yielded to the rule.

**As refactored (2026-10-22).** Symbols throughout; `npow`'s preamble gives the
`@[default_instance high]` mark its new reason (a numeral exponent is read through the default
instances alone, whatever the base); `int_pow` is `ofAdd 3 ^ 2 = ofAdd 6` and `int_one_pow :
ofAdd 1 ^ k = ofAdd k`, by `ofAdd_add` right to left and `ofAdd_inj` before `omega`;
`int_two_zpow_neg_three` is `ofAdd 2 ^ (-3 : ℤ) = ofAdd (-6)`; `int_one_not_isOfFinOrder`,
`orderOf_int_one` are about `ofAdd 1`; `orderOf_zmod_six_two : orderOf (ofAdd 2) = 3` and
`zmod_six_two_inv` are about `ofAdd 2` in `Multiplicative (ZMod 6)`; `orderOf_sr`'s preamble
says `1` is `r 0`. 21 problems over 4 concepts.

**As refactored (2026-10-23).** `to_additive` cannot copy a definition by recursion (the copy's
equations do not match the original's), so the multiples are the student's twins: `npow` keeps
`Group.npow`, now exponent first (`Group.npow n g`, Mathlib's `npowRec` order, so that the twin
takes its arguments in `SMul`'s order), and its instance `Group.toPow`, with `s3_pow_check`;
`nsmul` is new, `AddGroup.nsmul` and `AddGroup.toSMul : SMul ℕ A`, `3 • (2 : ℤ) = 6`, and the
lines pairing them; `pow_zero` and `pow_succ` move into `pow_one`, since their marks need the
twin; `int_pow` is `int_nsmul_one : k • (1 : ℤ) = k`; `zpow` keeps `Group.zpow`, exponent first,
and `Group.toZPow`, with `s3_zpow_check` moved in from `zpow_neg`; `zsmul` is new,
`AddGroup.zsmul` and `AddGroup.toZSMul : SMul ℤ A`, `(-3 : ℤ) • (2 : ℤ) = -6`; `zpow_natCast` and
`zpow_negSucc` move into `zpow_neg`; every theorem carries its mark, with Mathlib's names written
out (`zero_nsmul`, `succ_nsmul`, `add_nsmul`, `mul_nsmul'`, `neg_zsmul`, `add_zsmul`,
`IsOfFinAddOrder`, `addOrderOf`, `addOrderOf_nsmul_eq_zero`, `addOrderOf_eq_one_iff` by hand,
Lean's own being `…_eq_zero_iff`, and `neg_eq_addOrderOf_sub_one_nsmul` by hand); the examples
are `int_one_not_isOfFinAddOrder`, `addOrderOf_int_one`, `addOrderOf_zmod_six_two :
addOrderOf (2 : ZMod 6) = 3` and `zmod_six_two_neg`. 23 problems over 4 concepts.

### §5. Subgroups

Milne 1.11–1.16. The Lean that is new here: a `Membership` instance (Set Theory wrote one by
hand) and the coercion of a subgroup to a type (§1's `↥S`), both in the definition problem.

- `subgroups`: `structure Subgroup (G) [Group G]` with `carrier`, `one_mem'`, `mul_mem'`,
  `inv_mem'`, a `Membership` instance, `Subgroup.ext`; the criterion 1.11 (nonempty and closed
  under `a ∗ b⁻¹`); a subgroup is a group, `instance : Group H` on `{x // x ∈ H}` (Milne's 1.11
  proper, with a spec); `⊤`, `⊥`, and `≤` as inclusion of carriers; `pow_mem`, `zpow_mem`; the
  rotations of `Dₙ` as a subgroup, `{0, 2, 4}` in `ZMod 6`, and `nℤ` in `ℤ`. (7)
- `centre`: `Subgroup.center`; `mem_center_iff`; `G` commutative iff `center G = ⊤`;
  `center (Equiv.Perm (Fin 3)) = ⊥` by `decide`, and `center (DihedralGroup 4) = {𝟙, r 2}`. (4)
- `intersections`: `H ⊓ K`; `sInf` of a set of subgroups (1.13); `2ℤ ⊓ 3ℤ = 6ℤ`. (3)
- `generated_subgroups`: `Subgroup.closure X` as the intersection of the subgroups containing
  `X` (1.15); `subset_closure`, `closure_le`, `closure_mono`; `Subgroup.zpowers g` with carrier
  `Set.range (g ^ · : ℤ → G)`; `closure {g} = zpowers g`; the student's
  `IsCyclic G := ∃ g, ∀ x, x ∈ zpowers g`; cyclic groups are commutative (1.16); `ℤ` and
  `ZMod n` are cyclic, generated by `1`; `zpowers (n : ℤ) = nℤ`; `closure {r 1, sr 0} = ⊤` in
  `Dₙ`. (6)

Budget: 20, which is over: the three examples of `generated_subgroups` can be two problems, and
`intersections` can lose one. Hazard: the coercion `↥H` to a type; Profinite found that a
`@given` `CoeSort` does not reach later contexts, so it is a problem's target here, and the
first extract tests it.

**As built (2026-10-21).** `PolyaAlgebra/GroupTheory/Subgroups.lean`: 21 problems over 4
concepts, in this order: `subgroups` (`subgroup`, the structure with `carrier`, `one_mem'`,
`mul_mem'` and `inv_mem'` and the `Membership G (Subgroup G)` instance, five specs; `rotations`,
`DihedralGroup.rotations n` with carrier `Set.range r`, `r_mem_rotations` and
`sr_not_mem_rotations`, with `Subgroup.one_mem`, `mul_mem` and `inv_mem` as its givens;
`int_multiples`, `intMultiples n` with carrier `{x | n ∣ x}` by `Int.dvd_zero`, `Int.dvd_add`
and `Int.dvd_neg`, and `mem_intMultiples`; `zmod_six_evens`, `zmodSixEvens` with carrier
`{0, 2, 4}` by `decide` and `mem_zmodSixEvens`; `subgroup_as_type`, `Subgroup.coe_mem` and
`Subgroup.card_le_card_group : Fintype.card H.carrier ≤ Fintype.card G` under `open Classical
in`; `subgroup_group`, `instance : Group H.carrier` with `Subgroup.coe_mul`, `coe_one` and
`coe_inv`; `subgroup_ext`, `Subgroup.ext` by `cases … with | mk c _ _ _`, `Set.ext` and
`subst`; `top_bot`, the `Top` and `Bot` instances with `Subgroup.mem_top` and `mem_bot`;
`subgroup_le`, the `LE` instance as `∀ ⦃x⦄, x ∈ H → x ∈ K` with `Subgroup.bot_le`, `le_top` and
`le_antisymm`; `pow_mem`, `Subgroup.pow_mem`, `zpow_mem` and `zmod_six_two_zpow_mem`);
`centre` (`center`, `Subgroup.center G` with carrier `{z | ∀ g, g ∗ z = z ∗ g}` and
`mem_center_iff`; `center_eq_top`, `Subgroup.center_eq_top_iff`, `center_eq_top` under
`[CommGroup G]` and `center_int`; `center_dihedral`, `d3_center : center (DihedralGroup 3) = ⊥`
and `d4_center`, membership as `x = r 0 ∨ x = r 2`, both by `simp only` with the `mem_` equations
and `decide`, and `d4_center_ne_top` through `center_eq_top_iff` and `d4_not_comm`);
`intersections` (`inf`, the `Min` instance with `Subgroup.mem_inf`, `inf_le_left`, `inf_le_right`,
`le_inf` and `intMultiples_two_inf_three` by `omega`; `s_inf`, the `InfSet` instance with
`Subgroup.mem_sInf`, `sInf_le`, `le_sInf` and `mem_sInf_pair : x ∈ sInf {H, K} ↔ x ∈ H ⊓ K`);
and `generated_subgroups` (`closure`, `Subgroup.closure X = sInf {H | X ⊆ H.carrier}` with
`mem_closure`, `subset_closure` and `closure_le`; `zpowers`, `Subgroup.zpowers g` with carrier
`{x | ∃ k : ℤ, g ^ k = x}`, `mem_zpowers_iff` and `mem_zpowers`; `zpowers_eq_closure`;
`is_cyclic`, `IsCyclic G` as a `def` into `Prop` with `IsCyclic.mul_comm`; `int_cyclic`,
`int_zpow_eq_mul : n ^ k = n * k`, `mem_zpowers_int : x ∈ zpowers n ↔ n ∣ x`,
`zpowers_eq_intMultiples` and `isCyclic_int`; `zmod_cyclic`, `ZMod.val_one_pow : ((1 : ZMod n) ^
k).val = k % n`, `isCyclic_zmod` and `zpowers_two_zmod_six : zpowers 2 = zmodSixEvens`), with the
`@goal`. The criterion 1.11 is `Subgroup.ofDiv` in `ExtraCredit.lean`, concept
`subgroup_criterion`, with `one_mem_of_div` and `inv_mem_of_div` before it; `ExtraCredit.lean`
now imports `Subgroups`. Extraction: 103 problems, 0 errors; budgets and concept lengths clean
(the longest problems at 26 lines, the longest concept at 399 characters); every spec compiled
against variants (explicit binders and `carrier a` in the structure, the carrier of `rotations`
with the equation reversed, `nℤ` as an existential, `{0, 2, 4}` as a disjunction, `⊤` as
`{x | True}`, `⊥` as `{x | x = 𝟙}`, `≤` as `⊆` of carriers, the centre with the equation
reversed, `zpowers` as a `Set.range` and with the equation reversed, `IsCyclic` through
`Function.Surjective` and with the equation reversed, `closure` with the membership spelled
out) and a wrong definition each (a structure asking less, `{0, 3}`, a centre asking `g ∗ z = z`,
natural powers only, a product instance taking `b.1 ∗ a.1`); `links.yaml` carries
`programming/structures → grouptheory/subgroups`.

Six departures from the entry. (1) **There is no `CoeSort` instance.** The hazard the entry
named is real for a target as much as for a given: elaboration unfolds the coercion, no compiled
term names the instance, the closure never carries it, and the next problem's statement
`(a : H)` failed with `type expected` at the first extract, as Profinite Spaces §8 had found.
The rule is polya-topology's, spell the type out, and the spelling that costs no new device is
the first section's: a subgroup as a type is `H.carrier`, through Mathlib's `Set` coercion,
which is in every context; the prose says once that Mathlib writes `↥H`. The same holds for §6's
`CoeFun` (see **Next step**). (2) **The criterion 1.11 is extra credit**: nothing after it uses
it, and by the syllabus rule anything before the goal is recommended. (3) **`closure {r 1, sr 0}
= ⊤` in `Dₙ` waits for §8**, where `(r 1) ^ k = r k` is built; its place in the running-examples
table is taken by `zpowers 2 = zmodSixEvens`, the first cyclic subgroup computed, and
`closure_mono` and a `le_def` are not built, since nothing before §9 needs them (the three
order facts of `⊓` were built after the review, below). (4) **`center_eq_top_iff`** has no Mathlib name; `center_eq_top`
under `[CommGroup G]` is Mathlib's, and `center ℤ = ⊤` is its instance; the centre of `S₃` is
stated on `D₃`, as the previous next step said, and `D₄`'s as a membership. (5) **`IsCyclic` is
a `def` into `Prop`**, not Mathlib's class, with `IsCyclic.mul_comm` as the student's name for
"cyclic groups are commutative"; the two helper facts `int_zpow_eq_mul` and `ZMod.val_one_pow`
carry the examples. (6) **Twenty-one problems, not twenty**, plus the extra-credit one: the two
examples `nℤ` and `{0, 2, 4}` are separate problems, so that `∣` with its three core lemmas and a
set literal under `decide` do not arrive together, and `≤` is a problem of its own after `⊤` and
`⊥`, for the budget; `Subgroup.ext` is a problem rather than a given, since every later equation
of subgroups goes through it, and the three restatements `one_mem`, `mul_mem`, `inv_mem` are
givens of `rotations`, the §2 pattern, for the definition problem's budget.

The student review (one blind agent per concept, `scripts/review/`, `intersections` and the
extra-credit `subgroup_criterion` sharing a brief) ran the same day: every problem of the four
concepts and the extra credit passed on the reviewers' first attempt, no reviewer found double
teaching, and the draft changed in these ways. The commonest finding was again a context gap
behind a prose promise or a trained habit. The two `mem_` equations of `generated_subgroups`
were stated and never used, so `Subgroup.mem_zpowers_iff` was unknown in the four problems after
it and `mem_closure` in the one after it, while every problem since `int_multiples` had said its
`mem_` equation "is what later proofs rewrite with"; the references of `zpowers_eq_closure`,
`IsCyclic.mul_comm`, `mem_zpowers_int`, `isCyclic_zmod` and `zpowers_two_zmod_six` now rewrite
with them, and `mem_closure` is proved as `Subgroup.mem_sInf`, so that the previous problem's
equation is in its context. The context of `inf` lacked the `LE` instance although the concept
description promised a greatest lower bound, fixed by stating `inf_le_left`, `inf_le_right` and
`le_inf`; the numeral `0` of `ZMod n` is not in `rotations`' context, so its preamble names the
witness `𝟙`; and `pow_mem`'s description says that the integer case is a `cases` and not the
induction the previous section trained, since `zpow_add_one` is not there. Preambles that handed
over the witness, the lemma per step or the tactic script were cut to the idea in
`subgroup_group`, `subgroup_ext`, `center`, `center_eq_top`, `center_dihedral`,
`zpowers_eq_closure`, `is_cyclic`, `zmod_cyclic`, `inf` and `subgroup_of_div`, the centre's and
the intersections' reviewers finding that every problem passed by transcription. The one tactic
new to the student, `revert`, arrived in `center_dihedral` and was replaced by `simp only` under
the binder, which the examples section taught; `⊢` in an `at` clause left `top_bot`'s reference;
the first error a student meets is now said in `zmod_six_evens` (`decide` before any `intro`) and
`center_dihedral` (`failed to synthesize Decidable`); `outParam` is trimmed from the displayed
`Membership` and the instance's body is no longer given; `Min` and `InfSet` are shown as `Top`
was, with the keystrokes for `⊤`, `⊥` and `⊓`; three theorems were added where a reviewer found a
promise unkept, `d4_center_ne_top` (the equivalence in its non-commutative direction, through
`d4_not_comm`), the three order facts of `⊓`, and `mem_sInf_pair`, the family problem's instance;
`isCyclic_zmod` is in tactic style; and "state" became "prove, which holds by definition"
throughout. The section stays at 21 problems.

**As refactored (2026-10-22).** Symbols throughout; `rotations` has `one_mem' := ⟨0, rfl⟩`,
`r (i + j)` and `r (-i)`; `intMultiples n : Subgroup (Multiplicative ℤ)` with carrier `{x | n ∣
toAdd x}` and `mem_intMultiples : x ∈ intMultiples n ↔ n ∣ toAdd x`; `zmodSixEvens : Subgroup
(Multiplicative (ZMod 6))` with carrier `{ofAdd 0, ofAdd 2, ofAdd 4}`; `zmod_six_two_zpow_mem`
about `ofAdd 2`; `center_int : center (Multiplicative ℤ) = ⊤`; `intMultiples_two_inf_three`
unchanged in statement, `omega` taking `toAdd x` as its unknown; `int_zpow_eq_mul : ofAdd n ^ k
= ofAdd (n * k)`, `mem_zpowers_int : x ∈ zpowers (ofAdd n) ↔ n ∣ toAdd x`,
`zpowers_eq_intMultiples`, `isCyclic_int : IsCyclic (Multiplicative ℤ)` generated by `ofAdd 1`;
`ZMod.val_one_pow : (toAdd (ofAdd 1 ^ k)).val = k % n`, `isCyclic_zmod : IsCyclic (Multiplicative
(ZMod n))` through a `change`, `zpowers_two_zmod_six : zpowers (ofAdd 2) = zmodSixEvens`. 21
problems over 4 concepts; the goal stays on `generated_subgroups`. The student review of
`generated_subgroups` after the refactor (one blind agent, same day) solved all six problems at
the first attempt and found no double teaching and no context gap; its finding was that
`int_cyclic` and `zmod_cyclic` listed the reference's rewrites in order, so both preambles now
give the idea and leave the names to the context list, `zmod_cyclic` no longer hands over its
witness and says what goes wrong without the `change`, `is_cyclic` shows `apply Exists.intro g`,
and the concept's "generated by `1`" says "the number `1`". Left for the owner: the reviewer's
proposal of a non-example, `not_isCyclic_s3` from `IsCyclic.mul_comm` and `rot3_reflect3_ne`;
and `closure` and `zpowers`, untouched by the refactor, still hand over proofs and witnesses in
the reviewer's reading, as `zpowers`, `zpowers_eq_closure` and `is_cyclic` still sit under the
17-line floor, which they did before it.

**As refactored (2026-10-23).** `subgroup` names its instance `Subgroup.instMembership`;
`add_subgroup` is new, the twin `AddSubgroup` with `carrier`, `zero_mem'`, `add_mem'`,
`neg_mem'` and `AddSubgroup.instMembership`, paired by two lines after the block; the instances
of the section are named (`Subgroup.instGroupCarrier`, `instTop`, `instBot`, `instLE`,
`instMin`, `instInfSet`) and, with every definition and theorem, carry marks;
`intMultiples n : AddSubgroup ℤ` with carrier `{x | n ∣ x}`; `zmodSixEvens : AddSubgroup (ZMod
6)` with carrier `{0, 2, 4}`; `zmod_six_two_zsmul_mem : k • 2 ∈ zmodSixEvens` through
`AddSubgroup.zsmul_mem`; `center_int` became `center_klein : center (DihedralGroup 2) = ⊤`, since
an additive group's centre is the whole group and teaches nothing; `intMultiples_two_inf_three`
goes through `AddSubgroup.ext` and `AddSubgroup.mem_inf`; `Subgroup.zpowers` is marked
`AddSubgroup.zmultiples`, `IsCyclic` is marked `IsAddCyclic`; `int_cyclic` is
`int_zsmul_eq_mul : k • n = k * n`, `mem_zmultiples_int`, `zmultiples_eq_intMultiples` and
`isAddCyclic_int`; `zmod_cyclic` is `ZMod.val_nsmul_one : (k • 1).val = k % n`,
`isAddCyclic_zmod` (no `change` needed now) and `zmultiples_two_zmod_six`. 22 problems over 4
concepts; the goal stays on `generated_subgroups`. The whole subject extracts with 110 problems
and 0 errors through a publisher whose closure knows the marks (`STYLE.md`, **Learned
refactoring to additive groups**); the pinned v0.6.1 fails 44 of them until that change is
released and repinned.

### §6. Homomorphisms

Milne 1.20–1.23 and p. 20. The Lean that is new here: applying the student's structure as a
function. The entry planned a `CoeFun` instance, which §1's `Equiv` showed the use of; §5 found
that a coercion instance never reaches a later problem's context (**As built**, departure 1), so
the application is spelled out through a named function (`f.toFun x`, or a named `apply`), and
the §6 session chooses the spelling before writing.

- `homomorphisms`: the student's structure (`GroupHom`, **Decisions** 3) with
  `toFun` and `map_mul'`, a `CoeFun` instance, the notation `G →* H`; Milne 1.21 as the first
  theorems: `map_one`, `map_inv`, `map_pow`, `map_zpow`; `comp` and `id`; the examples: the
  reduction `ℤ →* ZMod n`, `k ↦ k % n` (with `Int.emod` and its non-negativity, said once),
  the reduction `ZMod 6 →* ZMod 2`, the orientation `DihedralGroup n →* Bool` (`r i ↦ false`,
  `sr i ↦ true`), the inclusion `H.subtype : H →* G`, `fst : G × H →* G`, conjugation by `g`.
  (7)
- `isomorphisms`: `GroupIso` extending `Equiv` with `map_mul'`, the notation `G ≃* H`;
  `GroupIso.ofBijective`; `symm`; isomorphic finite groups have the same cardinality; an
  isomorphism carries commutativity and orders of elements; `ZMod 2 ≃* Bool`;
  `DihedralGroup 3 ≃* Equiv.Perm (Fin 3)` (Milne: `D₃` is `S₃`), its map on six elements and
  `map_mul'` by `decide`; `DihedralGroup 2` is not isomorphic to `ZMod 4`, since it has no
  element of order 4. (6)
- `kernels_and_images`: `ker f : Subgroup G`, `range f : Subgroup H`; injective iff
  `ker f = ⊥`; surjective iff `range f = ⊤`; `Subgroup.map` and `Subgroup.comap`; the kernel of
  `ℤ →* ZMod n` is `nℤ`, of the reduction `ZMod 6 →* ZMod 2` is `{0, 2, 4}`, of the orientation
  the rotations. (5)
- `cayley`: `Equiv.mulLeft g : Equiv.Perm G`; `G →* Equiv.Perm G`, injective (1.22); the
  permutation of `ZMod 3` that `1` induces, written out; a finite group of order `n` embeds in
  `Sₙ` as prose (1.23 needs `Fin n ≃ G`, which §1 has). (3)

Budget: 21, which is over: `homomorphisms` can give the two reductions one problem and drop
conjugation to §11, where it is needed.

**As built (2026-10-26).** `PolyaAlgebra/GroupTheory/Homomorphisms.lean`: 22 problems over 4
concepts, in this order: `homomorphisms` (`group_hom`, the structure `GroupHom G H` with
`toFun` and `map_mul' : ∀ a b : G, toFun (a * b) = toFun a * toFun b`, applied as `f.toFun a`,
and the notation `G →* H`; `add_group_hom`, the twin `AddGroupHom` with `map_add'` and
`A →+ B`, paired by an `attribute [to_additive existing …]` line; `map_one`, with
`GroupHom.map_mul` and `GroupHom.map_one` given, the second worked as a `calc` through
`mul_eq_left`, and `GroupHom.map_inv` the exercise; `map_pow`, `GroupHom.map_pow` by induction
and `map_zpow` by cases; `comp`, `GroupHom.comp`, `GroupHom.id` and `GroupHom.fst`;
`zmod_reductions`, `zmodSixToTwo : AddGroupHom (ZMod 6) (ZMod 2)` through `toFin 2 a.val` with
its law by `decide`, and `intToZMod n : ℤ →+ ZMod n`, `k ↦ k • 1` by `add_zsmul`, with
`zmodSixToTwo_five` and `intToZMod_six_neg_one`; `orientation`, with `swap2`, `swap2_mul_self`
and `swap2_ne_one` given, `DihedralGroup.orientation n : DihedralGroup n →* Equiv.Perm (Fin 2)`);
`isomorphisms` (`group_iso`, `GroupIso G H extends G ≃ H` with `map_mul'` and `G ≃* H`;
`add_group_iso`, the twin `AddGroupIso` with `A ≃+ B`; `zmod_two_iso_bool`, `zmodTwoIsoBool :
ZMod 2 ≃+ Bool` from §3's `zmodTwoEquivBool` and `zmodTwoEquivBool_add`, with
`zmodTwoIsoBool_invFun_true`, the first value of a structure that extends another;
`group_iso_symm`, `GroupIso.toGroupHom` and `GroupIso.symm`;
`group_iso_invariants`, `GroupIso.card_eq` through `Fintype.card_congr` and `GroupIso.mul_comm`;
`klein_not_zmod_four`, `GroupIso.mul_self_eq_one`, `zmod_two_prod_add_self` and
`not_nonempty_addGroupIso_zmod_four : ¬ Nonempty (ZMod 2 × ZMod 2 ≃+ ZMod 4)`);
`kernels_and_images` (`ker`, `GroupHom.ker f` with carrier `{x | f.toFun x = 1}` and
`mem_ker`; `range`, `GroupHom.range f` with carrier `{y | ∃ x, f.toFun x = y}`, `mem_range` and
`range_eq_top`; `ker_eq_bot_iff`; `kernel_examples`, `ker_zmodSixToTwo : … = zmodSixEvens` and
`ker_orientation : … = rotations n` and `range_zmodSixToTwo : … = ⊤`; `int_to_zmod_nat_mem_ker`,
`intToZMod_natCast_mem_ker : (m : ℤ) ∈ (intToZMod n).ker ↔ n ∣ m`; `ker_int_to_zmod`,
`Subgroup.inv_mem_iff` and `ker_intToZMod : … = intMultiples n`; `to_perm3`,
`DihedralGroup.toPerm3 : DihedralGroup 3 →* Equiv.Perm (Fin 3)`, `r i ↦ rot3 ^ i.val`, `sr i ↦
reflect3 * rot3 ^ i.val`, its law by `decide`, and `ker_toPerm3 : … = ⊥`); and `cayley` (`mul_left`, `Equiv.mulLeft g : Equiv.Perm G` with its additive
version `Equiv.addLeft` and `addLeft_one_zmod_three : Equiv.addLeft 1 = rot3`; `cayley`, `cayley G
: G →* Equiv.Perm G` and `cayley_injective`), with the `@goal`. `FewerAxioms.lean` stays the
root's last import and now imports `Homomorphisms`. Extraction: 149 problems, 0 errors, 29
concepts in 7 sections; budgets and concept lengths clean, five problems under the 17-line floor
(`add_group_hom`, `comp`, `group_iso_invariants`, `ker_eq_bot_iff`, `mul_left`); prose names and
stub shortcuts clean after their exceptions; the vocabulary audit 0 of 149, once it read fenced
blocks (`STYLE.md`, **Learned building §6**). Every structure spec was compiled against implicit
binders and the law reversed (`GroupHom`, `GroupIso`), the kernel's and the image's carriers
with their equations reversed, and another `zmodSixToTwo` (`⟨a.val % 2, by omega⟩`), and rejects
a wrong `GroupHom` and a wrong `GroupIso`; `links.yaml` carries
`programming/structures → grouptheory/homomorphisms`.

Eight departures from the entry. (1) **No `CoeFun`**: a homomorphism applies as `f.toFun a`, and
the prose says once that Mathlib writes `f a`. (2) **`GroupIso.ofBijective` is not built**; the
isomorphisms are built from their equivalences, and the inverse is `symm`. (3) **`D₃ ≃* S₃` is an
injective homomorphism**, `toPerm3` with trivial kernel: `Equiv.Perm (Fin 3)` has no `Fintype`
under the fence, so the isomorphism's surjectivity cannot be decided, and the prose says that
`S₃` has six elements, a count the subject does not make. (4) **Orders of elements carried by an
isomorphism are not built**; the invariants are the number of elements and commutativity, and
`V₄ ≇ ZMod 4` goes through `a + a = 0` rather than an element of order 4. (5) **`Subgroup.map`,
`Subgroup.comap` and the inclusion `H.subtype` wait for §10**, and conjugation for §11, where they
are needed. (6) **`cayley` has no additive version**, since `Equiv.Perm G` is a multiplicative
group for an additive `G`. (7) **`zmodSixToTwo`'s type is written `AddGroupHom (ZMod 6) (ZMod
2)`**, not `ZMod 6 →+ ZMod 2`, because a later definition shares its auxiliary proof and the
closure does not replay the notation (`STYLE.md`, **Learned building §6**); and the isomorphism
`ZMod 2 ≃+ Bool` is a problem of its own. (8) **Twenty-two problems**, against a budget of
21: the twins `AddGroupHom` and `AddGroupIso` take a problem each, the isomorphism of the groups of
order two takes one, and the kernel of `ℤ →+ ZMod n` takes two (the natural numbers, then the
negatives through `Subgroup.inv_mem_iff`), while the reductions share a problem, as the entry
proposed; the orientation goes to `Equiv.Perm (Fin 2)` rather than `Bool`, as **Spelling** says.

The student review (one blind agent per concept, `scripts/review/`, briefs filled from
`PROMPT.md`) ran the same day: every one of the 22 problems passed, and no reviewer revealed a
solution before passing or found double teaching. The draft changed in these ways. The commonest
finding was a step that holds only by definition, unsaid: the `Int.ofNat` case of `map_zpow`
(`rw [map_pow]` does not match `a ^ Int.ofNat n`), `fst`'s law (the student reaches for
`prod_mul_def`, outside the context), `e.toGroupHom.map_one` in `klein_not_zmod_four` (`rw`
fails where `exact` works), and the goals of `cayley` (`rw [mul_assoc]` finds no pattern); each
preamble now says so in a sentence. Order: `zmod_two_iso_bool` moved before
`group_iso_symm`, since `symm` asked for a value of an extending structure before any problem
had shown one, and its check is now `zmodTwoIsoBool_invFun_true`; `to_perm3` moved to the end
of its concept, beside Cayley's theorem. The image was defined and never used, so
`kernel_examples` adds `range_zmodSixToTwo`; its preamble says that `decide` refuses a goal
about a variable named by `intro`, and that `simp only` rewrites under the `∀`. Giveaways cut:
`zmod_reductions` no longer pairs each law with its closer, and `cayley` no longer names the
point `1`. Smaller fixes: the law of a homomorphism is written as mathematics (f(ab) = f(a)
f(b)), not as Lean the student cannot type; context lists name `one_mul`, `inv_one` and
`Subgroup.inv_mem`; `Nonempty` was met in the first section, not the fourth; `ZMod 2 × ZMod 2`
is isomorphic to the Klein four-group; `mul_left` shows the two cancellation laws it names; and
the spec of `GroupIso` and `AddGroupIso` now accepts a law written through the coercion
`toEquiv (a * b)` (`first | exact h | exact h.symm | grind`), which `grind` alone rejected. Left
for the owner: the non-example `¬ ∀ a b : ZMod 5, toFin 2 (a + b).val = …` (checked by `decide`);
folding each twin structure into its original's problem; moving `Subgroup.inv_mem_iff` to §5's
`pow_mem`; and ending `cayley` with `(cayley G).ker = ⊥`. 149 problems, 0 errors; budgets, prose
names, stub shortcuts and the vocabulary audit clean.

### §7. Cosets and Lagrange's Theorem

Milne 1.24–1.26, 1.29. The Lean that is new here: a `HasQuotient` instance so that `G ⧸ H`
parses, in the definition problem; `Setoid`, `Quotient` and the counting chain are §1's.

- `cosets`: `leftCoset a H : Set G := (a ∗ ·) '' H` (Mathlib spells it `a • ↑H`; the prose
  says so); 1.25 (a)–(c): `a ∈ leftCoset a H`; `leftCoset a H = leftCoset b H ↔ a⁻¹ ∗ b ∈ H`;
  two cosets are disjoint or equal; `leftCoset a H = ↑H ↔ a ∈ H`; the cosets of `2ℤ` are the
  even and the odd integers; in `D₃` the two cosets of the rotations are the rotations and the
  reflections, and `r ∗ ⟨s⟩ ≠ ⟨s⟩ ∗ r`, with right cosets defined here for the purpose. (6)
- `coset_relation`: `QuotientGroup.leftRel H : Setoid G`, `a ≈ b ↔ a⁻¹ ∗ b ∈ H`, proved an
  equivalence; same class iff same coset; two integers are in the same coset of `nℤ` iff they
  have the same remainder. (3)
- `coset_space`: `G ⧸ H` as `Quotient (leftRel H)` through a `HasQuotient` instance;
  `QuotientGroup.mk`; `QuotientGroup.eq`; `mk_surjective`; `Fintype (G ⧸ H)` through §1's
  `Fintype.ofSurjective`, and `Subgroup.index H := Fintype.card (G ⧸ H)`; the rotations have
  index 2 in `Dₙ`. (4)
- `lagrange`: every coset is in bijection with `H` (1.25 d); `G ≃ (G ⧸ H) × H`
  (`Subgroup.groupEquivQuotientProdSubgroup`, through `Quotient.out`); Lagrange,
  `Fintype.card G = H.index * Fintype.card H`, by §1's counting chain and `Fintype.card_fin`;
  `Subgroup.card_subgroup_dvd_card`; `D₃` has no subgroup of order 4, and the subgroups of
  `ZMod 6` have order `1`, `2`, `3` or `6`. (5)

Budget: 18. Hazard: `Quotient.out` needs choice, so the bijection is `noncomputable`; §1 said
so once. The index of `nℤ` in `ℤ`, which is `n`, waits for §10's isomorphism `ℤ ⧸ nℤ ≃* ZMod n`,
since `ℤ` is not a `Fintype`.

**As built (2026-10-26).** `PolyaAlgebra/GroupTheory/Cosets.lean`: 20 problems over 4 concepts,
in this order: `cosets` (`left_coset`, `leftCoset a H : Set G := {x | ∃ h ∈ H, a * h = x}` with
its additive version `leftAddCoset` by the mark alone, and `mem_own_leftCoset`; `right_coset`,
the test `mem_leftCoset_iff : x ∈ leftCoset a H ↔ a⁻¹ * x ∈ H` given and worked as a `calc`, and
the exercise its mirror, `rightCoset H a` with `mem_rightCoset_iff`; `left_coset_eq_iff`,
`leftCoset_eq_iff : leftCoset a H = leftCoset b H ↔ a⁻¹ * b ∈ H` with its two equations of
expressions given; `left_coset_eq_of_mem`, two cosets with a common element are equal;
`int_cosets`, `leftAddCoset_one_two`, the odd integers, and `leftAddCoset_three_eq_one`;
`left_ne_right_coset`, the subgroup `d3FixZero = {r 0, sr 0}` of `D₃` given with
`mem_d3FixZero`, and `leftCoset (r 1) d3FixZero ≠ rightCoset d3FixZero (r 1)`);
`coset_relation` (`left_rel`, `QuotientGroup.leftRel H : Setoid G`, `a⁻¹ * b ∈ H`;
`left_rel_iff`, `QuotientGroup.leftRel_iff_leftCoset_eq` and
`QuotientGroup.setOf_leftRel_eq_leftCoset`; `int_left_rel`, `int_leftRel_iff :
… ↔ a % n = b % n`, `omega` for the step `-a + b = b - a` and then core's
`Int.dvd_iff_emod_eq_zero` and `Int.emod_eq_emod_iff_emod_sub_eq_zero`); `coset_space` (`quotient_group`, the instance
`QuotientGroup.instHasQuotient : HasQuotient G (Subgroup G)` and `QuotientGroup.mk`, each with
its additive version by the mark; `quotient_group_eq`, `QuotientGroup.eq`,
`QuotientGroup.mk_surjective` through the first section's `quotient_mk_surjective`, and
`QuotientGroup.mk_eq_mk_one_iff`; `index`, the named instance `QuotientGroup.fintype H` from
`Quotient.fintype` and `Subgroup.index H := Fintype.card (G ⧸ H)` under `open Classical`;
`index_bot`, `Subgroup.index_bot` through `Fintype.card_of_bijective`); and `lagrange`, with the `@goal` (`left_coset_equiv`,
`leftCosetEquivSubgroup a H : leftCoset a H ≃ H.carrier`; `card_eq_mul_of_equiv_prod`, a type
labelled by pairs of two finite types, through `Fintype.equivFin` and `Equiv.prodCongr`;
`quotient_out`, `QuotientGroup.out_eq'`, `QuotientGroup.inv_out_mul_mem` and
`QuotientGroup.mk_out_mul`;
`group_equiv_quotient_prod`, `Subgroup.groupEquivQuotientProdSubgroup H : G ≃ (G ⧸ H) ×
H.carrier`; `lagrange`, `Subgroup.index_mul_card : H.index * Fintype.card H.carrier =
Fintype.card G` and `Subgroup.card_subgroup_dvd_card`; `index_rotations`, `card_rotations` and
`index_rotations`; `lagrange_examples`, `dihedral_three_card_subgroup_ne_four` and
`zmod_six_card_addSubgroup`). `FewerAxioms.lean` stays the root's last import and now imports
`Cosets`. Extraction: 169 problems, 0 errors, 33 concepts in 8 sections; budgets and concept
lengths clean, two problems under the 17-line floor (`left_coset_eq_of_mem`,
`left_ne_right_coset`); prose names clean after their exceptions (the textbook's `aH`, `Ha`, `nℤ`,
the field `iseqv`, and `Nat.card` in the one sentence of divergence); stub shortcuts clean; the
vocabulary audit 0 of 169. The `leftCoset` and `rightCoset` specs were compiled against the
reversed equation and `H.carrier` for `H`, and reject the right coset passed off as a left one;
the `leftRel` spec rejects equality as the relation.

Six departures from the entry. (1) **A coset is a set-builder, not an image**: `(a * ·) '' H`
hands `intro ⟨h, hh, e⟩` the beta-redex `(fun h => a * h) h = x`, which `rw` cannot use (§5's
lesson for `Set.range`). (2) **Every coset notion has its additive version by the mark alone**:
`leftCoset`, `rightCoset`, `leftRel`, the `HasQuotient` instance, `QuotientGroup.mk`, the
`Fintype` instance and `index` are plain definitions, so `to_additive` copies them and no twin
problem is needed. (3) **`Fintype (G ⧸ H)` is an instance of its own, given by name**: instance
search does not look through `HasQuotient.Quotient` to the `Quotient` behind it, so
`Quotient.fintype` is not found for `G ⧸ H`; the instance shares the `index` problem. (4) **The
counting chain needed a problem of its own**: §1 rehearsed it on `Fin m × Fin n` only, so
`Fintype.equivFin` and `Equiv.prodCongr` arrive in `card_eq_mul_of_equiv_prod`, on no new
mathematics, before Lagrange; and `Quotient.out` in `quotient_out` before the equivalence that
uses it. (5) **The index of the rotations is computed after Lagrange**, from `card_rotations`
(`n` elements, through `Fintype.card_of_bijective`), since the index is classical and nothing
decides it; the cosets of the rotations in `D₃` are prose there, and `index ⊤ = 1` is not built
(`Fintype.card_eq_one_iff` is outside the fence). (6) **Twenty problems**, against a budget of
18: the counting problem is one extra, and the review split `index` from `index_bot`.

The student review (one blind agent per concept, `scripts/review/`) ran the same day: every one
of the 19 problems then built passed, all but one on the first attempt, and no reviewer revealed
before passing. Double teaching was found once, in `index`, where the index, the named instance and
`Fintype.card_of_bijective` arrived together; `index_bot` is now a problem of its own. The
commonest finding was again prose that handed over the proof: the witness and the plan of
`left_ne_right_coset`, context lists in the order of the `rw` chain (`left_coset_eq_iff`,
`left_coset_eq_of_mem`, `int_left_rel`), a routine second identity given as a chain, and the
three quotient laws named one per goal in `quotient_group_eq`; each was cut to the idea, and
context lists now go by origin. A context gap: `QuotientGroup.mk_surjective` reproved §1's
`quotient_mk_surjective`, so the student's direct use of it failed; the reference now uses it.
Added for substance: `QuotientGroup.mk_eq_mk_one_iff`, `QuotientGroup.setOf_leftRel_eq_leftCoset`
(the claim that the classes are the cosets, which the prose had made and no theorem kept),
`QuotientGroup.mk_out_mul` (the unstated step of the equivalence's right inverse), and
`leftAddCoset_three_eq_one` in place of a zero case that repeated the odd one. Smaller fixes:
`%` on negative integers, `outParam` said in half a sentence, the index defined only for a finite
group said once beside `Nat.card`, `Nat.pos_of_neZero` named again in `index_rotations`, the
numeral gotcha `(r 1 : DihedralGroup 3)`, and the title of `right_coset`. Left for the owner:
`Prod.ext` first appears in `group_equiv_quotient_prod`, the hardest problem of the concept (a
reviewer proposed meeting it in §3's `prod_group`), and `Fintype.equivFin` and `Equiv.prodCongr`
arrive together, though on no new mathematics; the checker rejects the coset relation written
as `b⁻¹ * a ∈ H`, the same relation, which the description rules out.

### §8. Cyclic Groups and Groups of Prime Order

Milne 1.16, 1.27, 1.28, 1.31, Exercise 1-5. No new Lean: `Nat.Coprime` is §1's.

- `cyclic_subgroups`: `Fin (orderOf g) ≃ zpowers g`, injective by minimality and onto by
  `zpow_mod_orderOf`; `Fintype.card (zpowers g) = orderOf g`; `orderOf_dvd_card` (1.27);
  `pow_card_eq_one`; `zpowers (r 1)` in `Dₙ` has `n` elements. (5)
- `primes`: the student's `Nat.Prime p`, Milne's definition, `2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p`
  (Mathlib's is `Irreducible p`, and `Nat.prime_def` is the hand-over, said once);
  `Nat.Prime.two_le`; a prime not dividing `n` is coprime to it; Euclid's lemma
  `Nat.Prime.dvd_mul`; a divisor of `p ^ n` other than `1` is divisible by `p`
  (`Nat.Coprime.pow_left`, `Nat.Coprime.eq_one_of_dvd`), which §12 needs. (4)
- `prime_order`: a group of prime order is cyclic and generated by any element other than `𝟙`
  (1.28); its only subgroups are `⊥` and `⊤`; `ZMod p` is the example, and that every group of
  order `p` is isomorphic to it is stated in prose until §10's first isomorphism theorem makes
  it a problem. (3)
- `index`: `(G : K) = (G : H) * (H : K)` for `K ≤ H` (1.31), by Lagrange three times; Exercise
  1-5, `g ^ H.index ∈ H` when `H` is normal, waits for §9. (2)

Budget: 14. Primes are arithmetic, not group theory; whether they are the student's problems
here or a library module's is an open decision (**Decisions** 5).

**As built (2026-10-27).** `PolyaAlgebra/GroupTheory/Cyclic.lean`: 14 problems over 3 concepts,
in this order: `cyclic_subgroups` (`zpow_mod_order_of`, `zpow_orderOf_mul_eq_one : g ^ (↑(orderOf
g) * q) = 1` by induction over `ℤ` and `zpow_mod_orderOf : g ^ (k % ↑(orderOf g)) = g ^ k` through
`Int.emod_add_mul_ediv`; `pow_inj_of_lt_order_of`, `pow_inj_of_lt_orderOf`;
`exists_pow_of_mem_zpowers`, `exists_pow_lt_orderOf_of_mem_zpowers` under `[Finite G]`, through
`Int.emod_nonneg`, `Int.emod_lt_of_pos` and `Int.eq_ofNat_of_zero_le`; `card_zpowers`,
`Fintype.card_zpowers : Fintype.card (zpowers g).carrier = orderOf g` by a bijection from
`Fin (orderOf g)`, as `card_rotations` was counted; `order_of_dvd_card`, `orderOf_dvd_card` and
`pow_card_eq_one`; `zmod_add_order_of_one`, `ZMod.addOrderOf_one : addOrderOf (1 : ZMod n) = n`);
`primes` (`nat_prime`, the student's `Nat.Prime p := 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p`,
`Nat.Prime.two_le`, `Nat.Prime.eq_one_or_self_of_dvd`, through which every later reference reads a
prime's divisors, and `Nat.prime_five` by a bounded `decide`; `prime_coprime`,
`Nat.Prime.coprime_iff_not_dvd`;
`prime_dvd_of_dvd_pow`, `Nat.Prime.dvd_of_dvd_pow_of_ne_one`, which §12 needs); and
`prime_order`, with the `@goal` (`eq_top_of_card_eq`, `Subgroup.eq_top_of_card_eq` through
`Fintype.bijective_iff_injective_and_card`; `eq_bot_of_card_eq`, `Subgroup.eq_bot_of_card_eq`
through `Fintype.card_eq_one_iff`; `prime_card_cyclic`, `Subgroup.zpowers_eq_top_of_prime_card`;
`is_cyclic_of_prime_card`, `isCyclic_of_prime_card` through `Fintype.exists_ne_of_one_lt_card`, and
`zmultiples_eq_top_zmod_five`; `prime_card_subgroups`,
`Subgroup.eq_bot_or_eq_top_of_prime_card`). Every general theorem but the arithmetic of primes
carries its additive version. `FewerAxioms.lean` stays the root's last import and now imports
`Cyclic`. Extraction: 183 problems, 0 errors, 36 concepts in 9 sections; every new problem
verified at once, with no repair; `checks.py all`, the budgets, prose names, stub shortcuts and
the vocabulary audit (0 of 183) clean. The `Nat.Prime` spec was compiled against `1 < p`,
`p ≥ 2` and the disjunction reversed, and rejects `1 ≤ p` and a definition without `m = p`.

Three departures from the entry. (1) **The index formula moved to §10** (the owner,
2026-10-27): `(H : K)` needs `K` as a subgroup of `H.carrier`, which is `comap` of the inclusion,
unbuilt. (2) **The running example of `cyclic_subgroups` is `1` in `ZMod n`, not `r 1` in
`Dₙ`**: `(r 1) ^ k = r k` is not built, while `ZMod n`'s multiples of `1` are §5's
`ZMod.val_nsmul_one`; the general `n` makes it a theorem rather than a `decide`. (3) **The
counting needed two warm-ups and two recognitions**: `pow_inj_of_lt_orderOf` and
`exists_pow_lt_orderOf_of_mem_zpowers` carry the two halves of the bijection, and
`Subgroup.eq_top_of_card_eq` and `Subgroup.eq_bot_of_card_eq` are problems of their own before
the prime-order theorems. That every group of order `p` is isomorphic to `ZMod p` is not stated
in the prose, which keeps no claim without a theorem; §10 proves it.

The review (2026-10-27) ran three rounds, through the polya-subject skill: blind students, Sonnet
and Haiku, one per concept, then Haiku alone on each changed concept, and an editor each round.
Every problem passed in every round, none revealed before passing, and no double teaching was
upheld. Round 1 found a later reference reading a student definition through its projection
(`hp.2` of `Nat.Prime`), now `Nat.Prime.eq_one_or_self_of_dvd`; prose that handed over the
proof in eight problems; context facts named without what they say; two concept descriptions
claiming more than was built; wrong origins; and three statements in one problem, now
`prime_card_cyclic` and `is_cyclic_of_prime_card`. Rounds 2 and 3 found defects the
fixes had made (a claimed classification, a forward reference, a symbol used before it was
introduced) and smaller wording; round 3's three fixes stand unreviewed. After the review the owner
dropped Euclid's lemma, `prime_dvd_mul`, as number theory nothing in the subject uses
(2026-10-27), and the lemma lists stay as the editor upheld them.

### §9. Normal Subgroups and Quotient Groups

Milne 1.32–1.37, 1.41–1.44, 1.49. The Lean that is new here: `Quotient.lift₂`, in the problem
that defines the quotient's operation.

- `normal_subgroups`: `Subgroup.Normal` with `conj_mem`; Milne's `gNg⁻¹ = N` is equivalent
  (1.32); `gN = Ng` (1.34, with right cosets); a subgroup of index two is normal (1.36 a), so
  the rotations are normal in `Dₙ`; `⟨s⟩` is not normal in `D₃` (1.36 b, by `decide`); every
  subgroup of a commutative group is normal, so every `nℤ` is; the centre is normal; kernels
  are normal (1.41). (7)
- `quotient_groups`: `Group (G ⧸ N)` through `Quotient.lift₂`, well defined by normality
  (1.42); `QuotientGroup.mk' N : G →* G ⧸ N`; `ker (mk' N) = N`; the quotient of a commutative
  group is commutative; `Fintype.card (G ⧸ N) = N.index`; Exercise 1-5; `ℤ ⧸ nℤ` with its
  elements the residues (Milne 1.44 a, its isomorphism with `ZMod n` in §10); `ZMod 6 ⧸ ⟨3⟩` has
  two elements, and `D₄ ⧸ ⟨r 2⟩` four, Milne 1.49. (7)
- `universal_property`: `QuotientGroup.lift N φ (h : N ≤ ker φ) : G ⧸ N →* H`; `lift_mk`;
  uniqueness (1.43); the orientation of `Dₙ` factors through `Dₙ ⧸ rotations`. (3)
- `products_of_subgroups`: `H ⊔ N` as the set `{h ∗ n}` when `N` is normal (1.37);
  `2ℤ ⊔ 3ℤ = ⊤` in `ℤ`, and `⟨2⟩ ⊔ ⟨3⟩ = ⊤` in `ZMod 6`. (2)

Budget: 19. Extra credit, after the goal's path: the quaternion group `Q₈` as an inductive
over `ZMod 4` with Mathlib's table, its one element of order 2, and every subgroup normal
(Exercise 1-1).

**As built (2026-10-29).** `PolyaAlgebra/GroupTheory/Quotients.lean`: 21 problems over 4
concepts, in this order: `normal_subgroups` (`normal`, the student's `class Subgroup.Normal N :
Prop` with `conj_mem : ∀ n, n ∈ N → ∀ g : G, g * n * g⁻¹ ∈ N`, taken as `[N.Normal]`;
`add_normal`, the twin `AddSubgroup.Normal` with `g + n + -g`, paired by `attribute [to_additive
existing]`; `conj_mem_inv`, `Subgroup.Normal.conj_mem' : g⁻¹ * n * g ∈ N`, the warm-up on the
instance argument, which the later references use; `normal_iff_cosets`,
`Subgroup.normal_iff_leftCoset_eq_rightCoset` and `d3FixZero_not_normal` through §7's
`leftCoset_ne_rightCoset`; `normal_of_comm`, the instances `Subgroup.normal_of_comm` and
`Subgroup.center_normal`; `normal_ker`, the instances `GroupHom.normal_ker` and
`DihedralGroup.rotations_normal` through `ker_orientation`); `products_of_subgroups` (`sup`, the
instance `Subgroup.instMax` with `H ⊔ K := closure (H.carrier ∪ K.carrier)`, `le_sup_left`,
`le_sup_right`, `sup_le`; `mul_normal`, `Subgroup.mulNormal H N`, the products `h * n` for normal
`N`, with no Mathlib name; `mem_sup_of_normal`, `Subgroup.mem_sup_of_normal`; `two_sup_three`,
`intMultiples_two_sup_three`); `quotient_groups` (`left_rel_mul`, `QuotientGroup.leftRel_mul` and
`QuotientGroup.leftRel_inv`, the well-definedness, a problem before the device; `quotient_mul`,
`QuotientGroup.mul` through `Quotient.lift₂` and `QuotientGroup.inv` through `Quotient.lift`,
with `mul_mk` and `inv_mk` by `rfl`; `quotient_is_group`, the instance
`QuotientGroup.Quotient.group N : Group (G ⧸ N)`, each law through §7's
`QuotientGroup.mk_surjective`; `mk_hom`, `QuotientGroup.mk_mul` and `QuotientGroup.mk_one` given,
`QuotientGroup.mk' N : G →* G ⧸ N`, `QuotientGroup.mk_pow` by induction and `QuotientGroup.ker_mk'`;
`quotient_comm`, the instance `QuotientGroup.Quotient.commGroup`; `pow_index_mem`,
`Subgroup.pow_index_mem`, Exercise 1-5; `int_quotient`, `addOrderOf_mk_one_int : addOrderOf
(QuotientAddGroup.mk 1 : ℤ ⧸ intMultiples n) = n`); and `universal_property`, with the `@goal`
(`eq_of_mem_ker`, `GroupHom.eq_of_inv_mul_mem_ker`; `lift`, `QuotientGroup.lift N f hN : G ⧸ N
→* H` for `hN : N ≤ f.ker`, with `lift_mk`; `lift_int`, `exists_hom_int_quotient`, `intToZMod n`
through `ℤ ⧸ nℤ` by `QuotientAddGroup.lift`; `lift_unique`, `QuotientGroup.lift_unique`). Every general definition and theorem
carries its additive version, so `ℤ ⧸ intMultiples n` is an additive group with nothing to add:
`AddSubgroup.normal_of_comm` finds its normality. `FewerAxioms.lean` stays the root's last import
and now imports `Quotients`. Extraction: 204 problems, 0 errors, 40 concepts in 10 sections;
every new problem verified at once, with no repair; budgets and concept lengths clean, six
problems under the 17-line floor (`normal`, `mem_sup_of_normal`, `two_sup_three`, `quotient_comm`,
`eq_of_mem_ker`, `lift_unique`); prose names
clean after their exceptions (the field `conj_mem`, the textbook's `nℤ`, `lift₂`'s `s₁` and `s₂`), stub shortcuts clean
after two (`mul_mk`, `inv_mk` and `lift_mk` by `rfl`); the vocabulary audit 0 of 204. The
`Subgroup.Normal` spec was compiled against an implicit `n` and the binders in the order `∀ g,
∀ n ∈ N`, and rejects `g * n ∈ N`; the `mulNormal` spec accepts `x = h * n` and rejects `n * h`.

Five departures from the entry. (1) **Products of subgroups come before the quotient groups**,
so that the goal, on the section's last concept, is the universal property; the concept needs
only normality and §5's `closure`. (2) **A subgroup of index two being normal (1.36 a) is not
built**: the rotations are normal as the kernel of the orientation, and the index-two theorem
needs a count of the quotient's two classes that the index, being classical, does not give by
`decide`. (3) **Milne's `gNg⁻¹ = N` (1.32) is not built**: the conjugate of a subgroup is not
defined, and `gN = Ng` carries the same content through §7's cosets. (4) **`Fintype.card (G ⧸ N)
= N.index` is not a problem**, since it is the index's definition; Exercise 1-5 uses it, and the
examples `ZMod 6 ⧸ ⟨3⟩` and `D₄ ⧸ ⟨r 2⟩` are not built (the first has three elements, not the
entry's two). The universal property's example is `intToZMod n` through `ℤ ⧸ nℤ`, which §10's
`ℤ ⧸ nℤ ≃+ ZMod n` continues, rather than the orientation through `Dₙ ⧸ rotations`. (5) **The
quaternion group, the entry's extra credit, is not built.** `Quotient.lift₂` arrives in
`quotient_mul` after its well-definedness has its own problem, and the instance argument
`[N.Normal]` in `conj_mem_inv`, on a one-line fact. The owner's calls at the gate (2026-10-29), on what three review rounds left open: the chain
of expressions in `mul_normal`'s preamble stays (STYLE's rule for a subtle identity, though two
students read it as the witness); `mem_sup_of_normal` is split, its `2ℤ ⊔ 3ℤ` becoming
`two_sup_three`, while `normal_iff_cosets` (with `d3FixZero` not normal) and `lift` (with
`lift_mk`) stay whole; `quotient_comm` and `lift_unique`, which follow `one_mul`'s worked pattern,
stay.

### §10. The Isomorphism Theorems

Milne 1.45–1.48, 1.50, 1.51, and equation (13). No new Lean.

- `first_isomorphism_theorem`: `QuotientGroup.quotientKerEquivRange φ : G ⧸ ker φ ≃* range φ`;
  `quotientKerEquivOfSurjective`; `G ⧸ ⊥ ≃* G`; `ℤ ⧸ nℤ ≃* ZMod n` from `k ↦ k % n`, so the index
  of `nℤ` is `n` (Milne 1.44 a); `ZMod 6 ⧸ ⟨2⟩ ≃* ZMod 2` from the reduction, and
  `Dₙ ⧸ rotations ≃* Bool` from the orientation; every group of prime order is isomorphic to
  `ZMod p`, finishing §8. (7)
- `second_isomorphism_theorem`: in Milne's proof's form: the restriction `H →* G ⧸ N`, its
  kernel `H ⊓ N`, and `H ⧸ (H ⊓ N) ≃* range`, the range being `HN ⧸ N` (1.46). (3)
- `correspondence_theorem`: `comap (mk' N)` and `map (mk' N)` are inverse bijections between the
  subgroups above `N` and the subgroups of `G ⧸ N`; inclusion and normality correspond (1.47,
  1.48); the subgroups of `ℤ` above `6ℤ` against those of `ZMod 6`, and the subgroups of `D₄`
  above `⟨r 2⟩` against those of `D₄ ⧸ ⟨r 2⟩`, Milne 1.49's two lattices; the third isomorphism
  theorem as extra credit. (5)
- `direct_products`: elements of two normal subgroups with trivial intersection commute; if
  also `H ⊔ K = ⊤` then `H × K ≃* G` (1.50, 1.51); `ZMod m × ZMod n ≃* ZMod (m * n)` for coprime
  `m` and `n` (Milne eq. 13, by the order of `(1, 1)` and §8's primes concept), so
  `ZMod 2 × ZMod 3 ≃* ZMod 6` while `ZMod 2 × ZMod 2` is `V₄`. (4)
- `index` (moved from §8 by the owner, 2026-10-27, since it needs `comap`): `Subgroup.comap` of
  the inclusion `H.carrier →* G` makes `K ≤ H` a subgroup `K.subgroupOf H` of the group
  `H.carrier`; `(G : K) = (G : H) * (H : K)` (Milne 1.31), by Lagrange three times. Exercise 1-5,
  `g ^ H.index ∈ H` for normal `H`, is §9's. (2)

Budget: 21 with `index`, over by three: the two lattice examples of `correspondence_theorem`
can be one problem, and `index` may move to `correspondence_theorem`, which builds `comap`.

**As built (2026-10-29).** `PolyaAlgebra/GroupTheory/Isomorphisms.lean`: 25 problems over 5
concepts, in this order: `first_isomorphism_theorem` (`of_bijective`, `GroupIso.ofBijective f hf`
through Mathlib's `Equiv.ofBijective`, the Lean that is new here; `lift_injective`,
`QuotientGroup.lift_injective (h : f.ker ≤ N)` and `QuotientGroup.lift_surjective`;
`quotient_ker_equiv_of_surjective`, `QuotientGroup.quotientKerEquivOfSurjective f hf : G ⧸ f.ker
≃* H`; `range_restrict`, `GroupHom.rangeRestrict f : G →* f.range.carrier` and
`GroupHom.rangeRestrict_surjective`; `ker_range_restrict`, `GroupHom.ker_rangeRestrict`; `quotient_ker_equiv_range`,
`QuotientGroup.quotientKerEquivRange f : G ⧸ f.ker ≃* f.range.carrier`; `int_to_zmod_surjective`,
`intToZMod_surjective`; `int_quotient_equiv`, `intQuotientEquivZMod n : ℤ ⧸ intMultiples n ≃+
ZMod n`; `zmod_six_quotient`, `exists_addGroupIso_zmodSix_quotient`); `correspondence_theorem`
(`comap`, `Subgroup.comap f K` with `mem_comap`; `map`, `Subgroup.map f K` with `mem_map`;
`map_comap_mk`, `QuotientGroup.le_comap_mk'` and `QuotientGroup.map_comap_mk'`; `comap_map_mk`,
`QuotientGroup.comap_map_mk'`; `zmod_six_correspondence`, `comap_bot_zmodSixToTwo` and
`map_zmodSixEvens_zmodSixToTwo`); `second_isomorphism_theorem` (`subgroup_of`,
`Subgroup.subtype H : H.carrier →* G`, `Subgroup.subgroupOf N H := N.comap H.subtype`,
`mem_subgroupOf`; `normal_subgroup_of`, the instance `Subgroup.normal_subgroupOf`; `ker_restrict`,
`QuotientGroup.ker_restrict`, the kernel of `(mk' N).comp H.subtype`; `second_isomorphism`,
`QuotientGroup.quotientSubgroupOfEquivRange H N`); `index_formula` (`card_subgroup_of`,
`Subgroup.card_subgroupOf`; `index_eq_mul_index`, `Subgroup.index_eq_mul_index : K.index =
H.index * (K.subgroupOf H).index` for `K ≤ H`); and `direct_products`, with the `@goal`
(`mul_comm_of_inf_eq_bot`, `Subgroup.mul_comm_of_inf_eq_bot`; `prod_mul`, `Subgroup.prodMul H K
hHK : H.carrier × K.carrier →* G`; `prod_mul_injective`; `prod_mul_equiv`,
`Subgroup.prodMulEquiv H K hHK hsup`; `zmod_six_product`, with `zmodSixThrees` given,
`zmodSixEvens_inf_threes`, `zmodSixEvens_sup_threes` and `zmodSixProdEquiv`). Every general
definition and theorem carries its additive version. `FewerAxioms.lean` stays the root's last
import and now imports `Isomorphisms`; the `@goal` leaves `universal_property`. Extraction: 227
problems, 0 errors, 45 concepts in 11 sections; every new problem verified at once, with no
repair (229 after the review's two splits: `normal_subgroup_of` from `subgroup_of` in round 1,
`ker_range_restrict` from `quotient_ker_equiv_range` in round 2). The `comap` and `map` specs were compiled against a carrier written as a preimage and an
equation reversed, and reject `⊤` and `f.range`.

Departures from the entry. (1) **Every isomorphism to a named quotient is built from the lift,
not from the first isomorphism theorem**: `quotientKerEquivRange f` has the type `G ⧸ f.ker`,
and `ℤ ⧸ (intToZMod n).ker` is a different type from `ℤ ⧸ intMultiples n`. A rewrite by
`ker_intToZMod` does carry the isomorphism across (the editor compiled it), but through a cast,
and the result no longer sends the class of `a` to its image by definition, which the spec and
every later use need; so `QuotientGroup.lift_injective` takes `f.ker ≤ N` and the student proves
the inclusions. (2) **The
first isomorphism theorem comes in two problems**, the surjective case and the image through
`rangeRestrict`. (3) **`zmod_six_quotient` is an existence theorem**: as a `def`, its proofs of
`NeZero 6` and of normality became auxiliary declarations that `zmod_six_product` reused, and the
closure then pulled the `def` without what it needs (the §6 lesson of shared proofs, in a new
form). (4) **Not built**: `G ⧸ ⊥ ≃* G` (`⊥` has no normality instance and `ker (id)` is not `⊥`
as an expression); `Dₙ ⧸ rotations ≃* Bool`, since `Equiv.Perm (Fin 2)` has no count here to
decide surjectivity; every group of prime order isomorphic to `ZMod p`, which needs the kernel of
`k ↦ k • a` and a composite of isomorphisms; normality's correspondence (Milne 1.48), the third
isomorphism theorem, and the lattices of Milne 1.49, for which `zmod_six_correspondence` stands;
the second isomorphism theorem's image as the quotient `(H ⊔ N) ⧸ N`, said in prose; and
`ZMod m × ZMod n ≃+ ZMod (m * n)` for coprime `m` and `n`, which needs a count of a product the
fence lacks; `ZMod 6` as the internal product of `{0, 2, 4}` and `{0, 3}` stands in. (5) **The
index formula has no running example.** (6) Names the subject coins where Mathlib's differ:
`Subgroup.index_eq_mul_index` (Mathlib's `relindex_mul_index` through `relindex`, not defined
here), `QuotientGroup.ker_restrict`, `QuotientGroup.quotientSubgroupOfEquivRange`,
`Subgroup.prodMul` and `Subgroup.prodMulEquiv`.

### §11. Group Actions

Milne 4.1–4.6, 4.10. The Lean that is new here: a class extending `SMul` (the definition), and
a type synonym with a copied instance (`ConjAct`), each in its own problem.

- `actions`: `class MulAction (G) (X) [Group G] extends SMul G X` with `one_smul`, `mul_smul`;
  the examples: `Sₙ` on `Fin n` by evaluation, `Dₙ` on the vertices `Fin n` (`r i • v = v + i`,
  `sr i • v = i - v`), `ZMod n` on `Fin n` by rotation, `G` on itself by left multiplication
  (the student's `SMul G G` instance, since the fence has none), `G` on `G ⧸ H`; an action is a
  homomorphism `G →* Equiv.Perm X` and conversely (`MulAction.toPermHom`). (6)
- `orbits`: `MulAction.orbit G x := Set.range (· • x)`; `mem_orbit_iff`; the orbit relation is
  an equivalence and the orbits partition `X`; transitive actions; `Dₙ` on the vertices has one
  orbit. (4)
- `stabilizers`: `MulAction.stabilizer G x : Subgroup G`; `stabilizer (g • x)` is the conjugate
  (4.4); the kernel of an action; faithful actions; the stabilizer of a vertex under `Dₙ` is
  `{𝟙, sr (2 • v)}`, of order 2; the kernel of the action on `G ⧸ H` is the largest normal
  subgroup inside `H` (4.10) as extra credit. (5)
- `conjugation`: `ConjAct G`, a type synonym with `G`'s group structure, acting by
  `g • x = g ∗ x ∗ g⁻¹` (the Lean device, taught once, in a problem that does nothing else);
  orbits are conjugacy classes; stabilizers are centralizers, `Subgroup.centralizer`; the fixed
  points are the centre; the five classes of `D₄` and the three of `S₃` by `decide`. (5)

Budget: 20, which is over by two: the `ZMod n` action and the `G ⧸ H` action can be one
problem, and `S₃`'s classes can be prose.

### §12. Counting with Actions

Milne 4.7–4.8, 4.11–4.12, 4.16, 4.18, 4.19, and Lemma 5.1. The Lean that is new here:
`Finset.induction_on`, in a problem of its own before the block count.

- `orbit_stabilizer`: `MulAction.orbitEquivQuotientStabilizer : orbit G x ≃ G ⧸ stabilizer G x`;
  `card (orbit G x) = (stabilizer G x).index`, so by Lagrange the size of an orbit divides the
  order of the group, with no product to count (4.7, 4.8); `n · 2 = 2n` for `Dₙ` on the
  vertices. (4)
- `block_counting`: induction over a finite set, `Finset.induction_on`, on a fact about finite
  sets alone; a finite type is the disjoint union of its orbits: for a finite set `s` of orbits,
  the elements lying in one of them number the sum of their sizes, stated by induction with
  `Finset.card_union_of_disjoint`; the student's Lemma 5.1: if every orbit has size `1` or a
  multiple of `p`, then `card X % p = card (fixedPoints) % p`; at `p = 2`, `Bool` acting on
  `Fin n` by `i ↦ -i`: an involution's fixed points have the parity of the set. (5)
- `class_equation`: `IsPGroup p G := ∃ n, Fintype.card G = p ^ n`, Milne's definition (Mathlib's
  is `∀ g, ∃ k, g ^ p ^ k = 𝟙`; the two agree once Cauchy is proved, in a later subject); for a
  `p`-group every orbit size is `1` or a multiple of `p` (§8's divisor lemma); under conjugation
  the fixed points are the centre, so `p ∣ card (center G)` and the centre of a nontrivial
  `p`-group is nontrivial (4.16); `D₄`, with `8 = 1 + 1 + 2 + 2 + 2` and centre `{𝟙, r 2}`. (4)
- `prime_square`: if `G ⧸ center G` is cyclic then `G` is commutative (4.19); a group of order
  `p ^ 2` is commutative (4.18), the `@goal`; `ZMod p × ZMod p` and `ZMod (p ^ 2)` are the two
  cases, and `D₄` of order `2³` shows `p²` is sharp, in prose. (3)

Budget: 16. Hazard: the set of orbits is `Finset.univ` of the quotient by the orbit relation,
whose `Fintype` and decidable equality are classical (`open Classical` again), and the fibres
of `X → Quotient` are the orbits (`Equiv.sigmaFiberEquiv` is in the fence if a bijection is
wanted instead of an induction).

## The goal

`prime_square`'s theorem, *every group of order `p ^ 2` is commutative*, closes the subject.
By the syllabus rule every concept declared before it is on its path, which is all of §1–§12
but the extra-credit problems named above, and the report's extra-credit list should hold only
those. Until §12 exists the `@goal` sits on the last concept built, as Profinite's did.

## What comes after

Two subjects, each with a plan of its own when its turn comes. Both import this subject's
modules as compiled theory, the way a later subject imports an earlier one, so that the
student's `Group`, `ℤ`, `ZMod n`, `Sₙ` and `Dₙ` stay the groups of the whole trilogy; the
hand-over to Mathlib's `Group` is a rings subject's to make (see **Decisions**, 7). Neither
needs a Prerequisites section of its own: §1 here is theirs too.

- **Permutation Groups** (Milne pp. 64–70): cycles, the cycle decomposition, transpositions, the
  sign homomorphism, `Aₙ`, conjugacy classes of `Sₙ`, and the simplicity of `Aₙ` for `n ≥ 5`.
  `Dₙ` is embedded in `Sₙ` there, through §11's action on the vertices.
- **The Sylow Theorems** (Milne 4.13, chapter 5): Cauchy's theorem, `p`-groups, Sylow I–III,
  and the applications on pp. 82–85. `ZMod p` acting on `p`-tuples by rotation is McKay's proof
  of Cauchy, and §11's rotation action is its warm-up.

## What is left out, and where it goes

| Milne | What | Where |
|---|---|---|
| 1.7, 1.8, 1.33, 1.56, 1.64 | matrix groups, `GLₙ`, bilinear forms | a linear algebra subject |
| 1.18, Exercise 1-1 | the quaternion group | extra credit in §9 |
| 1.19, 4.24–4.37 | transpositions, cycles, sign, `Aₙ` | *Permutation Groups* |
| 1.38–1.40 | the normal subgroup generated by a set | not needed before free groups |
| 1.44 (b) | `ℝ²/L` | `ZMod 6 ⧸ ⟨3⟩` and `ℤ ⧸ nℤ` stand in |
| 1.52 | direct products of `k` subgroups | prose remark in §10 |
| 1.53–1.58 | finitely generated commutative groups | a subject of its own, after modules over a PID or by Milne's elementary route |
| 1.59–1.63 | characters of commutative groups | the representation theory subject |
| 4.13–4.15, 4.17, 4.20–4.23 | Cauchy, groups of order `2p`, normal subgroups of order `pᵐ`, the five groups of order 8, action on cosets | *The Sylow Theorems* |
| 4.38–4.45, Todd–Coxeter | primitive actions, the algorithm | not planned |
| chapters 2, 3, 6, 7 | free groups, automorphisms and extensions, series, representations | later subjects, if at all; presentations are hard to serve as problems |

## Size

Twelve sections, about 52 concepts and 215 problems, one section per session of one to two
hours of active time, as Profinite Spaces ran: fourteen to sixteen days from a settled plan to
a first draft, then the review passes. The Group-free fence, the running examples and the
Prerequisites section add about sixty problems over the first draft of this plan, all of them
things a first course does by hand anyway: the language, the examples, the laws of exponents,
the order of an element, primes, counting by labelling and by blocks; and §1 takes about ten
warm-up problems out of the sections that follow. Six sections are over budget by one to five
problems, and each says which problems to merge or move.

## Before §1

What the repository needs before a section is written, in order:

1. **`git init`**, the plan committed, and a `README.md` with the subject table (one row per
   section, a status column).
2. **`lake exe polya new "Group Theory" --section Prerequisites --license CC-BY-4.0 --reference
   "J. S. Milne, Group Theory, v4.01 (2025), https://www.jmilne.org/math/CourseNotes/GT.pdf"`**,
   which writes `about.yaml` (title from the directory; the description is ours), the subject
   root `PolyaAlgebra/GroupTheory.lean` with its `@subject` block, the `LICENSE`, the first
   section file, and the import line in `PolyaAlgebra.lean`. Visibility `private` until the
   subject is reviewed.
3. **`about.yaml`**: title *Polya Algebra*, license `CC-BY-4.0`, and a description in the style
   of `polya-topology`'s: subjects on algebra built by the student from the axioms, under
   Mathlib's names; Milne's notes acknowledged as the outline.
4. **`STYLE.md`**, seeded from `polya-topology/STYLE.md`: the fence section rewritten for
   algebra (the probe above, `Group` as the name that must stay unknown, the list of modules
   that carry it), the definition-first pattern transposed, the running-examples rule (every
   concept returns to one of the eight), the notation rule (`∗`, `𝟙`, `⁻¹`; Mathlib's names;
   Mathlib's symbols named once), **the rule that no problem introduces a Mathlib idea and a
   hard mathematical idea at once**, with §1 as where the Lean is taught and the list of the
   devices taught in place, and every rule of `BEST_PRACTICES.md` Step 3 stated before §1
   rather than learned on a finished section: descriptions are textbook exercises and never
   proof outlines; Mathlib is mentioned only where the student can use it; a context fact the
   student did not prove is named where it is used, by position; no "fence", no
   author-to-agent asides; one goal per bullet in reference proofs; a Lean device motivated
   once at first use; titles name the object; each term defined at first use, in one sense.
5. **`scripts/`**, copied from `polya-topology/scripts/`: `check_budgets.py`,
   `check_budgets_lean.py`, `check_prose_names.py`, `check_stub_shortcuts.py`,
   `problem_files.py`, `audit_vocabulary.py`, with fresh `*_ok.txt` lists; the fence probe
   added as `scripts/fence_probe.py`, asking for `Group` first. The solver harness comes over
   when the draft is done. The vocabulary audit is what checks the rule mechanically: a
   reference proof that uses a name no earlier problem's prose has taught is a bug.
6. **`links.yaml`**: links from `polya-basic` into §1–§5 (the guide allows either subject to
   be in another repository): `settheory/set → grouptheory/mathlib_sets`,
   `settheory/image → grouptheory/mathlib_sets`, `logic/relations → grouptheory/relations`,
   `logic/classical → grouptheory/equivalence_classes`, `naturals/dvd →
   grouptheory/integers_and_remainders`, `programming/instances → grouptheory/group_axioms`,
   `programming/inductive_types → grouptheory/dihedral_groups`, `naturals/addition →
   grouptheory/natural_powers` (a recursive definition and its instance), `naturals/induction →
   grouptheory/natural_powers`, `programming/structures → grouptheory/subgroups`.
7. **`.env`** with `POLYA_SERVER` and `POLYA_API_KEY` for the dev app, the owner's.
8. **The remaining checks**, each a scratch compile under the fence: the core names of the
   `ℤ` cancellation laws (`Int.neg_add_cancel` is not one; `Int.add_left_neg` or its current
   name is); `zpow_add` by cases on `ℤ` (its length sizes §4); `ZMod n` with `[NeZero n]`
   against `ZMod (n + 1)`, and the `Fintype` of `DihedralGroup n` through `finProdFinEquiv`;
   `DecidableEq` and `Decidable (∀ x : DihedralGroup 4, …)` after the student's `Fintype`
   instance, so that `decide` reaches `D₄`'s centre and classes; the reduction `ℤ →* ZMod n`
   through `Int.emod` and `Int.toNat`; whether a problem-owned `CoeSort` instance reaches later
   contexts through an extract; `Nat.find` under `decide` for §1's example; the names of
   Mathlib's coset and quotient lemmas to mirror (`QuotientGroup.eq`, `mk_surjective`,
   `Subgroup.card_mul_index`, `MulAction.orbitEquivQuotientStabilizer`).

### Done, 2026-10-21

Items 1–7 are in place: the repository is a git repository; `polya new` wrote the subject
root, `LICENSE`, the first section file and `about.yaml`, whose description is written;
`STYLE.md` carries the fence, the definition-first rule, the running examples, the notation
rule, the one-idea rule with the list of devices taught in place, and every rule of
`BEST_PRACTICES.md` Step 3; `scripts/` holds the checks of `polya-topology` (adapted:
`load_bundle` takes a bundle directory, so `audit_vocabulary.py --prior
../polya-basic/.lake/polya/bundles/<subject>` reads polya-basic's bundles as the baseline), the
fence probe as `scripts/fence_probe.py` (Python, since macOS's bash is 3.2), fresh `*_ok.txt`
lists, and `scripts/review/` for the student review after each section; `links.yaml` carries the
seven links into §1, the rest to be added as their concepts are built; `.env` is the dev app's;
`plans/STUDENT_BACKGROUND.md` is the survey of what the student knows. Item 8, the remaining
checks, each a scratch compile under the fence, found:

- **The ℤ cancellation laws** are `Int.add_left_neg : -a + a = 0` and `Int.add_right_neg :
  a + -a = 0`; `Int.neg_add_cancel` and `Int.add_neg_cancel` are unknown under the fence.
  `ℤ` is an instance of the class with `mul := (· + ·)`, `one := 0`, `inv := (- ·)`, and the
  five laws are the five core lemmas by name.
- **`zpow_add` sizes §4 at five problems.** `zpow_add_one` is ten lines by `cases` on `ℤ`,
  `show` on the definitional equations `Int.ofNat k + 1 = Int.ofNat (k + 1)` and
  `Int.negSucc (k + 1) + 1 = Int.negSucc k`, and `pow_succ'` with `mul_inv_rev`;
  `zpow_sub_one` is four lines from it; `zpow_add` is four lines by `Int.induction_on`, whose
  cases are named `zero`, `succ` and `pred`; `zpow_neg` is one line. `pow_add`, `pow_mul`,
  `pow_succ'` and `(1 : ℤ) ^ k = k` are each a short induction.
- **`ZMod n` with `[NeZero n]`** is the shape: `@[ext] structure ZMod (n : ℕ) where val : ℕ;
  val_lt : val < n` with `deriving DecidableEq`, an `OfNat (ZMod n) k` instance for literals,
  and the five laws one `rw` each after `ext` and `show` (`Nat.mod_add_mod`, `Nat.add_mod_mod`,
  `Nat.add_assoc`; `Nat.zero_add` and `Nat.mod_eq_of_lt`; `Nat.sub_add_cancel` and
  `Nat.add_sub_cancel'` with `Nat.mod_self`). `Fintype (ZMod n)` is `Fintype.ofEquiv (Fin n)`
  of the evident equivalence, and `Fintype.card (ZMod n) = n` by `card_congr` and `card_fin`.
  `ZMod (n + 1)` is not needed.
- **`DihedralGroup n`'s `Fintype`** goes through `equivProd : DihedralGroup n ≃ Fin 2 × Fin n`
  and `finProdFinEquiv`, with `Fintype.card (DihedralGroup n) = 2 * n` by `card_congr` and
  `card_fin`. Its `one_mul` needs `inv_one` (`r 𝟙 ∗ sr a = sr (a ∗ 𝟙⁻¹)`), so §2's
  `consequences` must prove `inv_one` before §3; its associativity in general needs `ZMod n`'s
  commutativity and `mul_inv_rev`, so §3 proves `CommGroup (ZMod n)` before the table's laws.
- **`decide` reaches `D₄`**: `∀ x : DihedralGroup 4, (∀ y, x ∗ y = y ∗ x) ↔ (x = r 0 ∨ x = r 2)`
  closes by `decide`, and so do `D₄`'s associativity (512 cases), `D₃`'s sixth powers,
  `Fintype.card (DihedralGroup 4) = 8`, `ZMod 6`'s commutativity, `r ∗ s ≠ s ∗ r` in
  `Equiv.Perm (Fin 3)`, and `Bool` under `xor`. A literal such as `sr 0` needs its type,
  `(sr 0 : DihedralGroup 4)`, or `OfNat` is stuck on the metavariable.
- **The reduction `ℤ → ZMod n`** through `Int.emod` and `Int.toNat` is an eight-line `map_mul`
  (`Int.toNat_lt`, `Int.emod_nonneg`, `Int.emod_lt_of_pos`, `Int.add_emod`,
  `Int.natCast_emod`, `Int.natCast_add`, `Int.toNat_of_nonneg`, `Int.toNat_natCast`). The
  cheaper route for §6 is `k ↦ (1 : ZMod n) ^ k`, a homomorphism by `zpow_add`, with
  `1 ^ k = ⟨k % n, _⟩` a theorem; the §6 session chooses.
- **`Quotient.fintype` is in the fence** after all (the table above was wrong), so
  `Fintype (G ⧸ H)` is instance search under `open Classical in` and §7 builds nothing for it;
  §1 teaches it so. `finRotate` is not in the fence, `finTwoEquiv` is.
- **`Nat.find` under `decide`**: `rw [Nat.find_eq_iff]` then `decide` on both conjuncts; §1's
  `find_least` shows it.
- **A problem-owned `CoeSort`** could not be tested in §1, which owns no coercion; §5 tests it
  at its first extract, as the hazard there says.
- **Mathlib's names to mirror**, checked under `import Mathlib`: `QuotientGroup.leftRel_apply :
  leftRel s x y ↔ x⁻¹ * y ∈ s`, `QuotientGroup.eq`, `QuotientGroup.mk_surjective`,
  `QuotientGroup.mk' N : G →* G ⧸ N`, `QuotientGroup.lift`, `lift_mk`,
  `quotientKerEquivRange`, `quotientKerEquivOfSurjective`,
  `quotientInfEquivProdNormalQuotient` (the second isomorphism theorem),
  `comapMk'OrderIso` (the correspondence theorem), `quotientQuotientEquivQuotient` (the third);
  `Subgroup.card_mul_index : Nat.card H * H.index = Nat.card G`, `Subgroup.index_mul_card`,
  `Subgroup.groupEquivQuotientProdSubgroup : α ≃ (α ⧸ s) × s`, `Subgroup.Normal.conj_mem`,
  `MonoidHom.ker_eq_bot_iff`, `MonoidHom.range_eq_top`, `MulEquiv.ofBijective`,
  `Equiv.mulLeft`, `MulAction.toPermHom`, `MulAction.orbitEquivQuotientStabilizer α b`,
  `MulAction.fixedPoints`, `MulAction.orbitRel`, `ConjAct.toConjAct`, `IsPGroup p G`,
  `IsPGroup.center_nontrivial`, `IsPGroup.commutative_of_card_eq_prime_sq` (stated with
  `IsMulCommutative`), `commutative_of_cyclic_center_quotient`. Mathlib's `IsCyclic G` now
  needs only `[Pow G ℤ]`, so it is already the student's `∃ g, ∀ x, ∃ n : ℤ, g ^ n = x` in
  shape. Unknown under the names the plan guessed, to be found by their sections:
  `Subgroup.normal_of_index_two`, `MulAction.card_modEq_card_fixedPoints`, `leftCoset`,
  `Subgroup.card_center_eq_prime_pow`, `Fintype.card_eq_sum_card_fiberwise`.

## Building a section

The recipe is `BEST_PRACTICES.md` Step 2, kept here so that a fresh session finds it:

1. Load `polya-author` and `writing-clearly-and-concisely`; read this plan's entry and **Next
   step**, `STYLE.md`, the skill's reference files, and the previous section in full.
2. Run the fence probe with the section's imports: `Group` and the names it teaches unknown,
   the tools known.
3. Write the Lean first, with placeholder prose, and compile with `lake env lean` one file at a
   time; never `lake build` without a target.
4. Test each `@spec` against variants that must pass and wrong definitions that must fail.
5. Check every problem against the rule: the Lean in it is §1's, or the one device the
   section's entry names for that problem, and the mathematics in it is one idea. Check the
   section against **The running examples**: every concept returns to one of the eight, and the
   example problem is the smallest that shows the phenomenon.
6. Write the prose; measure it (17–27 lines at 55 characters per problem, 400 characters per
   concept).
7. Wire the section in: the import in the subject root, `@goal` on the last concept, the README
   row, this plan's **As built** and **Next step**.
8. `lake build PolyaAlgebra.GroupTheory.<Section>`, then
   `lake exe polya extract grouptheory`: `N problems, 0 errors`.
9. Run `scripts/` over the bundle: budgets, prose names, stub shortcuts, and the vocabulary
   audit against §1 and the earlier sections.
10. Read the section as the student would; fix; commit it on its own, "Group Theory §N, Title: …".
11. Record each lesson in `STYLE.md` and here.

After each section, a small student review of that section (one agent per concept, from the
answer-free bundle, at most three agents at a time), whose brief asks the rule's question
verbatim: does any problem teach a new piece of mathematics and an unfamiliar piece of Mathlib
at once? After the draft: the passes of `BEST_PRACTICES.md` Step 4 in order, reusing
`polya-topology/AUDIT.md` and `scripts/solver/`.

## Decisions

Dated. Items 1, 2, 6, 8 and 9 are the owner's; 3–5 are open and carry a recommendation, and 4
was reopened on 2026-10-22 and awaits the owner; the rest are settled by the house rules and
recorded so that a session does not reopen them.

- **1. The student defines `Group`** (the owner, 2026-10-21): "The student should redefine as
  much as possible, including Group and Homomorphism. See GeneralTopology in ../polya-topology
  for an example. And Naturals in ../polya-basic. That's the way to teach it. Plus, the Mathlib
  way of defining a group from One, Magma, etc. is a Mathlib API choice not a pedagogical one."
  The first draft had taken Mathlib's class to keep `Fintype.card_prod`, `Finset.sum` and
  `Nat.Prime`, whose modules carry it; those three are now the student's work, which is the
  point (see **The fence**, the table of replacements).
- **2. The student defines homomorphisms** (the owner, 2026-10-21, the same words). The first
  draft had taken `G →* H` from the fence because every `Fintype` module beyond `Card` carries
  `MonoidHom`; with `Group` itself out of the fence those modules are out too, and nothing
  forces the name.
- **3. The name of the homomorphism structure** (open, 2026-10-21; settled by the owner, 2026-10-26). By what §6's first
  definition is called:
  - *`MonoidHom`*, Mathlib's name for a homomorphism of groups, with Mathlib's notation
    `G →* H`, and a sentence in the prose saying that Mathlib names it after the monoid
    structure it preserves. A later subject that imports Mathlib reads unchanged.
  - *`GroupHom`*, the name a textbook would use, with the same notation; Mathlib has no such
    name, so the arrival at Mathlib renames one structure.

  **Recommendation: `MonoidHom`**, for the vocabulary rule; the field names `map_mul'`,
  `map_one` and the notation are Mathlib's in either case. **Taken as recommended, 2026-10-21**,
  by the session that built §1, the owner not having objected; a name, cheap to change before §6.
  **Overruled by the owner, 2026-10-26**, after §6 was built: `MonoidHom` names a structure the
  subject never defines, and the prose never said why, so the homomorphism is `GroupHom` with the
  twin `AddGroupHom`, and the isomorphism, for the same reason, `GroupIso` with the twin
  `AddGroupIso` in place of Mathlib's `MulEquiv` and `AddEquiv`; the notations `→*`, `→+`, `≃*`
  and `≃+` stay Mathlib's. The slugs moved with them (`group_hom`, `add_group_hom`, `group_iso`,
  `add_group_iso`, `group_iso_symm`, `group_iso_invariants`, `zmod_two_iso_bool`), the subject
  being unpublished. `Hom` alone was rejected: rings, modules and Mathlib's categories all have
  homomorphisms, and Mathlib's category theory already spells `Hom`.
- **4. The operation's symbol, and so the shape of the class** (open, 2026-10-21; it follows
  from the owner's two points of the same day, that `ZMod n` is built with `%` and that `ℤ` is
  an example). By what §2's first instance for `ℤ` looks like:
  - *The group's own symbols*: `class Group (G : Type) extends Inv G` with fields `mul` and
    `one`, `infixl:70 " ∗ " => Group.mul` and `notation "𝟙" => Group.one`, so that the axioms read
    `a ∗ b ∗ c = a ∗ (b ∗ c)` and `𝟙 ∗ a = a`, and `instance : Group ℤ` has `mul := (· + ·)`,
    `one := 0`, `inv := (- ·)`, with `(3 : ℤ) ∗ 4 = 7`, `(𝟙 : ℤ) = 0` and `(3 : ℤ)⁻¹ = -3` by
    `rfl` and `(3 : ℤ) * 4 = 12` as before. `∗` is Milne's symbol in Definition 1.1 and `𝟙`
    stands for his `e`; `⁻¹` comes from the notation class `Inv`, which `ℤ` and `Equiv.Perm X`
    do not already carry (checked). The lemma names stay Mathlib's. Checked to compile, with
    `ℤ`, `ZMod n` and `Equiv.Perm X` as instances and `decide` working on all three.
  - *Mathlib's symbols*: `class Group (G : Type) extends Mul G, One G, Inv G`, so that the axioms
    read `a * b * c = a * (b * c)` and `1 * a = a` as in Mathlib. Then `ℤ` under addition cannot
    be an instance, because `Mul ℤ` is multiplication and `One ℤ` is the integer `1`: the
    instance would make `3 * 4 = 7` and `(1 : ℤ) = 0`. `ℤ` would enter only through a wrapper
    (`Multiplicative`, Mathlib's own device) or as the translations inside `Equiv.Perm ℤ`, and
    `ZMod n` would read `a * b` for addition mod `n`.

  **Recommendation: the group's own symbols.** The examples decide it: a class whose instances
  are `ℤ` under `+`, `ZMod n` under `+ mod n`, `Sₙ` under `∘` and `Dₙ` under its table, each
  written `a ∗ b`, is the textbook's notion of a group, and the second option exists in Mathlib
  for the library's reasons. `𝟙` is typed `\b1`; `e` would collide with the variable name every
  `Equiv` wants. **Taken as recommended, 2026-10-21**, and recorded in `STYLE.md`; the shape was
  compiled again that day with all four examples and `decide` on each (see **Before §1**, 8).

  **Reopened 2026-10-22** by the owner: "Early on in the planning phase you said that because
  we were not using Mathlib's group that we therefore could not use the classes One and Mul.
  And you defined infix for \ast instead. But then you went ahead and used Inv. I see no reason
  why you can't use One and Mul as well. Just as you did with Inv, you don't need to have the
  Group class inherit from them." The reason is not the class's shape but `ℤ`, and a probe
  (`scripts/notation_probe.lean`, under the fence) settles what happens: with
  `instance [Group G] : Mul G := ⟨Group.mul⟩`, `instance [Group G] : One G := ⟨Group.one⟩` and
  the `ℤ` instance under addition, `(3 : ℤ) * 4` is still `12` and `(1 : ℤ)` still `1`, because
  Lean prefers the integers' own instances (a concrete key beats a generic one, as §4 found for
  `NatPow ℤ`), while `(One.one : ℤ)` is `0`; the group's `one_mul` applied to `3 : ℤ` prints
  `1 * 3 = 3` and means `0 + 3 = 3`; `example : (1 : ℤ) * 3 = 3 := one_mul 3` fails, and so does
  `rw [one_mul]` on that goal ("did not find `1 * ?a` in `1 * 3 = 3`"). `Inv` has no such
  collision because the fence gives `ℤ` no `Inv` (`#synth Inv ℤ` fails), and a second
  `postfix:max "⁻¹"` beside Mathlib's makes `a⁻¹` an "Ambiguous term".

  The same day the owner asked to explore the wrapper ("So the only thing preventing us from
  using Mul and One is the fact that we need to use the integers as an example? It seems worth
  exploring the Int wrapper then"), weighing the cost across the subject against the gains for
  the other examples and the handoff to the later subjects on Mathlib's `Group`. A second probe
  (`scripts/wrapper_probe.lean`) found two more facts. **`ℤ` is not the only obstacle: `ZMod n`
  has the same one, by the student's own numerals.** Under `*`, the student's `ZMod n` with its
  `OfNat` instance has `(3 : ZMod 5) * 4 = 2` and `(1 : ZMod 5) * 1 = 2`, and `one_mul
  (1 : ZMod 5)` prints `1 * 1 = 1` with two different ones, the numeral being the residue `1`
  and the group's `1` the residue `0`; `Dₙ`'s table would read `r (i * j)`. So under `*` every
  additive example (`ℤ`, `ZMod n`, and `Bool` under `xor`, whose `1` would be `false`) is
  wrapped or reads wrongly, which is why Mathlib has `AddGroup` and `Multiplicative`. **The
  wrapper works.** The student's `def Multiplicative (α : Type u) := α` with `ofAdd`, `toAdd`
  and `DecidableEq` by `inferInstanceAs`, and `instance : Group (Multiplicative ℤ)` from the
  five core laws, gives `ofAdd 3 * ofAdd 4 = ofAdd 7` by `rfl` and by `decide`,
  `(1 : Multiplicative ℤ) = ofAdd 0`, and no numeral `(3 : Multiplicative ℤ)`, so the two ones
  cannot be confused; `omega` is blind through the wrapper until a `show toAdd x = 4` or a
  rewrite with `ofAdd_mul : ofAdd a * ofAdd b = ofAdd (a + b)`, as `int_mul_eq_add` serves today,
  and `rw [h]` leaves `ofAdd 3 * ofAdd 4 = ofAdd 7` for an explicit `rfl`. The product diamond
  is benign: on `G × H` the fence's `Prod.instMul` wins the elaboration of `*`, and
  `rw [mul_assoc]`, `mul_assoc a b c` and `rfl` all accept it against the group's instance when
  the product's `mul` is componentwise. Under the fence `Unit`, `Bool`, `Equiv.Perm`, a subtype
  and the student's structures carry no `Mul` or `One`; `Fin n` carries both, which the
  student's `ZMod n` avoids by being a structure.

  The two designs, by what the content reads:
  - *The symbols stay* (`∗`, `𝟙`, `⁻¹`): `(3 : ℤ) ∗ 4 = 7`, `(3 : ZMod 5) ∗ 4 = 2`,
    `int_solve : (3 : ℤ) ∗ x = 7 ↔ x = 4`, `r (i ∗ j)` in `Dₙ`. No cost now beyond §2's **Fix**
    (half a session). No instance diamonds, since `∗` names `Group.mul` alone. The student types
    `\ast` and `\b1` (lean4monaco's abbreviations are in the editor). The handoff to Mathlib is
    one lesson for the theory (the symbols) and three relearnings for the examples: Mathlib has
    no `Group ℤ` (it has `AddGroup ℤ` and `Multiplicative ℤ`); Mathlib's `ZMod n` has `+` and a
    ring's `*` where the student's has only `∗` meaning `+`; Mathlib's `DihedralGroup` table
    reads `r (i + j)`.
  - *Mathlib's symbols* (`*`, `1`, `⁻¹` through `Mul`, `One`, `Inv` instances, the owner's
    shape): the three instances are the notation problem; `ZMod n` becomes additive, with the
    student's `Add`, `Zero` and `Neg` instances and `(3 : ZMod 5) + 4 = 2`, as Mathlib's; the
    student writes `Multiplicative`, and the groups are `Multiplicative ℤ` and
    `Multiplicative (ZMod n)`, with `ofAdd 3 * ofAdd 4 = ofAdd 7`,
    `int_solve : ofAdd 3 * x = ofAdd 7 ↔ x = ofAdd 4`, `intMultiples n : Subgroup
    (Multiplicative ℤ)` with carrier `{x | n ∣ toAdd x}`, `zpowers (ofAdd 2) = {ofAdd 0, ofAdd 2,
    ofAdd 4}`, and `r (i + j)` in `Dₙ`, Mathlib's table; `Bool` under `xor` stays bare with
    `1 = false`, said in a sentence, or yields to `Multiplicative (ZMod 2)` in §3; the product
    example reads `Multiplicative (ZMod 2) × Multiplicative (ZMod 3)`. Cost: of the 79 built
    problems after §1, 35 are reshaped (11 that use `ℤ` as a group: `int_add_group`,
    `solve_equation`, `comm_instances`, `int_pow`, `zpow`, `is_of_fin_order`, `order_of_cases`,
    `int_multiples`, `center_eq_top`, `int_cyclic`, `int_group_of_left_axioms`; 21 more on
    `ZMod n`, the whole `zmod` concept and the products and dihedral groups of §3 among them; 3
    on `Bool`), all 79 change symbol, §2 gains the wrapper problem (a type synonym and why
    instances do not cross it, the device §11 planned for `ConjAct`) and §3 a problem for
    `ZMod n`'s additive laws, and the changed concepts are reviewed again: two to three sessions.
    Of the planned §6–§12, about twenty example problems wear `ofAdd` (the reductions
    `Multiplicative ℤ →* Multiplicative (ZMod n)` and `ZMod 6 →* ZMod 2`, the kernels, the
    cosets of `nℤ`, `ℤ ⧸ nℤ ≃* ZMod n`, `ZMod p`, `⟨2⟩ ⊔ ⟨3⟩`); the other hundred or so, the
    theory, read character for character as Mathlib's statements, and so do the instances for
    `Equiv.Perm`, `DihedralGroup`, `G × H`, a subgroup as a type, `G ⧸ N` and `MulAction`.

  **Recommendation, 2026-10-22: Mathlib's symbols, decided now, if the owner accepts `ofAdd` on
  the two additive examples as the price.** The gain is the handoff the owner asks for: the
  theory of twelve sections reads as Mathlib's, `Multiplicative ℤ` is Mathlib's own type for
  this very situation, and `ZMod n` with `+` is Mathlib's reading of it; the cost is two to
  three sessions now, and it grows with every section built on `∗`. The symbols stay if the
  first-course reading of `ℤ` and `ZMod n` as bare instances matters more than
  Mathlib-identical statements; that design is sound, and its handoff is one lesson plus three
  relearnings. Awaiting the owner. The owner then asked to see the wrapper problems:
  `plans/notation_drafts.lean` (2026-10-22, deleted once they were built into §2 and §3 the
  same day) held them as compiled problem blocks in the house format, `group_notation` (the
  three instances), `multiplicative` (the copy, `ofAdd`, `toAdd`,
  `ofAdd_inj`, with `DecidableEq` carried across as a given), `int_add_group`
  (`Group (Multiplicative ℤ)` from the five core laws, `ofAdd_add`, `ofAdd_zero`, `ofAdd_neg`)
  and `zmod_group` (`Group (Multiplicative (ZMod n))` from five additive laws of the student's
  `ZMod n`, which gains `Add` and `Neg` instances), each within the page budget, with `int_solve`
  and `decide` over `Multiplicative (ZMod 6)` as downstream samples. A generic alternative, a
  student `AddGroup` class with one instance `Group (Multiplicative α)`, Mathlib's own shape, was
  compiled too: its generic `ofAdd_add` leaves `AddGroup.add` in a goal, which `omega` does not
  read, so it needs `+` notation on `AddGroup` (a benign diamond with `Int.instAdd`) or per-type
  restatements anyway, and the drafts take the per-type instances.

  **Taken 2026-10-22: Mathlib's symbols**, by the owner ("Ok, refactor the existing content and
  make sure the new plan is consistent with this pattern for future steps"), after seeing the
  drafts. §2–§5 and Extra Credit were refactored the same day, as each section's **As
  refactored** records, and **Spelling** under **The sections** is the rule for §6–§12.

  **Reopened and taken 2026-10-23: additive groups.** The owner, having worked the examples:
  "the Multiplicative definition is super cumbersome. It is generally annoying for the student to
  do coercions, especially coercing something that looks like multiplication to addition", and
  asked to explore the student's `AddGroup` for the plus-like examples with `Group` for the
  general theorems. The probes (`scripts/addgroup_probe.lean`, `scripts/addgroup_order_probe.lean`)
  found that a student `AddGroup ℤ` built from the integers' own operations lets every additive
  law reach `3 + x` as written (`rw [zero_add]` on `(0 : ℤ) + 3 = 3`, `add_left_cancel h` on
  `h : 3 + x = 3 + 4`), on `ZMod n`'s numerals too; that `@[to_additive]` works on the student's
  declarations once each class and structure has a hand-written twin, linked afterwards by
  `attribute [to_additive existing …]`; and that it cannot make the twin itself. The analysis
  for the owner: the examples lose every `ofAdd`, while the definitions double, the copy of each
  theorem being free under the mark and each class or structure costing one short problem. The
  owner's answers to four questions: `•` is accepted as the textbook's `na`; the mark is taught
  in a problem of its own, the student having met `@[simp]`; `Bool` under `xor` is plus-like
  (addition modulo two), so additive, and the parity maps land in `Equiv.Perm (Fin 2)`; and the
  student writes `AddGroup` and every twin. Then: "Ok, refactor the existing sections with these
  decisions." §2–§5 and Extra Credit were refactored the same day (each section's second **As
  refactored**), and **Spelling** under **The sections** is the rule for §6–§12.
- **5. Where primes live** (open, 2026-10-21). §8 needs `Nat.Prime`, Euclid's lemma and "a
  divisor of `p ^ n` other than `1` is divisible by `p`"; §12 uses the last.
  - *A concept `primes` in §8*, four problems, the student's: Milne's definition of a prime,
    `two_le`, coprimality from §1's `Nat.Coprime`, Euclid's lemma, the divisor lemma. The
    student redefines as much as possible, and Naturals plans the same material for `MyNat`.
  - *A library module `PolyaAlgebra/Arithmetic.lean`*, compiled theory the student uses and
    never writes, imported by §8; the prose introduces `Nat.Prime` by its definition before a
    statement uses it. Four problems fewer, and primes stay outside a subject about groups.

  **Recommendation: the concept in §8**, by the owner's rule, with the module as the fallback
  if §8 outgrows its budget. **Taken as recommended, 2026-10-21.** Euclid's lemma dropped by the owner, 2026-10-27: "If this is just number theory stuff, then drop it."
- **6. The running examples** (the owner, 2026-10-21): "One thing that will make this subject
  really nice is a good set of examples. Permutations, ZMod, etc. … all examples should be as
  basic as possible and there should be an early section called Examples." And the same day:
  "With z mod, it might be easier to just define the operation using % and not worry about
  Mathlib's ZMod. Also just Z (the integers) is going to be an example, right?" The eight of
  **The running examples**, §2 and §3, and the rule that every concept returns to them. What it
  settled along the way: `ZMod n` is the student's structure holding a `val : ℕ` with `val < n`,
  its operation `(a + b) % n`, owing nothing to Mathlib's `ZMod` but the name; `ℤ` is an
  instance as it stands, which is what Decision 4 is for; `Dₙ` has Mathlib's shape, an
  inductive over `ZMod n` with a four-line table, since that is the one shape in which every
  small fact about `D₄` is a `decide`; `V₄` is `D₂`.
- **7. How a later subject builds on this one** (deferred). *Permutation Groups* and *The Sylow
  Theorems* import this subject's `Group`, `Subgroup`, quotients and examples as compiled
  theory, so the student's definitions are the trilogy's. The hand-over to Mathlib's `Group`, an
  `Iff` or an equivalence of classes under Mathlib's names, is the first problem of the first
  subject that imports Mathlib's algebra, as Profinite Spaces did for topology. This plan keeps
  the names Mathlib's so that it is cheap.
- **8. A Prerequisites section, and the rule** (the owner, 2026-10-21): "we also need a
  Prerequisites section to introduce concepts (and the Mathlib/Lean implementation for them).
  If we assume that student has worked through the topics in polya-basic, then I am thinking
  we need things like relations (A -> A -> Prop), equivalence relations, etc. … make sure to
  recommend in the plan that we need to be careful not to simultaneously introduce a mathlib
  idea and a complicated mathematical idea in one problem." §1 is that section; the rule is
  the first design point, with the three places that enforce it; and the warm-ups that the
  earlier drafts had scattered through §2–§12 moved into §1, so that each later section's
  entry can name the one or two Lean devices it still introduces and say that nothing else in
  it is new Lean.
- **9. The notation is a problem of its own** (the owner, 2026-10-22): "there should be an
  explicit problem introducing the notation instances as problems or at least as @givens so the
  student sees how it works." §2 gets `group_notation`, whose target is the `Inv G` instance and
  whose prose introduces the two notation commands beside it; a notation command cannot be a
  `@given` (the publisher admits only declarations, instances, examples and directives as block
  members), so the commands stay outside the block and the problem shows them. §2's **Fix** is
  the subplan; §4's `Pow G ℕ` and `Pow G ℤ` instances were already targets of their own
  problems, so no other section changes. Under Mathlib's symbols (Decision 4, the second
  design) the problem's targets are the three instances `Mul G`, `One G` and `Inv G`, and it is
  the first step of the rework that decision describes. Built 2026-10-22 as `group_notation`, with the three instances as its targets.
- **The goal** (2026-10-21): *every group of order `p ^ 2` is commutative*, Milne 4.18. The
  alternatives considered were Cauchy's theorem (a section more and a cyclic group of order `p`
  acting on tuples) and Lagrange's theorem (eight sections, the rest a second subject); the
  owner has not objected to the first, and the plan takes it.
- **Cardinality is `Fintype.card`** (2026-10-21): `Nat.card` is beyond the fence. The prose at
  Lagrange says Mathlib states it with `Nat.card`.
- **Lagrange is counted by labelling, not by a product** (2026-10-21): `Fintype.card_prod`'s
  module carries `Group`; the chain `G ≃ (G ⧸ H) × H ≃ Fin (index) × Fin (card H) ≃
  Fin (index * card H)` uses only the fence, and §1 rehearses it.
- **The class equation is counted by blocks, not by a sum** (2026-10-21): `Finset.sum`'s
  module carries `Group`; the congruence modulo `p` is proved by `Finset.induction_on` over
  the orbits.
- **`Set` is Mathlib's** (2026-10-21), introduced in §1 beside Set Theory's, not the student's
  own again.
- **The symmetric group's operation is Mathlib's**, `f ∗ g = g.trans f` (2026-10-21), so
  that `(f ∗ g) x = f (g x)`.
- **`orderOf` follows Mathlib's convention**, `0` for infinite order (2026-10-21), defined
  through `Nat.find` under `open Classical` rather than `Function.minimalPeriod`.
- **`IsCyclic` and `IsPGroup` are the student's**, by Milne's definitions (2026-10-21):
  `∃ g, ∀ x, x ∈ zpowers g` and `∃ n, card G = p ^ n`; the prose says Mathlib's are
  `∃ g, Surjective (g ^ ·)` and the element-wise one.
- **Milne's notes are a syllabus only** (2026-10-21): CC BY-NC-SA 4.0 cannot be adapted into a
  CC BY subject. The subject's license is CC BY 4.0, the repository default.
- **No subject of `polya-basic` is imported** (2026-10-21): its `Set`, `Function.Injective` and
  `MyNat` are its own; the dependency is carried by `links.yaml`, and §1 re-proves on Mathlib's
  `Set` what Set Theory proved on its own.

## Next step

§11, Group Actions, in a fresh session: "Do the next section in Group Theory, which is §11 Group
Actions". Read §11's entry, §10's **As built** (the names as they are in Lean:
`GroupIso.ofBijective`, `QuotientGroup.lift_injective`, `lift_surjective`,
`quotientKerEquivOfSurjective`, `GroupHom.rangeRestrict`, `ker_rangeRestrict`,
`quotientKerEquivRange`, `intQuotientEquivZMod`; `Subgroup.comap`, `Subgroup.map`, `mem_comap`,
`mem_map`, `le_comap_mk'`, `map_comap_mk'`, `comap_map_mk'`; `Subgroup.subtype`, `subgroupOf`,
`mem_subgroupOf`, `normal_subgroupOf`, `ker_restrict`, `quotientSubgroupOfEquivRange`;
`card_subgroupOf`, `index_eq_mul_index`; `mul_comm_of_inf_eq_bot`, `prodMul`,
`prodMul_injective`, `prodMulEquiv`; every one with its additive version), `STYLE.md` with
**Learned building §10**, and §1–§10 in full before writing. Points for the entry. An
isomorphism onto a named quotient is built from the lift with `lift_injective`, so that its value
on a class holds by definition (a rewrite of the quotient's subgroup compiles but loses that); an example whose `def` would share an auxiliary proof with a
later problem's `def` is stated as an existence theorem. The goal moves to §11's last concept;
`FewerAxioms.lean` stays the root's last import and then imports §11's file.

The previous next step, kept for the record: §10, The Isomorphism Theorems, in a fresh session: "Do the next section in Group Theory, which
is §10 The Isomorphism Theorems". Read §10's entry, §9's **As built** (the names as they are in
Lean: `Subgroup.Normal N` taken as `[N.Normal]`, `conj_mem`, `conj_mem'`,
`normal_iff_leftCoset_eq_rightCoset`, the instances `normal_of_comm`, `center_normal`,
`GroupHom.normal_ker`, `DihedralGroup.rotations_normal`; `H ⊔ K` through `Subgroup.instMax`,
`le_sup_left`, `le_sup_right`, `sup_le`, `Subgroup.mulNormal`, `mem_sup_of_normal`;
`QuotientGroup.Quotient.group N`, `mk_mul`, `mk_one`, `mk_pow`, `QuotientGroup.mk' N`, `ker_mk'`,
`Quotient.commGroup`, `Subgroup.pow_index_mem`, `addOrderOf_mk_one_int`;
`GroupHom.eq_of_inv_mul_mem_ker`, `QuotientGroup.lift N f hN`, `lift_mk`, `lift_unique`,
`exists_hom_int_quotient`; every one with its additive version), `STYLE.md` with **Learned
building §9**, and §1–§9 in full before writing. Points for the entry. Its Mathlib names
(`quotientKerEquivRange`, `MulEquiv`'s `≃*`) are read as the student's: `≃*` is §6's `GroupIso`,
and a new structure name is asked of the owner first. The first isomorphism theorem is
`QuotientGroup.lift` of `f` on `ker f`, with `lift_unique` for the inverse's laws; `ℤ ⧸ nℤ ≃+
ZMod n` continues `lift_int`, and `addOrderOf_mk_one_int` gives the index of `nℤ`. `comap` and
`map` are not yet defined. The goal moves to §10's last concept; `FewerAxioms.lean` stays the
root's last import and then imports §10's file.

The previous next step, kept for the record: §9, Normal Subgroups and Quotient Groups, in a fresh session: "Do the next section in Group
Theory, which is §9 Normal Subgroups and Quotient Groups". Read §9's entry, §8's **As built**
(the names as they are in Lean: `zpow_mod_orderOf`, `Fintype.card_zpowers`, `orderOf_dvd_card`,
`pow_card_eq_one`, `ZMod.addOrderOf_one`; `Nat.Prime` read through `Nat.Prime.two_le` and
`Nat.Prime.eq_one_or_self_of_dvd`, never its projections; `Subgroup.eq_top_of_card_eq`,
`Subgroup.eq_bot_of_card_eq`, `Subgroup.zpowers_eq_top_of_prime_card`, `isCyclic_of_prime_card`,
`Subgroup.eq_bot_or_eq_top_of_prime_card`; every one with its additive version), `STYLE.md` with
**Learned building §8**, and §1–§8 in full before writing. Points for the entry. A subgroup of
index two is normal through `index_mul_card`, since the index is classical and nothing decides
it; `⟨s⟩` not normal in `D₃` is §7's `d3FixZero`, through `mem_d3FixZero`, since `decide` cannot
see inside a `def` subgroup. The `Group (G ⧸ N)` instance carries a name, and `G ⧸ N` already has
its `Fintype` instance, `QuotientGroup.fintype`. The goal moves to §9's last concept;
`FewerAxioms.lean` stays the root's last import and then imports §9's file.

The previous next step, kept for the record: §7, Cosets and Lagrange's Theorem, in a fresh session: "Do the next section in Group Theory,
which is §7 Cosets and Lagrange's Theorem". First, the student review of §6 with
`scripts/review/`, as §1–§5 had, if this session did not finish it (§6's **As built** says
whether it ran). Read §7's entry, §6's **As built** (the names as they are in Lean: `G →* H` for
`GroupHom G H` applied as `f.toFun a`, `GroupHom.map_mul`, `map_one`, `map_inv`, `map_pow`,
`map_zpow`, `comp`, `id`, `fst`; `G ≃* H` for `GroupIso G H` extending `G ≃ H`, with
`toGroupHom`, `symm`, `card_eq`, `mul_comm`, `mul_self_eq_one`; `f.ker`, `f.range`, `mem_ker`,
`mem_range`, `range_eq_top`, `ker_eq_bot_iff`, `Subgroup.inv_mem_iff`; the examples
`zmodSixToTwo`, `intToZMod n`, `DihedralGroup.orientation n`, `swap2`, `zmodTwoIsoBool`,
`DihedralGroup.toPerm3`, `ker_zmodSixToTwo`, `ker_orientation`, `ker_intToZMod`; `Equiv.mulLeft`
and `cayley`, each with its additive version but `cayley`), `STYLE.md` with **Learned building
§6** (a notation is replayed only for a pulled item that names its declaration; inside
`Group.x`, `mul_one` is the class field; `decide` and free variables; no `Fintype` on a product),
and §1–§6 in full before writing. The entry predates the symbols: its `∗` is `*`, and every coset,
relation and quotient carries a written `@[to_additive NAME]` (`leftAddCoset`,
`QuotientAddGroup.leftRel`, the additive `HasQuotient` instance a twin of the multiplicative one)
so that the cosets of `2ℤ` and the subgroups of `ZMod 6` are additive, as the running examples
are. The hazard the entry names, `Quotient.out` under choice, stands; test the `HasQuotient`
instance at the first extract, since §5 found that only an instance a compiled term names reaches
a later context. The goal moves to §7's last concept; `FewerAxioms.lean` stays the root's last
import and then imports §7's file.

## The prompts that produced this plan

Verbatim, from the session of 2026-10-21, typos included:

````
This will by a new polya content repo. Initialize a Lean project with Mathlib here and add the polya-publisher dependency as described in ../polya-publisher.
````
````
Now download https://www.jmilne.org/math/CourseNotes/GT.pdf and put it in an untracked directory called refs.
````
````
Make sure the polya publisher skill is installed and active. And then read the BEST_PROACTICES.md file in the publisher directory.
````
````
Now make a plan to build a new subject, GroupTheory, using the pdf in refs as a guide. Put the result plan in a directory called plans.
````
````
The student should redefine as much as possible, including Group and Homomorphism. See GeneralTopology in ../polya-topology for an example. And Naturals in ../polya-basic. That's they way to teach it. Plus, the Mathlib way of defining a group from One, Magma, etc. is a Mathlib API choice not a pedagogical one. Revise the plan accordingly.
````
````
One thing thing that will make this subject really nice is a good set of examples. Permuations, ZMod, etc. List the set of examples that the subject will use and describe how to keep coming back to them througout. If a concept is introduced and there is no interesting example then try to find one commonly used in the literature. At the same time, we don't want to require the student to have to know that much coming into this, so all examples should be as basic as possible and there should be an early section called Examples.
````
````
With z mod, it might be easier to just define the operation using % and not worry about Mathlib's ZMod. Also just Z (the integers) is going to be an example, right?
````
````
Ok. Now we also need a Prerequsites section to introduce concepts (and the the Mathlib/Lean implemenation for them). If we assume that student has worked through the topics in polya-basic, then I am thinking we need things like relations (A -> A -> Prop), equivalence relations, etc. Come up with a good list and make sure to recommend in the plan that we need to be careful not to simultaneously introduce a mathlib idea and a complicated mathematical idea in one problem.
````
