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
hard mathematical idea at once** (see **Design points**, the rule, and §1). Proposed, not
decided: the open questions are under **Decisions**, each with a recommendation.

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
| the group of order two | `Bool` under `xor` | the second instance, closed by `decide`; the target of every "parity" homomorphism (rotation or reflection, even or odd); `ZMod 2 ≃* Bool` is the first isomorphism |
| the integers | `ℤ` under addition, an instance of the student's class as it stands (Milne 1.3, `C∞`) | the infinite example: `𝟙` is `0` and `a⁻¹` is `-a`; an element of infinite order, so that `orderOf (1 : ℤ) = 0` means something; the subgroups `nℤ = zpowers n`; cosets of `2ℤ` are the evens and the odds; `ℤ ⧸ nℤ ≃* ZMod n` (1.44 a); the one group whose subgroups and quotients the student can list completely |
| the integers mod `n` | the student's `ZMod n`, a structure holding a `val : ℕ` with `val < n`, the operation `(a + b) % n` (Milne 1.3, `Cₙ`; nothing of Mathlib's `ZMod`) | the commutative finite example; every cyclic group; subgroups `⟨d⟩` for `d ∣ n`; the reduction `ZMod 6 →* ZMod 2`; quotients `ZMod 6 ⧸ ⟨3⟩`; `ZMod 2 × ZMod 3 ≃* ZMod 6`; groups of prime order; `ZMod p × ZMod p` and `ZMod (p²)` at the goal |
| the symmetric groups | `Equiv.Perm (Fin n)`, the student's instance (Milne 1.4, `Sₙ`); `S₃` with its rotation `r` and reflection `s` written out | the first non-commutative group; the smallest, `S₃`, with `r ∗ s ≠ s ∗ r` by `decide`; Cayley's theorem; the tautological action on `Fin n` |
| the dihedral groups | the student's `DihedralGroup n`, an inductive with constructors `r i` and `sr i` over `ZMod n` and a four-line multiplication table (Milne 1.17, `Dₙ`; Mathlib's shape) | the geometric example, the symmetries of the `n`-gon: order `2n`; `⟨r⟩` normal of index two, `⟨s⟩` not normal (1.36 b); `D₄`'s centre `{𝟙, r²}`, its classes, its quotient by `⟨r²⟩` (1.49); a `p`-group with nontrivial centre; `D₃ ≃* S₃`; the action on the vertices with orbit–stabilizer `n · 2 = 2n` |
| the Klein four-group | `DihedralGroup 2`, which Milne calls `V₄` or `D₂`, isomorphic to `ZMod 2 × ZMod 2` | order 4 without an element of order 4 (1.30); not isomorphic to `ZMod 4`; every subgroup normal; `D₄ ⧸ ⟨r²⟩ ≃* V₄` |
| the product | `G × H`, the student's instance (1.5) | the projections as homomorphisms; the internal direct product; `ZMod 2 × ZMod 3 ≃* ZMod 6` (Milne eq. 13) |

Extra credit, once, in §9: the quaternion group `Q₈` (Milne 1.18, Exercise 1-1) as a second
inductive over `ZMod 4`, the non-commutative group all of whose subgroups are normal, and the
other group of order 8 with centre of order 2.

How each concept returns to them, section by section (the problem count in parentheses is
inside the section's budget, not added to it):

| concept | example problem | shows |
|---|---|---|
| §2 `group_axioms` | `Unit`; `Bool` under `xor` by `decide`; `ℤ` under addition, `(3 : ℤ) ∗ 4 = 7` and `(3 : ℤ)⁻¹ = -3` by `rfl` | an instance is an operation that passes the axioms, whatever the operation is |
| §2 `consequences` | in `Bool`, every element is its own inverse; in `ℤ`, `𝟙` is `0` | a consequence read off |
| §2 `cancellation` | in `S₃`, `r ∗ s = r ∗ x → x = s` is not a computation but a law | cancellation needs no table |
| §3 all | the definitions themselves | — |
| §4 `natural_powers` | `r ^ 3 = 𝟙` and `s ^ 2 = 𝟙` in `S₃`; `(1 : ℤ) ^ k = k` | powers computed; a power in `ℤ` is a multiple |
| §4 `order_of_element` | `orderOf (2 : ZMod 6) = 3`; `orderOf (sr i) = 2` in `Dₙ`; `orderOf (1 : ℤ) = 0` | the three cases: a divisor, an involution, infinite |
| §5 `subgroups` | the rotations `{r i}` of `Dₙ`; `⟨2⟩ = {0, 2, 4}` in `ZMod 6`; `nℤ` in `ℤ` | the criterion applied |
| §5 `centre` | `center S₃ = ⊥` by `decide`; `center D₄ = {𝟙, r 2}`; `center ℤ = ⊤` | three sizes of centre |
| §5 `generated_subgroups` | `closure {r 1, sr 0} = ⊤` in `Dₙ`; `zpowers 1 = ⊤` in `ℤ` and in `ZMod n`; `zpowers (n : ℤ) = nℤ` | generators; `ℤ` is cyclic |
| §6 `homomorphisms` | reduction `ZMod 6 →* ZMod 2`; reduction `ℤ →* ZMod n`, `k ↦ k % n`; orientation `Dₙ →* Bool` (`r i ↦ false`, `sr i ↦ true`); `Prod.fst` | the standard maps |
| §6 `isomorphisms` | `ZMod 2 ≃* Bool`; `DihedralGroup 3 ≃* Equiv.Perm (Fin 3)` by `decide`; `V₄` is not isomorphic to `ZMod 4` | sameness and difference of groups |
| §6 `kernels_and_images` | the kernel of reduction is `⟨2⟩`, of `ℤ →* ZMod n` is `nℤ`, of orientation the rotations | kernels computed |
| §6 `cayley` | `S₃` inside `Equiv.Perm S₃` as prose; the left-multiplication permutation of `ZMod 3` written out | the theorem seen once |
| §7 `cosets` | the cosets of `2ℤ` in `ℤ`; the two cosets of the rotations in `D₃`; the three left cosets of `⟨s⟩` in `D₃`, and `r⟨s⟩ ≠ ⟨s⟩r` | cosets as residues and as rows of the table; left is not right |
| §7 `lagrange` | `D₃` has no subgroup of order 4; the subgroups of `ZMod 6` have orders `1, 2, 3, 6` | the theorem used |
| §8 `cyclic_subgroups` | `zpowers (r 1)` in `Dₙ` has `n` elements | the count |
| §8 `prime_order` | `ZMod p`, and every group of order `p` is isomorphic to it (prose, until §10) | the only group of order `p` |
| §9 `normal_subgroups` | the rotations in `Dₙ` (index two); `⟨s⟩` in `D₃`; every subgroup of `V₄` and of `ℤ` | normal and not |
| §9 `quotient_groups` | `ℤ ⧸ nℤ` has `n` elements (Milne 1.44 a); `ZMod 6 ⧸ ⟨3⟩`; `D₄ ⧸ ⟨r 2⟩`, Milne 1.49 | quotients computed |
| §10 `first_isomorphism_theorem` | `ℤ ⧸ nℤ ≃* ZMod n` from `k ↦ k % n`; `ZMod 6 ⧸ ⟨2⟩ ≃* ZMod 2`; `Dₙ ⧸ rotations ≃* Bool` | the theorem as a calculation |
| §10 `correspondence_theorem` | the subgroups of `D₄` above `⟨r 2⟩` against those of `V₄` (Milne 1.49's two lattices); the subgroups of `ℤ` above `6ℤ` against those of `ZMod 6` | the bijection drawn |
| §10 `direct_products` | `ZMod 2 × ZMod 3 ≃* ZMod 6`, and `ZMod 2 × ZMod 2 ≄ ZMod 4` | coprime orders |
| §11 `actions` | `Sₙ` on `Fin n`; `Dₙ` on the vertices `Fin n`; `ZMod n` on `Fin n` by rotation; `G` on itself | actions from the examples |
| §11 `orbits`, `stabilizers` | `Dₙ` on the vertices: one orbit, stabilizer of a vertex of order 2 | transitive, with a stabilizer |
| §11 `conjugation` | the five classes of `D₄` by `decide`; `S₃`'s three classes | classes computed |
| §12 `orbit_stabilizer` | `n · 2 = 2n` for `Dₙ` on the vertices | the count checked |
| §12 `block_counting` | `Bool` acting on `Fin n` by `i ↦ -i`: the fixed points of an involution have the parity of the set (the literature's example, Zagier's) | Lemma 5.1 at `p = 2` |
| §12 `class_equation` | `8 = 1 + 1 + 2 + 2 + 2` for `D₄`; its centre `{𝟙, r 2}` | the theorem on the running `p`-group |
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
`cases` and `omega` for fixed `n` and by the `ZMod n` laws in general. There is no
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
     own, just before the problem that needs it**, and the plan names each: a class with its own
     notation (§2, the definition of `Group` itself, on which nothing else is new); recursion
     for powers (§4, Naturals' pattern) and `Int.induction_on` for `zpow_add` (§4); a `Membership`
     instance and the coercion of a subgroup to a type (§5); `CoeFun` for the student's
     homomorphisms (§6, met on `Equiv` in §1); a `HasQuotient` instance for `G ⧸ H` (§7);
     `Quotient.lift₂` for the quotient group (§9); `extends SMul` (§11); a type synonym with a
     copied instance (§11, `ConjAct`); `Finset.induction_on` (§12). A definition problem may
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
- **The student defines everything**: `Group`, `CommGroup`, the eight examples, powers,
  `orderOf`, `Subgroup`, `Subgroup.closure`, `Subgroup.zpowers`, `IsCyclic`, homomorphisms and
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
- **The group operation has its own symbol, `a ∗ b`, with neutral element `𝟙` and inverse
  `a⁻¹`**, Milne's Definition 1.1 as he writes it (`∗`, `e`, `a′`) before he abbreviates. The
  reason is the examples: a group is a set with *some* operation, and the student should see
  `ℤ` under addition, `ZMod n` under addition mod `n`, `Sₙ` under composition and `Dₙ` under its
  table as instances of one class, each with `a ∗ b` meaning what that group's operation is
  (`(3 : ℤ) ∗ 4 = 7` by `rfl`). Mathlib's `*` and `1` cannot carry this: an instance of a class
  built on `Mul ℤ` would make `3 * 4 = 7`, and `One ℤ` would make `(1 : ℤ)` the neutral element
  `0`; Mathlib keeps a second, additive hierarchy and a wrapper `Multiplicative` to avoid it,
  which is the API choice the owner has ruled out. The lemma names stay Mathlib's (`mul_assoc`,
  `one_mul`, `inv_mul_cancel`) under the student's symbols, and the prose says once, in §2, that
  Mathlib writes `a * b` and `1` and that the names are its. (**Decisions**, 4.)
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
`Nat.Prime`, `Multiplicative`, `ZMod`, `DihedralGroup`, and with them every name of Mathlib's
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
those are the student's where needed. `One ℤ` exists (`One.ofOfNat1`), which is one more reason
the neutral element is not written `1`.

What the Group-free fence costs, and what replaces it:

| lost | replaced by |
|---|---|
| `Fintype.card_prod`, `Fintype (α × β)` | counting by labelling: `G ≃ (G ⧸ H) × H`, then `Equiv.prodCongr` of two `Fintype.equivFin`, then `finProdFinEquiv`, then `Fintype.card_congr` and `Fintype.card_fin` (§7, rehearsed in §1); `V₄` counted as `DihedralGroup 2` |
| `Finset.sum`, the class equation as a sum | block counting by `Finset.induction_on` and `Finset.card_union_of_disjoint` (§12) |
| `Quotient.fintype` | not lost after all: it is in the fence, and `Fintype (G ⧸ H)` is instance search under `open Classical in` (§1 teaches it; §7 uses it) |
| pigeonhole, `Fintype.exists_ne_map_eq_of_card_lt` | the contrapositive of `Fintype.card_le_of_injective` (§1, used in §4) |
| `Nat.Prime` and Euclid's lemma | the student's `Nat.Prime`, Milne's definition, with Euclid's lemma from core's `Nat.Coprime` (§8) |
| `ZMod n`, `DihedralGroup n`, `Group (G × H)`, `Group (Equiv.Perm X)` | the student's (§3), as the owner wants |
| `Multiplicative ℤ`, `AddGroup ℤ` | not needed: `ℤ` under addition is an instance of the student's class directly, because the operation is `∗` and not `*` |
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

### §6. Homomorphisms

Milne 1.20–1.23 and p. 20. The Lean that is new here: a `CoeFun` instance for the student's
structure, which §1's `Equiv` showed the use of.

- `homomorphisms`: the student's structure (`MonoidHom` or `GroupHom`, **Decisions** 3) with
  `toFun` and `map_mul'`, a `CoeFun` instance, the notation `G →* H`; Milne 1.21 as the first
  theorems: `map_one`, `map_inv`, `map_pow`, `map_zpow`; `comp` and `id`; the examples: the
  reduction `ℤ →* ZMod n`, `k ↦ k % n` (with `Int.emod` and its non-negativity, said once),
  the reduction `ZMod 6 →* ZMod 2`, the orientation `DihedralGroup n →* Bool` (`r i ↦ false`,
  `sr i ↦ true`), the inclusion `H.subtype : H →* G`, `fst : G × H →* G`, conjugation by `g`.
  (7)
- `isomorphisms`: `MulEquiv` extending `Equiv` with `map_mul'`, the notation `G ≃* H`;
  `MulEquiv.ofBijective`; `symm`; isomorphic finite groups have the same cardinality; an
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

Budget: 19, over by one: the two lattice examples of `correspondence_theorem` can be one
problem.

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

Dated. Items 1, 2, 6 and 8 are the owner's; 3–5 are open and carry a recommendation; the rest
are settled by the house rules and recorded so that a session does not reopen them.

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
- **3. The name of the homomorphism structure** (open, 2026-10-21). By what §6's first
  definition is called:
  - *`MonoidHom`*, Mathlib's name for a homomorphism of groups, with Mathlib's notation
    `G →* H`, and a sentence in the prose saying that Mathlib names it after the monoid
    structure it preserves. A later subject that imports Mathlib reads unchanged.
  - *`GroupHom`*, the name a textbook would use, with the same notation; Mathlib has no such
    name, so the arrival at Mathlib renames one structure.

  **Recommendation: `MonoidHom`**, for the vocabulary rule; the field names `map_mul'`,
  `map_one` and the notation are Mathlib's in either case. **Taken as recommended, 2026-10-21**,
  by the session that built §1, the owner not having objected; a name, cheap to change before §6.
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
- **5. Where primes live** (open, 2026-10-21). §8 needs `Nat.Prime`, Euclid's lemma and "a
  divisor of `p ^ n` other than `1` is divisible by `p`"; §12 uses the last.
  - *A concept `primes` in §8*, four problems, the student's: Milne's definition of a prime,
    `two_le`, coprimality from §1's `Nat.Coprime`, Euclid's lemma, the divisor lemma. The
    student redefines as much as possible, and Naturals plans the same material for `MyNat`.
  - *A library module `PolyaAlgebra/Arithmetic.lean`*, compiled theory the student uses and
    never writes, imported by §8; the prose introduces `Nat.Prime` by its definition before a
    statement uses it. Four problems fewer, and primes stay outside a subject about groups.

  **Recommendation: the concept in §8**, by the owner's rule, with the module as the fallback
  if §8 outgrows its budget. **Taken as recommended, 2026-10-21.**
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

§2, Groups, in a fresh session: "Do the next section in Group Theory, which is §2 Groups".
Read this entry's **Notes from §1**, **The fence**'s results under **Before §1**, `STYLE.md`,
`plans/STUDENT_BACKGROUND.md` and §1 in full before writing; the §1 names a later section
leans on are `injective_of_left_inverse`, `equiv_bijective`, `bijective_of_injective`,
`card_of_equiv_prod`, `mod_add_mod_eq_add_mod`, `mod_mod_of_pos`, `find_spec_and_min`,
`ker_equivalence`, `modSetoid`, `toFin`, `residue`, `card_quotient_le`, and `rot3`. After §2,
run the student review with `scripts/review/` as §1 did, and add §2's links to `links.yaml`
(`programming/instances → grouptheory/group_axioms`). Decisions 3–5 are taken; the owner may
still overrule any of them before the section that depends on it (§6, §2, §8).

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
