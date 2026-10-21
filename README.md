# Polya Algebra

A Polya content repository for algebra. Its subjects are built by the student from the axioms:
a group is a set with an operation that passes three tests, and the student writes that
definition, meets the handful of groups every course lives on, and builds what a first course
builds on them, under the names Mathlib uses. Today it holds the first three sections of its first
subject, Group Theory, and an Extra Credit section after the goal; `plans/GROUP_THEORY_PLAN.md` says what the rest is to be, and
`plans/STUDENT_BACKGROUND.md` what its student knows on arrival.

## Group Theory

One row per section of the plan, with where it stands.

| § | Section | What is in it | Status |
|---|---|---|---|
| 1 | Prerequisites | Mathlib's sets and a set as a type; injective, surjective and bijective functions; equivalences and permutations; finite types, `Fintype.card`, `decide` over a finite type and counting by labelling; the integers, remainders, `Nat.find` and coprime numbers; equivalence relations as setoids; quotients, with the classes modulo `n` as the remainders. 24 problems over 7 concepts, reviewed once by a student agent per concept. | built, 2026-10-21 |
| 2 | Groups | the student's `Group` class with its own symbols `∗`, `𝟙` and `⁻¹`; `Unit`, `Bool` under `xor` and `ℤ` under addition as instances; the consequences of the axioms (adjacent cancellation, uniqueness of the neutral element and of inverses, `inv_inv`, `mul_inv_rev`, self-inverse groups are commutative); cancellation, solving `a ∗ x = b`, left multiplication as a bijection; the one-sided axioms as extra credit, with `ℤ` built from three laws. 17 problems over 4 concepts, reviewed once by a student agent per concept. | built, 2026-10-21 |
| 3 | Examples | the student's `ZMod n`, a structure holding a remainder and its bound, with addition and reduction as the operation, counted by labelling with `Fin n`, and `ZMod 2` matched with `Bool`; the symmetric groups as an instance on `Equiv.Perm`, with a rotation and a reflection of three points that fail to commute; `CommGroup` extending `Group`, with `ℤ` and `ZMod n` as instances and two rearrangement rules; the product `G × H`; the dihedral groups as an inductive over `ZMod n` with a four-line table, its associativity from the commutativity of `ZMod n`, its order `2n`, and the Klein four-group as `D₂`. 19 problems over 5 concepts, reviewed once by a student agent per concept. | built, 2026-10-21 |
| 4 | Powers and the Order of an Element | natural and integer powers, their laws; `orderOf`; orders in finite groups | planned |
| 5 | Subgroups | the subgroup criterion; the centre; intersections; generated and cyclic subgroups | planned |
| 6 | Homomorphisms | homomorphisms and isomorphisms; kernels and images; Cayley's theorem | planned |
| 7 | Cosets and Lagrange's Theorem | cosets; the coset relation; the coset space `G ⧸ H` and the index; Lagrange's theorem | planned |
| 8 | Cyclic Groups and Groups of Prime Order | cyclic subgroups; primes; groups of prime order; the index formula | planned |
| 9 | Normal Subgroups and Quotient Groups | normal subgroups; the quotient group; its universal property; products of subgroups | planned |
| 10 | The Isomorphism Theorems | the first, second and correspondence theorems; direct products | planned |
| 11 | Group Actions | actions; orbits; stabilizers; conjugation | planned |
| 12 | Counting with Actions | orbit–stabilizer; counting by blocks; the class equation; groups of order `p²` are commutative, the goal | planned |
| — | Extra Credit | after the goal, what nothing builds on: the one-sided axioms (Milne's Aside 1.10), with `Group.ofLeftAxioms` and `ℤ` from three laws; a section of its own so that it stays after the goal as the goal moves | built, 2026-10-21 |

The outline follows J. S. Milne's *Group Theory* notes
(https://www.jmilne.org/math/CourseNotes/GT.pdf), which supply the selection and order of the
results and are gratefully acknowledged; the prose, the Lean and the problems are written here.
Subjects carry CC BY 4.0; the text is the `LICENSE` file in each subject's directory.

## Working on it

```bash
lake exe polya build grouptheory      # does the Lean compile?
lake exe polya extract grouptheory    # every problem checked against its own spec; writes .lake/polya/bundles/
lake exe polya publish grouptheory    # to the instance named in .env
python3 scripts/fence_probe.py        # the fence test, before any import changes
```

Read `STYLE.md` before writing content, and the `polya-author` skill for the house conventions
(`polya/skills/polya-author` in `polya-publisher`). `scripts/` holds the checks that run over a
bundle; `STYLE.md` lists them.
