# Polya Algebra

A Polya content repository for algebra. Its subjects are built by the student from the axioms:
a group is a set with an operation that passes three tests, and the student writes that
definition, meets the handful of groups every course lives on, and builds what a first course
builds on them, under the names Mathlib uses. Today it holds the first five sections of its first
subject, Group Theory, and an Extra Credit section after the goal, in Mathlib's symbols `*`, `1`
and `⁻¹`, with the integers, the integers modulo `n` and the Booleans under exclusive or as additive
groups (`+`, `0`, `-`) and every general theorem copied to them by `@[to_additive]`;
`plans/GROUP_THEORY_PLAN.md` says what the rest is to be, and
`plans/STUDENT_BACKGROUND.md` what its student knows on arrival.

## Group Theory

One row per section of the plan, with where it stands.

| § | Section | What is in it | Status |
|---|---|---|---|
| 1 | Prerequisites | Mathlib's sets and a set as a type; injective, surjective and bijective functions; equivalences and permutations; finite types, `Fintype.card`, `decide` over a finite type and counting by labelling; the integers, remainders, `Nat.find` and coprime numbers; equivalence relations as setoids; quotients, with the classes modulo `n` as the remainders. 24 problems over 7 concepts, reviewed once by a student agent per concept. | built, 2026-10-21 |
| 2 | Groups | the student's `Group` class under Mathlib's symbols `*`, `1` and `⁻¹`, reached through `Mul`, `One` and `Inv` instances the student supplies; `Unit` as an instance; the student's `AddGroup`, its twin, with the integers and `Bool` under `xor` as instances; the mark `@[to_additive]`, which copies every general theorem to additive groups; the consequences of the axioms (adjacent cancellation, uniqueness of the neutral element and of inverses, `inv_inv`, `mul_inv_rev`, self-inverse groups are commutative); cancellation, solving `a * x = b`, left multiplication as a bijection. 17 problems over 4 concepts, reviewed once by a student agent per concept, `group_axioms` again after the first refactor. | built, 2026-10-21; refactored to Mathlib's symbols, 2026-10-22, and to additive groups, 2026-10-23 |
| 3 | Examples | the student's `ZMod n`, a structure holding a remainder and its bound, with `+` and `-` and their six laws, an additive group, counted by labelling with `Fin n`, and `ZMod 2` matched with `Bool`; the symmetric groups as an instance on `Equiv.Perm`, with a rotation and a reflection of three points that fail to commute; `CommGroup` extending `Group` and its twin `AddCommGroup`, with the integers, `ZMod n` and `Bool` as instances, and two rearrangement rules; the product `G × H`, additive when its factors are; the dihedral groups as an inductive over `ZMod n` with Mathlib's four-line table, its associativity from that arithmetic, its order `2n`, and the Klein four-group as `D₂`. 20 problems over 5 concepts, reviewed once by a student agent per concept, the changed concepts again after the first refactor. | built, 2026-10-21; refactored, 2026-10-22 and 2026-10-23 |
| 4 | Powers and the Order of an Element | `g ^ n` by recursion with its `Pow` instance and the twin `n • a` with its `SMul` instance, `pow_zero`, `pow_succ`, `pow_one`, `one_pow`, `pow_succ'`, `pow_add` and `pow_mul` with their copies, and `k • 1 = k` in the integers; integer multiples `k • a` beside integer powers; integer powers by cases on `ℤ`, `zpow_neg`, `zpow_add_one`, `zpow_sub_one`, and `zpow_add` by `Int.induction_on`; `IsOfFinOrder` and `orderOf` through `Nat.find` under `open Classical`, `pow_orderOf_eq_one`, `orderOf_eq_iff`, `pow_mod_orderOf`, `orderOf_dvd_iff_pow_eq_one`, `orderOf_eq_one_iff`, with `addOrderOf 2 = 3` in `ZMod 6`, every reflection of order `2` and `1` of order `0` in the integers; the pigeonhole principle, two powers of an element of a finite group coinciding, every element of finite order, and the inverse as a power. 23 problems over 4 concepts, reviewed once by a student agent per concept. | built, 2026-10-21; refactored, 2026-10-22 and 2026-10-23 |
| 5 | Subgroups | the student's `Subgroup` structure with `carrier`, `one_mem'`, `mul_mem'` and `inv_mem'` and its `Membership` instance, and its twin `AddSubgroup`; the rotations of `Dₙ` as a subgroup, the multiples `nℤ` and `{0, 2, 4}` in `ZMod 6` as additive subgroups; a subgroup as a type, with no more elements than the group, and as a group; `Subgroup.ext`; `⊤`, `⊥` and `≤`; `pow_mem` and `zpow_mem`; the centre, `center G = ⊤` exactly for a commutative group, as for `V₄`, and the centres of `D₃` and `D₄` by `decide`; `H ⊓ K` with `2ℤ ⊓ 3ℤ = 6ℤ`, and `sInf` of a family; `closure` as the intersection of the subgroups containing a set, `zpowers`, `zpowers g = closure {g}`, `IsCyclic` with cyclic groups commutative, `IsAddCyclic ℤ` and `IsAddCyclic (ZMod n)`, and `zmultiples 2 = {0, 2, 4}` in `ZMod 6`. 22 problems over 4 concepts, reviewed once by a student agent per concept. | built, 2026-10-21; refactored, 2026-10-22 and 2026-10-23 |
| 6 | Homomorphisms | homomorphisms and isomorphisms; kernels and images; Cayley's theorem | planned |
| 7 | Cosets and Lagrange's Theorem | cosets; the coset relation; the coset space `G ⧸ H` and the index; Lagrange's theorem | planned |
| 8 | Cyclic Groups and Groups of Prime Order | cyclic subgroups; primes; groups of prime order; the index formula | planned |
| 9 | Normal Subgroups and Quotient Groups | normal subgroups; the quotient group; its universal property; products of subgroups | planned |
| 10 | The Isomorphism Theorems | the first, second and correspondence theorems; direct products | planned |
| 11 | Group Actions | actions; orbits; stabilizers; conjugation | planned |
| 12 | Counting with Actions | orbit–stabilizer; counting by blocks; the class equation; groups of order `p²` are commutative, the goal | planned |
| — | Extra Credit | after the goal, what nothing builds on: the one-sided axioms (Milne's Aside 1.10), with `Group.ofLeftAxioms` and, through its copy, the integers from three laws; the subgroup criterion (Milne 1.11), `Subgroup.ofDiv` from one closure condition; a section of its own so that it stays after the goal as the goal moves | built, 2026-10-21; refactored, 2026-10-22 and 2026-10-23 |

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
