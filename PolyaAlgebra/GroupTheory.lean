import PolyaAlgebra.GroupTheory.Prerequisites
import PolyaAlgebra.GroupTheory.Groups
import PolyaAlgebra.GroupTheory.Examples
import PolyaAlgebra.GroupTheory.ExtraCredit

/-! @subject grouptheory
@title Group Theory
@author Eric Klavins
@license CC-BY-4.0
@visibility private
@reference J. S. Milne, Group Theory, v4.01 (November 2025), https://www.jmilne.org/math/CourseNotes/GT.pdf — the outline: the selection and order of the results; the prose, the Lean and the problems are written here
A group is a set with an operation that passes three tests: it is associative, it has a neutral element, and every element has an inverse. The integers under addition are one, and so are the remainders modulo `n`, the permutations of a finite set and the symmetries of a polygon. This subject writes that definition and builds, in order, what a first course builds on it: the examples, powers and the order of an element, subgroups, homomorphisms, cosets and Lagrange's theorem, cyclic groups and groups of prime order, normal subgroups and quotients, the isomorphism theorems, and group actions with the counting they make possible. Its goal is the first structural theorem those tools prove, that every group of order `p²` is commutative.

Everything is the student's: the class `Group` itself, each of the eight groups the subject lives on, and every notion after them, each defined as a problem before anything is proved about it, under the name Mathlib gives it, so that a later subject which imports Mathlib's algebra changes the imports and not the vocabulary. The student arrives from the five subjects of Polya Basic, knowing sets, logic, induction, structures and instances, and nothing of groups.

**Prerequisites** introduces, on mathematics the student already has, the part of Lean and Mathlib the subject is written in, so that no later problem has to teach a Mathlib idea and a hard mathematical idea at once. Mathlib's sets are Set Theory's under their own names, and a set is used as a type; injective, surjective and bijective functions are met as Mathlib spells them; a bijection packaged with its inverse is an equivalence, built field by field, and a permutation is an equivalence of a type with itself; a finite type is one whose elements are listed, counted by `Fintype.card`, with `decide` checking a statement about all of them and a type counted by labelling its elements with pairs; the integers are taken apart by their two constructors, remainders are added, the least number with a property is found, and coprime numbers are met; an equivalence relation is bundled as a setoid; and its classes form a quotient, on which a function is defined by a representative, with the classes modulo `n` shown to be the remainders and a quotient of a finite type counted.

**Groups** writes the definition: a class with the operation, the neutral element and the inverse as its data and the five laws as its fields, under the group's own symbols `a ∗ b`, `𝟙` and `a⁻¹`, so that the one-element set, the Booleans under exclusive or and the integers under addition are instances of one class, each with `∗` meaning its own operation. Then the first consequences of the axioms, under Mathlib's names: the neutral element and inverses are unique, the inverse of a product is the product of the inverses in reverse order, a group whose elements are their own inverses is commutative; and the cancellation laws, with the solution of `a ∗ x = b` and left multiplication as a permutation of the group.

**Examples** builds the groups the subject lives on, each a definition before anything is proved about it. The integers modulo `n` are a structure holding a remainder and its bound, with addition and reduction as the operation, counted by labelling its elements with `Fin n`, and `ZMod 2` matched with the group of order two; the permutations of a type form the symmetric group under composition, and on three points a rotation and a reflection fail to commute; a commutative group is a class extending `Group` by one law, with `ℤ` and `ZMod n` as instances and two rearrangement rules; the product of two groups multiplies componentwise; and the dihedral group of the `n`-gon is an inductive type with a constructor for the rotations and one for the reflections, a four-line table whose associativity is proved from the commutativity of `ZMod n`, a count of `2n` elements, and the Klein four-group as `D₂`.

**Extra Credit**, after the goal, holds what nothing builds on: a left neutral element and left inverses already make a group.
-/
