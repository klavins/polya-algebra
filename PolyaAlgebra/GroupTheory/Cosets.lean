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
import PolyaAlgebra.GroupTheory.Homomorphisms

/-! @section Cosets and Lagrange's Theorem -/

universe u v w

namespace GroupTheory

set_option linter.translateGenerateName false

/-!
@concept cosets
@title Cosets
@kind definition

A left coset of a subgroup is the set of products of one fixed element with the elements of the subgroup. Two left cosets are either equal or disjoint, so the cosets cut the group into pieces, and each element lies in exactly one of them. Counting those pieces is how the subject learns what sizes a subgroup can have.
-/

/-!
@problem left_coset
@title The Left Cosets of a Subgroup
@concept cosets

@preamble
The *left coset* of `H` by `a` is the set of products of `a` with the elements of `H`:
```lean
{x | ∃ h ∈ H, a * h = x}
```
Textbooks write it `aH`.

We write `leftCoset a H`, a set of elements of `G`; Mathlib writes it `a • (H : Set G)`. Its additive version `leftAddCoset a H` is the set `a + H` of sums. A membership `x ∈ leftCoset a H` is, by definition, the statement that some `h ∈ H` has `a * h = x`.
@description
Define `leftCoset a H` as the set above, keeping the `@[to_additive]` line, and show that `a ∈ leftCoset a H`, under the name `mem_own_leftCoset`.
-/

@[to_additive leftAddCoset]
def leftCoset {G : Type u} [Group G] (a : G) (H : Subgroup G) : Set G :=
  {x | ∃ h ∈ H, a * h = x}

/-- @spec -/
example {G : Type u} [Group G] (a x : G) (H : Subgroup G) :
    x ∈ leftCoset a H ↔ ∃ h, h ∈ H ∧ a * h = x := by
  constructor
  · intro hx
    obtain ⟨h, hh, e⟩ := hx
    exact ⟨h, hh, by grind⟩
  · intro ⟨h, hh, e⟩
    exact ⟨h, hh, by grind⟩

@[to_additive mem_own_leftAddCoset]
theorem mem_own_leftCoset {G : Type u} [Group G] (a : G) (H : Subgroup G) : a ∈ leftCoset a H :=
  ⟨1, H.one_mem, mul_one a⟩

/-! @end -/

/-!
@problem right_coset
@title Right Cosets and Their Membership Test
@concept cosets

@preamble
A test for membership in a coset avoids the existence statement: `x` lies in `aH` exactly when `a⁻¹ * x` lies in `H`. If `x = a * h`, then `a⁻¹ * x` is `h`; conversely, `x` is `a` times `a⁻¹ * x`. The starting code proves it, as `mem_leftCoset_iff`, for the problems after this one.

The *right coset* `Ha` is the set of products `h * a`, and its test multiplies by `a⁻¹` on the right.
@description
Define `rightCoset H a`, the set of products `h * a` with `h ∈ H`, keeping the `@[to_additive]` line. Show that `x ∈ rightCoset H a` exactly when `x * a⁻¹ ∈ H`, under the name `mem_rightCoset_iff`. The context holds the right cancellations of the second section, `mul_inv_cancel_right` and `inv_mul_cancel_right`.
-/

/-- @given -/
@[to_additive mem_leftAddCoset_iff]
theorem mem_leftCoset_iff {G : Type u} [Group G] {a x : G} {H : Subgroup G} :
    x ∈ leftCoset a H ↔ a⁻¹ * x ∈ H := by
  constructor
  · intro ⟨h, hh, e⟩
    have e' : a⁻¹ * x = h := by
      calc a⁻¹ * x = a⁻¹ * (a * h) := by rw [e]
        _ = h := by rw [inv_mul_cancel_left]
    rw [e']
    exact hh
  · intro hx
    exact ⟨a⁻¹ * x, hx, mul_inv_cancel_left a x⟩

@[to_additive rightAddCoset]
def rightCoset {G : Type u} [Group G] (H : Subgroup G) (a : G) : Set G :=
  {x | ∃ h ∈ H, h * a = x}

/-- @spec -/
example {G : Type u} [Group G] (a x : G) (H : Subgroup G) :
    x ∈ rightCoset H a ↔ ∃ h, h ∈ H ∧ h * a = x := by
  constructor
  · intro hx
    obtain ⟨h, hh, e⟩ := hx
    exact ⟨h, hh, by grind⟩
  · intro ⟨h, hh, e⟩
    exact ⟨h, hh, by grind⟩

@[to_additive mem_rightAddCoset_iff]
theorem mem_rightCoset_iff {G : Type u} [Group G] {a x : G} {H : Subgroup G} :
    x ∈ rightCoset H a ↔ x * a⁻¹ ∈ H := by
  constructor
  · intro ⟨h, hh, e⟩
    rw [← e, mul_inv_cancel_right]
    exact hh
  · intro hx
    exact ⟨x * a⁻¹, hx, inv_mul_cancel_right x a⟩

/-! @end -/

/--
@problem left_coset_eq_iff
@title When Two Left Cosets Are Equal
@concept cosets

@preamble
A coset has many names: `aH = bH` exactly when `a⁻¹ * b ∈ H`. One direction rests on the identity
```lean
b⁻¹ * x = (a⁻¹ * b)⁻¹ * (a⁻¹ * x)
```
and the other on an identity of the same kind. The context holds `mem_leftCoset_iff` and `mem_own_leftCoset` of this section, `Subgroup.mul_mem` and `Subgroup.inv_mem` of the section on subgroups, and the laws of the second section.
@description
Show that the left cosets of `H` by `a` and by `b` are equal exactly when `a⁻¹ * b ∈ H`, under the name `leftCoset_eq_iff`.
-/
@[to_additive leftAddCoset_eq_iff]
theorem leftCoset_eq_iff {G : Type u} [Group G] {a b : G} {H : Subgroup G} :
    leftCoset a H = leftCoset b H ↔ a⁻¹ * b ∈ H := by
  constructor
  · intro h
    rw [← mem_leftCoset_iff, h]
    exact mem_own_leftCoset b H
  · intro h
    apply Set.ext
    intro x
    rw [mem_leftCoset_iff, mem_leftCoset_iff]
    constructor
    · intro hx
      have e : b⁻¹ * x = (a⁻¹ * b)⁻¹ * (a⁻¹ * x) := by
        rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
      rw [e]
      exact H.mul_mem (H.inv_mem h) hx
    · intro hx
      rw [← mul_inv_cancel_left b x, ← mul_assoc]
      exact H.mul_mem h hx

/--
@problem left_coset_eq_of_mem
@title Two Left Cosets Are Disjoint or Equal
@concept cosets

@preamble
The context holds `leftCoset_eq_iff` and `mem_leftCoset_iff`, and the laws of the previous problem.
@description
Show that two left cosets of `H` with a common element `x` are equal, under the name `leftCoset_eq_of_mem`.
-/
@[to_additive leftAddCoset_eq_of_mem]
theorem leftCoset_eq_of_mem {G : Type u} [Group G] {a b x : G} {H : Subgroup G}
    (ha : x ∈ leftCoset a H) (hb : x ∈ leftCoset b H) : leftCoset a H = leftCoset b H := by
  rw [mem_leftCoset_iff] at ha hb
  rw [leftCoset_eq_iff]
  have e : a⁻¹ * b = (a⁻¹ * x) * (b⁻¹ * x)⁻¹ := by
    rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
  rw [e]
  exact H.mul_mem ha (H.inv_mem hb)

/-!
@problem int_cosets
@title The Cosets of the Even Integers
@concept cosets

@preamble
The subgroup `2ℤ` of the integers has two cosets: the even integers and the odd ones. Written additively, the coset of `a` is `a + 2ℤ`; in Lean it is `leftAddCoset a H` with `H` the subgroup `intMultiples 2`. The test of the second problem reads:
```lean
theorem mem_leftAddCoset_iff : x ∈ leftAddCoset a H ↔ -a + x ∈ H
```
A membership in `{x | x % 2 = 1}` is, by definition, the property `x % 2 = 1`, and `change` restates a goal as that property. On `ℤ`, `%` is `Int.emod`, whose remainder is never negative when the divisor is not `0`: `x % 2` is `0` or `1`, and `-3 % 2 = 1`. `omega` knows it. The context holds `mem_leftAddCoset_iff`, `leftAddCoset_eq_iff` and `mem_intMultiples`.
@description
Show that the coset `1 + 2ℤ` is the set of integers with remainder `1` on division by `2`, and that `3 + 2ℤ = 1 + 2ℤ`.
-/
theorem leftAddCoset_one_two : leftAddCoset 1 (intMultiples 2) = {x | x % 2 = 1} := by
  apply Set.ext
  intro x
  rw [mem_leftAddCoset_iff, mem_intMultiples]
  change _ ↔ x % 2 = 1
  omega

theorem leftAddCoset_three_eq_one : leftAddCoset 3 (intMultiples 2) = leftAddCoset 1 (intMultiples 2) := by
  rw [leftAddCoset_eq_iff, mem_intMultiples]
  decide

/-! @end -/

/-!
@problem left_ne_right_coset
@title Left and Right Cosets Differ
@concept cosets

@preamble
In a commutative group `aH = Ha`, but not in general. In D₃ the identity `r 0` and the reflection `sr 0` form a subgroup, `d3FixZero`, with carrier `{r 0, sr 0}`. The previous section's `toPerm3` sends `sr 0` to the reflection through the vertex `0`, hence the name. The starting code checks its closure conditions by `decide`. `mem_d3FixZero` says that `x ∈ d3FixZero` exactly when `x = r 0 ∨ x = sr 0`.

Its left and right cosets by the rotation `r 1` both contain `r 1`, but they are not the same set. `decide` cannot test membership in a coset directly. A statement in which nothing else names D₃, such as `r 1 * sr 0 = sr 2`, needs the type written: `(r 1 : DihedralGroup 3)`.
@description
Show that the left and right cosets of `d3FixZero` by `r 1` are different sets.
-/

open DihedralGroup in
/-- @given -/
def d3FixZero : Subgroup (DihedralGroup 3) where
  carrier := {r 0, sr 0}
  one_mem' := by decide
  mul_mem' := by decide
  inv_mem' := by decide

open DihedralGroup in
/-- @given -/
theorem mem_d3FixZero (x : DihedralGroup 3) : x ∈ d3FixZero ↔ x = r 0 ∨ x = sr 0 := Iff.rfl

open DihedralGroup in
theorem leftCoset_ne_rightCoset : leftCoset (r 1) d3FixZero ≠ rightCoset d3FixZero (r 1) := by
  intro h
  have hx : sr 2 ∈ leftCoset (r 1) d3FixZero := by
    rw [mem_leftCoset_iff, mem_d3FixZero]
    decide
  rw [h, mem_rightCoset_iff, mem_d3FixZero] at hx
  exact absurd hx (by decide)

/-! @end -/

/-!
@concept coset_relation
@title The Coset Relation
@kind definition

Two elements lie in the same left coset of a subgroup exactly when the inverse of the first times the second lies in the subgroup. This is an equivalence relation whose classes are the left cosets, so the quotients of the first section apply to cosets.
-/

/-!
@problem left_rel
@title The Relation of Lying in the Same Coset
@concept coset_relation

@preamble
We make the relation `a⁻¹ * b ∈ H` a setoid, as the congruence `modSetoid n` was in the first section, and call it `QuotientGroup.leftRel H`, Mathlib's name. Its additive version `QuotientAddGroup.leftRel H` relates `a` and `b` when `-a + b ∈ H`. In the proof of `iseqv`, a goal stating the relation shows as the membership it is. The context holds `Subgroup.one_mem`, `Subgroup.mul_mem` and `Subgroup.inv_mem` of the section on subgroups, and the laws of the second section.
@description
Define `QuotientGroup.leftRel H`, the setoid on `G` whose relation holds of `a` and `b` when `a⁻¹ * b ∈ H`, keeping the `@[to_additive]` line.
-/

@[to_additive QuotientAddGroup.leftRel]
def QuotientGroup.leftRel {G : Type u} [Group G] (H : Subgroup G) : Setoid G where
  r a b := a⁻¹ * b ∈ H
  iseqv := by
    constructor
    · intro a
      rw [inv_mul_cancel]
      exact H.one_mem
    · intro a b h
      rw [← inv_inv a, ← mul_inv_rev]
      exact H.inv_mem h
    · intro a b c hab hbc
      rw [← mul_inv_cancel_left b c, ← mul_assoc]
      exact H.mul_mem hab hbc

/-- @spec -/
example {G : Type u} [Group G] (H : Subgroup G) (a b : G) :
    (QuotientGroup.leftRel H) a b ↔ a⁻¹ * b ∈ H := Iff.rfl

/-! @end -/

/-!
@problem left_rel_iff
@title The Classes of the Coset Relation Are the Cosets
@concept coset_relation

@preamble
The context holds `leftCoset_eq_iff` and `mem_leftCoset_iff`.
@description
Show that `a` and `b` are related by `QuotientGroup.leftRel H` exactly when their left cosets are equal, under the name `QuotientGroup.leftRel_iff_leftCoset_eq`. Then show that the set of elements related to `a` is the coset `aH`, under the name `QuotientGroup.setOf_leftRel_eq_leftCoset`.
-/
@[to_additive QuotientAddGroup.leftRel_iff_leftAddCoset_eq]
theorem QuotientGroup.leftRel_iff_leftCoset_eq {G : Type u} [Group G] {H : Subgroup G} {a b : G} :
    (QuotientGroup.leftRel H) a b ↔ leftCoset a H = leftCoset b H := by
  rw [leftCoset_eq_iff]
  exact Iff.rfl

@[to_additive QuotientAddGroup.setOf_leftRel_eq_leftAddCoset]
theorem QuotientGroup.setOf_leftRel_eq_leftCoset {G : Type u} [Group G] {H : Subgroup G} (a : G) :
    {b | (QuotientGroup.leftRel H) a b} = leftCoset a H := by
  apply Set.ext
  intro b
  rw [mem_leftCoset_iff]
  exact Iff.rfl

/-! @end -/

/--
@problem int_left_rel
@title Integers in the Same Coset of nℤ
@concept coset_relation

@preamble
Two integers lie in the same coset of `nℤ` exactly when they leave the same remainder on division by `n`, as the even and the odd integers did for `n = 2`. The coset relation of the additive subgroup `intMultiples n` holds of `a` and `b` when `n ∣ -a + b`, by definition, and `change` restates it so. The remainder `Int.emod` of the integers' cosets is never negative when `n ≠ 0`, and `a % 0` is `a`. Core Lean relates divisibility to it:
```lean
theorem Int.dvd_iff_emod_eq_zero {a b : ℤ} :
    a ∣ b ↔ b % a = 0
theorem Int.emod_eq_emod_iff_emod_sub_eq_zero
    {m n k : ℤ} : m % n = k % n ↔ (m - k) % n = 0
```
`omega` proves linear equations between integers, but not the statement itself, whose remainders are by a variable `n`. The second lemma, read from right to left, leaves the two remainders in the order `b % n = a % n`. The context does not hold `mem_intMultiples`.
@description
Show that two integers are related by the coset relation of `intMultiples n` exactly when they leave the same remainder on division by `n`, for every integer `n`.
-/
theorem int_leftRel_iff {n a b : ℤ} :
    (QuotientAddGroup.leftRel (intMultiples n)) a b ↔ a % n = b % n := by
  change n ∣ -a + b ↔ _
  have e : -a + b = b - a := by omega
  rw [e, Int.dvd_iff_emod_eq_zero, ← Int.emod_eq_emod_iff_emod_sub_eq_zero]
  exact eq_comm

/-!
@concept coset_space
@title The Coset Space and the Index
@kind definition

The left cosets of a subgroup, taken as the elements of a new type, form the coset space, the quotient of the group by the coset relation. The number of cosets is the index of the subgroup, and counting the group through its cosets is how Lagrange's theorem is proved.
-/

/-!
@problem quotient_group
@title The Coset Space G ⧸ H
@concept coset_space

@preamble
The left cosets of `H` are the classes of the coset relation, and the first section collected the classes of a setoid into a new type, its quotient. We write the quotient of `G` by the coset relation of `H` as `G ⧸ H` (typed `\quot`), read "`G` modulo `H`". The symbol comes from Mathlib's class `HasQuotient`:
```lean
class HasQuotient (A : outParam (Type u)) (B : Type v) where
  Quotient : B → Type (max u v)
```
`outParam` lets Lean find `G` from `H`. The instance for subgroups sends each `H` to the type of its cosets. The class of `a` is the coset `aH` as one element of `G ⧸ H`; we write it `QuotientGroup.mk a`. For an additive subgroup the quotient is written `A ⧸ H` too, through the additive instance, and the class of `a` is `QuotientAddGroup.mk a`.
@description
Supply the instance `QuotientGroup.instHasQuotient`, which sends a subgroup `H` to the quotient of `G` by its coset relation, and define `QuotientGroup.mk a`, the class of `a` in `G ⧸ H`, keeping the `@[to_additive]` lines.
-/

@[to_additive QuotientAddGroup.instHasQuotient]
instance QuotientGroup.instHasQuotient {G : Type u} [Group G] : HasQuotient G (Subgroup G) :=
  ⟨fun H => Quotient (QuotientGroup.leftRel H)⟩

@[to_additive QuotientAddGroup.mk]
def QuotientGroup.mk {G : Type u} [Group G] {H : Subgroup G} (a : G) : G ⧸ H :=
  Quotient.mk (QuotientGroup.leftRel H) a

/-- @spec -/
example {G : Type u} [Group G] (H : Subgroup G) (a : G) :
    (QuotientGroup.mk a : G ⧸ H) = Quotient.mk (QuotientGroup.leftRel H) a := rfl

/-! @end -/

/-!
@problem quotient_group_eq
@title Equal Cosets in the Coset Space
@concept coset_space

@preamble
Two elements of `G ⧸ H` are equal exactly when their representatives are related: the classes of `a` and `b` are equal exactly when `a⁻¹ * b ∈ H`. And every element of `G ⧸ H` is the coset of some element of `G`. Both are laws of a quotient from the first section, since `QuotientGroup.mk a` is a class of the coset relation: `Quotient.sound`, `Quotient.exact` and `quotient_mk_surjective`.

The coset of `a` is the coset of `1`, which is `H` itself, exactly when `a ∈ H`. The context holds `Subgroup.inv_mem` of the section on subgroups and the laws of the second section.
@description
Show that the classes of `a` and `b` in `G ⧸ H` are equal exactly when `a⁻¹ * b ∈ H`, under the name `QuotientGroup.eq`, and that every element of `G ⧸ H` is the class of an element of `G`, under the name `QuotientGroup.mk_surjective`. Then show that the class of `a` is the class of `1` exactly when `a ∈ H`, under the name `QuotientGroup.mk_eq_mk_one_iff`.
-/
@[to_additive QuotientAddGroup.eq]
theorem QuotientGroup.eq {G : Type u} [Group G] {H : Subgroup G} {a b : G} :
    (QuotientGroup.mk a : G ⧸ H) = QuotientGroup.mk b ↔ a⁻¹ * b ∈ H := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

@[to_additive QuotientAddGroup.mk_surjective]
theorem QuotientGroup.mk_surjective {G : Type u} [Group G] {H : Subgroup G} :
    Function.Surjective (QuotientGroup.mk : G → G ⧸ H) :=
  quotient_mk_surjective (QuotientGroup.leftRel H)

@[to_additive QuotientAddGroup.mk_eq_mk_zero_iff]
theorem QuotientGroup.mk_eq_mk_one_iff {G : Type u} [Group G] {H : Subgroup G} {a : G} :
    (QuotientGroup.mk a : G ⧸ H) = QuotientGroup.mk 1 ↔ a ∈ H := by
  rw [QuotientGroup.eq, mul_one]
  constructor
  · intro h
    rw [← inv_inv a]
    exact H.inv_mem h
  · intro h
    exact H.inv_mem h

/-! @end -/

/-!
@problem index
@title The Index of a Subgroup
@concept coset_space

@preamble
The number of left cosets of `H` is its *index*. When `G` is finite, so is `G ⧸ H`, by Mathlib's instance `Quotient.fintype`, met in the first section, under `open Classical`. Instance search does not see the quotient behind `G ⧸ H`, so `G ⧸ H` needs an instance of its own, `QuotientGroup.fintype H`.

We define `H.index`, for `Subgroup.index H`, as the number of elements of `G ⧸ H`, for a finite group only; Mathlib's index counts with `Nat.card` and is defined for every group.
@description
Supply the instance `QuotientGroup.fintype H`, which makes `G ⧸ H` finite when `G` is finite, and define `Subgroup.index H`, the number of elements of `G ⧸ H`. Keep the `open Classical in` and `@[to_additive]` lines.
-/

open Classical in
@[to_additive QuotientAddGroup.fintype]
noncomputable instance QuotientGroup.fintype {G : Type u} [Group G] [Fintype G] (H : Subgroup G) :
    Fintype (G ⧸ H) :=
  Quotient.fintype (QuotientGroup.leftRel H)

open Classical in
@[to_additive AddSubgroup.index]
noncomputable def Subgroup.index {G : Type u} [Group G] [Fintype G] (H : Subgroup G) : ℕ :=
  Fintype.card (G ⧸ H)

/-- @spec -/
example {G : Type u} [Group G] [Fintype G] (H : Subgroup G) :
    H.index = Fintype.card (G ⧸ H) :=
  Fintype.card_congr (Equiv.refl _)

/-! @end -/

/-!
@problem index_bot
@title The Index of the Trivial Subgroup
@concept coset_space

@preamble
The trivial subgroup has one coset for each element of `G`, each coset a single element, so its index is the number of elements of `G`. Mathlib counts a type through a bijection:
```lean
theorem Fintype.card_of_bijective {f : α → β}
    (hf : Function.Bijective f) :
    Fintype.card α = Fintype.card β
```
The context holds `QuotientGroup.eq` and `QuotientGroup.mk_surjective` of this section, `Subgroup.mem_bot` of the section on subgroups, and the laws of the second section.
@description
Show that the index of the trivial subgroup is the order of `G`, under the name `Subgroup.index_bot`.
-/
open Classical in
@[to_additive AddSubgroup.index_bot]
theorem Subgroup.index_bot {G : Type u} [Group G] [Fintype G] :
    (⊥ : Subgroup G).index = Fintype.card G := by
  unfold Subgroup.index
  apply Eq.symm
  apply Fintype.card_of_bijective
  constructor
  · intro a b h
    rw [QuotientGroup.eq, Subgroup.mem_bot] at h
    rw [← mul_inv_cancel_left a b, h, mul_one]
  · exact QuotientGroup.mk_surjective

/-! @end -/

/-!
@concept lagrange
@title Lagrange's Theorem
@kind theorem

In a finite group, the number of elements is the index of a subgroup times the number of elements of the subgroup. So the order of a subgroup divides the order of the group, which rules out subgroups of most sizes before any is looked for.
-/

/-!
@problem left_coset_equiv
@title A Coset Has as Many Elements as the Subgroup
@concept lagrange

@preamble
Every left coset of `H` has as many elements as `H`: the function `h ↦ a * h` matches `H` with `aH`. So the cosets cut `G` into pieces of equal size, which is the heart of Lagrange's theorem.

As an equivalence, the coset is the type of its members, a set used as a type as in the first section, whose elements are the pairs `⟨x, hx⟩`. Mathlib's name for the equivalence is `leftCosetEquivSubgroup`. The context holds `mem_leftCoset_iff` of this section, `Subtype.ext`, and the laws of the second section.
@description
Define `leftCosetEquivSubgroup a H`, the equivalence that sends a member `x` of the coset `aH`, as a type, to `a⁻¹ * x` in `H.carrier`, keeping the `@[to_additive]` line.
-/

@[to_additive leftAddCosetEquivAddSubgroup]
def leftCosetEquivSubgroup {G : Type u} [Group G] (a : G) (H : Subgroup G) :
    leftCoset a H ≃ H.carrier where
  toFun x := ⟨a⁻¹ * x, mem_leftCoset_iff.mp x.2⟩
  invFun h := ⟨a * h, h, h.2, rfl⟩
  left_inv x := Subtype.ext (mul_inv_cancel_left a x)
  right_inv h := Subtype.ext (inv_mul_cancel_left a h)

/-- @spec -/
example {G : Type u} [Group G] (a : G) (H : Subgroup G) (x : leftCoset a H) (h : H.carrier) :
    ((leftCosetEquivSubgroup a H x : H.carrier) : G) = a⁻¹ * x ∧
    (((leftCosetEquivSubgroup a H).symm h : leftCoset a H) : G) = a * h :=
  ⟨rfl, rfl⟩

/-! @end -/

/--
@problem card_eq_mul_of_equiv_prod
@title Counting a Type Labelled by Pairs
@concept lagrange

@preamble
The first section counted a type labelled by pairs of numbers, `Fin m × Fin n`, as `card_of_equiv_prod`. A type labelled by pairs from two finite types is counted the same way, once each finite type is labelled by numbers. Mathlib labels the elements of a finite type `β` by the numbers below its count, and puts two equivalences side by side:
```lean
def Fintype.equivFin (β : Type u) [Fintype β] :
    β ≃ Fin (Fintype.card β)
def Equiv.prodCongr (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    α₁ × β₁ ≃ α₂ × β₂
```
Equivalences compose by `e.trans e'`, as in the first section. The context holds `card_of_equiv_prod`.
@description
Let `α`, `β` and `γ` be finite types and `e : α ≃ β × γ`. Show that the number of elements of `α` is the product of the numbers of elements of `β` and `γ`.
-/
theorem card_eq_mul_of_equiv_prod {α : Type u} {β : Type v} {γ : Type w} [Fintype α] [Fintype β]
    [Fintype γ] (e : α ≃ β × γ) : Fintype.card α = Fintype.card β * Fintype.card γ :=
  card_of_equiv_prod (e.trans (Equiv.prodCongr (Fintype.equivFin β) (Fintype.equivFin γ)))

/-!
@problem quotient_out
@title A Representative of Each Coset
@concept lagrange

@preamble
Lagrange's theorem labels each element of `G` by its coset and by its place inside the coset, and a place needs a starting point in each coset. Mathlib picks a representative of every class of a quotient, `Quotient.out q`, an element whose class is `q`:
```lean
theorem Quotient.out_eq (q : Quotient s) : ⟦q.out⟧ = q
```
For a coset `q = gH`, the representative `Quotient.out q` and `g` lie in the same coset, so they are related; and multiplying the representative by an element of `H` stays in `q`. The context holds `QuotientGroup.eq` of this section and the laws of the second section.
@description
Show that the class of the representative of `q` is `q`, under the name `QuotientGroup.out_eq'`; that `g` is related to the representative of its own class, under the name `QuotientGroup.inv_out_mul_mem`; and that the representative of `q` times an element of `H` lies in `q`, under the name `QuotientGroup.mk_out_mul`.
-/
@[to_additive QuotientAddGroup.out_eq']
theorem QuotientGroup.out_eq' {G : Type u} [Group G] {H : Subgroup G} (q : G ⧸ H) :
    QuotientGroup.mk (Quotient.out q) = q :=
  Quotient.out_eq q

@[to_additive QuotientAddGroup.neg_out_add_mem]
theorem QuotientGroup.inv_out_mul_mem {G : Type u} [Group G] {H : Subgroup G} (g : G) :
    (Quotient.out (QuotientGroup.mk g : G ⧸ H))⁻¹ * g ∈ H := by
  rw [← QuotientGroup.eq]
  exact QuotientGroup.out_eq' _

@[to_additive QuotientAddGroup.mk_out_add]
theorem QuotientGroup.mk_out_mul {G : Type u} [Group G] {H : Subgroup G} (q : G ⧸ H) {h : G}
    (hh : h ∈ H) : QuotientGroup.mk (Quotient.out q * h) = q := by
  have e : (QuotientGroup.mk (Quotient.out q) : G ⧸ H) = QuotientGroup.mk (Quotient.out q * h) := by
    rw [QuotientGroup.eq, inv_mul_cancel_left]
    exact hh
  rw [← e, QuotientGroup.out_eq']

/-! @end -/

/-!
@problem group_equiv_quotient_prod
@title A Group as Cosets Times a Subgroup
@concept lagrange

@preamble
Each element `g` is labelled by a pair: its coset `q = gH`, and its place in the coset, the element `(Quotient.out q)⁻¹ * g` of `H`. The pair `(q, h)` labels the element `Quotient.out q * h`. These are inverse to each other, so
```lean
G ≃ (G ⧸ H) × H.carrier
```
Mathlib's name for it is `Subgroup.groupEquivQuotientProdSubgroup`. `Quotient.out` chooses from every class at once, which is the axiom of choice, so the definition is `noncomputable`.

Two pairs are equal when their components are, `Prod.ext`, and two elements of `H.carrier` when their values are, `Subtype.ext` of the section on subgroups. The second component of the pair the definition builds is, by definition, the place of `g` in its coset, and `change` writes that value out before a rewrite. The context holds `QuotientGroup.inv_out_mul_mem` and `QuotientGroup.mk_out_mul` of the previous problem and the laws of the second section.
@description
Define `Subgroup.groupEquivQuotientProdSubgroup H`, sending `g` to the pair above, keeping the `@[to_additive]` line.
-/

@[to_additive AddSubgroup.addGroupEquivQuotientProdAddSubgroup]
noncomputable def Subgroup.groupEquivQuotientProdSubgroup {G : Type u} [Group G] (H : Subgroup G) :
    G ≃ (G ⧸ H) × H.carrier where
  toFun g := (QuotientGroup.mk g, ⟨_, QuotientGroup.inv_out_mul_mem g⟩)
  invFun p := Quotient.out p.1 * p.2
  left_inv g := mul_inv_cancel_left _ g
  right_inv := by
    intro ⟨q, h⟩
    have hq : (QuotientGroup.mk (Quotient.out q * h) : G ⧸ H) = q := QuotientGroup.mk_out_mul q h.2
    apply Prod.ext
    · exact hq
    · apply Subtype.ext
      change (Quotient.out (QuotientGroup.mk (Quotient.out q * h) : G ⧸ H))⁻¹ *
        (Quotient.out q * h) = h
      rw [hq, inv_mul_cancel_left]

/-- @spec -/
example {G : Type u} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) (h : H.carrier) :
    (H.groupEquivQuotientProdSubgroup g).1 = QuotientGroup.mk g ∧
    ((H.groupEquivQuotientProdSubgroup g).2 : G) = (Quotient.out (QuotientGroup.mk g : G ⧸ H))⁻¹ * g ∧
    H.groupEquivQuotientProdSubgroup.symm (q, h) = Quotient.out q * h :=
  ⟨rfl, rfl, rfl⟩

/-! @end -/

/-!
@problem lagrange
@title Lagrange's Theorem
@concept lagrange

@preamble
The labelling of the previous problem counts `G` as pairs of a coset and an element of `H`. The index is the number of elements of `G ⧸ H` by definition. Mathlib states the theorem with `Nat.card`, a count for every type, finite or not. Core Lean has
```lean
theorem Nat.dvd_mul_left (a b : ℕ) : a ∣ b * a
```
The context holds `card_eq_mul_of_equiv_prod` and `Subgroup.groupEquivQuotientProdSubgroup`.
@description
Show that the order of `G` is the index of `H` times the order of `H`, under the name `Subgroup.index_mul_card`, and that the order of `H` divides the order of `G`, under the name `Subgroup.card_subgroup_dvd_card`.
-/
open Classical in
@[to_additive AddSubgroup.index_mul_card]
theorem Subgroup.index_mul_card {G : Type u} [Group G] [Fintype G] (H : Subgroup G) :
    H.index * Fintype.card H.carrier = Fintype.card G := by
  rw [card_eq_mul_of_equiv_prod H.groupEquivQuotientProdSubgroup]
  rfl

open Classical in
@[to_additive AddSubgroup.card_addSubgroup_dvd_card]
theorem Subgroup.card_subgroup_dvd_card {G : Type u} [Group G] [Fintype G] (H : Subgroup G) :
    Fintype.card H.carrier ∣ Fintype.card G := by
  rw [← H.index_mul_card]
  exact Nat.dvd_mul_left _ _

/-! @end -/

/-!
@problem index_rotations
@title The Rotations Have Index Two
@concept lagrange

@preamble
The rotations of the `n`-gon are `n` of the `2n` symmetries of Dₙ, so by Lagrange's theorem they have index `2`: their two cosets are the rotations and the reflections. The rotations are counted through `i ↦ r i`, a bijection from `ZMod n` onto them. A member of the rotations is, by definition, a member of `Set.range r`. Two constructors `r i` and `r j` are equal only when `i = j`, and `cases` on the equation finds it. Then `n` is cancelled from both sides of an equation:
```lean
theorem Nat.eq_of_mul_eq_mul_right {n m k : ℕ}
    (hm : 0 < m) (h : n * m = k * m) : n = k
```
Its hypothesis `hm`, here `0 < n`, comes from `[NeZero n]` through `Nat.pos_of_neZero n`, met in the first section. The context holds `card_zmod` and `card_dihedral` of the section on examples, `Subgroup.index_mul_card` of this section, and Mathlib's `Fintype.card_of_bijective`.
@description
Show that the rotations of Dₙ have `n` elements, under the name `card_rotations`, and that they have index `2`, under the name `index_rotations`.
-/
open Classical in
theorem card_rotations (n : ℕ) [NeZero n] :
    Fintype.card (DihedralGroup.rotations n).carrier = n := by
  have hf : Function.Bijective
      (fun i : ZMod n => (⟨DihedralGroup.r i, i, rfl⟩ : (DihedralGroup.rotations n).carrier)) := by
    constructor
    · intro i j h
      have h' : DihedralGroup.r i = DihedralGroup.r j := congrArg Subtype.val h
      cases h'
      rfl
    · intro ⟨x, i, hi⟩
      exact ⟨i, Subtype.ext hi⟩
  rw [← Fintype.card_of_bijective hf, card_zmod]

open Classical in
theorem index_rotations (n : ℕ) [NeZero n] : (DihedralGroup.rotations n).index = 2 := by
  have h := (DihedralGroup.rotations n).index_mul_card
  rw [card_rotations, card_dihedral] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_neZero n) h

/-! @end -/

/-!
@problem lagrange_examples
@title Subgroups of the Groups of Order Six
@concept lagrange

@preamble
D₃ has six elements, so no subgroup of it has four. `ZMod 6` has six elements too, so its subgroups have `1`, `2`, `3` or `6` elements.

A divisor of a positive number is at most that number, and `decide` checks a statement about every natural number below a fixed bound:
```lean
theorem Nat.le_of_dvd {m n : ℕ} (h1 : 0 < n) :
    m ∣ n → m ≤ n
```
The context holds `card_dihedral` and `card_zmod` of the section on examples, and `Subgroup.card_subgroup_dvd_card` of this section with its additive version `AddSubgroup.card_addSubgroup_dvd_card`.
@description
Show that no subgroup of `DihedralGroup 3` has four elements, and that every additive subgroup of `ZMod 6` has `1`, `2`, `3` or `6` elements.
-/
open Classical in
theorem dihedral_three_card_subgroup_ne_four (H : Subgroup (DihedralGroup 3)) :
    Fintype.card H.carrier ≠ 4 := by
  intro h
  have hd := H.card_subgroup_dvd_card
  rw [h, card_dihedral] at hd
  exact absurd hd (by decide)

open Classical in
theorem zmod_six_card_addSubgroup (H : AddSubgroup (ZMod 6)) :
    Fintype.card H.carrier = 1 ∨ Fintype.card H.carrier = 2 ∨ Fintype.card H.carrier = 3 ∨
      Fintype.card H.carrier = 6 := by
  have hd := H.card_addSubgroup_dvd_card
  rw [card_zmod] at hd
  have hle : Fintype.card H.carrier ≤ 6 := Nat.le_of_dvd (by decide) hd
  have key : ∀ d ≤ 6, d ∣ 6 → d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6 := by
    decide
  exact key _ hle hd

/-! @end -/

end GroupTheory
