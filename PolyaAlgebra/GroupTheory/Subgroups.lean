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
import PolyaAlgebra.GroupTheory.Powers

/-! @section Subgroups -/

universe u v

namespace GroupTheory

set_option linter.translateGenerateName false

/-!
@concept subgroups
@title Subgroups
@kind definition

A subgroup is a subset of a group that is a group under the same operation: it contains the neutral element, and the product and the inverse of any of its elements. Centres and the subgroup an element generates are the first examples.
-/

/-!
@problem subgroup
@title The Definition of a Subgroup
@concept subgroups

@preamble
A *subgroup* of `G` is a subset that is a group under the operation of `G`: it contains `1`, the product of any two of its elements, and the inverse of each. The laws hold there because they hold in `G`.

We make a subgroup a structure holding a set and the three conditions as fields:
```lean
carrier : Set G
one_mem' : 1 ∈ carrier
mul_mem' : ∀ {a b : G}, a ∈ carrier → b ∈ carrier → a * b ∈ carrier
inv_mem' : ∀ {a : G}, a ∈ carrier → a⁻¹ ∈ carrier
```
The elements are implicit: in `H.mul_mem' ha hb` Lean reads them off `ha` and `hb`. Writing `x ∈ H` for `x ∈ H.carrier` takes an instance of Lean's class
```lean
class Membership (α : Type u) (γ : Type v) where
  mem : γ → α → Prop
```
as Set Theory gave its sets one; the collection comes first in `mem`, so the instance's function takes `H` before `x`.
@description
Define the structure `Subgroup G` with the four fields as the preamble states them, and supply the instance `Subgroup.instMembership : Membership G (Subgroup G)`.
-/

structure Subgroup (G : Type u) [Group G] where
  carrier : Set G
  one_mem' : 1 ∈ carrier
  mul_mem' : ∀ {a b : G}, a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  inv_mem' : ∀ {a : G}, a ∈ carrier → a⁻¹ ∈ carrier

instance Subgroup.instMembership {G : Type u} [Group G] : Membership G (Subgroup G) :=
  ⟨fun H x => x ∈ H.carrier⟩

/-- @spec -/
example {G : Type u} [Group G] (H : Subgroup G) : Set G := H.carrier

/-- @spec -/
example {G : Type u} [Group G] (H : Subgroup G) : (1 : G) ∈ H.carrier := H.one_mem'

/-- @spec -/
example {G : Type u} [Group G] (H : Subgroup G) (a b : G) (ha : a ∈ H.carrier)
    (hb : b ∈ H.carrier) : a * b ∈ H.carrier :=
  @Subgroup.mul_mem' G _ H a b ha hb

/-- @spec -/
example {G : Type u} [Group G] (H : Subgroup G) (a : G) (ha : a ∈ H.carrier) :
    a⁻¹ ∈ H.carrier :=
  @Subgroup.inv_mem' G _ H a ha

/-- @spec -/
example {G : Type u} [Group G] (H : Subgroup G) (x : G) : x ∈ H ↔ x ∈ H.carrier := Iff.rfl

/-! @end -/

/-!
@problem add_subgroup
@title Additive Subgroups
@concept subgroups

@preamble
A subgroup of an additive group is a subset that contains `0`, the sum of any two of its elements and the negative of each. We write `AddSubgroup A`, with the fields `carrier`, `zero_mem'`, `add_mem'` and `neg_mem'`. It is the previous definition written additively, as `AddGroup` was `Group`. Lean is told that `AddSubgroup` is the additive version of `Subgroup`, so each theorem about subgroups below comes with its additive version, its name translated as for groups.
@description
Define the structure `AddSubgroup A` with the four fields named above, written as those of `Subgroup` are, and supply the instance `AddSubgroup.instMembership : Membership A (AddSubgroup A)`.
-/

structure AddSubgroup (A : Type u) [AddGroup A] where
  carrier : Set A
  zero_mem' : 0 ∈ carrier
  add_mem' : ∀ {a b : A}, a ∈ carrier → b ∈ carrier → a + b ∈ carrier
  neg_mem' : ∀ {a : A}, a ∈ carrier → -a ∈ carrier

instance AddSubgroup.instMembership {A : Type u} [AddGroup A] : Membership A (AddSubgroup A) :=
  ⟨fun H x => x ∈ H.carrier⟩

/-- @spec -/
example {A : Type u} [AddGroup A] (H : AddSubgroup A) : Set A := H.carrier

/-- @spec -/
example {A : Type u} [AddGroup A] (H : AddSubgroup A) : (0 : A) ∈ H.carrier := H.zero_mem'

/-- @spec -/
example {A : Type u} [AddGroup A] (H : AddSubgroup A) (a b : A) (ha : a ∈ H.carrier)
    (hb : b ∈ H.carrier) : a + b ∈ H.carrier :=
  @AddSubgroup.add_mem' A _ H a b ha hb

/-- @spec -/
example {A : Type u} [AddGroup A] (H : AddSubgroup A) (a : A) (ha : a ∈ H.carrier) :
    -a ∈ H.carrier :=
  @AddSubgroup.neg_mem' A _ H a ha

/-- @spec -/
example {A : Type u} [AddGroup A] (H : AddSubgroup A) (x : A) : x ∈ H ↔ x ∈ H.carrier := Iff.rfl

/-! @end -/

attribute [to_additive existing AddSubgroup] Subgroup

attribute [to_additive existing AddSubgroup.instMembership] Subgroup.instMembership

/-!
@problem rotations
@title The Rotations Form a Subgroup
@concept subgroups

@preamble
The rotations of the `n`-gon are a subgroup of Dₙ: the trivial rotation `r 0` is `1`, two rotations compose to a rotation, `r i * r j = r (i + j)`, and the inverse of a rotation is a rotation, `(r i)⁻¹ = r (-i)`. A reflection is not a rotation, since two constructors of an inductive type never agree, as in the previous section.

As a set the rotations are the range of the constructor `r`, `Set.range r`, as the first section met ranges. A subgroup is built with `where`, the carrier first and then the three proofs, each a statement about members of the carrier. In a tactic proof of such a field, `intro` names the implicit elements too, while a `fun` names only the hypotheses.

The context holds the three conditions of a subgroup `H` restated through `∈ H`, as `H.one_mem`, `H.mul_mem ha hb` and `H.inv_mem ha`, with their additive versions `AddSubgroup.zero_mem`, `AddSubgroup.add_mem` and `AddSubgroup.neg_mem`.
@description
Define `DihedralGroup.rotations n`, the subgroup of `DihedralGroup n` with carrier `Set.range DihedralGroup.r`, and show that `r i` belongs to it and `sr i` does not.
-/

/-- @given -/
@[to_additive AddSubgroup.zero_mem]
theorem Subgroup.one_mem {G : Type u} [Group G] (H : Subgroup G) : 1 ∈ H := H.one_mem'

/-- @given -/
@[to_additive AddSubgroup.add_mem]
theorem Subgroup.mul_mem {G : Type u} [Group G] (H : Subgroup G) {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) : a * b ∈ H :=
  H.mul_mem' ha hb

/-- @given -/
@[to_additive AddSubgroup.neg_mem]
theorem Subgroup.inv_mem {G : Type u} [Group G] (H : Subgroup G) {a : G} (ha : a ∈ H) : a⁻¹ ∈ H :=
  H.inv_mem' ha

def DihedralGroup.rotations (n : ℕ) [NeZero n] : Subgroup (DihedralGroup n) where
  carrier := Set.range DihedralGroup.r
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    intro a b ⟨i, hi⟩ ⟨j, hj⟩
    rw [← hi, ← hj]
    exact ⟨i + j, rfl⟩
  inv_mem' := by
    intro a ⟨i, hi⟩
    rw [← hi]
    exact ⟨-i, rfl⟩

/-- @spec -/
example {n : ℕ} [NeZero n] (i : ZMod n) :
    DihedralGroup.r i ∈ DihedralGroup.rotations n ∧
    DihedralGroup.sr i ∉ DihedralGroup.rotations n :=
  ⟨⟨i, rfl⟩, fun ⟨j, h⟩ => by cases h⟩

open DihedralGroup in
theorem r_mem_rotations {n : ℕ} [NeZero n] (i : ZMod n) : r i ∈ rotations n :=
  ⟨i, rfl⟩

open DihedralGroup in
theorem sr_not_mem_rotations {n : ℕ} [NeZero n] (i : ZMod n) : sr i ∉ rotations n := by
  intro ⟨j, h⟩
  cases h

/-! @end -/

/-!
@problem int_multiples
@title The Multiples of n
@concept subgroups

@preamble
The multiples of a fixed integer `n` are an additive subgroup of the integers, written `nℤ`: `0` is a multiple of `n`, so is a sum of two multiples, and so is the negative of one. A multiple of `n` is an `x` with `n ∣ x`, divisibility on `ℤ` as the first section met it on `ℕ`. Core Lean has the three facts:
```lean
theorem Int.dvd_zero (n : ℤ) : n ∣ 0
theorem Int.dvd_add {a b c : ℤ} : a ∣ b → a ∣ c → a ∣ b + c
theorem Int.dvd_neg {a b : ℤ} : a ∣ -b ↔ a ∣ b
```
`2ℤ` is the subgroup of even integers, and `1ℤ` is everything.
@description
Define `intMultiples n`, the additive subgroup `nℤ` of `ℤ` with carrier `{x | n ∣ x}`, and prove `mem_intMultiples`, that membership in it is divisibility by `n`; it holds by definition.
-/

def intMultiples (n : ℤ) : AddSubgroup ℤ where
  carrier := {x | n ∣ x}
  zero_mem' := Int.dvd_zero n
  add_mem' := by
    intro a b ha hb
    exact Int.dvd_add ha hb
  neg_mem' := by
    intro a ha
    exact Int.dvd_neg.mpr ha

/-- @spec -/
example (n x : ℤ) : x ∈ intMultiples n ↔ n ∣ x := Iff.rfl

theorem mem_intMultiples {n x : ℤ} : x ∈ intMultiples n ↔ n ∣ x :=
  Iff.rfl

/-! @end -/

/-!
@problem zmod_six_evens
@title The Even Residues Modulo 6
@concept subgroups

@preamble
In `ZMod 6` the residues `0`, `2` and `4` form an additive subgroup: the sum of two of them is one of them, as `2 + 4 = 0` and `4 + 4 = 2`, and the negative of `2` is `4`. The carrier is the set `{0, 2, 4}`, written by listing its elements, and a membership in it means, by definition,
```lean
x = 0 ∨ x = 2 ∨ x = 4
```
Each closure condition is a statement about finitely many residues.
@description
Define `zmodSixEvens`, the additive subgroup of `ZMod 6` with carrier `{0, 2, 4}`, and prove `mem_zmodSixEvens`, that membership in it is that disjunction; it holds by definition.
-/

def zmodSixEvens : AddSubgroup (ZMod 6) where
  carrier := {0, 2, 4}
  zero_mem' := by decide
  add_mem' := by decide
  neg_mem' := by decide

/-- @spec -/
example : ∀ x : ZMod 6, x ∈ zmodSixEvens ↔ x = 0 ∨ x = 2 ∨ x = 4 :=
  fun _ => Iff.rfl

theorem mem_zmodSixEvens (x : ZMod 6) : x ∈ zmodSixEvens ↔ x = 0 ∨ x = 2 ∨ x = 4 := Iff.rfl

/-! @end -/

/-!
@problem subgroup_as_type
@title A Subgroup as a Type
@concept subgroups

@preamble
A subgroup is to be a group in its own right, so its elements must form a type. Its carrier is a set, which stands where a type is expected, as in the first section. We write this type `H.carrier`, and Lean prints it `↥H.carrier`. Its elements are the pairs `⟨x, hx⟩` of an `x : G` and a proof `hx : x ∈ H.carrier`. For `a : H.carrier`, the element `(a : G)`, printed `↑a`, is `a.1` of the first section, and `a.2` is the proof that it lies in the carrier.

One consequence is a count: the function `a ↦ (a : G)` from `H.carrier` to `G` is injective, Mathlib's `Subtype.val_injective`, so `H` has no more elements than `G`. Counting `H.carrier` needs membership in it to be decidable, which `open Classical in` supplies, as it did for a quotient.
@description
Show that `(a : G) ∈ H` for every `a : H.carrier`. Show also, under `open Classical in`, that a subgroup of a finite group has at most as many elements as the group:
```lean
Fintype.card H.carrier ≤ Fintype.card G
```
-/

@[to_additive AddSubgroup.coe_mem]
theorem Subgroup.coe_mem {G : Type u} [Group G] {H : Subgroup G} (a : H.carrier) : (a : G) ∈ H :=
  a.2

open Classical in
@[to_additive AddSubgroup.card_le_card_addGroup]
theorem Subgroup.card_le_card_group {G : Type u} [Group G] [Fintype G] (H : Subgroup G) :
    Fintype.card H.carrier ≤ Fintype.card G :=
  Fintype.card_le_of_injective (fun a : H.carrier => (a : G)) Subtype.val_injective

/-! @end -/

/-!
@problem subgroup_group
@title A Subgroup is a Group
@concept subgroups

@preamble
With its elements as the type `H.carrier`, a subgroup `H` is a group under the operation of `G`. The operations are those of `G`, and the three conditions of the definition keep their results in `H`. Two elements of `H.carrier` are equal when their elements of `G` are, as for `Fin n`:
```lean
theorem Subtype.ext {a b : H.carrier} : (a : G) = (b : G) → a = b
```
@description
Supply the instance `Group H.carrier` for a subgroup `H` of `G`, and prove the three equations below, `Subgroup.coe_mul`, `Subgroup.coe_one` and `Subgroup.coe_inv`, each of which holds by definition. On the right of the first, both factors are taken into `G` first.
```lean
((a * b : H.carrier) : G) = (a : G) * (b : G)
((1 : H.carrier) : G) = 1
((a⁻¹ : H.carrier) : G) = (a : G)⁻¹
```
-/

@[to_additive AddSubgroup.instAddGroupCarrier]
instance Subgroup.instGroupCarrier {G : Type u} [Group G] (H : Subgroup G) : Group H.carrier where
  mul a b := ⟨a.1 * b.1, H.mul_mem a.2 b.2⟩
  one := ⟨1, H.one_mem⟩
  inv a := ⟨a.1⁻¹, H.inv_mem a.2⟩
  mul_assoc a b c := Subtype.ext (mul_assoc a.1 b.1 c.1)
  one_mul a := Subtype.ext (one_mul a.1)
  mul_one a := Subtype.ext (mul_one a.1)
  inv_mul_cancel a := Subtype.ext (inv_mul_cancel a.1)
  mul_inv_cancel a := Subtype.ext (mul_inv_cancel a.1)

/-- @spec -/
example {G : Type u} [Group G] {H : Subgroup G} (a b : H.carrier) :
    ((a * b : H.carrier) : G) = (a : G) * (b : G) ∧ ((1 : H.carrier) : G) = 1 ∧
    ((a⁻¹ : H.carrier) : G) = (a : G)⁻¹ :=
  ⟨rfl, rfl, rfl⟩

@[to_additive AddSubgroup.coe_add]
theorem Subgroup.coe_mul {G : Type u} [Group G] {H : Subgroup G} (a b : H.carrier) :
    ((a * b : H.carrier) : G) = (a : G) * (b : G) := rfl

@[to_additive AddSubgroup.coe_zero]
theorem Subgroup.coe_one {G : Type u} [Group G] {H : Subgroup G} : ((1 : H.carrier) : G) = 1 := rfl

@[to_additive AddSubgroup.coe_neg]
theorem Subgroup.coe_inv {G : Type u} [Group G] {H : Subgroup G} (a : H.carrier) :
    ((a⁻¹ : H.carrier) : G) = (a : G)⁻¹ := rfl

/-! @end -/

/--
@problem eq_of_coe_eq
@title An Element of a Subgroup is Determined by Its Value
@concept subgroups

@preamble
The previous problem used `Subtype.ext`: two elements of `H.carrier` with the same element of `G` are equal. It is proved by taking the two pairs apart. A value of a structure type is built by the structure's one constructor, which Lean names `mk`, from its fields, and
```lean
cases a with
| mk x hx => …
```
opens `a : H.carrier` into its element `x` and its proof `hx`. The tactic `subst h` replaces one variable by the other through an equation `h : x = y`. Two pairs with the same element differ only in their proofs, and two proofs of one proposition are equal in Lean.
@description
Show that two elements `a` and `b` of `H.carrier` with `(a : G) = (b : G)` are equal, without `Subtype.ext`.
-/
@[to_additive AddSubgroup.eq_of_coe_eq]
theorem Subgroup.eq_of_coe_eq {G : Type u} [Group G] {H : Subgroup G} {a b : H.carrier}
    (h : (a : G) = (b : G)) : a = b := by
  cases a with
  | mk x hx =>
    cases b with
    | mk y hy =>
      change x = y at h
      subst h
      rfl

/--
@problem subgroup_ext
@title Two Subgroups With the Same Elements Are Equal
@concept subgroups

@preamble
A subgroup is determined by its elements: two subgroups with the same members are equal, as two sets are. We name this `Subgroup.ext`. A subgroup opens into its four fields as an element of `H.carrier` opened into two in the previous problem. Two subgroups with the same carrier differ only in three proofs, which make no difference, as the proof in a pair made none.
@description
Show that two subgroups `H` and `K` with `x ∈ H ↔ x ∈ K` for every `x` are equal. `Set.ext` of the first section may be useful.
-/
@[to_additive AddSubgroup.ext]
theorem Subgroup.ext {G : Type u} [Group G] {H K : Subgroup G} (h : ∀ x, x ∈ H ↔ x ∈ K) :
    H = K := by
  cases H with
  | mk c _ _ _ =>
    cases K with
    | mk c' _ _ _ =>
      have e : c = c' := Set.ext h
      subst e
      rfl

/-!
@problem top_bot
@title The Whole Group and the Trivial Subgroup
@concept subgroups

@preamble
Every group has two obvious subgroups: the whole group, and `{1}`, with the neutral element alone, the *trivial subgroup*. We write them `⊤` and `⊥` (typed `\top` and `\bot`), the largest and the smallest subgroup, through the notation class
```lean
class Top (α : Type u) where
  top : α
```
and `Bot`, the same with the field `bot`. Each instance is `⟨…⟩` around a subgroup written with the brace notation for structures. The carrier of `⊤` is `Set.univ`, the set of all elements, and the carrier of `⊥` is the singleton `{1}`. Mathlib's laws for them are
```lean
theorem Set.mem_univ (x : α) : x ∈ Set.univ
theorem Set.mem_singleton (a : α) : a ∈ {a}
theorem Set.mem_singleton_iff {a b : α} : a ∈ {b} ↔ a = b
```
The context holds `one_mul` and `inv_one`.
@description
Supply the instances `Top (Subgroup G)` and `Bot (Subgroup G)`, and prove `Subgroup.mem_top`, that every `x` is in `⊤`, and `Subgroup.mem_bot`, that `x ∈ ⊥ ↔ x = 1`.
-/

@[to_additive AddSubgroup.instTop]
instance Subgroup.instTop {G : Type u} [Group G] : Top (Subgroup G) :=
  ⟨{ carrier := Set.univ
     one_mem' := Set.mem_univ 1
     mul_mem' := fun _ _ => Set.mem_univ _
     inv_mem' := fun _ => Set.mem_univ _ }⟩

@[to_additive AddSubgroup.instBot]
instance Subgroup.instBot {G : Type u} [Group G] : Bot (Subgroup G) :=
  ⟨{ carrier := {1}
     one_mem' := Set.mem_singleton 1
     mul_mem' := by
       intro a b ha hb
       rw [Set.mem_singleton_iff] at ha hb
       rw [Set.mem_singleton_iff, ha, hb, one_mul]
     inv_mem' := by
       intro a ha
       rw [Set.mem_singleton_iff] at ha
       rw [Set.mem_singleton_iff, ha, inv_one] }⟩

/-- @spec -/
example {G : Type u} [Group G] (x : G) : x ∈ (⊤ : Subgroup G) := Set.mem_univ x

/-- @spec -/
example {G : Type u} [Group G] (x : G) : x ∈ (⊥ : Subgroup G) ↔ x = 1 := Iff.rfl

@[to_additive AddSubgroup.mem_top]
theorem Subgroup.mem_top {G : Type u} [Group G] (x : G) : x ∈ (⊤ : Subgroup G) := Set.mem_univ x

@[to_additive AddSubgroup.mem_bot]
theorem Subgroup.mem_bot {G : Type u} [Group G] {x : G} : x ∈ (⊥ : Subgroup G) ↔ x = 1 := Iff.rfl

/-! @end -/

/-!
@problem subgroup_le
@title Inclusion of Subgroups
@concept subgroups

@preamble
Subgroups are compared by inclusion: `H ≤ K` when every element of `H` is in `K`. So `⊥` is the smallest subgroup and `⊤` the largest, and since a subgroup is determined by its elements, `H ≤ K` and `K ≤ H` force `H = K`. The symbol comes from Lean's class
```lean
class LE (α : Type u) where
  le : α → α → Prop
```
`H ≤ K` is defined with the strict implicit binder of `Function.Injective`, so for `h : H ≤ K` and `hx : x ∈ H` the term `h hx` proves `x ∈ K`. We prove the three facts as `Subgroup.bot_le`, `Subgroup.le_top` and `Subgroup.le_antisymm`. The context holds `Subgroup.mem_bot`, `Subgroup.mem_top`, `Subgroup.one_mem` and `Subgroup.ext`.
@description
Supply the instance `LE (Subgroup G)` with `H ≤ K` defined as
```lean
∀ ⦃x⦄, x ∈ H → x ∈ K
```
Show that `⊥ ≤ H` and `H ≤ ⊤` for every subgroup `H`, and that `H ≤ K` and `K ≤ H` give `H = K`.
-/

@[to_additive AddSubgroup.instLE]
instance Subgroup.instLE {G : Type u} [Group G] : LE (Subgroup G) :=
  ⟨fun H K => ∀ ⦃x⦄, x ∈ H → x ∈ K⟩

/-- @spec -/
example {G : Type u} [Group G] (H K : Subgroup G) : H ≤ K ↔ ∀ x, x ∈ H → x ∈ K := Iff.rfl

@[to_additive AddSubgroup.bot_le]
theorem Subgroup.bot_le {G : Type u} [Group G] (H : Subgroup G) : ⊥ ≤ H := by
  intro x hx
  rw [Subgroup.mem_bot] at hx
  rw [hx]
  exact H.one_mem

@[to_additive AddSubgroup.le_top]
theorem Subgroup.le_top {G : Type u} [Group G] (H : Subgroup G) : H ≤ ⊤ := by
  intro x _
  exact Subgroup.mem_top x

@[to_additive AddSubgroup.le_antisymm]
theorem Subgroup.le_antisymm {G : Type u} [Group G] {H K : Subgroup G} (h₁ : H ≤ K)
    (h₂ : K ≤ H) : H = K := by
  apply Subgroup.ext
  intro x
  exact ⟨fun hx => h₁ hx, fun hx => h₂ hx⟩

/-! @end -/

/-!
@problem pow_mem
@title Powers Stay in a Subgroup
@concept subgroups

@preamble
A subgroup closed under products is closed under powers: `g ^ n ∈ H` whenever `g ∈ H`, and then `g ^ k ∈ H` for every integer `k`, a negative power being the inverse of a natural one. An additive subgroup contains every multiple of each of its elements, by the additive version `AddSubgroup.zsmul_mem`. In `ZMod 6` every integer multiple of `2` is `0`, `2` or `4`. The context holds `pow_zero`, `pow_succ` and `zpow_negSucc` of the previous section, and `mem_zmodSixEvens`.
@description
Show that `g ^ n ∈ H` for every natural number `n`, and `g ^ k ∈ H` for every integer `k`, whenever `g ∈ H`, under the names `Subgroup.pow_mem` and `Subgroup.zpow_mem`. Conclude that `k • 2 ∈ zmodSixEvens` for every integer `k`.
-/

@[to_additive AddSubgroup.nsmul_mem]
theorem Subgroup.pow_mem {G : Type u} [Group G] (H : Subgroup G) {g : G} (hg : g ∈ H) (n : ℕ) :
    g ^ n ∈ H := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact H.one_mem
  | succ n ih =>
    rw [pow_succ]
    exact H.mul_mem ih hg

@[to_additive AddSubgroup.zsmul_mem]
theorem Subgroup.zpow_mem {G : Type u} [Group G] (H : Subgroup G) {g : G} (hg : g ∈ H) (k : ℤ) :
    g ^ k ∈ H := by
  cases k with
  | ofNat n => exact H.pow_mem hg n
  | negSucc n =>
    rw [zpow_negSucc]
    exact H.inv_mem (H.pow_mem hg (n + 1))

theorem zmod_six_two_zsmul_mem (k : ℤ) : k • (2 : ZMod 6) ∈ zmodSixEvens := by
  apply zmodSixEvens.zsmul_mem
  rw [mem_zmodSixEvens]
  decide

/-! @end -/

/-!
@concept centre
@title The Centre
@kind definition

The centre of a group is the set of elements that commute with every element. It is a subgroup, and it is the whole group exactly when the group is commutative, so it measures how far a group is from commutative: trivial in D₃, two elements in D₄, everything in the Klein four-group.
-/

/-!
@problem center
@title The Centre of a Group
@concept centre

@preamble
The *centre* of `G` is the set of elements that commute with every element of `G`:
```lean
{z | ∀ g, g * z = z * g}
```
It is a subgroup. `1` commutes with everything. If `a` and `b` commute with `g`, so does `a * b`. If `a` commutes with every element, so does `a⁻¹`. A hypothesis that `a` lies in this set is the statement it abbreviates, so `ha g` is the equation for `g`, and such a goal opens on `intro g`. The additive version is `AddSubgroup.center`. The context holds `mul_inv_rev` and `inv_inv`.
@description
Define `Subgroup.center G`, the centre of `G`, as the subgroup with that carrier, and prove `Subgroup.mem_center_iff`, which says that `z ∈ center G` means that `z` commutes with every `g`; it holds by definition.
-/

@[to_additive AddSubgroup.center]
def Subgroup.center (G : Type u) [Group G] : Subgroup G where
  carrier := {z | ∀ g, g * z = z * g}
  one_mem' := by
    intro g
    rw [mul_one, one_mul]
  mul_mem' := by
    intro a b ha hb g
    rw [← mul_assoc, ha g, mul_assoc, hb g, ← mul_assoc]
  inv_mem' := by
    intro a ha g
    have h : (g⁻¹ * a)⁻¹ = (a * g⁻¹)⁻¹ := by
      rw [ha g⁻¹]
    rw [mul_inv_rev, mul_inv_rev, inv_inv] at h
    exact h.symm

/-- @spec -/
example {G : Type u} [Group G] (z : G) : z ∈ Subgroup.center G ↔ ∀ g, g * z = z * g := by
  constructor
  · intro h g
    have h' := h g
    grind
  · intro h g
    have h' := h g
    grind

@[to_additive AddSubgroup.mem_center_iff]
theorem Subgroup.mem_center_iff {G : Type u} [Group G] {z : G} :
    z ∈ Subgroup.center G ↔ ∀ g, g * z = z * g := Iff.rfl

/-! @end -/

/-!
@problem center_eq_top
@title The Centre of a Commutative Group
@concept centre

@preamble
The centre is the whole group exactly when every pair of elements commutes. So a commutative group is its own centre; so is the Klein four-group, through the instance `CommGroup (DihedralGroup 2)` of the examples section, which the context holds. The additive groups `ℤ`, `ZMod n` and `Bool` are commutative, so their centres are everything, through the additive versions and the instance `AddCommGroup ℤ`. A hypothesis `h : center G = ⊤` is an equation between subgroups, and `rw` uses it as it uses any equation. The context holds `Subgroup.ext`, `Subgroup.mem_top`, `Subgroup.mem_center_iff` and `mul_comm`.
@description
Show that `center G = ⊤` exactly when `a * b = b * a` for all `a` and `b`; that the centre of a commutative group is `⊤`; that `center (DihedralGroup 2) = ⊤`; and that `AddSubgroup.center ℤ = ⊤`.
-/

@[to_additive AddSubgroup.center_eq_top_iff]
theorem Subgroup.center_eq_top_iff {G : Type u} [Group G] :
    Subgroup.center G = ⊤ ↔ ∀ a b : G, a * b = b * a := by
  constructor
  · intro h a b
    have ha : a ∈ Subgroup.center G := by
      rw [h]
      exact Subgroup.mem_top a
    rw [Subgroup.mem_center_iff] at ha
    exact (ha b).symm
  · intro h
    apply Subgroup.ext
    intro x
    constructor
    · intro _
      exact Subgroup.mem_top x
    · intro _
      rw [Subgroup.mem_center_iff]
      intro g
      exact h g x

@[to_additive AddSubgroup.center_eq_top]
theorem Subgroup.center_eq_top {G : Type u} [CommGroup G] : Subgroup.center G = ⊤ :=
  Subgroup.center_eq_top_iff.mpr mul_comm

theorem center_klein : Subgroup.center (DihedralGroup 2) = ⊤ :=
  Subgroup.center_eq_top

theorem int_center : AddSubgroup.center ℤ = ⊤ :=
  AddSubgroup.center_eq_top

/-! @end -/

/-!
@problem center_dihedral
@title The Centres of D₃ and D₄
@concept centre

@preamble
In D₃, the triangle, nothing but `1` commutes with every symmetry: its centre is `⊥`. In D₄, the square, the half turn `r 2` commutes with everything, since turning the square halfway round and then reflecting it is reflecting it and then turning it halfway round. Nothing else does but `1`: the centre is `{1, r 2}`, that is, `r 0` and `r 2`.

The first two statements below are about finitely many elements, but `decide` needs the memberships written out as what they say first. The context holds `Subgroup.ext`, `Subgroup.mem_center_iff`, `Subgroup.mem_bot`, `Subgroup.center_eq_top_iff` and `d4_not_comm`.
@description
Show that the centre of `DihedralGroup 3` is `⊥`; that `x` is in the centre of `DihedralGroup 4` exactly when `x = r 0` or `x = r 2`; and that the centre of `DihedralGroup 4` is not `⊤`.
-/

theorem d3_center : Subgroup.center (DihedralGroup 3) = ⊥ := by
  apply Subgroup.ext
  simp only [Subgroup.mem_center_iff, Subgroup.mem_bot]
  decide

open DihedralGroup in
theorem d4_center :
    ∀ x : DihedralGroup 4, x ∈ Subgroup.center (DihedralGroup 4) ↔ x = r 0 ∨ x = r 2 := by
  simp only [Subgroup.mem_center_iff]
  decide

open DihedralGroup in
theorem d4_center_ne_top : Subgroup.center (DihedralGroup 4) ≠ ⊤ := by
  intro h
  exact d4_not_comm (Subgroup.center_eq_top_iff.mp h (r 1) (sr 0))

/-! @end -/

/-!
@concept intersections
@title Intersections of Subgroups
@kind definition

The intersection of two subgroups is a subgroup, and so is the intersection of any family of them, so any two subgroups have a greatest subgroup below both. The intersection of all the subgroups containing a set is the smallest subgroup containing it.
-/

/-!
@problem inf
@title The Intersection of Two Subgroups
@concept intersections

@preamble
Two subgroups `H` and `K` meet in a subgroup: `1` is in both, a product of two elements of both is in both, and so is an inverse. We write the intersection `H ⊓ K` (typed `\glb`), for `min H K`, through the class
```lean
class Min (α : Type u) where
  min : α → α → α
```
Its carrier is `H.carrier ∩ K.carrier`. The halves of `ha : x ∈ H ⊓ K` read `x ∈ H.carrier` and `x ∈ K.carrier`, and `exact` accepts them as proofs of `x ∈ H` and `x ∈ K`. It is the greatest subgroup below both, which we prove as `Subgroup.inf_le_left`, `Subgroup.inf_le_right` and `Subgroup.le_inf`. `⊓` works for additive subgroups as well. In the integers the multiples of both `2` and `3` are the multiples of `6`. The context holds `mem_intMultiples`, `AddSubgroup.ext`, and `AddSubgroup.mem_inf`, the additive version of `Subgroup.mem_inf`.
@description
Supply the instance `Min (Subgroup G)`, and prove `Subgroup.mem_inf`, that `x ∈ H ⊓ K` exactly when `x ∈ H` and `x ∈ K`, which holds by definition. Show that `H ⊓ K` lies below `H` and below `K`, and above every subgroup that lies below both, and that `2ℤ ⊓ 3ℤ = 6ℤ`. `omega`, which decides divisibility by a numeral, may be useful.
-/

@[to_additive AddSubgroup.instMin]
instance Subgroup.instMin {G : Type u} [Group G] : Min (Subgroup G) :=
  ⟨fun H K =>
    { carrier := H.carrier ∩ K.carrier
      one_mem' := ⟨H.one_mem, K.one_mem⟩
      mul_mem' := fun ha hb => ⟨H.mul_mem ha.1 hb.1, K.mul_mem ha.2 hb.2⟩
      inv_mem' := fun ha => ⟨H.inv_mem ha.1, K.inv_mem ha.2⟩ }⟩

/-- @spec -/
example {G : Type u} [Group G] (H K : Subgroup G) (x : G) : x ∈ H ⊓ K ↔ x ∈ H ∧ x ∈ K := Iff.rfl

@[to_additive AddSubgroup.mem_inf]
theorem Subgroup.mem_inf {G : Type u} [Group G] {H K : Subgroup G} {x : G} :
    x ∈ H ⊓ K ↔ x ∈ H ∧ x ∈ K := Iff.rfl

@[to_additive AddSubgroup.inf_le_left]
theorem Subgroup.inf_le_left {G : Type u} [Group G] (H K : Subgroup G) : H ⊓ K ≤ H := by
  intro x hx
  exact hx.1

@[to_additive AddSubgroup.inf_le_right]
theorem Subgroup.inf_le_right {G : Type u} [Group G] (H K : Subgroup G) : H ⊓ K ≤ K := by
  intro x hx
  exact hx.2

@[to_additive AddSubgroup.le_inf]
theorem Subgroup.le_inf {G : Type u} [Group G] {H K L : Subgroup G} (h₁ : L ≤ H) (h₂ : L ≤ K) :
    L ≤ H ⊓ K := by
  intro x hx
  exact ⟨h₁ hx, h₂ hx⟩

theorem intMultiples_two_inf_three : intMultiples 2 ⊓ intMultiples 3 = intMultiples 6 := by
  apply AddSubgroup.ext
  intro x
  rw [AddSubgroup.mem_inf, mem_intMultiples, mem_intMultiples, mem_intMultiples]
  omega

/-! @end -/

/-!
@problem s_inf
@title The Intersection of a Family of Subgroups
@concept intersections

@preamble
The intersection of any set `S` of subgroups, not only of two, is a subgroup: an element of the intersection lies in every `H ∈ S`. We write it `sInf S`, the greatest lower bound of a set, through the class
```lean
class InfSet (α : Type u) where
  sInf : Set α → α
```
The carrier is `{x | ∀ H ∈ S, x ∈ H}`, where `∀ H ∈ S, …` abbreviates `∀ H, H ∈ S → …`, as `∃ x ∈ S, …` abbreviated `∃ x, x ∈ S ∧ …` in the first section, so a membership in it is a function of a subgroup `H` and a proof `hH : H ∈ S`. The intersection lies below every member of `S`, and above every subgroup that lies below all of them. For the two-element set `{H, K}` it has the same elements as `H ⊓ K`. A membership `L ∈ {H, K}` means `L = H ∨ L ∈ {K}`, and `rw` accepts the second half as `L = K`. The context holds `Subgroup.mem_inf`.
@description
Supply the instance `InfSet (Subgroup G)`, and prove `Subgroup.mem_sInf`, which holds by definition:
```lean
x ∈ sInf S ↔ ∀ H ∈ S, x ∈ H
```
Show that `sInf S ≤ H` for every `H ∈ S`, and that `K ≤ sInf S` whenever `K ≤ H` for every `H ∈ S`. Show that `x ∈ sInf {H, K}` exactly when `x ∈ H ⊓ K`.
-/

@[to_additive AddSubgroup.instInfSet]
instance Subgroup.instInfSet {G : Type u} [Group G] : InfSet (Subgroup G) :=
  ⟨fun S =>
    { carrier := {x | ∀ H ∈ S, x ∈ H}
      one_mem' := fun H _ => H.one_mem
      mul_mem' := fun ha hb H hH => H.mul_mem (ha H hH) (hb H hH)
      inv_mem' := fun ha H hH => H.inv_mem (ha H hH) }⟩

/-- @spec -/
example {G : Type u} [Group G] (S : Set (Subgroup G)) (x : G) :
    x ∈ sInf S ↔ ∀ H ∈ S, x ∈ H := Iff.rfl

@[to_additive AddSubgroup.mem_sInf]
theorem Subgroup.mem_sInf {G : Type u} [Group G] {S : Set (Subgroup G)} {x : G} :
    x ∈ sInf S ↔ ∀ H ∈ S, x ∈ H := Iff.rfl

@[to_additive AddSubgroup.sInf_le]
theorem Subgroup.sInf_le {G : Type u} [Group G] {S : Set (Subgroup G)} {H : Subgroup G}
    (h : H ∈ S) : sInf S ≤ H := by
  intro x hx
  exact hx H h

@[to_additive AddSubgroup.le_sInf]
theorem Subgroup.le_sInf {G : Type u} [Group G] {S : Set (Subgroup G)} {K : Subgroup G}
    (h : ∀ H ∈ S, K ≤ H) : K ≤ sInf S := by
  intro x hx H hH
  exact h H hH hx

@[to_additive AddSubgroup.mem_sInf_pair]
theorem Subgroup.mem_sInf_pair {G : Type u} [Group G] {H K : Subgroup G} {x : G} :
    x ∈ sInf {H, K} ↔ x ∈ H ⊓ K := by
  rw [Subgroup.mem_sInf, Subgroup.mem_inf]
  constructor
  · intro h
    exact ⟨h H (Or.inl rfl), h K (Or.inr rfl)⟩
  · intro h L hL
    cases hL with
    | inl hL =>
      rw [hL]
      exact h.1
    | inr hL =>
      rw [hL]
      exact h.2

/-! @end -/

/-!
@concept generated_subgroups
@title Generated Subgroups and Cyclic Groups
@kind definition
@goal

The subgroup generated by a set is the smallest subgroup containing it, and the subgroup generated by one element is the set of its powers. A group generated by one element is cyclic: the integers, and the integers modulo n, each generated by 1. Every cyclic group is commutative.
-/

/-!
@problem closure
@title The Subgroup Generated by a Set
@concept generated_subgroups

@preamble
The subgroup *generated* by a set `X` is the smallest subgroup containing `X`: the intersection of all the subgroups that contain `X`. It is called the *closure* of `X`, `Subgroup.closure X`, since it is `X` closed up under products and inverses. A membership in it is, by definition, a statement about every subgroup containing `X`, as a membership in `sInf` was. The context holds `Subgroup.mem_sInf` and `Subgroup.sInf_le`.
@description
Define `Subgroup.closure X` as the intersection of the subgroups containing `X`, and prove `Subgroup.mem_closure`, which holds by definition:
```lean
x ∈ closure X ↔ ∀ H : Subgroup G, X ⊆ H.carrier → x ∈ H
```
Show `Subgroup.subset_closure`, that `X` lies in the carrier of its closure, and `Subgroup.closure_le`:
```lean
closure X ≤ H ↔ X ⊆ H.carrier
```
-/

@[to_additive AddSubgroup.closure]
def Subgroup.closure {G : Type u} [Group G] (X : Set G) : Subgroup G := sInf {H | X ⊆ H.carrier}

/-- @spec -/
example {G : Type u} [Group G] (X : Set G) : Subgroup.closure X = sInf {H | X ⊆ H.carrier} := rfl

@[to_additive AddSubgroup.mem_closure]
theorem Subgroup.mem_closure {G : Type u} [Group G] {X : Set G} {x : G} :
    x ∈ Subgroup.closure X ↔ ∀ H : Subgroup G, X ⊆ H.carrier → x ∈ H :=
  Subgroup.mem_sInf

@[to_additive AddSubgroup.subset_closure]
theorem Subgroup.subset_closure {G : Type u} [Group G] {X : Set G} :
    X ⊆ (Subgroup.closure X).carrier := by
  intro x hx
  change x ∈ Subgroup.closure X
  rw [Subgroup.mem_closure]
  intro H hH
  exact hH hx

@[to_additive AddSubgroup.closure_le]
theorem Subgroup.closure_le {G : Type u} [Group G] {X : Set G} {H : Subgroup G} :
    Subgroup.closure X ≤ H ↔ X ⊆ H.carrier := by
  constructor
  · intro h x hx
    exact h (Subgroup.subset_closure hx)
  · intro h
    exact Subgroup.sInf_le h

/-! @end -/

/-!
@problem zpowers
@title The Subgroup Generated by an Element
@concept generated_subgroups

@preamble
The powers of one element `g`, with every integer as exponent, form a subgroup, by the laws of integer powers of the previous section. We write it `Subgroup.zpowers g`, and its carrier is
```lean
{x | ∃ k : ℤ, g ^ k = x}
```
Its additive version is `AddSubgroup.zmultiples a`, the integer multiples `k • a` of `a`. The context holds `zpow_zero`, `zpow_one`, `zpow_add` and `zpow_neg`.
@description
Define `Subgroup.zpowers g`, and prove `Subgroup.mem_zpowers_iff`, that `x ∈ zpowers g` exactly when `x` is an integer power of `g`, which holds by definition. Show that `g ∈ zpowers g`, under the name `Subgroup.mem_zpowers`.
-/

@[to_additive AddSubgroup.zmultiples]
def Subgroup.zpowers {G : Type u} [Group G] (g : G) : Subgroup G where
  carrier := {x | ∃ k : ℤ, g ^ k = x}
  one_mem' := ⟨0, zpow_zero g⟩
  mul_mem' := by
    intro a b ⟨k, hk⟩ ⟨l, hl⟩
    rw [← hk, ← hl]
    exact ⟨k + l, zpow_add g k l⟩
  inv_mem' := by
    intro a ⟨k, hk⟩
    rw [← hk]
    exact ⟨-k, zpow_neg g k⟩

/-- @spec -/
example {G : Type u} [Group G] (g x : G) : x ∈ Subgroup.zpowers g ↔ ∃ k : ℤ, g ^ k = x := by
  constructor
  · intro ⟨k, hk⟩
    exact ⟨k, by grind⟩
  · intro ⟨k, hk⟩
    exact ⟨k, by grind⟩

@[to_additive AddSubgroup.mem_zmultiples_iff]
theorem Subgroup.mem_zpowers_iff {G : Type u} [Group G] {g x : G} :
    x ∈ Subgroup.zpowers g ↔ ∃ k : ℤ, g ^ k = x := Iff.rfl

@[to_additive AddSubgroup.mem_zmultiples]
theorem Subgroup.mem_zpowers {G : Type u} [Group G] (g : G) : g ∈ Subgroup.zpowers g :=
  ⟨1, zpow_one g⟩

/-! @end -/

/--
@problem zpowers_eq_closure
@title The Subgroup Generated by One Element Is Its Powers
@concept generated_subgroups

@preamble
The subgroup generated by the set `{g}` and the subgroup of powers of `g` are the same subgroup. Each contains the other: a subgroup that contains `g` contains all of its powers, and `zpowers g` is itself a subgroup containing `g`. The set `{g}` is a singleton, with the laws `Set.mem_singleton` and `Set.mem_singleton_iff` met for `⊥`. `Subgroup.zpow_mem` takes its subgroup as an explicit first argument, written `K.zpow_mem` for a subgroup `K`, as `H.mul_mem` is. The context holds `Subgroup.le_antisymm`, `Subgroup.zpow_mem`, `Subgroup.subset_closure`, `Subgroup.closure_le`, `Subgroup.mem_zpowers_iff` and `Subgroup.mem_zpowers`.
@description
Show that `zpowers g = closure {g}`.
-/
@[to_additive AddSubgroup.zmultiples_eq_closure]
theorem Subgroup.zpowers_eq_closure {G : Type u} [Group G] (g : G) :
    Subgroup.zpowers g = Subgroup.closure {g} := by
  apply Subgroup.le_antisymm
  · intro x hx
    rw [Subgroup.mem_zpowers_iff] at hx
    obtain ⟨k, hk⟩ := hx
    rw [← hk]
    exact (Subgroup.closure {g}).zpow_mem (Subgroup.subset_closure (Set.mem_singleton g)) k
  · apply Subgroup.closure_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Subgroup.mem_zpowers g

/-!
@problem is_cyclic
@title Cyclic Groups
@concept generated_subgroups

@preamble
A group is *cyclic* when a single element generates it: some `g` with every `x` in `zpowers g`. We write `IsCyclic G`, and its additive version is `IsAddCyclic A`. A cyclic group is commutative, since any two of its elements are powers of the one generator. `IsCyclic G` is a proposition with a name, a `def` into `Prop` as `IsOfFinOrder` was, and `obtain ⟨g, hg⟩ := h` opens a hypothesis `h : IsCyclic G`. Mathlib makes `IsCyclic` a class; here it is a definition. The context holds `zpow_add`, `Subgroup.mem_zpowers_iff` and core's `Int.add_comm`.
@description
Define `IsCyclic G` as
```lean
∃ g : G, ∀ x, x ∈ Subgroup.zpowers g
```
and show that in a cyclic group `a * b = b * a`.
-/

@[to_additive IsAddCyclic]
def IsCyclic (G : Type u) [Group G] : Prop := ∃ g : G, ∀ x, x ∈ Subgroup.zpowers g

/-- @spec -/
example {G : Type u} [Group G] : IsCyclic G ↔ ∃ g : G, ∀ x, ∃ k : ℤ, g ^ k = x := by
  constructor
  · intro ⟨g, hg⟩
    exact ⟨g, fun x => by obtain ⟨k, hk⟩ := hg x; exact ⟨k, by grind⟩⟩
  · intro ⟨g, hg⟩
    exact ⟨g, fun x => by obtain ⟨k, hk⟩ := hg x; exact ⟨k, by grind⟩⟩

@[to_additive IsAddCyclic.add_comm]
theorem IsCyclic.mul_comm {G : Type u} [Group G] (h : IsCyclic G) (a b : G) : a * b = b * a := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
  rw [← hk, ← hl, ← zpow_add, ← zpow_add, Int.add_comm]

/-! @end -/

/--
@problem int_zsmul_eq_mul
@title Multiples in the Integers Are Products
@concept generated_subgroups

@preamble
In the integers an integer multiple is a product, `k • n = k * n` for all integers `k` and `n`, as the previous section showed `k • 1 = k`: by induction over the integers in both directions, each step the distributive law. The step up is routine. The step down is not, since lowering the multiplier by one adds a negative, `+ -n`, where the distributive law subtracts, `- 1 * n`, and the two sides meet only after `a - b` is rewritten as `a + -b`:
```lean
(-↑k - 1) • n = (-↑k) • n + -n = -↑k * n + -n
  = -↑k * n - 1 * n = (-↑k - 1) * n
```
The context holds `zero_zsmul`, `add_one_zsmul`, `sub_one_zsmul`, and core Lean's laws of `ℤ`, among them `Int.add_mul`, `Int.sub_mul` and `Int.sub_eq_add_neg`.
@description
Show that `k • n = k * n` for all integers `k` and `n`.
-/
theorem int_zsmul_eq_mul (k n : ℤ) : k • n = k * n := by
  induction k with
  | zero => rw [zero_zsmul, Int.zero_mul]
  | succ k ih => rw [add_one_zsmul, ih, Int.add_mul, Int.one_mul]
  | pred k ih => rw [sub_one_zsmul, ih, Int.sub_mul, Int.one_mul, Int.sub_eq_add_neg]

/-!
@problem int_cyclic
@title The Integers Are Cyclic
@concept generated_subgroups

@preamble
Since a multiple in the integers is a product, the multiples of `n` in the group's sense are its multiples in the everyday sense. So `zmultiples n` is `intMultiples n`, the subgroup `nℤ` of the first concept of this section, and the subgroups `nℤ` are the cyclic subgroups of the integers. The integers themselves are cyclic, `IsAddCyclic ℤ`. The context holds `int_zsmul_eq_mul`, `AddSubgroup.mem_zmultiples_iff`, `AddSubgroup.ext`, `mem_intMultiples`, and core's `Int.mul_comm` and `Int.one_dvd`.
@description
Show that in `ℤ` the membership `x ∈ zmultiples n` is `n ∣ x`, that `zmultiples n = intMultiples n`, and that `ℤ` is cyclic.
-/

theorem mem_zmultiples_int {n x : ℤ} : x ∈ AddSubgroup.zmultiples n ↔ n ∣ x := by
  rw [AddSubgroup.mem_zmultiples_iff]
  constructor
  · intro ⟨k, hk⟩
    exact ⟨k, by rw [← hk, int_zsmul_eq_mul, Int.mul_comm]⟩
  · intro ⟨c, hc⟩
    exact ⟨c, by rw [int_zsmul_eq_mul, hc, Int.mul_comm]⟩

theorem zmultiples_eq_intMultiples (n : ℤ) : AddSubgroup.zmultiples n = intMultiples n := by
  apply AddSubgroup.ext
  intro x
  rw [mem_zmultiples_int, mem_intMultiples]

theorem isAddCyclic_int : IsAddCyclic ℤ :=
  ⟨1, fun x => mem_zmultiples_int.mpr (Int.one_dvd x)⟩

/-! @end -/

/-!
@problem zmod_cyclic
@title The Integers Modulo n Are Cyclic
@concept generated_subgroups

@preamble
The value of the multiple `k • 1` in `ZMod n` is `k % n`, with remainders added as in the first section; the value of the residue `1` is `1 % n` by definition. In `ZMod 6` the multiples of `2` are the even residues. The context holds `zero_nsmul`, `succ_nsmul`, `natCast_zsmul`, `ZMod.val_add`, `ZMod.val_zero`, `Fin.ext`, `Nat.mod_eq_of_lt`, `mod_add_mod_eq_add_mod`, `AddSubgroup.mem_zmultiples_iff`, `AddSubgroup.ext`, `mem_zmodSixEvens` and `zmod_six_two_zsmul_mem`.
@description
Show that the value of the multiple `k • (1 : ZMod n)` is `k % n` for every natural number `k`, that `ZMod n` is cyclic, and that `zmultiples 2 = zmodSixEvens` in `ZMod 6`.
-/

theorem ZMod.val_nsmul_one {n : ℕ} [NeZero n] (k : ℕ) : (k • (1 : ZMod n)).val = k % n := by
  induction k with
  | zero => rw [zero_nsmul, ZMod.val_zero]
  | succ k ih =>
    rw [succ_nsmul, ZMod.val_add, ih]
    change (k % n + 1 % n) % n = (k + 1) % n
    rw [mod_add_mod_eq_add_mod]

theorem isAddCyclic_zmod (n : ℕ) [NeZero n] : IsAddCyclic (ZMod n) := by
  apply Exists.intro 1
  intro x
  rw [AddSubgroup.mem_zmultiples_iff]
  apply Exists.intro (x.val : ℤ)
  rw [natCast_zsmul]
  apply Fin.ext
  rw [ZMod.val_nsmul_one, Nat.mod_eq_of_lt x.isLt]

theorem zmultiples_two_zmod_six : AddSubgroup.zmultiples (2 : ZMod 6) = zmodSixEvens := by
  apply AddSubgroup.ext
  intro x
  rw [AddSubgroup.mem_zmultiples_iff, mem_zmodSixEvens]
  constructor
  · intro ⟨k, hk⟩
    rw [← hk]
    exact zmod_six_two_zsmul_mem k
  · intro hx
    cases hx with
    | inl h => exact ⟨0, by rw [h]; decide⟩
    | inr h =>
      cases h with
      | inl h => exact ⟨1, by rw [h]; decide⟩
      | inr h => exact ⟨2, by rw [h]; decide⟩

/-! @end -/

end GroupTheory
