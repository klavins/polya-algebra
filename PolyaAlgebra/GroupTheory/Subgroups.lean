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

/-!
@concept subgroups
@title Subgroups
@kind definition

A subgroup is a subset of a group that is a group under the same operation: it contains the neutral element, and the product and the inverse of any of its elements. Centres, kernels and the subgroup an element generates are all subgroups, and Lagrange's theorem counts them. This concept writes the definition, builds three subgroups of the running examples, and makes a subgroup a type and a group.
-/

/-!
@problem subgroup
@title The Definition of a Subgroup
@concept subgroups

@preamble
A *subgroup* of `G` is a subset that is a group under the operation of `G`: it contains `𝟙`, the product of any two of its elements, and the inverse of each. The laws hold in the subset because they hold in `G`, so these three conditions are the whole definition.

In Lean a subgroup is a structure holding a set, `carrier`, and the three conditions as fields: `one_mem' : 𝟙 ∈ carrier`, `mul_mem' : ∀ {a b : G}, a ∈ carrier → b ∈ carrier → a ∗ b ∈ carrier` and `inv_mem' : ∀ {a : G}, a ∈ carrier → a⁻¹ ∈ carrier`, with the elements implicit, read off the proofs in `H.mul_mem' ha hb`. Writing `x ∈ H` for `x ∈ H.carrier` takes an instance of Lean's class
```lean
class Membership (α : Type u) (γ : Type v) where
  mem : γ → α → Prop
```
as Set Theory gave its sets one (Lean's own marks `α` an `outParam`, which changes nothing here); the collection comes first in `mem`, so the instance's function takes `H` before `x`. Mathlib builds `Subgroup` in two layers; this one is the textbook's.
@description
Define the structure `Subgroup G` with the four fields as the preamble states them, and supply the instance `Membership G (Subgroup G)`.
-/

structure Subgroup (G : Type u) [Group G] where
  carrier : Set G
  one_mem' : 𝟙 ∈ carrier
  mul_mem' : ∀ {a b : G}, a ∈ carrier → b ∈ carrier → a ∗ b ∈ carrier
  inv_mem' : ∀ {a : G}, a ∈ carrier → a⁻¹ ∈ carrier

instance {G : Type u} [Group G] : Membership G (Subgroup G) := ⟨fun H x => x ∈ H.carrier⟩

/-- @spec -/
example {G : Type u} [Group G] (H : Subgroup G) : Set G := H.carrier

/-- @spec -/
example {G : Type u} [Group G] (H : Subgroup G) : (𝟙 : G) ∈ H.carrier := H.one_mem'

/-- @spec -/
example {G : Type u} [Group G] (H : Subgroup G) (a b : G) (ha : a ∈ H.carrier)
    (hb : b ∈ H.carrier) : a ∗ b ∈ H.carrier :=
  @Subgroup.mul_mem' G _ H a b ha hb

/-- @spec -/
example {G : Type u} [Group G] (H : Subgroup G) (a : G) (ha : a ∈ H.carrier) :
    a⁻¹ ∈ H.carrier :=
  @Subgroup.inv_mem' G _ H a ha

/-- @spec -/
example {G : Type u} [Group G] (H : Subgroup G) (x : G) : x ∈ H ↔ x ∈ H.carrier := Iff.rfl

/-! @end -/

/-!
@problem rotations
@title The Rotations Form a Subgroup
@concept subgroups

@preamble
The rotations of the `n`-gon are a subgroup of Dₙ: the trivial rotation `r 𝟙`, with `𝟙` the neutral element of `ZMod n`, is `𝟙`, two rotations compose to a rotation, `r i ∗ r j = r (i ∗ j)`, and the inverse of a rotation is a rotation, `(r i)⁻¹ = r i⁻¹`, each by the definition of the instance; the numeral `0` of `ZMod n` is not `𝟙` by definition, and its instance is not in the context. The reflections are not a subgroup, since two reflections compose to a rotation. As a set the rotations are the range of the constructor `r`, `Set.range r`, whose membership `∃ i, r i = x` the first section took apart with `intro ⟨i, hi⟩`; a subgroup is built with `where`, the carrier first and then the three proofs, each a statement about members of the carrier. A reflection is not a rotation because the two constructors of an inductive type never agree: `cases h` on `h : r j = sr i` closes any goal, as it did on `sr i = 𝟙` in the previous section. The three conditions of a subgroup `H`, restated through `∈ H` as `H.one_mem`, `H.mul_mem ha hb` and `H.inv_mem ha`, are given in the context for the problems to come.
@description
Define `DihedralGroup.rotations n`, the subgroup of `DihedralGroup n` with carrier `Set.range DihedralGroup.r`, and show that `r i` belongs to it and `sr i` does not.
-/

/-- @given -/
theorem Subgroup.one_mem {G : Type u} [Group G] (H : Subgroup G) : 𝟙 ∈ H := H.one_mem'

/-- @given -/
theorem Subgroup.mul_mem {G : Type u} [Group G] (H : Subgroup G) {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) : a ∗ b ∈ H :=
  H.mul_mem' ha hb

/-- @given -/
theorem Subgroup.inv_mem {G : Type u} [Group G] (H : Subgroup G) {a : G} (ha : a ∈ H) : a⁻¹ ∈ H :=
  H.inv_mem' ha

def DihedralGroup.rotations (n : ℕ) [NeZero n] : Subgroup (DihedralGroup n) where
  carrier := Set.range DihedralGroup.r
  one_mem' := ⟨𝟙, rfl⟩
  mul_mem' := by
    intro a b ⟨i, hi⟩ ⟨j, hj⟩
    rw [← hi, ← hj]
    exact ⟨i ∗ j, rfl⟩
  inv_mem' := by
    intro a ⟨i, hi⟩
    rw [← hi]
    exact ⟨i⁻¹, rfl⟩

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
The multiples of a fixed integer `n` are a subgroup of `ℤ`, written `nℤ`: `0` is a multiple of `n`, so is a sum of two multiples, and so is the negative of one. A multiple of `n` is an `x` with `n ∣ x`, divisibility on `ℤ` as the first section met it on `ℕ`, and core Lean has the three facts as `Int.dvd_zero n : n ∣ 0`, `Int.dvd_add : n ∣ a → n ∣ b → n ∣ a + b` and `Int.dvd_neg : n ∣ -a ↔ n ∣ a`. On `ℤ` the operation is addition, so the goals `𝟙 ∈ carrier`, `a ∗ b ∈ carrier` and `a⁻¹ ∈ carrier` are the statements `n ∣ 0`, `n ∣ a + b` and `n ∣ -a` up to unfolding, which `exact` sees through. The equation `x ∈ intMultiples n ↔ n ∣ x`, which holds by definition, is what later proofs rewrite with; `2ℤ` is the subgroup of even integers, and `1ℤ` is all of `ℤ`.
@description
Define `intMultiples n`, the subgroup `nℤ` of `ℤ` with carrier `{x | n ∣ x}`, and prove `mem_intMultiples`, that `x ∈ intMultiples n ↔ n ∣ x`, which holds by definition.
-/

def intMultiples (n : ℤ) : Subgroup ℤ where
  carrier := {x | n ∣ x}
  one_mem' := Int.dvd_zero n
  mul_mem' := by
    intro a b ha hb
    exact Int.dvd_add ha hb
  inv_mem' := by
    intro a ha
    exact Int.dvd_neg.mpr ha

/-- @spec -/
example (n x : ℤ) : x ∈ intMultiples n ↔ n ∣ x := Iff.rfl

theorem mem_intMultiples {n x : ℤ} : x ∈ intMultiples n ↔ n ∣ x := Iff.rfl

/-! @end -/

/-!
@problem zmod_six_evens
@title The Even Residues Modulo 6
@concept subgroups

@preamble
In `ZMod 6` the residues `0`, `2` and `4` form a subgroup: the sum of two of them is one of them, as `2 ∗ 4 = 0` and `4 ∗ 4 = 2`, and the inverse of `2` is `4`. The carrier is the set `{0, 2, 4}`, written by listing its elements, and `x ∈ {0, 2, 4}` unfolds to `x = 0 ∨ x = 2 ∨ x = 4`. Each closure condition is a statement about finitely many elements of `ZMod 6`, which `decide` settles through the instances of the examples section, on the field as it stands and before any `intro`, since `decide` cannot run with a free `a` in the goal, as the symmetric groups concept noted; a hypothesis `a ∈ {0, 2, 4}` is decided like any other proposition about `a`. The equation `x ∈ zmodSixEvens ↔ x = 0 ∨ x = 2 ∨ x = 4`, which holds by definition, is how a later proof takes such a membership apart. The odd residues `1`, `3`, `5` are not a subgroup: `1 ∗ 1 = 2`.
@description
Define `zmodSixEvens`, the subgroup of `ZMod 6` with carrier `{0, 2, 4}`, and prove `mem_zmodSixEvens`, that `x ∈ zmodSixEvens ↔ x = 0 ∨ x = 2 ∨ x = 4`, which holds by definition.
-/

def zmodSixEvens : Subgroup (ZMod 6) where
  carrier := {0, 2, 4}
  one_mem' := by decide
  mul_mem' := by decide
  inv_mem' := by decide

/-- @spec -/
example : ∀ x : ZMod 6, x ∈ zmodSixEvens ↔ x = 0 ∨ x = 2 ∨ x = 4 := fun _ => Iff.rfl

theorem mem_zmodSixEvens (x : ZMod 6) : x ∈ zmodSixEvens ↔ x = 0 ∨ x = 2 ∨ x = 4 := Iff.rfl

/-! @end -/

/-!
@problem subgroup_as_type
@title A Subgroup as a Type
@concept subgroups

@preamble
A subgroup is to be a group in its own right, so its elements must form a type, and its carrier is a set, which stands where a type is expected as in the first section: `H.carrier` as a type, which Lean prints `↥H.carrier`, has as its elements the pairs `⟨x, hx⟩` of an `x : G` and a proof `hx : x ∈ H.carrier`, and for `a : H.carrier`, `(a : G)` is its element, printed `↑a`, with `a.2` the proof that it lies in the carrier, which is to say in `H`. Mathlib writes this type `↥H`; in this subject it is always written `H.carrier`.

One consequence is a count: the function `a ↦ (a : G)` from `H.carrier` to `G` is injective, Mathlib's `Subtype.val_injective`, so `H` has no more elements than `G`, by `Fintype.card_le_of_injective` as in the previous section. Counting `H.carrier` needs membership in it to be decidable, which `open Classical in` supplies, as it did for a quotient.
@description
Show that `(a : G) ∈ H` for every `a : H.carrier`, and that a subgroup of a finite group has at most as many elements as the group, `Fintype.card H.carrier ≤ Fintype.card G`, under `open Classical in`.
-/

theorem Subgroup.coe_mem {G : Type u} [Group G] {H : Subgroup G} (a : H.carrier) : (a : G) ∈ H :=
  a.2

open Classical in
theorem Subgroup.card_le_card_group {G : Type u} [Group G] [Fintype G] (H : Subgroup G) :
    Fintype.card H.carrier ≤ Fintype.card G :=
  Fintype.card_le_of_injective (fun a : H.carrier => (a : G)) Subtype.val_injective

/-! @end -/

/-!
@problem subgroup_group
@title A Subgroup is a Group
@concept subgroups

@preamble
With its elements as the type `H.carrier`, a subgroup `H` is a group under the operation of `G`: the product of two elements of `H` is their product in `G`, paired with the proof, from `H.mul_mem`, that it lies in `H`, and the neutral element and the inverse are built the same way from `H.one_mem` and `H.inv_mem`, so the three conditions of the definition are what the instance is built from. Each law is an equation between two elements of the subtype, which holds as soon as their elements of `G` are equal: Mathlib's `Subtype.ext : (a : G) = b → a = b`, as `Fin.ext` for `Fin n`. The equations `((a ∗ b : H.carrier) : G) = (a : G) ∗ (b : G)`, `((𝟙 : H.carrier) : G) = 𝟙` and `((a⁻¹ : H.carrier) : G) = (a : G)⁻¹` hold by definition, and later proofs rewrite with them. In the first, both factors on the right are taken into `G` before they are multiplied; written `a ∗ b`, the product would be formed in `H.carrier` and taken into `G` afterwards, and the equation would say nothing.
@description
Supply the instance `Group H.carrier` for a subgroup `H` of `G`, and prove the three equations `Subgroup.coe_mul`, `Subgroup.coe_one` and `Subgroup.coe_inv`, each of which holds by definition.
-/

instance {G : Type u} [Group G] (H : Subgroup G) : Group H.carrier where
  mul a b := ⟨a.1 ∗ b.1, H.mul_mem a.2 b.2⟩
  one := ⟨𝟙, H.one_mem⟩
  inv a := ⟨a.1⁻¹, H.inv_mem a.2⟩
  mul_assoc a b c := Subtype.ext (mul_assoc a.1 b.1 c.1)
  one_mul a := Subtype.ext (one_mul a.1)
  mul_one a := Subtype.ext (mul_one a.1)
  inv_mul_cancel a := Subtype.ext (inv_mul_cancel a.1)
  mul_inv_cancel a := Subtype.ext (mul_inv_cancel a.1)

/-- @spec -/
example {G : Type u} [Group G] {H : Subgroup G} (a b : H.carrier) :
    ((a ∗ b : H.carrier) : G) = (a : G) ∗ (b : G) ∧ ((𝟙 : H.carrier) : G) = 𝟙 ∧
    ((a⁻¹ : H.carrier) : G) = (a : G)⁻¹ :=
  ⟨rfl, rfl, rfl⟩

theorem Subgroup.coe_mul {G : Type u} [Group G] {H : Subgroup G} (a b : H.carrier) :
    ((a ∗ b : H.carrier) : G) = (a : G) ∗ (b : G) := rfl

theorem Subgroup.coe_one {G : Type u} [Group G] {H : Subgroup G} : ((𝟙 : H.carrier) : G) = 𝟙 := rfl

theorem Subgroup.coe_inv {G : Type u} [Group G] {H : Subgroup G} (a : H.carrier) :
    ((a⁻¹ : H.carrier) : G) = (a : G)⁻¹ := rfl

/-! @end -/

/--
@problem subgroup_ext
@title Two Subgroups With the Same Elements Are Equal
@concept subgroups

@preamble
A subgroup is determined by its elements: two subgroups with the same members are equal, as two sets are, because the proofs of the three conditions make no difference to equality. This is how every equation between subgroups is proved from here on, Mathlib's `Subgroup.ext`: `apply Subgroup.ext`, then `intro x`, then a statement about one element.

A structure is opened into its fields by `cases H with | mk c _ _ _ =>`, naming the carrier and leaving the proofs unnamed, as `ZMod.ext` was proved in the examples section. The two carriers are then sets with the same members, equal by `Set.ext`; once they are identified, the two sides differ only in their proofs of the three conditions, and two proofs of one proposition are equal in Lean, so nothing remains to check.
@description
Show that two subgroups `H` and `K` with `x ∈ H ↔ x ∈ K` for every `x` are equal.
-/
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
Every group has two subgroups at once: the whole group, and `{𝟙}`, with the neutral element alone, the *trivial subgroup*. Mathlib writes them `⊤` and `⊥` (typed `\top` and `\bot`), the top and the bottom of the subgroups ordered by inclusion, through the notation class
```lean
class Top (α : Type u) where
  top : α
```
and `Bot`, the same with the field `bot`; each is built as `⟨…⟩` with the subgroup inside it written `{ carrier := …, one_mem' := …, … }`. The carrier of `⊤` is `Set.univ`, the set of all elements, with `Set.mem_univ x : x ∈ Set.univ`; the carrier of `⊥` is the singleton `{𝟙}`, with `Set.mem_singleton 𝟙 : 𝟙 ∈ {𝟙}` and `Set.mem_singleton_iff : x ∈ {a} ↔ x = a`, which turns a hypothesis `ha : a ∈ {𝟙}` into the equation `a = 𝟙` that `rw` can use. The memberships `x ∈ ⊤`, always, and `x ∈ ⊥ ↔ x = 𝟙`, the second by definition, are what later proofs use, under Mathlib's names. The context holds `one_mul` and `inv_one`.
@description
Supply the instances `Top (Subgroup G)` and `Bot (Subgroup G)`, and prove `Subgroup.mem_top`, that every `x` is in `⊤`, and `Subgroup.mem_bot`, that `x ∈ ⊥ ↔ x = 𝟙`.
-/

instance {G : Type u} [Group G] : Top (Subgroup G) :=
  ⟨{ carrier := Set.univ
     one_mem' := Set.mem_univ 𝟙
     mul_mem' := fun _ _ => Set.mem_univ _
     inv_mem' := fun _ => Set.mem_univ _ }⟩

instance {G : Type u} [Group G] : Bot (Subgroup G) :=
  ⟨{ carrier := {𝟙}
     one_mem' := Set.mem_singleton 𝟙
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
example {G : Type u} [Group G] (x : G) : x ∈ (⊥ : Subgroup G) ↔ x = 𝟙 := Iff.rfl

theorem Subgroup.mem_top {G : Type u} [Group G] (x : G) : x ∈ (⊤ : Subgroup G) := Set.mem_univ x

theorem Subgroup.mem_bot {G : Type u} [Group G] {x : G} : x ∈ (⊥ : Subgroup G) ↔ x = 𝟙 := Iff.rfl

/-! @end -/

/-!
@problem subgroup_le
@title Inclusion of Subgroups
@concept subgroups

@preamble
Subgroups are compared by inclusion: `H ≤ K` when every element of `H` is in `K`. So `⊥` is the smallest subgroup and `⊤` the largest, and since a subgroup is determined by its elements, `H ≤ K` and `K ≤ H` force `H = K`. The symbol comes from Lean's class `LE`, with the one field `le`, and `H ≤ K` is defined as `∀ ⦃x⦄, x ∈ H → x ∈ K`, with the strict implicit binder of `Function.Injective`: for `h : H ≤ K` and `hx : x ∈ H` the term `h hx` proves `x ∈ K`, and a goal `H ≤ K` opens on `intro x hx`. Mathlib's names for these facts, on any ordered type, are `bot_le`, `le_top` and `le_antisymm`; here they are proved for subgroups under those names. The context holds `Subgroup.mem_bot`, `Subgroup.mem_top`, `Subgroup.one_mem` and `Subgroup.ext`.
@description
Supply the instance `LE (Subgroup G)` with `H ≤ K` as `∀ ⦃x⦄, x ∈ H → x ∈ K`; show that `⊥ ≤ H` and `H ≤ ⊤` for every subgroup `H`; and show that `H ≤ K` and `K ≤ H` give `H = K`.
-/

instance {G : Type u} [Group G] : LE (Subgroup G) := ⟨fun H K => ∀ ⦃x⦄, x ∈ H → x ∈ K⟩

/-- @spec -/
example {G : Type u} [Group G] (H K : Subgroup G) : H ≤ K ↔ ∀ x, x ∈ H → x ∈ K := Iff.rfl

theorem Subgroup.bot_le {G : Type u} [Group G] (H : Subgroup G) : ⊥ ≤ H := by
  intro x hx
  rw [Subgroup.mem_bot] at hx
  rw [hx]
  exact H.one_mem

theorem Subgroup.le_top {G : Type u} [Group G] (H : Subgroup G) : H ≤ ⊤ := by
  intro x _
  exact Subgroup.mem_top x

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
A subgroup closed under products is closed under powers: `g ^ n ∈ H` whenever `g ∈ H`, by induction on `n`, since `g ^ (n + 1)` is `g ^ n ∗ g`; and then `g ^ k ∈ H` for every integer `k`, by the two cases of an integer, a negative power being the inverse of a natural one. So a subgroup containing `g` contains every power of `g`. In `ZMod 6` every integer power of `2` is `0`, `2` or `4`: the general fact applied to the subgroup of even residues, once `2` is seen to be in it, which `decide` checks after the membership is rewritten into the disjunction it stands for. The context holds `pow_zero`, `pow_succ` and `zpow_negSucc` of the previous section, and `mem_zmodSixEvens`; it does not hold `zpow_add_one` and `zpow_sub_one`, so the integer case is a `cases` on `k` and not an induction, and for `Int.ofNat n` the power `g ^ Int.ofNat n` is `g ^ n` by definition, which `exact` sees through.
@description
Show that `g ^ n ∈ H` for every natural number `n`, and `g ^ k ∈ H` for every integer `k`, whenever `g ∈ H`, under Mathlib's names `Subgroup.pow_mem` and `Subgroup.zpow_mem`; and conclude that `2 ^ k ∈ zmodSixEvens` for every integer `k`.
-/

theorem Subgroup.pow_mem {G : Type u} [Group G] (H : Subgroup G) {g : G} (hg : g ∈ H) (n : ℕ) :
    g ^ n ∈ H := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact H.one_mem
  | succ n ih =>
    rw [pow_succ]
    exact H.mul_mem ih hg

theorem Subgroup.zpow_mem {G : Type u} [Group G] (H : Subgroup G) {g : G} (hg : g ∈ H) (k : ℤ) :
    g ^ k ∈ H := by
  cases k with
  | ofNat n => exact H.pow_mem hg n
  | negSucc n =>
    rw [zpow_negSucc]
    exact H.inv_mem (H.pow_mem hg (n + 1))

theorem zmod_six_two_zpow_mem (k : ℤ) : (2 : ZMod 6) ^ k ∈ zmodSixEvens := by
  apply zmodSixEvens.zpow_mem
  rw [mem_zmodSixEvens]
  decide

/-! @end -/

/-!
@concept centre
@title The Centre
@kind definition

The centre of a group is the set of elements that commute with every element. It is a subgroup, and it is the whole group exactly when the group is commutative, so it measures how far a group is from commutative: trivial in D₃, two elements in D₄, everything in `ℤ`. The subject's goal, that a group of order `p²` is commutative, is proved by showing that its centre is large.
-/

/-!
@problem center
@title The Centre of a Group
@concept centre

@preamble
The *centre* of `G` is the set of elements that commute with every element of `G`, `{z | ∀ g, g ∗ z = z ∗ g}`, Mathlib's `Subgroup.center G`. It is a subgroup: `𝟙` commutes with everything; if `a` and `b` commute with `g`, so does `a ∗ b`, by moving `g` across one factor at a time; and if `a` commutes with every element, so does `a⁻¹`, since an equation between two elements still holds after both of its sides are inverted, and the inverse of a product is known. A hypothesis `ha : a ∈ {z | ∀ g, …}` is the statement it abbreviates, so `ha g` is the equation for `g`, and a goal `a ∗ b ∈ {z | ∀ g, …}` opens on `intro g`. The equation `z ∈ center G ↔ ∀ g, g ∗ z = z ∗ g` holds by definition and is the form later proofs rewrite with. The context holds `mul_inv_rev` and `inv_inv`.
@description
Define `Subgroup.center G`, the centre of `G`, as the subgroup with carrier `{z | ∀ g, g ∗ z = z ∗ g}`, and prove `Subgroup.mem_center_iff`, which holds by definition.
-/

def Subgroup.center (G : Type u) [Group G] : Subgroup G where
  carrier := {z | ∀ g, g ∗ z = z ∗ g}
  one_mem' := by
    intro g
    rw [mul_one, one_mul]
  mul_mem' := by
    intro a b ha hb g
    rw [← mul_assoc, ha g, mul_assoc, hb g, ← mul_assoc]
  inv_mem' := by
    intro a ha g
    have h : (g⁻¹ ∗ a)⁻¹ = (a ∗ g⁻¹)⁻¹ := by
      rw [ha g⁻¹]
    rw [mul_inv_rev, mul_inv_rev, inv_inv] at h
    exact h.symm

/-- @spec -/
example {G : Type u} [Group G] (z : G) : z ∈ Subgroup.center G ↔ ∀ g, g ∗ z = z ∗ g := by
  constructor
  · intro h g
    have h' := h g
    grind
  · intro h g
    have h' := h g
    grind

theorem Subgroup.mem_center_iff {G : Type u} [Group G] {z : G} :
    z ∈ Subgroup.center G ↔ ∀ g, g ∗ z = z ∗ g := Iff.rfl

/-! @end -/

/-!
@problem center_eq_top
@title The Centre of a Commutative Group
@concept centre

@preamble
The centre is the whole group exactly when every pair of elements commutes: the two subgroups have the same members exactly when every element commutes with every other. So a commutative group is its own centre, and the integers are: `center ℤ = ⊤`. Read the other way, the equivalence says that a group with two elements that do not commute has a centre smaller than the whole group. A hypothesis `h : center G = ⊤` is an equation between subgroups, and `rw` uses it as it uses any equation. The context holds `Subgroup.ext`, `Subgroup.mem_top`, `Subgroup.mem_center_iff` and `mul_comm`.
@description
Show that `center G = ⊤` exactly when `a ∗ b = b ∗ a` for all `a` and `b`; that the centre of a commutative group is `⊤`; and that `center ℤ = ⊤`.
-/

theorem Subgroup.center_eq_top_iff {G : Type u} [Group G] :
    Subgroup.center G = ⊤ ↔ ∀ a b : G, a ∗ b = b ∗ a := by
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

theorem Subgroup.center_eq_top {G : Type u} [CommGroup G] : Subgroup.center G = ⊤ :=
  Subgroup.center_eq_top_iff.mpr mul_comm

theorem center_int : Subgroup.center ℤ = ⊤ :=
  Subgroup.center_eq_top

/-! @end -/

/-!
@problem center_dihedral
@title The Centres of D₃ and D₄
@concept centre

@preamble
In D₃, the triangle, nothing but `𝟙` commutes with every symmetry: its centre is `⊥`. In D₄, the square, the half turn `r 2` commutes with everything, since turning the square halfway round and then reflecting it is reflecting it and then turning it halfway round, and nothing else does but `𝟙`: the centre is `{𝟙, r 2}`, that is, `r 0` and `r 2`; and since D₄ is not commutative, its centre is not `⊤`, by the previous problem's equivalence and `d4_not_comm` of the examples section. The first two are statements about finitely many elements, but `decide` fails on them as they stand, with `failed to synthesize Decidable`, since it cannot see inside `Subgroup.center` or `⊥`; each membership is first rewritten into what it says, under the `∀` that a statement about every element carries, as `simp only` unfolded the table under its binders in the examples section. The centre of D₄ is stated element by element, as a membership. D₃ stands in for the symmetric group on three points, whose centre is trivial too. The context holds `Subgroup.ext`, `Subgroup.mem_center_iff`, `Subgroup.mem_bot`, `Subgroup.center_eq_top_iff` and `d4_not_comm`.
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

The intersection of two subgroups is a subgroup, and so is the intersection of any family of them, so any two subgroups have a greatest subgroup below both. The intersection of all the subgroups containing a set is the smallest subgroup containing it, which is how the subgroup generated by a set is defined.
-/

/-!
@problem inf
@title The Intersection of Two Subgroups
@concept intersections

@preamble
Two subgroups `H` and `K` meet in a subgroup: `𝟙` is in both, a product of two elements of both is in both, and so is an inverse, each by the condition of `H` and the condition of `K`. Mathlib writes the intersection `H ⊓ K` (typed `\glb`), through the class
```lean
class Min (α : Type u) where
  min : α → α → α
```
The carrier is `H.carrier ∩ K.carrier`, and `x ∈ H ⊓ K ↔ x ∈ H ∧ x ∈ K` holds by definition, with `ha.1` and `ha.2` the two halves of a membership `ha`. The intersection is the greatest subgroup below both: it lies below `H` and below `K`, and above every subgroup that lies below both, Mathlib's `inf_le_left`, `inf_le_right` and `le_inf`. In `ℤ`, the multiples of `2` that are multiples of `3` are the multiples of `6`: `2ℤ ⊓ 3ℤ = 6ℤ`; `omega` decides divisibility by a numeral. The context holds `Subgroup.ext` and `mem_intMultiples`.
@description
Supply the instance `Min (Subgroup G)` with `H ⊓ K` the subgroup with carrier `H.carrier ∩ K.carrier`; prove `Subgroup.mem_inf`, which holds by definition; show that `H ⊓ K` lies below `H` and below `K`, and above every subgroup that lies below both; and show that `intMultiples 2 ⊓ intMultiples 3 = intMultiples 6`.
-/

instance {G : Type u} [Group G] : Min (Subgroup G) :=
  ⟨fun H K =>
    { carrier := H.carrier ∩ K.carrier
      one_mem' := ⟨H.one_mem, K.one_mem⟩
      mul_mem' := fun ha hb => ⟨H.mul_mem ha.1 hb.1, K.mul_mem ha.2 hb.2⟩
      inv_mem' := fun ha => ⟨H.inv_mem ha.1, K.inv_mem ha.2⟩ }⟩

/-- @spec -/
example {G : Type u} [Group G] (H K : Subgroup G) (x : G) : x ∈ H ⊓ K ↔ x ∈ H ∧ x ∈ K := Iff.rfl

theorem Subgroup.mem_inf {G : Type u} [Group G] {H K : Subgroup G} {x : G} :
    x ∈ H ⊓ K ↔ x ∈ H ∧ x ∈ K := Iff.rfl

theorem Subgroup.inf_le_left {G : Type u} [Group G] (H K : Subgroup G) : H ⊓ K ≤ H := by
  intro x hx
  exact hx.1

theorem Subgroup.inf_le_right {G : Type u} [Group G] (H K : Subgroup G) : H ⊓ K ≤ K := by
  intro x hx
  exact hx.2

theorem Subgroup.le_inf {G : Type u} [Group G] {H K L : Subgroup G} (h₁ : L ≤ H) (h₂ : L ≤ K) :
    L ≤ H ⊓ K := by
  intro x hx
  exact ⟨h₁ hx, h₂ hx⟩

theorem intMultiples_two_inf_three : intMultiples 2 ⊓ intMultiples 3 = intMultiples 6 := by
  apply Subgroup.ext
  intro x
  rw [Subgroup.mem_inf, mem_intMultiples, mem_intMultiples, mem_intMultiples]
  omega

/-! @end -/

/-!
@problem s_inf
@title The Intersection of a Family of Subgroups
@concept intersections

@preamble
The intersection of any set `S` of subgroups, not only of two, is a subgroup: an element of the intersection lies in every `H ∈ S`, and each condition holds in the intersection because it holds in each `H`. Mathlib writes it `sInf S`, the greatest lower bound of a set, through the class
```lean
class InfSet (α : Type u) where
  sInf : Set α → α
```
The carrier is `{x | ∀ H ∈ S, x ∈ H}`, where `∀ H ∈ S, …` abbreviates `∀ H, H ∈ S → …`, so a membership in it is a function of a subgroup `H` and a proof `hH : H ∈ S`. The intersection lies below every member of `S`, and above every subgroup that lies below all of them: `sInf_le` and `le_sInf` in Mathlib, which say that it is the greatest lower bound. For the two-element set `{H, K}`, whose membership `L ∈ {H, K}` unfolds to `L = H ∨ L = K` as for `{0, 2, 4}`, it is `H ⊓ K`, Mathlib's `sInf_pair`. The context holds `Subgroup.mem_inf`.
@description
Supply the instance `InfSet (Subgroup G)`; prove `Subgroup.mem_sInf`, that `x ∈ sInf S ↔ ∀ H ∈ S, x ∈ H`, which holds by definition; show that `sInf S ≤ H` for every `H ∈ S`, and that `K ≤ sInf S` whenever `K ≤ H` for every `H ∈ S`; and show that `x ∈ sInf {H, K} ↔ x ∈ H ⊓ K`.
-/

instance {G : Type u} [Group G] : InfSet (Subgroup G) :=
  ⟨fun S =>
    { carrier := {x | ∀ H ∈ S, x ∈ H}
      one_mem' := fun H _ => H.one_mem
      mul_mem' := fun ha hb H hH => H.mul_mem (ha H hH) (hb H hH)
      inv_mem' := fun ha H hH => H.inv_mem (ha H hH) }⟩

/-- @spec -/
example {G : Type u} [Group G] (S : Set (Subgroup G)) (x : G) :
    x ∈ sInf S ↔ ∀ H ∈ S, x ∈ H := Iff.rfl

theorem Subgroup.mem_sInf {G : Type u} [Group G] {S : Set (Subgroup G)} {x : G} :
    x ∈ sInf S ↔ ∀ H ∈ S, x ∈ H := Iff.rfl

theorem Subgroup.sInf_le {G : Type u} [Group G] {S : Set (Subgroup G)} {H : Subgroup G}
    (h : H ∈ S) : sInf S ≤ H := by
  intro x hx
  exact hx H h

theorem Subgroup.le_sInf {G : Type u} [Group G] {S : Set (Subgroup G)} {K : Subgroup G}
    (h : ∀ H ∈ S, K ≤ H) : K ≤ sInf S := by
  intro x hx H hH
  exact h H hH hx

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

The subgroup generated by a set is the smallest subgroup containing it, and the subgroup generated by one element is the set of its powers. A group generated by one element is cyclic: the integers, and the integers modulo `n`, each generated by `1`. Cyclic groups are the simplest groups, and the subgroup an element generates is what Lagrange's theorem counts to bound the order of the element.
-/

/-!
@problem closure
@title The Subgroup Generated by a Set
@concept generated_subgroups

@preamble
The subgroup *generated* by a set `X` is the smallest subgroup containing `X`: the intersection of all the subgroups that contain `X`, `sInf {H | X ⊆ H.carrier}`, Mathlib's `Subgroup.closure X`, the *closure* of `X`, since it is `X` closed up under the three operations. The intersection contains `X`, since each subgroup in the family does, and it lies below every subgroup `H` containing `X`, since `H` is in the family. Together, `closure X ≤ H` exactly when `X ⊆ H.carrier`, which is what makes it the smallest. A membership `x ∈ closure X` is, by definition, `∀ H : Subgroup G, X ⊆ H.carrier → x ∈ H`, a function of a subgroup and a proof that it contains `X`, and the previous problem's `Subgroup.mem_sInf` says so already, up to unfolding. `X ⊆ H.carrier` is `∀ ⦃a⦄, a ∈ X → a ∈ H.carrier`, so `h hx` for `hx : x ∈ X` proves `x ∈ H.carrier`, which is `x ∈ H` up to unfolding; `change` restates one as the other, and `rw` sees only what is written. The context holds `Subgroup.mem_sInf` and `Subgroup.sInf_le`, and not `le_sInf`.
@description
Define `Subgroup.closure X` as the intersection of the subgroups containing `X`; prove `Subgroup.mem_closure`, which holds by definition; and show `Subgroup.subset_closure`, that `X ⊆ (closure X).carrier`, and `Subgroup.closure_le`, that `closure X ≤ H ↔ X ⊆ H.carrier`.
-/

def Subgroup.closure {G : Type u} [Group G] (X : Set G) : Subgroup G := sInf {H | X ⊆ H.carrier}

/-- @spec -/
example {G : Type u} [Group G] (X : Set G) : Subgroup.closure X = sInf {H | X ⊆ H.carrier} := rfl

theorem Subgroup.mem_closure {G : Type u} [Group G] {X : Set G} {x : G} :
    x ∈ Subgroup.closure X ↔ ∀ H : Subgroup G, X ⊆ H.carrier → x ∈ H :=
  Subgroup.mem_sInf

theorem Subgroup.subset_closure {G : Type u} [Group G] {X : Set G} :
    X ⊆ (Subgroup.closure X).carrier := by
  intro x hx
  change x ∈ Subgroup.closure X
  rw [Subgroup.mem_closure]
  intro H hH
  exact hH hx

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
The powers of one element `g`, with every integer as exponent, form a subgroup: `𝟙 = g ^ 0`, `g ^ k ∗ g ^ l = g ^ (k + l)` and `(g ^ k)⁻¹ = g ^ (-k)`, the laws of integer powers of the previous section. Mathlib writes it `Subgroup.zpowers g`, and its carrier is `{x | ∃ k : ℤ, g ^ k = x}`, so a membership is taken apart by `intro ⟨k, hk⟩` and proved by a witness, `⟨k + l, _⟩`. In `ℤ` it is the multiples of `g`. The element generates its own subgroup, `g ∈ zpowers g`, as `g ^ 1`. The context holds `zpow_zero`, `zpow_one`, `zpow_add` and `zpow_neg`.
@description
Define `Subgroup.zpowers g`; prove `Subgroup.mem_zpowers_iff`, that `x ∈ zpowers g ↔ ∃ k : ℤ, g ^ k = x`, which holds by definition; and show that `g ∈ zpowers g`.
-/

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

theorem Subgroup.mem_zpowers_iff {G : Type u} [Group G] {g x : G} :
    x ∈ Subgroup.zpowers g ↔ ∃ k : ℤ, g ^ k = x := Iff.rfl

theorem Subgroup.mem_zpowers {G : Type u} [Group G] (g : G) : g ∈ Subgroup.zpowers g :=
  ⟨1, zpow_one g⟩

/-! @end -/

/--
@problem zpowers_eq_closure
@title The Subgroup Generated by One Element Is Its Powers
@concept generated_subgroups

@preamble
The subgroup generated by the set `{g}` and the subgroup of powers of `g` are the same subgroup, Mathlib's `Subgroup.zpowers_eq_closure`. Each contains the other: a subgroup that contains `g` contains all of its powers, and `zpowers g` is itself a subgroup containing `g`. The set `{g}` is a singleton, with `Set.mem_singleton g : g ∈ {g}` and `Set.mem_singleton_iff : x ∈ {g} ↔ x = g`, as for `⊥`. So the smallest subgroup containing `g` is the one built from `g` by multiplying and inverting, which justifies calling `zpowers g` the subgroup generated by `g`. The context holds `Subgroup.le_antisymm`, `Subgroup.zpow_mem`, `Subgroup.subset_closure`, `Subgroup.closure_le`, `Subgroup.mem_zpowers_iff` and `Subgroup.mem_zpowers`.
@description
Show that `zpowers g = closure {g}`.
-/
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
A group is *cyclic* when a single element generates it: some `g` with every `x` in `zpowers g`, Mathlib's `IsCyclic G`, which it states as the surjectivity of `k ↦ g ^ k`. A cyclic group is commutative, since any two of its elements are powers of the one generator, and two powers of one element commute; core Lean has `Int.add_comm`. `IsCyclic G` is a proposition with a name, a `def` into `Prop` as `IsOfFinOrder` was, so a proof of it is a witness with a function, `⟨g, fun x => …⟩`, and `obtain ⟨g, hg⟩ := h` opens a hypothesis `h : IsCyclic G`. The context holds `zpow_add` and `Subgroup.mem_zpowers_iff`.
@description
Define `IsCyclic G` as `∃ g : G, ∀ x, x ∈ Subgroup.zpowers g`, and show that in a cyclic group `a ∗ b = b ∗ a`.
-/

def IsCyclic (G : Type u) [Group G] : Prop := ∃ g : G, ∀ x, x ∈ Subgroup.zpowers g

/-- @spec -/
example {G : Type u} [Group G] : IsCyclic G ↔ ∃ g : G, ∀ x, ∃ k : ℤ, g ^ k = x := by
  constructor
  · intro ⟨g, hg⟩
    exact ⟨g, fun x => by obtain ⟨k, hk⟩ := hg x; exact ⟨k, by grind⟩⟩
  · intro ⟨g, hg⟩
    exact ⟨g, fun x => by obtain ⟨k, hk⟩ := hg x; exact ⟨k, by grind⟩⟩

theorem IsCyclic.mul_comm {G : Type u} [Group G] (h : IsCyclic G) (a b : G) : a ∗ b = b ∗ a := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
  rw [← hk, ← hl, ← zpow_add, ← zpow_add, Int.add_comm]

/-! @end -/

/-!
@problem int_cyclic
@title The Integers Are Cyclic
@concept generated_subgroups

@preamble
In `ℤ` a power is a multiple: `n ^ k = n * k` for all integers `n` and `k`, as `1 ^ k = k` was for natural `k` in the previous section, by the induction over the integers in both directions, with `zpow_add_one` and `zpow_sub_one` for the two steps and `Int.mul_zero`, `Int.mul_add`, `Int.mul_sub`, `Int.mul_one` and `Int.sub_eq_add_neg` for the arithmetic. So the powers of `n` are its multiples, `x ∈ zpowers n ↔ n ∣ x`, where a proof of `n ∣ x` is a `c` with `x = n * c`, as on `ℕ`; and `zpowers n` is the subgroup `nℤ` of the first concept: the subgroups `nℤ` are the cyclic subgroups of `ℤ`. With `n = 1`, every integer is a power of `1`, since `1` divides everything, `Int.one_dvd x`: `ℤ` is cyclic, generated by `1`. The context holds `zpow_zero`, `zpow_add_one`, `zpow_sub_one`, `int_mul_eq_add`, `int_one_eq_zero`, `int_inv_eq_neg`, `Subgroup.mem_zpowers_iff`, `Subgroup.ext` and `mem_intMultiples`.
@description
Show that `n ^ k = n * k` in `ℤ`; that `x ∈ zpowers n ↔ n ∣ x`; that `zpowers n = intMultiples n`; and that `ℤ` is cyclic.
-/

theorem int_zpow_eq_mul (n k : ℤ) : n ^ k = n * k := by
  induction k with
  | zero => rw [zpow_zero, int_one_eq_zero, Int.mul_zero]
  | succ k ih => rw [zpow_add_one, ih, int_mul_eq_add, Int.mul_add, Int.mul_one]
  | pred k ih =>
    rw [zpow_sub_one, ih, int_mul_eq_add, int_inv_eq_neg, Int.mul_sub, Int.mul_one,
      Int.sub_eq_add_neg]

theorem mem_zpowers_int {n x : ℤ} : x ∈ Subgroup.zpowers n ↔ n ∣ x := by
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · intro ⟨k, hk⟩
    exact ⟨k, by rw [← hk, int_zpow_eq_mul]⟩
  · intro ⟨c, hc⟩
    exact ⟨c, by rw [int_zpow_eq_mul, hc]⟩

theorem zpowers_eq_intMultiples (n : ℤ) : Subgroup.zpowers n = intMultiples n := by
  apply Subgroup.ext
  intro x
  rw [mem_zpowers_int, mem_intMultiples]

theorem isCyclic_int : IsCyclic ℤ :=
  ⟨1, fun x => mem_zpowers_int.mpr (Int.one_dvd x)⟩

/-! @end -/

/-!
@problem zmod_cyclic
@title The Integers Modulo n Are Cyclic
@concept generated_subgroups

@preamble
The numeral `1` of `ZMod n` is the residue `1`, not the neutral element `𝟙`, which is `0`; its value is `1 % n` by definition, which a `change` makes visible. `ZMod n` is cyclic, generated by it: the power `1 ^ k` has the value `k % n`, by induction on `k`, with `ZMod.val_mul` unfolding each product, `ZMod.val_one` giving `𝟙` its value, and the first section's `mod_add_mod_eq_add_mod` adding remainders. Every residue `x` is then `1 ^ x.val`. In `ZMod 6` the powers of `2` are the even residues, `zpowers 2 = zmodSixEvens`: each power is even by `zmod_six_two_zpow_mem`, and each even residue is itself a power of `2`, which `decide` checks once the exponent is named. The context holds `pow_zero`, `pow_succ`, `Nat.zero_mod`, `ZMod.ext`, `Nat.mod_eq_of_lt`, `zpow_natCast`, which reads an exponent `(m : ℤ)` as the natural one, `Subgroup.mem_zpowers_iff`, `mem_zmodSixEvens` and `Subgroup.ext`.
@description
Show that `((1 : ZMod n) ^ k).val = k % n` for every natural number `k`; that `ZMod n` is cyclic; and that `zpowers (2 : ZMod 6) = zmodSixEvens`.
-/

theorem ZMod.val_one_pow {n : ℕ} [NeZero n] (k : ℕ) : ((1 : ZMod n) ^ k).val = k % n := by
  induction k with
  | zero => rw [pow_zero, ZMod.val_one, Nat.zero_mod]
  | succ k ih =>
    rw [pow_succ, ZMod.val_mul, ih]
    change (k % n + 1 % n) % n = (k + 1) % n
    rw [mod_add_mod_eq_add_mod]

theorem isCyclic_zmod (n : ℕ) [NeZero n] : IsCyclic (ZMod n) := by
  apply Exists.intro 1
  intro x
  rw [Subgroup.mem_zpowers_iff]
  apply Exists.intro (x.val : ℤ)
  apply ZMod.ext
  rw [zpow_natCast, ZMod.val_one_pow, Nat.mod_eq_of_lt x.val_lt]

theorem zpowers_two_zmod_six : Subgroup.zpowers (2 : ZMod 6) = zmodSixEvens := by
  apply Subgroup.ext
  intro x
  rw [Subgroup.mem_zpowers_iff, mem_zmodSixEvens]
  constructor
  · intro ⟨k, hk⟩
    rw [← hk]
    exact zmod_six_two_zpow_mem k
  · intro hx
    cases hx with
    | inl h => exact ⟨0, by rw [h]; decide⟩
    | inr h =>
      cases h with
      | inl h => exact ⟨1, by rw [h]; decide⟩
      | inr h => exact ⟨2, by rw [h]; decide⟩

/-! @end -/

end GroupTheory
