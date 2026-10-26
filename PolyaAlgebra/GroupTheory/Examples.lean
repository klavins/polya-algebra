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
import PolyaAlgebra.GroupTheory.Groups

/-! @section Examples -/

universe u v

namespace GroupTheory

set_option linter.translateGenerateName false

/-!
@concept integers_mod_n
@title The Integers Modulo n
@kind definition

The integers modulo `n` are the remainders `0, …, n - 1`, added by adding and reducing. They are the commutative finite groups every course computes in: one for each `n`, among them a group of each prime order. They are built from the remainders, their addition is shown to satisfy the group laws, and the integers modulo 2 are matched with the group of order two.
-/

/-!
@problem zmod
@title The Integers Modulo n
@concept integers_mod_n

@preamble
The first section showed that the classes of congruence modulo `n` correspond to the remainders `0, …, n - 1`, and met Lean's `Fin n`, whose elements are those remainders. Lean already adds and negates them modulo `n`; trimmed, its definitions are
```lean
structure Fin (n : ℕ) where
  val : ℕ
  isLt : val < n
-- a + b is ⟨(a.val + b.val) % n, _⟩, and -a is ⟨(n - a.val) % n, _⟩
-- a numeral k is ⟨k % n, _⟩, which needs n ≠ 0
```
so `fin_four_add_neg` of the first section was already arithmetic modulo `4`. The integers modulo `n` are `Fin n` under Mathlib's name for them, `ZMod n`; Mathlib's `ZMod 0` is `ℤ`, and here `n` is always positive. An `abbrev` is a definition that Lean treats as its body when it looks for instances, so `ZMod n` has the numerals, `+`, `-`, decidable equality and count of `Fin n`. The equations that read the values back hold by definition.
@description
Define `ZMod n` as `Fin n` by an `abbrev`; prove `ZMod.val_add`, `ZMod.val_neg` and `ZMod.val_zero`; and show that `ZMod n` has `n` elements and that `(7 : ZMod 5) = 2`. Mathlib provides `Fintype.card_fin`.
-/

abbrev ZMod (n : ℕ) := Fin n

/-- @spec -/
example (n : ℕ) : ZMod n = Fin n := rfl

theorem ZMod.val_add {n : ℕ} (a b : ZMod n) : (a + b).val = (a.val + b.val) % n := rfl

theorem ZMod.val_neg {n : ℕ} (a : ZMod n) : (-a).val = (n - a.val) % n := rfl

theorem ZMod.val_zero {n : ℕ} [NeZero n] : (0 : ZMod n).val = 0 % n := rfl

theorem card_zmod (n : ℕ) [NeZero n] : Fintype.card (ZMod n) = n :=
  Fintype.card_fin n

theorem zmod_five_seven : (7 : ZMod 5) = 2 := by
  decide

/-! @end -/

/-!
@problem zmod_add_laws
@title The Laws of Addition Modulo n
@concept integers_mod_n

@preamble
Addition modulo `n` is associative and commutative, `0` is neutral, and `-a` cancels `a` on either side. Two residues are equal when their values are; this is `Fin.ext`. So a law is proved by passing to values and computing with remainders. The two laws whose arithmetic is fiddly, `ZMod.add_assoc` and `ZMod.neg_add_cancel`, are given with their proofs. Here is the proof that `0` is neutral on the left, one rewrite per line, with the goal each leaves:
```lean
theorem ZMod.zero_add [NeZero n] (a : ZMod n) : 0 + a = a := by
  apply Fin.ext  -- (0 + a).val = a.val
  rw [ZMod.val_add]  -- (0.val + a.val) % n = a.val
  rw [ZMod.val_zero]  -- (0 % n + a.val) % n = a.val
  rw [Nat.zero_mod, Nat.zero_add]  -- a.val % n = a.val
  rw [Nat.mod_eq_of_lt a.isLt]  -- closed
```
`Nat.mod_eq_of_lt` drops the `%` from a number below `n`. The laws of `ℕ` the proofs need are core Lean's, under the names of The Natural Numbers.
@description
Prove `ZMod.add_zero`, `ZMod.add_comm` and `ZMod.add_neg_cancel : a + -a = 0`. The context holds `ZMod.zero_add`, `ZMod.neg_add_cancel` and the equations of the previous problem.
-/

/-- @given -/
theorem ZMod.add_assoc {n : ℕ} (a b c : ZMod n) : a + b + c = a + (b + c) := by
  apply Fin.ext
  simp only [ZMod.val_add]
  rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

/-- @given -/
theorem ZMod.neg_add_cancel {n : ℕ} [NeZero n] (a : ZMod n) : -a + a = 0 := by
  apply Fin.ext
  rw [ZMod.val_add, ZMod.val_neg, ZMod.val_zero, Nat.mod_add_mod,
    Nat.sub_add_cancel (Nat.le_of_lt a.isLt), Nat.mod_self, Nat.zero_mod]

/-- @given -/
theorem ZMod.zero_add {n : ℕ} [NeZero n] (a : ZMod n) : 0 + a = a := by
  apply Fin.ext
  rw [ZMod.val_add]
  rw [ZMod.val_zero]
  rw [Nat.zero_mod, Nat.zero_add]
  rw [Nat.mod_eq_of_lt a.isLt]

theorem ZMod.add_zero {n : ℕ} [NeZero n] (a : ZMod n) : a + 0 = a := by
  apply Fin.ext
  rw [ZMod.val_add, ZMod.val_zero, Nat.zero_mod, Nat.add_zero, Nat.mod_eq_of_lt a.isLt]

theorem ZMod.add_comm {n : ℕ} (a b : ZMod n) : a + b = b + a := by
  apply Fin.ext
  rw [ZMod.val_add, ZMod.val_add, Nat.add_comm]

theorem ZMod.add_neg_cancel {n : ℕ} [NeZero n] (a : ZMod n) : a + -a = 0 := by
  rw [ZMod.add_comm, ZMod.neg_add_cancel]

/-! @end -/

/-!
@problem zmod_group
@title The Group of Integers Modulo n
@concept integers_mod_n

@preamble
`ZMod n` under `+` is an additive group for every positive `n`: the instance takes the addition, the numeral `0` and the negation of `Fin n` as its data, and the laws of the previous problem as its five laws. As for the integers, the instance's `+` is the residues' own, so every theorem about additive groups applies to residues as they are written, with no new proof. The previous section proved that inversion undoes itself, `inv_inv`, and that it reverses a product, `mul_inv_rev`; the context holds their additive versions, `neg_neg` and `neg_add_rev`.
@description
Supply the instance `AddGroup (ZMod n)` for positive `n`, and show, from those additive versions, that `-(-a) = a` and `-(a + b) = -b + -a` for all residues `a` and `b`.
-/

instance (n : ℕ) [NeZero n] : AddGroup (ZMod n) where
  add a b := a + b
  zero := 0
  neg a := -a
  add_assoc := ZMod.add_assoc
  zero_add := ZMod.zero_add
  add_zero := ZMod.add_zero
  neg_add_cancel := ZMod.neg_add_cancel
  add_neg_cancel := ZMod.add_neg_cancel

/-- @spec -/
example : AddGroup.add (4 : ZMod 6) 5 = 3 ∧ (AddGroup.zero : ZMod 6) = 0 ∧
    AddGroup.neg (4 : ZMod 6) = 2 := by decide

theorem zmod_neg_neg {n : ℕ} [NeZero n] (a : ZMod n) : -(-a) = a :=
  neg_neg a

theorem zmod_neg_add_rev {n : ℕ} [NeZero n] (a b : ZMod n) : -(a + b) = -b + -a :=
  neg_add_rev a b

/-! @end -/

/-!
@problem zmod_two_equiv_bool
@title The Integers Modulo 2 and the Booleans
@concept integers_mod_n

@preamble
`ZMod 2` has two elements, `0` and `1`, with `1 + 1 = 0`. The group of order two of the previous section, `Bool` under `xor`, also has two, with `true + true = false`. The two are the same group under different names: the renaming `0 ↦ false`, `1 ↦ true` is a bijection `e` that carries the one table to the other,
```lean
e (a + b) = e a + e b
```
for all `a` and `b`. The equivalence is built as `boolEquivFinTwo` was in the first section, by its four fields. The laws of the equivalence, like the equation of the tables, are statements about the finitely many elements of `ZMod 2` and `Bool`.
@description
Define `zmodTwoEquivBool : ZMod 2 ≃ Bool`, sending `0` to `false` and `1` to `true`, and show that it carries the addition of `ZMod 2` to the addition of `Bool`.
-/

def zmodTwoEquivBool : ZMod 2 ≃ Bool where
  toFun a := if a.val = 1 then true else false
  invFun b := if b then ⟨1, by decide⟩ else ⟨0, by decide⟩
  left_inv := by decide
  right_inv := by decide

/-- @spec -/
example : zmodTwoEquivBool 0 = false ∧ zmodTwoEquivBool 1 = true := by decide

theorem zmodTwoEquivBool_add :
    ∀ a b : ZMod 2, zmodTwoEquivBool (a + b) = zmodTwoEquivBool a + zmodTwoEquivBool b := by
  decide

/-! @end -/

/-!
@concept symmetric_groups
@title The Symmetric Groups
@kind definition

The permutations of a set form a group under composition, the symmetric group of the set; on `n` points it is `Sₙ`. It is the first group of the subject in which the order of the factors matters. On three points it is already not commutative.
-/

/-!
@problem perm_group
@title The Symmetric Group
@concept symmetric_groups

@preamble
The first section met the permutations of a type `X`, the bijections from `X` to itself that form `Equiv.Perm X`, and composed them: `g` and then `f` is `g.trans f`. We take `f * g` to be `g.trans f`, the permutation that applies `g` first, so that `(f * g) x = f (g x)`, as for functions; the identity `Equiv.refl X` is neutral, and the inverse of `f` is `f.symm`. Associativity and the two laws of the identity hold by definition.

Under this convention `f⁻¹ * f` is `f` followed by `f.symm`, and `f * f⁻¹` is `f.symm` followed by `f`. Two equivalences that agree at every point are equal:
```lean
theorem Equiv.ext {e e' : α ≃ β} (h : ∀ x, e x = e' x) : e = e'
```
@description
Supply the instance `Group (Equiv.Perm X)` with the convention above: `f * g = g.trans f`, not `f.trans g`.
-/

instance (X : Type u) : Group (Equiv.Perm X) where
  mul f g := g.trans f
  one := Equiv.refl X
  inv f := f.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel f := by
    apply Equiv.ext
    intro x
    exact f.symm_apply_apply x
  mul_inv_cancel f := by
    apply Equiv.ext
    intro x
    exact f.apply_symm_apply x

/-- @spec -/
example (X : Type u) (f g : Equiv.Perm X) (x : X) :
    (f * g) x = f (g x) ∧ (1 : Equiv.Perm X) x = x ∧ f⁻¹ (f x) = x :=
  ⟨rfl, rfl, f.symm_apply_apply x⟩

/-! @end -/

/-!
@problem reflect3
@title A Reflection of Three Points
@concept symmetric_groups

@preamble
The symmetric group on three points, `Equiv.Perm (Fin 3)`, is the group of symmetries of a triangle with vertices `0`, `1` and `2`. The rotation `rot3` of the first section, `i ↦ i + 1`, turns it, and is an element of this group as it stands. The reflection through the vertex `0` fixes `0` and exchanges `1` and `2`, which is `i ↦ -i`, since `-1 = 2` and `-2 = 1` in `Fin 3`. A reflection undoes itself, so applied twice it is the identity and it is its own inverse; a third of a turn is undone by two more thirds.
@description
Define `reflect3 : Equiv.Perm (Fin 3)`, the permutation sending `i` to `-i`, and show that
```lean
reflect3 * reflect3 = 1
reflect3⁻¹ = reflect3
rot3⁻¹ = rot3 * rot3
```
The context holds `inv_eq_of_mul_eq_one_right` of the previous section, which says that `a * b = 1` gives `a⁻¹ = b`.
-/

def reflect3 : Equiv.Perm (Fin 3) where
  toFun i := -i
  invFun i := -i
  left_inv := by decide
  right_inv := by decide

/-- @spec -/
example : reflect3 0 = 0 ∧ reflect3 1 = 2 ∧ reflect3 2 = 1 := by decide

theorem reflect3_mul_self : reflect3 * reflect3 = 1 := by
  decide

theorem reflect3_inv : reflect3⁻¹ = reflect3 :=
  inv_eq_of_mul_eq_one_right reflect3_mul_self

theorem rot3_inv : rot3⁻¹ = rot3 * rot3 := by
  decide

/-! @end -/

/-!
@problem s3_not_comm
@title The Symmetric Group on Three Points is Not Commutative
@concept symmetric_groups

@preamble
The first section found two permutations of three points that do not commute, `rot3` and `flip3`. `rot3` and `reflect3` do not commute either: reflecting and then rotating is not rotating and then reflecting. Follow the vertex `0` under each.

In place of commutativity there is a rule: reflecting after a rotation is rotating the other way after the reflection,
```lean
reflect3 * rot3 = rot3⁻¹ * reflect3
```
In any group, an element `s` with `s * r = r⁻¹ * s` can pass `r` only by inverting it.
@description
Show that `rot3 * reflect3 ≠ reflect3 * rot3` and that the rule above holds. Prove that in any group `s * r = r⁻¹ * s` gives `r * s * r = s`, under the name `mul_mul_eq_of_mul_eq_inv_mul`, and deduce
```lean
rot3 * reflect3 * rot3 = reflect3
```
-/

theorem rot3_reflect3_ne : rot3 * reflect3 ≠ reflect3 * rot3 := by
  decide

theorem reflect3_mul_rot3 : reflect3 * rot3 = rot3⁻¹ * reflect3 := by
  decide

@[to_additive add_add_eq_of_add_eq_neg_add]
theorem mul_mul_eq_of_mul_eq_inv_mul {G : Type u} [Group G] {r s : G} (h : s * r = r⁻¹ * s) :
    r * s * r = s := by
  rw [mul_assoc, h, mul_inv_cancel_left]

theorem rot3_reflect3_rot3 : rot3 * reflect3 * rot3 = reflect3 :=
  mul_mul_eq_of_mul_eq_inv_mul reflect3_mul_rot3

/-! @end -/

/-!
@concept commutative_groups
@title Commutative Groups
@kind definition

A group is commutative when any two of its elements commute. The integers, the integers modulo `n`, and the groups of order one and two are commutative; the symmetric group on three points is not. In a commutative group the factors of a product may be freely rearranged.
-/

/-!
@problem comm_group
@title The Definition of a Commutative Group
@concept commutative_groups

@preamble
A group is *commutative*, or abelian, when `a * b = b * a` for all `a` and `b`. Lean expresses "a group with one more law" as a class that extends the first. The head
```lean
class CommGroup (G : Type u) extends Group G where
```
is followed by the new field alone, `mul_comm`. The symbol `*` may be used in the new field, since `extends Group G` supplies the group. An instance of `CommGroup G` then carries an instance of `Group G` inside it, as the field `toGroup`, which Lean finds whenever a law of groups is used on `G`. The additive version is `AddCommGroup A`, extending `AddGroup A` by `add_comm`, and Lean is told that the two correspond.
@description
Define the class `CommGroup G`, extending `Group G` by the law `mul_comm`, and its additive version `AddCommGroup A`, extending `AddGroup A` by the law `add_comm`, each written with the elements as explicit arguments, `∀ a b : G, a * b = b * a`.
-/

class CommGroup (G : Type u) extends Group G where
  mul_comm : ∀ a b : G, a * b = b * a

class AddCommGroup (A : Type u) extends AddGroup A where
  add_comm : ∀ a b : A, a + b = b + a

/-- @spec -/
example (G : Type u) [CommGroup G] : Group G := CommGroup.toGroup

/-- @spec -/
example (G : Type u) [CommGroup G] (a b : G) : a * b = b * a := by
  have h := @CommGroup.mul_comm G _ a b
  grind

/-- @spec -/
example (A : Type u) [AddCommGroup A] : AddGroup A := AddCommGroup.toAddGroup

/-- @spec -/
example (A : Type u) [AddCommGroup A] (a b : A) : a + b = b + a := by
  have h := @AddCommGroup.add_comm A _ a b
  grind

/-! @end -/

attribute [to_additive existing AddCommGroup] CommGroup

/-!
@problem comm_instances
@title The Commutative Examples
@concept commutative_groups

@preamble
Addition is commutative on each of the additive groups met so far: on `ℤ` by core Lean's `Int.add_comm`, on `ZMod n` by `ZMod.add_comm` of this section, and on `Bool` by `bool_add_comm` of the previous section, which the context holds. The trivial group is commutative too. Each instance needs only the new field: written with `where` and that field alone, it takes the group instance already given. The context holds `mul_comm`, the new field restated as a theorem, and its additive version `add_comm`.
@description
Supply the instances `CommGroup Unit`, `AddCommGroup ℤ`, `AddCommGroup (ZMod n)` and `AddCommGroup Bool`.
-/

/-- @given -/
@[to_additive add_comm]
theorem mul_comm {G : Type u} [CommGroup G] (a b : G) : a * b = b * a :=
  CommGroup.mul_comm a b

instance : CommGroup Unit where
  mul_comm := by decide

instance : AddCommGroup ℤ where
  add_comm := Int.add_comm

instance (n : ℕ) [NeZero n] : AddCommGroup (ZMod n) where
  add_comm := ZMod.add_comm

instance : AddCommGroup Bool where
  add_comm := bool_add_comm

/-- @spec -/
example (a b : ℤ) : a + b = b + a := add_comm a b

/-- @spec -/
example (a b : Bool) : a + b = b + a := add_comm a b

/-- @spec -/
example (n : ℕ) [NeZero n] (a b : ZMod n) : a + b = b + a := add_comm a b

/-- @spec -/
example (a b : Unit) : a * b = b * a := mul_comm a b

/-! @end -/

/-!
@problem comm_rearrange
@title Rearranging a Product in a Commutative Group
@concept commutative_groups

@preamble
In a commutative group the factors of a product can be put in any order, and two rearrangements are used so often that they have names. The first exchanges the first two factors of a product grouped to the right, and the second the last two of one grouped to the left:
```lean
mul_left_comm : a * (b * c) = b * (a * c)
mul_right_comm : a * b * c = a * c * b
```
Each is associativity and a single commutation. Here is the first, as a `calc` chain with the law of each step beside it:
```lean
theorem mul_left_comm (a b c : G) : a * (b * c) = b * (a * c) := by
  calc a * (b * c) = a * b * c := by rw [mul_assoc]
    _ = b * a * c := by rw [mul_comm a b]
    _ = b * (a * c) := by rw [mul_assoc]
```
`rw [mul_comm]` exchanges the first product it finds, the outer one; `rw [mul_comm a b]` names the product to exchange. The additive versions are `add_left_comm` and `add_right_comm`.
@description
Show that in a commutative group `a * b * c = a * c * b`, under the name `mul_right_comm`. The context holds `mul_assoc`, `mul_comm` and `mul_left_comm`.
-/

/-- @given -/
@[to_additive add_left_comm]
theorem mul_left_comm {G : Type u} [CommGroup G] (a b c : G) : a * (b * c) = b * (a * c) := by
  calc a * (b * c) = a * b * c := by rw [mul_assoc]
    _ = b * a * c := by rw [mul_comm a b]
    _ = b * (a * c) := by rw [mul_assoc]

@[to_additive add_right_comm]
theorem mul_right_comm {G : Type u} [CommGroup G] (a b c : G) : a * b * c = a * c * b := by
  rw [mul_assoc, mul_comm b c, ← mul_assoc]

/-! @end -/

/--
@problem mul_mul_mul_comm
@title Exchanging the Middle Factors
@concept commutative_groups

@preamble
A product of two products, `a * b` and `c * d`, has four factors, and in a commutative group the middle two may be exchanged. Read additively, it is the familiar rule for adding two sums term by term:
```lean
a * b * (c * d) = a * c * (b * d)
(a + b) + (c + d) = (a + c) + (b + d)
```
It is a rearrangement of the kind of the previous problem, with one factor more. We name it `mul_mul_mul_comm`, and its additive version `add_add_add_comm`.
@description
Show that in a commutative group the middle factors of a product of two products may be exchanged. The context holds `mul_assoc`, `mul_comm` and `mul_left_comm`.
-/
@[to_additive add_add_add_comm]
theorem mul_mul_mul_comm {G : Type u} [CommGroup G] (a b c d : G) :
    a * b * (c * d) = a * c * (b * d) := by
  rw [mul_assoc, mul_left_comm b c d, ← mul_assoc]

/-!
@concept product_groups
@title Product Groups
@kind definition

Two groups `G` and `H` make a third, their product `G × H`: the pairs `(g, h)`, multiplied componentwise. It is how groups are assembled from smaller ones: the integers modulo 2 and modulo 3 make a commutative group of six elements.
-/

/-!
@problem prod_group
@title The Product of Two Groups
@concept product_groups

@preamble
The product of two groups `G` and `H` is the set of pairs `(g, h)` with each component multiplied in its own group:
```lean
(g, h) * (g', h') = (g * g', h * h')
```
The neutral element is `(1, 1)` and the inverse of `(g, h)` is `(g⁻¹, h⁻¹)`. The elements of `G × H` are Lean's pairs, with `a.1` and `a.2` the components of `a`. Each law is an equation between two pairs whose components are the same law in `G` and in `H`. A goal may show a component as the first component of a pair of products; that is the product itself, and `rw` finds it there. The instance carries `@[to_additive]`, so the product of two additive groups is an additive group, added componentwise.
@description
Supply the instance `Group (G × H)`, and prove `prod_mul_def`, the equation
```lean
a * b = (a.1 * b.1, a.2 * b.2)
```
Then show that `-a + a = 0` for every `a` in `ZMod 2 × ZMod 3`.
-/

@[to_additive Prod.instAddGroup]
instance Prod.instGroup {G : Type u} {H : Type v} [Group G] [Group H] : Group (G × H) where
  mul a b := (a.1 * b.1, a.2 * b.2)
  one := (1, 1)
  inv a := (a.1⁻¹, a.2⁻¹)
  mul_assoc a b c := by
    rw [mul_assoc, mul_assoc]
  one_mul a := by
    rw [one_mul, one_mul]
  mul_one a := by
    rw [mul_one, mul_one]
  inv_mul_cancel a := by
    rw [inv_mul_cancel, inv_mul_cancel]
  mul_inv_cancel a := by
    rw [mul_inv_cancel, mul_inv_cancel]

/-- @spec -/
example {G : Type u} {H : Type v} [Group G] [Group H] (a c : G) (b d : H) :
    (a, b) * (c, d) = (a * c, b * d) ∧ (1 : G × H) = (1, 1) ∧ (a, b)⁻¹ = (a⁻¹, b⁻¹) :=
  ⟨rfl, rfl, rfl⟩

@[to_additive prod_add_def]
theorem prod_mul_def {G : Type u} {H : Type v} [Group G] [Group H] (a b : G × H) :
    a * b = (a.1 * b.1, a.2 * b.2) := rfl

theorem zmod_two_three_neg_add_cancel (a : ZMod 2 × ZMod 3) : -a + a = 0 :=
  neg_add_cancel a

/-! @end -/

/-!
@problem prod_fintype
@title Counting a Product
@concept product_groups

@preamble
`ZMod 2 × ZMod 3` is finite, with as many elements as there are pairs, `2 * 3 = 6`. A `Fintype` instance for a product is not available in this subject, so we build this one from a labelling by `Fin 6`, as the first section counted pairs with `finProdFinEquiv`. Lean cannot work out from `6` alone that the factors have sizes `2` and `3`, so the sizes are given to `finProdFinEquiv` by name, as `Nat.find` was given its `p`. `Fintype.ofEquiv α e` counts `β` from a counted type `α` and an equivalence `e : α ≃ β`, with `α` given explicitly.
@description
Define the equivalence `finSixEquivZModTwoThree` from `Fin 6` to `ZMod 2 × ZMod 3`, supply the instance `Fintype (ZMod 2 × ZMod 3)`, and show that it has six elements. Mathlib provides `finProdFinEquiv`, `Fintype.ofEquiv`, `Fintype.card_congr` and `Fintype.card_fin`.
-/

def finSixEquivZModTwoThree : Fin 6 ≃ ZMod 2 × ZMod 3 :=
  (finProdFinEquiv (m := 2) (n := 3)).symm

/-- @spec -/
example : Function.Bijective finSixEquivZModTwoThree := finSixEquivZModTwoThree.bijective

instance : Fintype (ZMod 2 × ZMod 3) :=
  Fintype.ofEquiv (Fin 6) finSixEquivZModTwoThree

theorem card_zmod_two_three : Fintype.card (ZMod 2 × ZMod 3) = 6 := by
  rw [← Fintype.card_congr finSixEquivZModTwoThree, Fintype.card_fin]

/-! @end -/

/-!
@problem prod_comm_group
@title The Product of Two Commutative Groups
@concept product_groups

@preamble
When `G` and `H` are commutative, so is `G × H`: the two components of `a * b` and of `b * a` are products in `G` and in `H`, which commute. The instance is built from the group instance of the product by supplying the one field `mul_comm`, as the commutative examples were. The instance carries `@[to_additive]`, so the product of two commutative additive groups is a commutative additive group.
@description
Supply the instance `CommGroup (G × H)` for commutative `G` and `H`, and show that `a + b = b + a` for all `a` and `b` in `ZMod 2 × ZMod 3`. The context holds `prod_mul_def` and `mul_comm`.
-/

@[to_additive Prod.instAddCommGroup]
instance Prod.instCommGroup {G : Type u} {H : Type v} [CommGroup G] [CommGroup H] :
    CommGroup (G × H) where
  mul_comm a b := by
    rw [prod_mul_def, prod_mul_def, mul_comm a.1 b.1, mul_comm a.2 b.2]

/-- @spec -/
example {G : Type u} {H : Type v} [CommGroup G] [CommGroup H] (a b : G × H) : a * b = b * a :=
  mul_comm a b

theorem zmod_two_three_add_comm (a b : ZMod 2 × ZMod 3) : a + b = b + a :=
  add_comm a b

/-! @end -/

/--
@problem comm_of_prod_comm
@title A Factor of a Commutative Product is Commutative
@concept product_groups

@preamble
The product of two commutative groups is commutative, and the converse holds as well: if `G × H` is commutative, so is each factor. An element of `G` sits in `G × H` as the first component of a pair, and the first component of a product of pairs is the product of the first components. So an equation between products in `G × H` gives an equation between products in `G`, as Set Theory took equations of pairs apart. The additive version is `add_comm_of_prod_add_comm`.
@description
Show that if the product `G × H` is commutative, then so is `G`. The context holds `prod_mul_def`.
-/
@[to_additive add_comm_of_prod_add_comm]
theorem comm_of_prod_comm {G : Type u} {H : Type v} [Group G] [Group H]
    (h : ∀ a b : G × H, a * b = b * a) (x y : G) : x * y = y * x := by
  have hxy := h (x, 1) (y, 1)
  rw [prod_mul_def, prod_mul_def] at hxy
  exact congrArg Prod.fst hxy

/-!
@concept dihedral_groups
@title The Dihedral Groups
@kind definition

The dihedral group Dₙ is the group of symmetries of a regular `n`-gon: `n` rotations and `n` reflections, `2n` elements in all, multiplied by composing symmetries. It is the subject's standard noncommutative example, small enough to compute in; D₂ is the Klein four-group. It is built from a four-line table and counted.
-/

/-!
@problem dihedral_mul
@title The Elements and the Table of the Dihedral Group
@concept dihedral_groups

@preamble
The symmetries of a regular `n`-gon are the `n` rotations `r i`, through `i` steps of a full turn divided by `n`, and the `n` reflections `sr i`, each the rotation through `i` steps followed by a fixed reflection `s`, with `i : ZMod n`. Composing symmetries gives the table, where in `mul a b` the symmetry `b` acts first, as for permutations:
```lean
mul (r i) (r j) = r (i + j)
mul (sr i) (r j) = sr (i + j)
mul (r i) (sr j) = sr (j + -i)
mul (sr i) (sr j) = r (j + -i)
```
A rotation after a reflection is a reflection with the rotation reversed, since a mirror reverses the sense of turning. Write `j + -i`, not `j - i`: the laws of residues are proved for `+` and `-`, not for subtraction. The table carries `[NeZero n]`, as those laws do. `deriving DecidableEq` has Lean decide equality of symmetries, for `decide`.
@description
Define the inductive type `DihedralGroup n` with the constructors `r` and `sr`, each taking an `i : ZMod n`, closed by `deriving DecidableEq`; define `DihedralGroup.mul` by the four-line table; and check in `DihedralGroup 4` that `sr 0` times `r 1` times `sr 0` is `r 3`.
-/

inductive DihedralGroup (n : ℕ) where
  | r (i : ZMod n)
  | sr (i : ZMod n)
  deriving DecidableEq

def DihedralGroup.mul {n : ℕ} [NeZero n] : DihedralGroup n → DihedralGroup n → DihedralGroup n
  | r i, r j => r (i + j)
  | r i, sr j => sr (j + -i)
  | sr i, r j => sr (i + j)
  | sr i, sr j => r (j + -i)

/-- @spec -/
example {n : ℕ} [NeZero n] (i j : ZMod n) :
    DihedralGroup.mul (.r i) (.r j) = .r (i + j) ∧
    DihedralGroup.mul (.r i) (.sr j) = .sr (j + -i) ∧
    DihedralGroup.mul (.sr i) (.r j) = .sr (i + j) ∧
    DihedralGroup.mul (.sr i) (.sr j) = .r (j + -i) :=
  ⟨rfl, rfl, rfl, rfl⟩

open DihedralGroup in
theorem d4_table :
    DihedralGroup.mul (DihedralGroup.mul (sr 0) (r 1)) (sr 0) = (r 3 : DihedralGroup 4) := by
  decide

/-! @end -/

/-!
@problem dihedral_mul_assoc
@title The Dihedral Table is Associative
@concept dihedral_groups

@preamble
The table defines a group only if it is associative. Both sides of the law are always one constructor applied to a sum in `ZMod n`, and the two sums agree by the laws of a commutative additive group.

`rw` does not compute `mul` on constructors. The four equations of the table, given in the context as `DihedralGroup.r_mul_r` and its three companions, rewrite each product to its value.
@description
Show that `DihedralGroup.mul` is associative. The context holds the four equations of the table and the additive versions of laws of the previous section and of this one: `add_assoc`, `neg_add_rev`, `neg_neg`, `add_left_comm` and `add_right_comm`.
-/

/-- @given -/
theorem DihedralGroup.r_mul_r {n : ℕ} [NeZero n] (i j : ZMod n) :
    DihedralGroup.mul (r i) (r j) = r (i + j) := rfl

/-- @given -/
theorem DihedralGroup.r_mul_sr {n : ℕ} [NeZero n] (i j : ZMod n) :
    DihedralGroup.mul (r i) (sr j) = sr (j + -i) := rfl

/-- @given -/
theorem DihedralGroup.sr_mul_r {n : ℕ} [NeZero n] (i j : ZMod n) :
    DihedralGroup.mul (sr i) (r j) = sr (i + j) := rfl

/-- @given -/
theorem DihedralGroup.sr_mul_sr {n : ℕ} [NeZero n] (i j : ZMod n) :
    DihedralGroup.mul (sr i) (sr j) = r (j + -i) := rfl

theorem dihedral_mul_assoc {n : ℕ} [NeZero n] (a b c : DihedralGroup n) :
    DihedralGroup.mul (DihedralGroup.mul a b) c = DihedralGroup.mul a (DihedralGroup.mul b c) := by
  cases a <;> cases b <;> cases c <;> simp only [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
    DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
  · rw [add_assoc]
  · rw [neg_add_rev, add_assoc]
  · rw [add_right_comm]
  · rw [neg_add_rev, neg_neg, add_left_comm]
  · rw [add_assoc]
  · rw [neg_add_rev, add_assoc]
  · rw [add_right_comm]
  · rw [neg_add_rev, neg_neg, add_left_comm]

/-! @end -/

/-!
@problem dihedral_group
@title The Dihedral Group
@concept dihedral_groups

@preamble
`DihedralGroup n` is a group, Dₙ, with the table as its operation and the trivial rotation `r 0` as its neutral element. A rotation is undone by the opposite rotation and a reflection by itself, so the inverse is `(r i)⁻¹ = r (-i)` and `(sr i)⁻¹ = sr i`. Associativity is the previous problem. A function field is defined by cases:
```lean
inv | r i => …
    | sr i => …
```
@description
Supply the instance `Group (DihedralGroup n)`, and show that in `DihedralGroup 4`, `r 1 * sr 0 ≠ sr 0 * r 1`. The context holds `dihedral_mul_assoc`, the four equations of the table, the laws of additive groups and `neg_zero : -0 = 0`.
-/

open DihedralGroup in
instance (n : ℕ) [NeZero n] : Group (DihedralGroup n) where
  mul := DihedralGroup.mul
  one := r 0
  inv
    | r i => r (-i)
    | sr i => sr i
  mul_assoc := dihedral_mul_assoc
  one_mul a := by
    cases a with
    | r i => rw [r_mul_r, zero_add]
    | sr i => rw [r_mul_sr, neg_zero, add_zero]
  mul_one a := by
    cases a with
    | r i => rw [r_mul_r, add_zero]
    | sr i => rw [sr_mul_r, add_zero]
  inv_mul_cancel a := by
    cases a with
    | r i => rw [r_mul_r, neg_add_cancel]
    | sr i => rw [sr_mul_sr, add_neg_cancel]
  mul_inv_cancel a := by
    cases a with
    | r i => rw [r_mul_r, add_neg_cancel]
    | sr i => rw [sr_mul_sr, add_neg_cancel]

/-- @spec -/
example : (DihedralGroup.r 1 : DihedralGroup 4) * DihedralGroup.sr 0 = DihedralGroup.sr 3 ∧
    (DihedralGroup.sr 0 : DihedralGroup 4)⁻¹ = DihedralGroup.sr 0 ∧
    (1 : DihedralGroup 4) = DihedralGroup.r 0 := by decide

open DihedralGroup in
theorem d4_not_comm : (r 1 : DihedralGroup 4) * sr 0 ≠ sr 0 * r 1 := by
  decide

/-! @end -/

/-!
@problem dihedral_fintype
@title Counting the Dihedral Group
@concept dihedral_groups

@preamble
Dₙ has `2n` elements, `n` of each kind, and the count is by labelling, as in the first section. An element is a kind, `0` for a rotation and `1` for a reflection, together with a residue, so `DihedralGroup n` is in bijection with `Fin 2 × ZMod n`. A function out of `Fin 2 × ZMod n` may be defined by matching on the pair, `| (0, k) => …` and `| (1, k) => …`, and no third case is needed, since `Fin 2` has only `0` and `1`. The type needs a `Fintype` instance before it can be counted.
@description
Define the equivalence `DihedralGroup.equivProd n` from `DihedralGroup n` to `Fin 2 × ZMod n`, supply the instance `Fintype (DihedralGroup n)`, and show that `DihedralGroup n` has `2 * n` elements. The context holds `card_of_equiv_prod` of the first section, which counts a type in bijection with `Fin m × Fin n` as `m * n`.
-/

def DihedralGroup.equivProd (n : ℕ) : DihedralGroup n ≃ Fin 2 × ZMod n where
  toFun
    | r i => (0, i)
    | sr i => (1, i)
  invFun
    | (0, i) => r i
    | (1, i) => sr i
  left_inv a := by
    cases a with
    | r i => rfl
    | sr i => rfl
  right_inv p := by
    match p with
    | (0, i) => rfl
    | (1, i) => rfl

/-- @spec -/
example (n : ℕ) (i : ZMod n) :
    DihedralGroup.equivProd n (DihedralGroup.r i) = (0, i) ∧
    DihedralGroup.equivProd n (DihedralGroup.sr i) = (1, i) := ⟨rfl, rfl⟩

instance (n : ℕ) : Fintype (DihedralGroup n) :=
  Fintype.ofEquiv (Fin (2 * n)) ((DihedralGroup.equivProd n).trans finProdFinEquiv).symm

theorem card_dihedral (n : ℕ) : Fintype.card (DihedralGroup n) = 2 * n :=
  card_of_equiv_prod (DihedralGroup.equivProd n)

/-! @end -/

/-!
@problem klein_four
@title The Klein Four-Group
@concept dihedral_groups

@preamble
D₂, the symmetries of a segment, has four elements, `r 0`, `r 1`, `sr 0` and `sr 1`, and is the *Klein four-group* V₄. Each of its elements is its own inverse, and so V₄ is commutative, unlike D₄. `ZMod 4` also has four elements, but its residue `1` is not its own negative, since `1 + 1 = 2`. So no renaming carries the one table to the other: the two groups of order four differ.
@description
Show that every element of `DihedralGroup 2` is its own inverse, supply the instance `CommGroup (DihedralGroup 2)`, and check that in `ZMod 4` the residue `1` is not its own negative. The context holds `mul_comm_of_inv_eq_self` of the previous section, which says that a group in which every element is its own inverse is commutative.
-/

theorem klein_inv_self : ∀ x : DihedralGroup 2, x⁻¹ = x := by
  decide

instance : CommGroup (DihedralGroup 2) where
  mul_comm := mul_comm_of_inv_eq_self klein_inv_self

theorem zmod_four_neg_one : -(1 : ZMod 4) ≠ 1 := by
  decide

/-- @spec -/
example (a b : DihedralGroup 2) : a * b = b * a := mul_comm a b

/-! @end -/

end GroupTheory
