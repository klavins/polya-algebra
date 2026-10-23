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
import PolyaAlgebra.GroupTheory.Prerequisites

/-! @section Groups -/

universe u

namespace GroupTheory

set_option linter.translateGenerateName false

/-!
@concept group_axioms
@title The Group Axioms
@kind definition

A group is a set with an operation that is associative, has a neutral element, and gives every element an inverse. Everything the subject proves follows from these three conditions. This concept writes them as a class under Mathlib's symbols and again with `+` for an addition, and shows that a one-element set, the integers and the Booleans under exclusive or satisfy them.
-/

/-!
@problem group
@title The Definition of a Group
@concept group_axioms

@preamble
A group is a set `G` with a way of combining two elements into a third, written `a * b`, that satisfies three conditions: the operation is associative, `(a * b) * c = a * (b * c)`; there is a neutral element `1`, with `1 * a = a` and `a * 1 = a`; and every `a` has an inverse `a⁻¹`, with `a⁻¹ * a = 1` and `a * a⁻¹ = 1`. What the operation is differs from group to group, and `*` stands for whichever it is, as `1` stands for whichever element is neutral: on the integers the operation is addition and `0` is neutral.

In Lean the definition is a class, as `Add` was in Programming in Lean. Its data are the fields `mul`, `one` and `inv`; its laws are five more fields whose types are propositions, each a statement about every element, as `∀ a : G, mul one a = a`. The symbols come after the class, in the next problem; the names of the laws are Mathlib's.
@description
Define the class `Group G`: the data `mul`, `one` and `inv`, and the five laws `mul_assoc`, `one_mul`, `mul_one`, `inv_mul_cancel` and `mul_inv_cancel`, named by the order of their symbols (`one_mul` for `1 * a = a`), written as the preamble states them, with the elements as explicit arguments.
-/

class Group (G : Type u) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : G, mul one a = a
  mul_one : ∀ a : G, mul a one = a
  inv_mul_cancel : ∀ a : G, mul (inv a) a = one
  mul_inv_cancel : ∀ a : G, mul a (inv a) = one

/-- @spec -/
example (G : Type u) [Group G] : (G → G → G) × G × (G → G) := (Group.mul, Group.one, Group.inv)

/-- @spec -/
example (G : Type u) [Group G] (a b c : G) :
    Group.mul (Group.mul a b) c = Group.mul a (Group.mul b c) := by
  have h := @Group.mul_assoc G _ a b c
  grind

/-- @spec -/
example (G : Type u) [Group G] (a : G) : Group.mul Group.one a = a := by
  have h := @Group.one_mul G _ a
  grind

/-- @spec -/
example (G : Type u) [Group G] (a : G) : Group.mul a Group.one = a := by
  have h := @Group.mul_one G _ a
  grind

/-- @spec -/
example (G : Type u) [Group G] (a : G) : Group.mul (Group.inv a) a = Group.one := by
  have h := @Group.inv_mul_cancel G _ a
  grind

/-- @spec -/
example (G : Type u) [Group G] (a : G) : Group.mul a (Group.inv a) = Group.one := by
  have h := @Group.mul_inv_cancel G _ a
  grind

/-! @end -/

/-!
@problem group_notation
@title The Notation of a Group
@concept group_axioms

@preamble
In Lean a symbol belongs to a class. `+` is the notation of `Add`, as Programming in Lean showed; `*` is the notation of `Mul`, `1` of `One` and `a⁻¹` of `Inv`, each a class with a single field:
```lean
class Mul (α : Type u) where
  mul : α → α → α
```
with `one : α` the field of `One` and `inv : α → α` the field of `Inv`. A type gets the symbol through an instance of the class, so a group gets its three symbols through three instances, each handing the class the matching field of `Group` through the anonymous constructor, as `instance : Add Vec3 := ⟨fun v w => …⟩` handed `Add` its function in Programming in Lean; each is one line, with `{G : Type u} [Group G]` before the colon, and is named, as `Group.toMul`, for a later problem to refer to. With them in place the laws read as the mathematics writes them, `1 * a = a`, which the next problems check on each instance. Mathlib builds `Group` on top of these three classes; here they come after it, and nothing else differs.
@description
Supply the instances `Group.toMul : Mul G`, `Group.toOne : One G` and `Group.toInv : Inv G` for every group `G`, so that `a * b` is `Group.mul a b`, `1` is `Group.one` and `a⁻¹` is `Group.inv a`.
-/

instance Group.toMul {G : Type u} [Group G] : Mul G := ⟨Group.mul⟩

instance Group.toOne {G : Type u} [Group G] : One G := ⟨Group.one⟩

instance Group.toInv {G : Type u} [Group G] : Inv G := ⟨Group.inv⟩

/-- @spec -/
example {G : Type u} [Group G] (a b : G) :
    a * b = Group.mul a b ∧ (1 : G) = Group.one ∧ a⁻¹ = Group.inv a := ⟨rfl, rfl, rfl⟩

/-! @end -/

/-!
@problem unit_group
@title The Trivial Group
@concept group_axioms

@preamble
The smallest group has one element, which is then the neutral element, and the operation and the inverse have only one value to take. Lean's type `Unit` has the one element `()`, and a statement about every element of `Unit` is settled by `decide`, as one about `Fin 4` was.

An instance of a class with several fields is built with `where`, as an equivalence was in the first section: `instance : Group Unit where`, then one field per line, a function field with its arguments before the `:=`, as `mul _ _ := ()`, a constant field as `one := ()`, and a law as `mul_assoc := by decide`.
@description
Supply the instance `Group Unit`, the trivial group.
-/

instance : Group Unit where
  mul _ _ := ()
  one := ()
  inv _ := ()
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide
  mul_inv_cancel := by decide

/-- @spec -/
example : (1 : Unit) = () ∧ () * () = () ∧ ()⁻¹ = () := by decide

/-! @end -/

/-!
@problem add_group
@title Additive Groups
@concept group_axioms

@preamble
The integers under addition are a group, but `ℤ` cannot carry the instance `Group ℤ`. Its symbols are taken: `3 * 4` is `12` and `1` is the integer one, by instances Lean already has, and a second `Mul ℤ` would say two things with one symbol. A group whose operation is an addition is written as the textbooks write the integers, with `a + b`, `0` and `-a`, and in Lean that is a second class, `AddGroup`: the definition of a group under additive names. The data are `add`, `zero` and `neg` in place of `mul`, `one` and `inv`, and the laws are `add_assoc`, `zero_add`, `add_zero`, `neg_add_cancel` and `add_neg_cancel`. The symbols come from `Add`, `Zero` and `Neg` through three instances, as before; Mathlib has both classes under these names.

The two classes are one definition in two spellings, and the lines `attribute [to_additive existing AddGroup] Group` and the like after this problem record the correspondence for Lean; the next concept puts it to use.
@description
Define the class `AddGroup A`, the additive copy of `Group`, with the data `add`, `zero` and `neg` and the five laws named above, written as the laws of `Group` are; and supply the instances `AddGroup.toAdd : Add A`, `AddGroup.toZero : Zero A` and `AddGroup.toNeg : Neg A`.
-/

class AddGroup (A : Type u) where
  add : A → A → A
  zero : A
  neg : A → A
  add_assoc : ∀ a b c : A, add (add a b) c = add a (add b c)
  zero_add : ∀ a : A, add zero a = a
  add_zero : ∀ a : A, add a zero = a
  neg_add_cancel : ∀ a : A, add (neg a) a = zero
  add_neg_cancel : ∀ a : A, add a (neg a) = zero

instance AddGroup.toAdd {A : Type u} [AddGroup A] : Add A := ⟨AddGroup.add⟩

instance AddGroup.toZero {A : Type u} [AddGroup A] : Zero A := ⟨AddGroup.zero⟩

instance AddGroup.toNeg {A : Type u} [AddGroup A] : Neg A := ⟨AddGroup.neg⟩

/-- @spec -/
example (A : Type u) [AddGroup A] : (A → A → A) × A × (A → A) :=
  (AddGroup.add, AddGroup.zero, AddGroup.neg)

/-- @spec -/
example (A : Type u) [AddGroup A] (a b c : A) :
    AddGroup.add (AddGroup.add a b) c = AddGroup.add a (AddGroup.add b c) := by
  have h := @AddGroup.add_assoc A _ a b c
  grind

/-- @spec -/
example (A : Type u) [AddGroup A] (a : A) : AddGroup.add AddGroup.zero a = a := by
  have h := @AddGroup.zero_add A _ a
  grind

/-- @spec -/
example (A : Type u) [AddGroup A] (a : A) : AddGroup.add a AddGroup.zero = a := by
  have h := @AddGroup.add_zero A _ a
  grind

/-- @spec -/
example (A : Type u) [AddGroup A] (a : A) : AddGroup.add (AddGroup.neg a) a = AddGroup.zero := by
  have h := @AddGroup.neg_add_cancel A _ a
  grind

/-- @spec -/
example (A : Type u) [AddGroup A] (a : A) : AddGroup.add a (AddGroup.neg a) = AddGroup.zero := by
  have h := @AddGroup.add_neg_cancel A _ a
  grind

/-- @spec -/
example {A : Type u} [AddGroup A] (a b : A) :
    a + b = AddGroup.add a b ∧ (0 : A) = AddGroup.zero ∧ -a = AddGroup.neg a := ⟨rfl, rfl, rfl⟩

/-! @end -/

attribute [to_additive existing AddGroup] Group

attribute [to_additive existing AddGroup.toAdd] Group.toMul

attribute [to_additive existing AddGroup.toZero] Group.toOne

attribute [to_additive existing AddGroup.toNeg] Group.toInv

/-!
@problem int_add_group
@title The Integers as an Additive Group
@concept group_axioms

@preamble
With `+` as its symbol the integers are an instance as they stand: `AddGroup ℤ` takes the integers' own addition, zero and negation as its data, and core Lean has the five laws, `Int.add_assoc`, `Int.zero_add`, `Int.add_zero`, `Int.add_left_neg : -a + a = 0` and `Int.add_right_neg : a + -a = 0`, so that `add_assoc := Int.add_assoc` is accepted as it stands. Since the instance's `+` is the integers' own, a sum `3 + x` written in `ℤ` is a sum in the group: every law proved below for additive groups applies to it, and `omega` and `decide`, which know the integers, apply to it as before.
@description
Supply the instance `AddGroup ℤ` with the integers' own addition, zero and negation.
-/

instance : AddGroup ℤ where
  add a b := a + b
  zero := 0
  neg a := -a
  add_assoc := Int.add_assoc
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  neg_add_cancel := Int.add_left_neg
  add_neg_cancel := Int.add_right_neg

/-- @spec -/
example : AddGroup.add (3 : ℤ) 4 = 7 ∧ (AddGroup.zero : ℤ) = 0 ∧ AddGroup.neg (3 : ℤ) = -3 := by
  decide

/-! @end -/

/-!
@problem bool_xor_group
@title The Group of Order Two
@concept group_axioms

@preamble
The *order* of a finite group is its number of elements, `Fintype.card G`. A group of order two has the neutral element and one other element `a`, and the only room left in its table is `a + a = 0`, since `a + a = a` would force `a = 0` once `-a` is added to both sides: the other element is its own negative. The Booleans under exclusive or are this group. `xor a b` is `true` when exactly one of `a` and `b` is, so `false` is neutral, and `xor a a = false` for both values of `a`: it is addition modulo two, with `false` for `0` and `true` for `1`, and the group is written with `+`. Each law is a statement about every element of `Bool`, which `decide` settles; so is the order.
@description
Supply the instance `AddGroup Bool` with `xor` as the addition, `false` as zero and each element as its own negative, and show that this group has order two.
-/

instance : AddGroup Bool where
  add := xor
  zero := false
  neg b := b
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  neg_add_cancel := by decide
  add_neg_cancel := by decide

/-- @spec -/
example : true + true = false ∧ true + false = true ∧ false + true = true ∧
    false + false = false ∧ (0 : Bool) = false := by decide

theorem card_bool : Fintype.card Bool = 2 := by
  decide

/-! @end -/

/-!
@concept consequences
@title Consequences of the Axioms
@kind theorem

The axioms ask for a neutral element and for inverses; they do not say that these are unique, that the inverse of a product is the product of the inverses in reverse order, or that the inverse of `a⁻¹` is `a`. Each follows in a few steps from the five laws. These facts are the tools every later proof reaches for, so they are proved once here, with additive copies, under Mathlib's names.
-/

/-!
@problem cancel_adjacent
@title Cancelling an Adjacent Inverse
@concept consequences

@preamble
The five laws, restated under the notation, are given in the context: `mul_assoc : a * b * c = a * (b * c)`, `one_mul : 1 * a = a`, `mul_one : a * 1 = a`, `inv_mul_cancel : a⁻¹ * a = 1` and `mul_inv_cancel : a * a⁻¹ = 1`. They are rewrite rules. `rw [mul_assoc]` moves a parenthesis to the right and `rw [← mul_assoc]` moves it to the left; `rw [inv_mul_cancel]` replaces an `a⁻¹ * a` by `1`. Since `a * b * c` is `(a * b) * c`, a product written without parentheses associates to the left, and the rewrite that regroups it has to be chosen accordingly.

The first use of the laws is that an inverse standing next to its element cancels it, whatever else is in the product: `a⁻¹ * (a * b) = b`, and likewise with the inverse on the other side, or at the other end of the product. These four equations are the steps every later argument is made of. Each theorem about groups from here on carries a mark such as `@[to_additive add_assoc]`, which the next problem explains; it belongs to the statement and stays in place.
@description
Show the four forms of adjacent cancellation: `a⁻¹ * (a * b) = b`, `a * (a⁻¹ * b) = b`, `a * b * b⁻¹ = a` and `a * b⁻¹ * b = a`.
-/

/-- @given -/
@[to_additive add_assoc]
theorem mul_assoc {G : Type u} [Group G] (a b c : G) : a * b * c = a * (b * c) := by
  apply Group.mul_assoc

/-- @given -/
@[to_additive zero_add]
theorem one_mul {G : Type u} [Group G] (a : G) : 1 * a = a := by
  apply Group.one_mul

/-- @given -/
@[to_additive add_zero]
theorem mul_one {G : Type u} [Group G] (a : G) : a * 1 = a := by
  apply Group.mul_one

/-- @given -/
@[to_additive neg_add_cancel]
theorem inv_mul_cancel {G : Type u} [Group G] (a : G) : a⁻¹ * a = 1 := by
  apply Group.inv_mul_cancel

/-- @given -/
@[to_additive add_neg_cancel]
theorem mul_inv_cancel {G : Type u} [Group G] (a : G) : a * a⁻¹ = 1 := by
  apply Group.mul_inv_cancel

@[to_additive neg_add_cancel_left]
theorem inv_mul_cancel_left {G : Type u} [Group G] (a b : G) : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc, inv_mul_cancel, one_mul]

@[to_additive add_neg_cancel_left]
theorem mul_inv_cancel_left {G : Type u} [Group G] (a b : G) : a * (a⁻¹ * b) = b := by
  rw [← mul_assoc, mul_inv_cancel, one_mul]

@[to_additive add_neg_cancel_right]
theorem mul_inv_cancel_right {G : Type u} [Group G] (a b : G) : a * b * b⁻¹ = a := by
  rw [mul_assoc, mul_inv_cancel, mul_one]

@[to_additive neg_add_cancel_right]
theorem inv_mul_cancel_right {G : Type u} [Group G] (a b : G) : a * b⁻¹ * b = a := by
  rw [mul_assoc, inv_mul_cancel, mul_one]

/-! @end -/

/-!
@problem to_additive
@title Additive Copies of a Theorem
@concept consequences

@preamble
A theorem about groups is a theorem about additive groups once its names are translated: `*` becomes `+`, `1` becomes `0` and `a⁻¹` becomes `-a`, and in the names `mul` becomes `add`, `one` becomes `zero` and `inv` becomes `neg`. Its proof translates the same way, so the copy needs no new argument, and Lean writes it. The mark `@[to_additive n]` above a theorem, standing where `@[simp]` stood in Polya Basic, tells Lean to translate the theorem and its proof and to add the copy under the name `n`, the translated name: the previous problem's `inv_mul_cancel_left : a⁻¹ * (a * b) = b` came with `neg_add_cancel_left : -a + (a + b) = b`, which holds in `ℤ` and in `Bool`. Lean checks the copy like any theorem, and can make it only when everything the proof uses has a copy too, which is why the laws carry the mark and the two classes carry the correspondence.
@description
Show that `a * b * b⁻¹ * a⁻¹ = 1` in every group, under the mark the starting code gives, and conclude from its additive copy, `add_add_neg_add_neg_cancel`, that `x + 5 + -5 + -x = 0` for every integer `x`. The context holds the adjacent cancellations of the previous problem.
-/

@[to_additive add_add_neg_add_neg_cancel]
theorem mul_mul_inv_mul_inv_cancel {G : Type u} [Group G] (a b : G) : a * b * b⁻¹ * a⁻¹ = 1 := by
  rw [mul_inv_cancel_right, mul_inv_cancel]

theorem int_add_add_neg_add_neg (x : ℤ) : x + 5 + -5 + -x = 0 :=
  add_add_neg_add_neg_cancel x 5

/-! @end -/

/-!
@problem neutral_unique
@title The Neutral Element is Unique
@concept consequences

@preamble
The axioms say that there is a neutral element; they do not say that there is only one. There is: a second neutral element `e` would give `e = e * 1 = 1`. More is true. An element that acts as a neutral element on a single `a`, with `a * b = a`, is already `1`: multiply by `a⁻¹` on the left, and the adjacent inverse cancels. In particular `1` is the only solution of `x * x = x`.

Mathlib states these as equivalences, `mul_eq_left : a * b = a ↔ b = 1` and `mul_eq_right : a * b = b ↔ a = 1`, with the elements implicit, since a use `mul_eq_left.mp h` reads them off `h`.
@description
Show that `a * b = a` exactly when `b = 1`, and that `a * b = b` exactly when `a = 1`; conclude that an element `e` with `e * a = a` for every `a` is `1`. The context holds the four adjacent cancellations of the previous problem.
-/

@[to_additive add_eq_left]
theorem mul_eq_left {G : Type u} [Group G] {a b : G} : a * b = a ↔ b = 1 := by
  constructor
  · intro h
    rw [← inv_mul_cancel_left a b, h, inv_mul_cancel]
  · intro h
    rw [h, mul_one]

@[to_additive add_eq_right]
theorem mul_eq_right {G : Type u} [Group G] {a b : G} : a * b = b ↔ a = 1 := by
  constructor
  · intro h
    rw [← mul_inv_cancel_right a b, h, mul_inv_cancel]
  · intro h
    rw [h, one_mul]

@[to_additive eq_zero_of_left_neutral]
theorem eq_one_of_left_neutral {G : Type u} [Group G] {e : G} (he : ∀ a : G, e * a = a) :
    e = 1 :=
  mul_eq_right.mp (he 1)

/-! @end -/

/-!
@problem inverse_unique
@title The Inverse is Unique
@concept consequences

@preamble
An element has one inverse, not several, and the argument shows more. Call `b` a left inverse of `a` when `b * a = 1`, as for functions in the first section, and `c` a right inverse when `a * c = 1`. Then `b = c`: the product `b * a * c` reduces to either one, by the one hypothesis or the other. So an element with a right inverse has it equal to `a⁻¹`, which is a left inverse; this is why a text whose axiom only asks that an inverse exist may write it `a⁻¹`, as a function of `a`. It is also how an inverse is recognized: to show that some `b` is `a⁻¹`, it is enough to check `a * b = 1`, which Mathlib names `inv_eq_of_mul_eq_one_right`. The elements are implicit in both theorems, since each is applied to the hypotheses that fix them.
@description
Show that a left inverse and a right inverse of the same element are equal, and deduce that `a * b = 1` forces `a⁻¹ = b`. The context holds the five laws; the cancellations of the first problem are not needed here.
-/

@[to_additive left_neg_eq_right_neg]
theorem left_inv_eq_right_inv {G : Type u} [Group G] {a b c : G} (hba : b * a = 1)
    (hac : a * c = 1) : b = c := by
  rw [← mul_one b, ← hac, ← mul_assoc, hba, one_mul]

@[to_additive neg_eq_of_add_eq_zero_right]
theorem inv_eq_of_mul_eq_one_right {G : Type u} [Group G] {a b : G} (h : a * b = 1) : a⁻¹ = b :=
  left_inv_eq_right_inv (inv_mul_cancel a) h

/-! @end -/

/-!
@problem inv_inv
@title The Inverse of an Inverse
@concept consequences

@preamble
Uniqueness turns a question about `⁻¹` into a check. To identify the inverse of `a⁻¹`, written `a⁻¹⁻¹`, it is enough to find an element `b` with `a⁻¹ * b = 1`, and one of the laws names such an element. The same check identifies the inverse of `1`. Since every element is the inverse of its inverse, inversion undoes itself; and a function that is undone by some function is injective, as the first section proved in `injective_of_left_inverse`, which the context holds together with `inv_eq_of_mul_eq_one_right`.
@description
Show that `a⁻¹⁻¹ = a`, that `1⁻¹ = 1`, and that `a ↦ a⁻¹` is an injective function on `G`. A hypothesis drawn from the last statement by `intro` reads `(fun a => a⁻¹) a = (fun a => a⁻¹) b`; `exact` sees it as `a⁻¹ = b⁻¹`, and `rw` does not, as with `∘` in the first section.
-/

@[to_additive neg_neg]
theorem inv_inv {G : Type u} [Group G] (a : G) : a⁻¹⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (inv_mul_cancel a)

@[to_additive neg_zero]
theorem inv_one {G : Type u} [Group G] : (1 : G)⁻¹ = 1 :=
  inv_eq_of_mul_eq_one_right (one_mul 1)

@[to_additive neg_injective]
theorem inv_injective {G : Type u} [Group G] : Function.Injective (fun a : G => a⁻¹) :=
  injective_of_left_inverse (fun a => a⁻¹) inv_inv

/-! @end -/

/--
@problem mul_inv_rev
@title The Inverse of a Product
@concept consequences

@preamble
The inverse of a product is the product of the inverses in the reverse order: `(a * b)⁻¹ = b⁻¹ * a⁻¹`. The order matters when the operation is not commutative, and it is the order of undoing: what was done last is undone first. Its additive copy, `neg_add_rev`, reads `-(a + b) = -b + -a`. By the uniqueness of inverses it is enough to check that the product of `a * b` with `b⁻¹ * a⁻¹` is `1`.
@description
Show that `(a * b)⁻¹ = b⁻¹ * a⁻¹`. The context holds `inv_eq_of_mul_eq_one_right` and the adjacent cancellations.
-/
@[to_additive neg_add_rev]
theorem mul_inv_rev {G : Type u} [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [mul_assoc, mul_inv_cancel_left, mul_inv_cancel]

/-!
@problem self_inverse_comm
@title A Group of Self-Inverse Elements is Commutative
@concept consequences

@preamble
In the group of order two every element is its own negative, a fact about two elements that `decide` checks. In any group where every element is its own inverse, the operation is commutative: compare `a * b` with its inverse, which the previous problem computes. The commutativity of `xor` is a line of `decide` as well, on `∀ a b : Bool, …`; what the general argument gives is the reason, which no table shows, and its additive copy, `add_comm_of_neg_eq_self`, applied to `Bool` is a second proof of the same equation.
@description
Show that every element of `Bool` is its own negative; that in any group in which every element is its own inverse, `a * b = b * a`; and conclude that `a + b = b + a` in `Bool` from the additive copy of the general fact. The context holds `mul_inv_rev` and the instance `AddGroup Bool` of the previous concept.
-/

theorem bool_neg_self : ∀ b : Bool, -b = b := by
  decide

@[to_additive add_comm_of_neg_eq_self]
theorem mul_comm_of_inv_eq_self {G : Type u} [Group G] (h : ∀ a : G, a⁻¹ = a) (a b : G) :
    a * b = b * a := by
  rw [← h (a * b), mul_inv_rev, h a, h b]

theorem bool_add_comm (a b : Bool) : a + b = b + a :=
  add_comm_of_neg_eq_self bool_neg_self a b

/-! @end -/

/-!
@concept cancellation
@title Cancellation
@kind theorem

In a group an equal factor on the same side of two equal products can be cancelled: `a * b = a * c` forces `b = c`. So the equation `a * x = b` has exactly one solution, and multiplying by a fixed element permutes the group, which is how every group will later be found inside a group of permutations. Cancellation is what the inverses buy, and the form in which every later proof uses them.
-/

/-!
@problem mul_left_cancel
@title Cancellation on the Left
@concept cancellation

@preamble
Two products with the same left factor are equal only when their right factors are: from `a * b = a * c` follows `b = c`, by multiplying both sides by `a⁻¹` on the left, where the adjacent inverse cancels. The converse is immediate, so the law is also an equivalence, `a * b = a * c ↔ b = c`. Both forms are used backwards, to turn a goal `b = c` into an equation of products or to read `b = c` off a hypothesis, so the elements are implicit: `mul_left_cancel h` for `h : a * b = a * c`, and `mul_left_cancel_iff.mpr h` for `h : b = c`.
@description
Show that `a * b = a * c` implies `b = c`, and state the law as an equivalence. The context holds `inv_mul_cancel_left`.
-/

@[to_additive add_left_cancel]
theorem mul_left_cancel {G : Type u} [Group G] {a b c : G} (h : a * b = a * c) : b = c := by
  rw [← inv_mul_cancel_left a b, h, inv_mul_cancel_left]

@[to_additive add_left_cancel_iff]
theorem mul_left_cancel_iff {G : Type u} [Group G] {a b c : G} : a * b = a * c ↔ b = c :=
  ⟨mul_left_cancel, fun h => by rw [h]⟩

/-! @end -/

/-!
@problem mul_right_cancel
@title Cancellation on the Right
@concept cancellation

@preamble
The mirror image: two products with the same right factor are equal only when their left factors are, so from `a * b = c * b` follows `a = c`. Since the operation need not be commutative, this is not the previous law in disguise; it is proved the same way, with the inverse multiplied on the other side.
@description
Show that `a * b = c * b` implies `a = c`, and state the law as an equivalence. The context holds `mul_inv_cancel_right`.
-/

@[to_additive add_right_cancel]
theorem mul_right_cancel {G : Type u} [Group G] {a b c : G} (h : a * b = c * b) : a = c := by
  rw [← mul_inv_cancel_right a b, h, mul_inv_cancel_right]

@[to_additive add_right_cancel_iff]
theorem mul_right_cancel_iff {G : Type u} [Group G] {a b c : G} : a * b = c * b ↔ a = c :=
  ⟨mul_right_cancel, fun h => by rw [h]⟩

/-! @end -/

/-!
@problem solve_equation
@title Solving an Equation in a Group
@concept cancellation

@preamble
In a group the equation `a * x = c` has exactly one solution, `x = a⁻¹ * c`: it is a solution by adjacent cancellation, and any solution equals it by cancellation on the left. The two directions together are an equivalence, `b = a⁻¹ * c ↔ a * b = c`, which is how an equation in a group is solved; `rw` takes an equivalence as it takes an equation, replacing one side by the other. On the integers it is the rule that `3 + x = 7` has the solution `x = -3 + 7`, the additive copy `eq_neg_add_iff_add_eq`; a closed sum such as `-3 + 7` is `4` by definition, so an equivalence whose two sides differ only by computing it holds by `Iff.rfl`.
@description
Show that `b = a⁻¹ * c` exactly when `a * b = c`, and conclude from its additive copy that in `ℤ` the equation `3 + x = 7` holds exactly when `x = 4`. The context holds `mul_left_cancel`, the adjacent cancellations and the instance `AddGroup ℤ`.
-/

@[to_additive eq_neg_add_iff_add_eq]
theorem eq_inv_mul_iff_mul_eq {G : Type u} [Group G] {a b c : G} : b = a⁻¹ * c ↔ a * b = c := by
  constructor
  · intro h
    rw [h, mul_inv_cancel_left]
  · intro h
    have h' : a * b = a * (a⁻¹ * c) := by
      rw [mul_inv_cancel_left]
      exact h
    exact mul_left_cancel h'

theorem int_solve (x : ℤ) : 3 + x = 7 ↔ x = 4 := by
  rw [← eq_neg_add_iff_add_eq]
  exact Iff.rfl

/-! @end -/

/-!
@problem mul_left_bijective
@title Left Multiplication is a Bijection
@concept cancellation

@preamble
Fix an element `a` and consider the function `x ↦ a * x` from the group to itself. Cancellation on the left says that it is injective, and the solvability of `a * x = b` says that it is surjective; so it is a bijection, a permutation of the group's elements. Every row of a multiplication table is therefore a rearrangement of the elements, with each element appearing once. Its additive copy says that adding a fixed element is a bijection: in the group of order two, adding `true` swaps the two elements, which is Boolean not, `!x`; on the integers, adding `3` shifts the number line. In a goal the function appears applied, as `(fun x => a * x) y`, which `exact` reads as `a * y` and `rw` does not, as with `∘` in the first section. The name is Mathlib's, `Group.mulLeft_bijective`.
@description
Show that for each `a`, the function `fun x => a * x` is a bijection, and check that on `Bool` adding `true` is `!`. The context holds `mul_left_cancel`, `mul_inv_cancel_left` and the instance `AddGroup Bool`.
-/

@[to_additive AddGroup.addLeft_bijective]
theorem Group.mulLeft_bijective {G : Type u} [Group G] (a : G) :
    Function.Bijective (fun x : G => a * x) := by
  constructor
  · intro x y h
    exact mul_left_cancel h
  · intro b
    exact ⟨a⁻¹ * b, mul_inv_cancel_left a b⟩

theorem bool_true_add : ∀ x : Bool, true + x = !x := by
  decide

/-! @end -/

end GroupTheory
