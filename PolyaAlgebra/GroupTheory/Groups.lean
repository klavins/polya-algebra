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

/-!
@concept group_axioms
@title The Group Axioms
@kind definition

A group is a set with an operation that is associative, has a neutral element, and gives every element an inverse. Everything the subject proves follows from these three conditions. This concept writes them as a class with its own notation, and shows that three familiar structures satisfy them: a one-element set, the Booleans under exclusive or, and the integers under addition.
-/

/-!
@problem group
@title The Definition of a Group
@concept group_axioms

@preamble
A group is a set `G` with a way of combining two elements into a third, written `a ∗ b`, that satisfies three conditions: the operation is associative, `(a ∗ b) ∗ c = a ∗ (b ∗ c)`; there is a neutral element `𝟙`, with `𝟙 ∗ a = a` and `a ∗ 𝟙 = a`; and every `a` has an inverse `a⁻¹`, with `a⁻¹ ∗ a = 𝟙` and `a ∗ a⁻¹ = 𝟙`. What the operation is differs from group to group, and `∗` stands for whichever it is: on the integers it is addition, with `0` neutral.

In Lean the definition is a class, as `Add` was in Programming in Lean. Its data are the fields `mul`, `one` and `inv`; its laws are five more fields whose types are propositions, each a statement about every element, as `∀ a : G, mul one a = a`. The notation comes after the class: `a ∗ b` for `mul a b` (typed `\ast`), `𝟙` for `one` (typed `\b1`), and `a⁻¹` for `inv a`, through Lean's class `Inv`. Mathlib writes the operation `*` and the neutral element `1`; the names of the laws are its.
@description
Define the class `Group G`: the data `mul`, `one` and `inv`, and the five laws `mul_assoc`, `one_mul`, `mul_one`, `inv_mul_cancel` and `mul_inv_cancel`, named by the order of their symbols (`one_mul` for `𝟙 ∗ a = a`), written as the preamble states them, with the elements as explicit arguments.
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

/-- `a ∗ b`: the group operation, whatever the group's operation is. -/
infixl:70 " ∗ " => Group.mul

/-- `𝟙`: the neutral element of a group. -/
notation "𝟙" => Group.one

/-!
@problem unit_group
@title The Trivial Group
@concept group_axioms

@preamble
The smallest group has one element, which is then the neutral element, and the operation and the inverse have only one value to take. Lean's type `Unit` has the one element `()`, and a statement about every element of `Unit` is settled by `decide`, as one about `Fin 4` was.

`a⁻¹` is the notation of Lean's class
```lean
class Inv (α : Type u) where
  inv : α → α
```
as `+` is the notation of `Add`. The instance given in the context says that every type with a `Group` instance has one, with the field `Group.inv` as its `inv`; the lines `infixl:70 " ∗ " => Group.mul` and `notation "𝟙" => Group.one` after the class give the other two symbols.

An instance of a class with several fields is built with `where`, as an equivalence was in the first section: `instance : Group Unit where`, then one field per line, a function field with its arguments before the `:=`, as `mul _ _ := ()`, a constant field as `one := ()`, and a law as `mul_assoc := by decide`.
@description
Supply the instance `Group Unit`, the trivial group.
-/

/-- @given -/
instance {G : Type u} [Group G] : Inv G := ⟨Group.inv⟩

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
example : (𝟙 : Unit) = () ∧ () ∗ () = () ∧ ()⁻¹ = () := by decide

/-! @end -/

/-!
@problem bool_xor_group
@title The Group of Order Two
@concept group_axioms

@preamble
The *order* of a finite group is its number of elements, `Fintype.card G`. A group of order two has the neutral element and one other element `a`, and the only room left in its table is `a ∗ a = 𝟙`, since `a ∗ a = a` would force `a = 𝟙` once an `a` is cancelled: the other element is its own inverse. The Booleans under exclusive or are this group. `xor a b` is `true` when exactly one of `a` and `b` is, so `false` is neutral, and `xor a a = false` for both values of `a`. Each law is a statement about every element of `Bool`, which `decide` settles; so is the order.
@description
Supply the instance `Group Bool` with `xor` as the operation, `false` as the neutral element and each element as its own inverse, and show that this group has order two.
-/

instance : Group Bool where
  mul := xor
  one := false
  inv b := b
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide
  mul_inv_cancel := by decide

/-- @spec -/
example : true ∗ true = false ∧ true ∗ false = true ∧ false ∗ true = true ∧
    false ∗ false = false ∧ (𝟙 : Bool) = false := by decide

theorem card_bool : Fintype.card Bool = 2 := by
  decide

/-! @end -/

/-!
@problem int_add_group
@title The Integers Under Addition
@concept group_axioms

@preamble
The integers under addition are a group: addition is associative, `0` is neutral, and `-a` is the inverse of `a`. The operation of this group is `+`, so on `ℤ` the symbol `a ∗ b` means `a + b`, `𝟙` means `0` and `a⁻¹` means `-a`; the product `a * b` is untouched, since `∗` is a symbol of its own. Core Lean has the five laws of addition on `ℤ` under the names `Int.add_assoc`, `Int.zero_add`, `Int.add_zero`, `Int.add_left_neg : -a + a = 0` and `Int.add_right_neg : a + -a = 0`. Inside the instance, where a law is stated in the `+` the field was just defined as, `omega` also closes it once its elements are introduced. Outside the instance `a ∗ b` is `Group.mul a b`, a term `omega` does not open; an equation that unfolds to itself is closed by `rfl`.
@description
Supply the instance `Group ℤ` with addition as the operation, and show that on `ℤ` the three symbols mean what they should: `a ∗ b = a + b`, `𝟙 = 0` and `a⁻¹ = -a`, each of which holds by definition.
-/

instance : Group ℤ where
  mul := (· + ·)
  one := 0
  inv := (- ·)
  mul_assoc := Int.add_assoc
  one_mul := Int.zero_add
  mul_one := Int.add_zero
  inv_mul_cancel := Int.add_left_neg
  mul_inv_cancel := Int.add_right_neg

/-- @spec -/
example : (3 : ℤ) ∗ 4 = 7 ∧ (𝟙 : ℤ) = 0 ∧ (3 : ℤ)⁻¹ = -3 := by decide

theorem int_mul_eq_add (a b : ℤ) : a ∗ b = a + b := rfl

theorem int_one_eq_zero : (𝟙 : ℤ) = 0 := rfl

theorem int_inv_eq_neg (a : ℤ) : a⁻¹ = -a := rfl

/-! @end -/

/-!
@concept consequences
@title Consequences of the Axioms
@kind theorem

The axioms ask for a neutral element and for inverses; they do not say that these are unique, that the inverse of a product is the product of the inverses in reverse order, or that the inverse of `a⁻¹` is `a`. Each follows in a few steps from the five laws. These facts are the tools every later proof reaches for, so they are proved once here, under the names Mathlib gives them.
-/

/-!
@problem cancel_adjacent
@title Cancelling an Adjacent Inverse
@concept consequences

@preamble
The five laws, restated under the notation, are given in the context: `mul_assoc : a ∗ b ∗ c = a ∗ (b ∗ c)`, `one_mul : 𝟙 ∗ a = a`, `mul_one : a ∗ 𝟙 = a`, `inv_mul_cancel : a⁻¹ ∗ a = 𝟙` and `mul_inv_cancel : a ∗ a⁻¹ = 𝟙`. They are rewrite rules. `rw [mul_assoc]` moves a parenthesis to the right and `rw [← mul_assoc]` moves it to the left; `rw [inv_mul_cancel]` replaces an `a⁻¹ ∗ a` by `𝟙`. Since `a ∗ b ∗ c` is `(a ∗ b) ∗ c`, a product written without parentheses associates to the left, and the rewrite that regroups it has to be chosen accordingly.

The first use of the laws is that an inverse standing next to its element cancels it, whatever else is in the product: `a⁻¹ ∗ (a ∗ b) = b`, and likewise with the inverse on the other side, or at the other end of the product. These four equations are the steps every later argument is made of.
@description
Show the four forms of adjacent cancellation: `a⁻¹ ∗ (a ∗ b) = b`, `a ∗ (a⁻¹ ∗ b) = b`, `a ∗ b ∗ b⁻¹ = a` and `a ∗ b⁻¹ ∗ b = a`.
-/

/-- @given -/
theorem mul_assoc {G : Type u} [Group G] (a b c : G) : a ∗ b ∗ c = a ∗ (b ∗ c) := by
  apply Group.mul_assoc

/-- @given -/
theorem one_mul {G : Type u} [Group G] (a : G) : 𝟙 ∗ a = a := by
  apply Group.one_mul

/-- @given -/
theorem mul_one {G : Type u} [Group G] (a : G) : a ∗ 𝟙 = a := by
  apply Group.mul_one

/-- @given -/
theorem inv_mul_cancel {G : Type u} [Group G] (a : G) : a⁻¹ ∗ a = 𝟙 := by
  apply Group.inv_mul_cancel

/-- @given -/
theorem mul_inv_cancel {G : Type u} [Group G] (a : G) : a ∗ a⁻¹ = 𝟙 := by
  apply Group.mul_inv_cancel

theorem inv_mul_cancel_left {G : Type u} [Group G] (a b : G) : a⁻¹ ∗ (a ∗ b) = b := by
  rw [← mul_assoc, inv_mul_cancel, one_mul]

theorem mul_inv_cancel_left {G : Type u} [Group G] (a b : G) : a ∗ (a⁻¹ ∗ b) = b := by
  rw [← mul_assoc, mul_inv_cancel, one_mul]

theorem mul_inv_cancel_right {G : Type u} [Group G] (a b : G) : a ∗ b ∗ b⁻¹ = a := by
  rw [mul_assoc, mul_inv_cancel, mul_one]

theorem inv_mul_cancel_right {G : Type u} [Group G] (a b : G) : a ∗ b⁻¹ ∗ b = a := by
  rw [mul_assoc, inv_mul_cancel, mul_one]

/-! @end -/

/-!
@problem neutral_unique
@title The Neutral Element is Unique
@concept consequences

@preamble
The axioms say that there is a neutral element; they do not say that there is only one. There is: a second neutral element `e` would give `e = e ∗ 𝟙 = 𝟙`. More is true. An element that acts as a neutral element on a single `a`, with `a ∗ b = a`, is already `𝟙`: multiply by `a⁻¹` on the left, and the adjacent inverse cancels. In particular `𝟙` is the only solution of `x ∗ x = x`.

Mathlib states these as equivalences, `mul_eq_left : a ∗ b = a ↔ b = 𝟙` and `mul_eq_right : a ∗ b = b ↔ a = 𝟙`, with the elements implicit, since a use `mul_eq_left.mp h` reads them off `h`.
@description
Show that `a ∗ b = a` exactly when `b = 𝟙`, and that `a ∗ b = b` exactly when `a = 𝟙`; conclude that an element `e` with `e ∗ a = a` for every `a` is `𝟙`. The context holds the four adjacent cancellations of the previous problem.
-/

theorem mul_eq_left {G : Type u} [Group G] {a b : G} : a ∗ b = a ↔ b = 𝟙 := by
  constructor
  · intro h
    rw [← inv_mul_cancel_left a b, h, inv_mul_cancel]
  · intro h
    rw [h, mul_one]

theorem mul_eq_right {G : Type u} [Group G] {a b : G} : a ∗ b = b ↔ a = 𝟙 := by
  constructor
  · intro h
    rw [← mul_inv_cancel_right a b, h, mul_inv_cancel]
  · intro h
    rw [h, one_mul]

theorem eq_one_of_left_neutral {G : Type u} [Group G] {e : G} (he : ∀ a : G, e ∗ a = a) :
    e = 𝟙 :=
  mul_eq_right.mp (he 𝟙)

/-! @end -/

/-!
@problem inverse_unique
@title The Inverse is Unique
@concept consequences

@preamble
An element has one inverse, not several, and the argument shows more. Call `b` a left inverse of `a` when `b ∗ a = 𝟙`, as for functions in the first section, and `c` a right inverse when `a ∗ c = 𝟙`. Then `b = c`: the product `b ∗ a ∗ c` reduces to either one, by the one hypothesis or the other. So an element with a right inverse has it equal to `a⁻¹`, which is a left inverse; this is why a text whose axiom only asks that an inverse exist may write it `a⁻¹`, as a function of `a`. It is also how an inverse is recognized: to show that some `b` is `a⁻¹`, it is enough to check `a ∗ b = 𝟙`, which Mathlib names `inv_eq_of_mul_eq_one_right`. The elements are implicit in both theorems, since each is applied to the hypotheses that fix them.
@description
Show that a left inverse and a right inverse of the same element are equal, and deduce that `a ∗ b = 𝟙` forces `a⁻¹ = b`. The context holds the five laws; the cancellations of the first problem are not needed here.
-/

theorem left_inv_eq_right_inv {G : Type u} [Group G] {a b c : G} (hba : b ∗ a = 𝟙)
    (hac : a ∗ c = 𝟙) : b = c := by
  rw [← mul_one b, ← hac, ← mul_assoc, hba, one_mul]

theorem inv_eq_of_mul_eq_one_right {G : Type u} [Group G] {a b : G} (h : a ∗ b = 𝟙) : a⁻¹ = b :=
  left_inv_eq_right_inv (inv_mul_cancel a) h

/-! @end -/

/-!
@problem inv_inv
@title The Inverse of an Inverse
@concept consequences

@preamble
Uniqueness turns a question about `⁻¹` into a check. To identify the inverse of `a⁻¹`, written `a⁻¹⁻¹`, it is enough to find an element `b` with `a⁻¹ ∗ b = 𝟙`, and one of the laws names such an element. The same check identifies the inverse of `𝟙`. Since every element is the inverse of its inverse, inversion undoes itself; and a function that is undone by some function is injective, as the first section proved in `injective_of_left_inverse`, which the context holds together with `inv_eq_of_mul_eq_one_right`.
@description
Show that `a⁻¹⁻¹ = a`, that `𝟙⁻¹ = 𝟙`, and that `a ↦ a⁻¹` is an injective function on `G`. A hypothesis drawn from the last statement by `intro` reads `(fun a => a⁻¹) a = (fun a => a⁻¹) b`; `exact` sees it as `a⁻¹ = b⁻¹`, and `rw` does not, as with `∘` in the first section.
-/

theorem inv_inv {G : Type u} [Group G] (a : G) : a⁻¹⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (inv_mul_cancel a)

theorem inv_one {G : Type u} [Group G] : (𝟙 : G)⁻¹ = 𝟙 :=
  inv_eq_of_mul_eq_one_right (one_mul 𝟙)

theorem inv_injective {G : Type u} [Group G] : Function.Injective (fun a : G => a⁻¹) :=
  injective_of_left_inverse (fun a => a⁻¹) inv_inv

/-! @end -/

/--
@problem mul_inv_rev
@title The Inverse of a Product
@concept consequences

@preamble
The inverse of a product is the product of the inverses in the reverse order: `(a ∗ b)⁻¹ = b⁻¹ ∗ a⁻¹`. The order matters when the operation is not commutative, and it is the order of undoing: what was done last is undone first. On `ℤ`, where the operation is addition, the statement reads `-(a + b) = -b + -a`. By the uniqueness of inverses it is enough to check that the product of `a ∗ b` with `b⁻¹ ∗ a⁻¹` is `𝟙`.
@description
Show that `(a ∗ b)⁻¹ = b⁻¹ ∗ a⁻¹`. The context holds `inv_eq_of_mul_eq_one_right` and the adjacent cancellations.
-/
theorem mul_inv_rev {G : Type u} [Group G] (a b : G) : (a ∗ b)⁻¹ = b⁻¹ ∗ a⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [mul_assoc, mul_inv_cancel_left, mul_inv_cancel]

/-!
@problem self_inverse_comm
@title A Group of Self-Inverse Elements is Commutative
@concept consequences

@preamble
In the group of order two every element is its own inverse, a fact about two elements that `decide` checks. In any group where every element is its own inverse, the operation is commutative: compare `a ∗ b` with its inverse, which the previous problem computes. The commutativity of `xor` is a line of `decide` as well, on `∀ a b : Bool, …`; what the general argument gives is the reason, which no table shows, and the general fact applied to `Bool` is a second proof of the same equation.
@description
Show that every element of `Bool` is its own inverse; that in any group with this property, `a ∗ b = b ∗ a`; and conclude that `a ∗ b = b ∗ a` in `Bool` from the general fact. The context holds `mul_inv_rev` and the instance `Group Bool` of the previous concept.
-/

theorem bool_inv_self : ∀ b : Bool, b⁻¹ = b := by
  decide

theorem mul_comm_of_inv_eq_self {G : Type u} [Group G] (h : ∀ a : G, a⁻¹ = a) (a b : G) :
    a ∗ b = b ∗ a := by
  rw [← h (a ∗ b), mul_inv_rev, h a, h b]

theorem bool_mul_comm (a b : Bool) : a ∗ b = b ∗ a :=
  mul_comm_of_inv_eq_self bool_inv_self a b

/-! @end -/

/-!
@concept cancellation
@title Cancellation
@kind theorem

In a group an equal factor on the same side of two equal products can be cancelled: `a ∗ b = a ∗ c` forces `b = c`. So the equation `a ∗ x = b` has exactly one solution, and multiplying by a fixed element permutes the group, which is how every group will later be found inside a group of permutations. Cancellation is what the inverses buy, and the form in which every later proof uses them.
-/

/-!
@problem mul_left_cancel
@title Cancellation on the Left
@concept cancellation

@preamble
Two products with the same left factor are equal only when their right factors are: from `a ∗ b = a ∗ c` follows `b = c`, by multiplying both sides by `a⁻¹` on the left, where the adjacent inverse cancels. The converse is immediate, so the law is also an equivalence, `a ∗ b = a ∗ c ↔ b = c`. Both forms are used backwards, to turn a goal `b = c` into an equation of products or to read `b = c` off a hypothesis, so the elements are implicit: `mul_left_cancel h` for `h : a ∗ b = a ∗ c`, and `mul_left_cancel_iff.mpr h` for `h : b = c`.
@description
Show that `a ∗ b = a ∗ c` implies `b = c`, and state the law as an equivalence. The context holds `inv_mul_cancel_left`.
-/

theorem mul_left_cancel {G : Type u} [Group G] {a b c : G} (h : a ∗ b = a ∗ c) : b = c := by
  rw [← inv_mul_cancel_left a b, h, inv_mul_cancel_left]

theorem mul_left_cancel_iff {G : Type u} [Group G] {a b c : G} : a ∗ b = a ∗ c ↔ b = c :=
  ⟨mul_left_cancel, fun h => by rw [h]⟩

/-! @end -/

/-!
@problem mul_right_cancel
@title Cancellation on the Right
@concept cancellation

@preamble
The mirror image: two products with the same right factor are equal only when their left factors are, so from `a ∗ b = c ∗ b` follows `a = c`. Since the operation need not be commutative, this is not the previous law in disguise; it is proved the same way, with the inverse multiplied on the other side.
@description
Show that `a ∗ b = c ∗ b` implies `a = c`, and state the law as an equivalence. The context holds `mul_inv_cancel_right`.
-/

theorem mul_right_cancel {G : Type u} [Group G] {a b c : G} (h : a ∗ b = c ∗ b) : a = c := by
  rw [← mul_inv_cancel_right a b, h, mul_inv_cancel_right]

theorem mul_right_cancel_iff {G : Type u} [Group G] {a b c : G} : a ∗ b = c ∗ b ↔ a = c :=
  ⟨mul_right_cancel, fun h => by rw [h]⟩

/-! @end -/

/-!
@problem solve_equation
@title Solving an Equation in a Group
@concept cancellation

@preamble
In a group the equation `a ∗ x = c` has exactly one solution, `x = a⁻¹ ∗ c`: it is a solution by adjacent cancellation, and any solution equals it by cancellation on the left. The two directions together are an equivalence, `b = a⁻¹ ∗ c ↔ a ∗ b = c`, which is how an equation in a group is solved; `rw` takes an equivalence as it takes an equation, replacing one side by the other. On the integers it is the rule that `3 + x = 7` has the solution `x = -3 + 7`, computed in the group's operation. In a statement about `ℤ`, `omega` does not see the addition beneath `∗`; the three theorems of the integers' instance, `int_mul_eq_add` and its companions, unfold the symbols, and a closed equation such as `3⁻¹ ∗ 7 = 4` holds by `rfl`.
@description
Show that `b = a⁻¹ ∗ c` exactly when `a ∗ b = c`, and that in `ℤ` the equation `3 ∗ x = 7` holds exactly when `x = 4`. The context holds `mul_left_cancel`, the adjacent cancellations, the instance `Group ℤ`, and `int_mul_eq_add` and `int_inv_eq_neg` from the first concept.
-/

theorem eq_inv_mul_iff_mul_eq {G : Type u} [Group G] {a b c : G} : b = a⁻¹ ∗ c ↔ a ∗ b = c := by
  constructor
  · intro h
    rw [h, mul_inv_cancel_left]
  · intro h
    have h' : a ∗ b = a ∗ (a⁻¹ ∗ c) := by
      rw [mul_inv_cancel_left]
      exact h
    exact mul_left_cancel h'

theorem int_solve (x : ℤ) : (3 : ℤ) ∗ x = 7 ↔ x = 4 := by
  rw [← eq_inv_mul_iff_mul_eq, int_inv_eq_neg, int_mul_eq_add]
  omega

/-! @end -/

/-!
@problem mul_left_bijective
@title Left Multiplication is a Bijection
@concept cancellation

@preamble
Fix an element `a` and consider the function `x ↦ a ∗ x` from the group to itself. Cancellation on the left says that it is injective, and the solvability of `a ∗ x = b` says that it is surjective; so it is a bijection, a permutation of the group's elements. Every row of a multiplication table is therefore a rearrangement of the elements, with each element appearing once. In the group of order two, multiplication by `true` swaps the two elements, which is negation; on `ℤ`, adding `3` shifts the number line. In a goal the function appears applied, as `(fun x => a ∗ x) y`, which `exact` reads as `a ∗ y` and `rw` does not, as with `∘` in the first section. The name is Mathlib's, `Group.mulLeft_bijective`.
@description
Show that for each `a`, the function `fun x => a ∗ x` is a bijection, and check that on `Bool` multiplication by `true` is negation. The context holds `mul_left_cancel`, `mul_inv_cancel_left` and the instance `Group Bool`.
-/

theorem Group.mulLeft_bijective {G : Type u} [Group G] (a : G) :
    Function.Bijective (fun x : G => a ∗ x) := by
  constructor
  · intro x y h
    exact mul_left_cancel h
  · intro b
    exact ⟨a⁻¹ ∗ b, mul_inv_cancel_left a b⟩

theorem bool_mul_true : ∀ x : Bool, true ∗ x = !x := by
  decide

/-! @end -/

end GroupTheory
