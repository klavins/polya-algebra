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

/-! @section Prerequisites -/

universe u v w

namespace GroupTheory

/-!
@concept mathlib_sets
@title Mathlib's Sets
@kind theorem

Set Theory built sets as predicates and proved their laws by hand. Mathlib's sets are the same objects under their own names. A subgroup is a set of group elements, and a set can serve as a type, which is how a subgroup becomes a group in its own right.
-/

/--
@problem image_union
@title The Image of a Union
@concept mathlib_sets

@preamble
Mathlib's `Set α` is `α → Prop`, as in Set Theory, and the image and the union are the sets they were there:
```lean
def Set (α : Type u) := α → Prop
def Set.image (f : α → β) (S : Set α) : Set β := {y | ∃ x ∈ S, f x = y}
def Set.union (S T : Set α) : Set α := {x | x ∈ S ∨ x ∈ T}
```
`{x | p x}` is the set of the `x` with `p x`, and a membership `y ∈ {x | p x}` means `p y`. We write `f '' S` for `Set.image f S`. The quantifier `∃ x ∈ S, …` abbreviates `∃ x, x ∈ S ∧ …`, so the pattern `⟨x, hx, hy⟩` takes apart a membership in an image, as in Set Theory.

Two sets with the same members are equal. This is one direction of Set Theory's `setext`, and Mathlib calls it `Set.ext`:
```lean
theorem Set.ext {S T : Set α} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T
```
@description
Show that the image of a union is the union of the images, as Set Theory proved for its own sets.
-/
theorem image_union {α : Type u} {β : Type v} (f : α → β) (S T : Set α) :
    f '' (S ∪ T) = f '' S ∪ f '' T := by
  apply Set.ext
  intro y
  constructor
  · intro ⟨x, hx, hy⟩
    cases hx with
    | inl h => exact Or.inl ⟨x, h, hy⟩
    | inr h => exact Or.inr ⟨x, h, hy⟩
  · intro h
    cases h with
    | inl h =>
      obtain ⟨x, hx, hy⟩ := h
      exact ⟨x, Or.inl hx, hy⟩
    | inr h =>
      obtain ⟨x, hx, hy⟩ := h
      exact ⟨x, Or.inr hx, hy⟩

/--
@problem image_mono
@title Images Preserve Inclusion
@concept mathlib_sets

@preamble
Mathlib's inclusion differs from Set Theory's in one detail. Set Theory's `A ⊆ B` was `∀ x, x ∈ A → x ∈ B`; Mathlib's makes the point strict implicit, as in the `Function.Injective` of The Natural Numbers:
```lean
def Set.Subset (S T : Set α) : Prop := ∀ ⦃a⦄, a ∈ S → a ∈ T
```
So a proof `h : S ⊆ T` is applied to a membership alone, and Lean reads the point off it; `h x hx` is an error. A goal `S ⊆ T` is still opened by `intro`, which names the point and its membership.
@description
Show that the image of a smaller set is smaller: if `S ⊆ T`, then `f '' S ⊆ f '' T`.
-/
theorem image_mono {α : Type u} {β : Type v} (f : α → β) (S T : Set α) (h : S ⊆ T) :
    f '' S ⊆ f '' T := by
  intro y ⟨x, hx, hy⟩
  exact ⟨x, h hx, hy⟩

/--
@problem restrict_mem_image
@title A Set as a Type
@concept mathlib_sets

@preamble
A set `S : Set α` can stand where a type is expected, and then it means the type of its elements. We write it `↥S`, or usually just `S`. An element of that type is a pair `⟨x, hx⟩` of a point `x : α` and a proof `hx : x ∈ S`.

An element `a : S` holds its point and its proof as the fields `a.1` and `a.2`. The point is also written `(a : α)`, by coercion, and Lean prints it as `↑a` in a goal. Where a point of `α` is expected and an element of `S` is given, as in `f a`, Lean inserts the coercion by itself.
@description
Let `a` be an element of `S` taken as a type. Show that `f a` lies in the image `f '' S`.
-/
theorem restrict_mem_image {α : Type u} {β : Type v} (f : α → β) (S : Set α) (a : S) :
    f a ∈ f '' S :=
  ⟨a.1, a.2, rfl⟩

/--
@problem image_eq_range
@title The Image as a Range
@concept mathlib_sets

@preamble
The set of all values of a function `g : ι → β` is its range, `Set.range g`:
```lean
def Set.range (g : ι → β) : Set β := {y | ∃ i, g i = y}
```
An `intro` pattern takes a membership in a range apart directly, as it does for an image. Restricting `f : α → β` to the set `S` gives a function on `S` as a type, `fun x : S => f x`, whose values are the values of `f` at the points of `S`: its range is the image of `S`.
@description
Show that the image of `S` under `f` is the range of the restriction of `f` to `S`.
-/
theorem image_eq_range {α : Type u} {β : Type v} (f : α → β) (S : Set α) :
    f '' S = Set.range (fun x : S => f x) := by
  apply Set.ext
  intro y
  constructor
  · intro ⟨x, hx, hy⟩
    exact ⟨⟨x, hx⟩, hy⟩
  · intro ⟨⟨x, hx⟩, hy⟩
    exact ⟨x, hx, hy⟩

/-!
@concept functions
@title Injective and Surjective Functions
@kind theorem

A function is injective when distinct inputs have distinct values, and surjective when every value is taken. Homomorphisms are functions, and the subject's counting rests on injections and surjections.
-/

/-!
@problem composites
@title Composites of Injective and Surjective Functions
@concept functions

@preamble
Set Theory called a function injective when it sends distinct elements to distinct values, and The Natural Numbers wrote the property in Lean's form, to show that `succ` has it. Mathlib's two definitions are
```lean
def Function.Injective (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂
def Function.Surjective (f : α → β) : Prop := ∀ b, ∃ a, f a = b
```
The binders `⦃a₁ a₂⦄` are strict implicit: from `hf : Function.Injective f` and `h : f a = f b`, the term `hf h` proves `a = b`, the two points being read off `h`. A goal `Function.Injective f` is still opened by `intro`, which names the two points and the equation.

The composite `g ∘ f` is `fun x => g (f x)`, so `(g ∘ f) x` is `g (f x)` by definition. `exact` accepts either form for the other, but `rw` matches only what is written, and this rewrite turns the one into the other:
```lean
theorem Function.comp_apply : (g ∘ f) x = g (f x)
```
@description
Show that the composite of two injective functions is injective, and that the composite of two surjective functions is surjective.
-/

theorem injective_comp {α : Type u} {β : Type v} {γ : Type w} {f : α → β} {g : β → γ}
    (hg : Function.Injective g) (hf : Function.Injective f) : Function.Injective (g ∘ f) := by
  intro a b h
  exact hf (hg h)

theorem surjective_comp {α : Type u} {β : Type v} {γ : Type w} {f : α → β} {g : β → γ}
    (hg : Function.Surjective g) (hf : Function.Surjective f) : Function.Surjective (g ∘ f) := by
  intro c
  obtain ⟨b, hb⟩ := hg c
  obtain ⟨a, ha⟩ := hf b
  exact ⟨a, by rw [Function.comp_apply, ha, hb]⟩

/-! @end -/

/-!
@problem one_sided_inverses
@title One-Sided Inverses
@concept functions

@preamble
A function is often shown injective or surjective not from the definition but from a second function that undoes it, in one direction or the other. A *left inverse* of `f : α → β` is a function `g : β → α` with `g (f x) = x` for every `x`; a *right inverse* is a `g` with `f (g y) = y` for every `y`. A function may have one without the other: doubling on `ℕ` has a left inverse, halving, and no right inverse. Mathlib names the two conditions, with the inverse written first:
```lean
def Function.LeftInverse (g : β → α) (f : α → β) : Prop := ∀ x, g (f x) = x
def Function.RightInverse (g : β → α) (f : α → β) : Prop := Function.LeftInverse f g
```
The statements below write the two conditions out instead of using these names.
@description
Show that a function with a left inverse is injective, and that a function with a right inverse is surjective.
-/

theorem injective_of_left_inverse {α : Type u} {β : Type v} {f : α → β} (g : β → α)
    (h : ∀ x, g (f x) = x) : Function.Injective f := by
  intro a b hab
  rw [← h a, ← h b, hab]

theorem surjective_of_right_inverse {α : Type u} {β : Type v} {f : α → β} (g : β → α)
    (h : ∀ y, f (g y) = y) : Function.Surjective f := by
  intro y
  exact ⟨g y, h y⟩

/-! @end -/

/-!
@concept bijections
@title Bijections as Equivalences
@kind definition

A bijection between two types, packaged with its inverse, is an equivalence. Two types in equivalence are the same up to renaming, and two groups are the same when an equivalence between them respects the operation. A permutation of a type is an equivalence of the type with itself, and the permutations of three points are the first noncommutative group met.
-/

/-!
@problem not_equiv
@title Negation as an Equivalence
@concept bijections

@preamble
An equivalence between `α` and `β` is a function in each direction, with the two laws saying that they undo each other:
```lean
structure Equiv (α : Type u) (β : Type v) where
  toFun : α → β
  invFun : β → α
  left_inv : Function.LeftInverse invFun toFun
  right_inv : Function.RightInverse invFun toFun
```
We write `α ≃ β` for the type of equivalences, and `e x` for `e.toFun x`, by coercion.

A structure is built with the brace notation of Programming in Lean. Lean also accepts the same fields without braces and commas, one `field := …` per line after `def e : α ≃ β where`.

`decide` proves a statement about every element of a type with finitely many elements, such as `Bool`, by checking each one, so it settles the two inverse laws here.
@description
Define `notEquiv : Bool ≃ Bool`, the equivalence that negates a Boolean, with `not` in both directions.
-/

def notEquiv : Bool ≃ Bool where
  toFun := not
  invFun := not
  left_inv := by decide
  right_inv := by decide

/-- @spec -/
example : notEquiv true = false ∧ notEquiv false = true := by decide

/-! @end -/

/-!
@problem bool_equiv_fin_two
@title The Booleans and the Two-Element Type
@concept bijections

@preamble
`Fin n` is the type of natural numbers below `n`. An element of `Fin n` is a pair `⟨k, h⟩` of a value `k : ℕ` and a proof `h : k < n`; for an element `i` these are `i.val` and `i.isLt`. The numerals `0`, …, `n - 1` of `Fin n` are the numbers they name.

`Fin 2` has two elements, and so does `Bool`, so the two types are in bijection. The shape of the previous problem serves again, with `Fin 2` in place of the second `Bool`. `Fin n` has decidable equality, so a function out of it may test `if i = 0 then … else …`, and a `match` on the numerals `0`, `1`, … is accepted when they cover the type.
@description
Define `boolEquivFinTwo : Bool ≃ Fin 2`, sending `false` to `0` and `true` to `1`.
-/

def boolEquivFinTwo : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := if i = 1 then true else false
  left_inv := by decide
  right_inv := by decide

/-- @spec -/
example : boolEquivFinTwo false = 0 ∧ boolEquivFinTwo true = 1 := by decide

/-! @end -/

/--
@problem equiv_bijective
@title An Equivalence is a Bijection
@concept bijections

@preamble
We write `e.symm : β ≃ α` for the inverse of an equivalence `e : α ≃ β`. Its two laws are used under Mathlib's names:
```lean
theorem Equiv.symm_apply_apply (e : α ≃ β) (x : α) : e.symm (e x) = x
theorem Equiv.apply_symm_apply (e : α ≃ β) (y : β) : e (e.symm y) = y
```
A function is *bijective* when it is both injective and surjective, and Mathlib's definition is the conjunction:
```lean
def Function.Bijective (f : α → β) : Prop :=
  Function.Injective f ∧ Function.Surjective f
```
`hf.1` and `hf.2` are the halves of `hf : Function.Bijective f`.
@description
Show that the function of an equivalence is a bijection. The context holds `injective_of_left_inverse` and `surjective_of_right_inverse` of the previous problem.
-/
theorem equiv_bijective {α : Type u} {β : Type v} (e : α ≃ β) : Function.Bijective e := by
  constructor
  · exact injective_of_left_inverse e.symm e.symm_apply_apply
  · exact surjective_of_right_inverse e.symm e.apply_symm_apply

/-!
@problem rot3
@title A Rotation of Three Points
@concept bijections

@preamble
A permutation of a type `X` is a bijection from `X` to itself, and Mathlib writes the type of permutations `Equiv.Perm X`, which is `X ≃ X`. Two equivalences compose: `e.trans f : α ≃ γ`, for `e : α ≃ β` and `f : β ≃ γ`, applies `e` and then `f`; and `Equiv.refl X` is the identity permutation of `X`.

The three points `0`, `1`, `2` of `Fin 3` are rotated by `i ↦ i + 1`: addition in `Fin n` wraps around, so `2 + 1 = 0`. A closed statement about `Fin 3`, such as `rot3 2 = 0`, is settled by `decide`, which computes both sides. Two permutations of `Fin 3` are equal when they agree at each of the three points, so an equation between them is a closed statement too.
@description
Define `rot3 : Equiv.Perm (Fin 3)`, the rotation sending `i` to `i + 1`, together with its inverse, and show that applying it three times is the identity.
-/

def rot3 : Equiv.Perm (Fin 3) where
  toFun i := i + 1
  invFun i := i + 2
  left_inv := by decide
  right_inv := by decide

/-- @spec -/
example : rot3 0 = 1 ∧ rot3 1 = 2 ∧ rot3 2 = 0 := by decide

theorem rot3_cube : (rot3.trans rot3).trans rot3 = Equiv.refl (Fin 3) := by
  decide

/-! @end -/

/-!
@problem flip3
@title Two Permutations That Do Not Commute
@concept bijections

@preamble
Adding numbers does not depend on their order, but composing functions does. Exchanging the points `0` and `1` of `Fin 3` and leaving `2` where it is reflects the triangle with vertices `0`, `1` and `2`; it sends `i` to `1 - i`. Subtraction in `Fin 3` wraps around as addition does, so `1 - 2 = 2` and `2` stays put. The reflection undoes itself. Rotating and then reflecting is not reflecting and then rotating: the two composites differ at a point, and so they differ as permutations.
@description
Define `flip3 : Equiv.Perm (Fin 3)`, the reflection sending `i` to `1 - i`, and show that `rot3.trans flip3 ≠ flip3.trans rot3`.
-/

def flip3 : Equiv.Perm (Fin 3) where
  toFun i := 1 - i
  invFun i := 1 - i
  left_inv := by decide
  right_inv := by decide

/-- @spec -/
example : flip3 0 = 1 ∧ flip3 1 = 0 ∧ flip3 2 = 2 := by decide

theorem rot3_flip3 : rot3.trans flip3 ≠ flip3.trans rot3 := by
  decide

/-! @end -/

/-!
@concept finite_types
@title Finite Types and Counting
@kind theorem

A type is finite when its elements can be listed, and the number of its elements is the length of the list. Every finite group has an order and every subgroup a size, so the subject counts. On a finite type a statement about every element can be checked by running through the list.
-/

/-!
@problem fin_four_add_neg
@title Negatives in the Four-Element Type
@concept finite_types

@preamble
Mathlib's class of finite types holds the list of all the elements, as a `Finset α`, Mathlib's type of finite sets of elements of `α`, and a proof that every element is in it:
```lean
class Fintype (α : Type u) where
  elems : Finset α
  complete : ∀ x, x ∈ elems
```
`Fintype.card α` is the number of elements, and Mathlib provides the instances for `Bool`, `Unit` and `Fin n`, with
```lean
theorem Fintype.card_fin (n : ℕ) : Fintype.card (Fin n) = n
```

A statement `∀ x : α, p x` over a finite type `α` is decided by checking `p` at each element of the list, and `∃ x : α, p x` by finding one. So `decide` settles such statements when `p` is decidable, as it settled the laws of `notEquiv` and the cube of `rot3`. It needs the type fixed: it cannot run through `Fin n` for a variable `n`.
@description
Show that every element of `Fin 4` has a negative, a `y` with `x + y = 0`, and that `Fin 4` has four elements.
-/

theorem fin_four_add_neg : ∀ x : Fin 4, ∃ y, x + y = 0 := by
  decide

theorem card_fin_four : Fintype.card (Fin 4) = 4 := by
  decide

/-! @end -/

/--
@problem card_of_equiv_prod
@title A Type Labelled by Pairs Has m * n Elements
@concept finite_types

@preamble
Two finite types in bijection have the same number of elements, and pairs of numbers can be labelled by single numbers:
```lean
theorem Fintype.card_congr (e : α ≃ β) : Fintype.card α = Fintype.card β
def finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)
```
We count a type labelled by pairs through single numbers.
@description
Let `α` be a finite type whose elements are labelled by pairs, through an equivalence `e : α ≃ Fin m × Fin n`. Show that `α` has `m * n` elements.
-/
theorem card_of_equiv_prod {α : Type u} [Fintype α] {m n : ℕ} (e : α ≃ Fin m × Fin n) :
    Fintype.card α = m * n := by
  rw [Fintype.card_congr (e.trans finProdFinEquiv), Fintype.card_fin]

/-!
@problem bijective_of_injective
@title An Injective Self-Map of a Finite Type is a Bijection
@concept finite_types

@preamble
On a finite type an injective function into the type itself must take every value. The argument is a count: an injective `f` has as many values as the type has elements, and a set of that many elements of a finite type is the whole type. Mathlib has done the count:
```lean
theorem Finite.injective_iff_surjective [Finite α] {f : α → α} :
    Function.Injective f ↔ Function.Surjective f
```
`Finite α` is a second class of finite types. It asks for no list, only that `α` be in bijection with some `Fin n`, which is what a mathematics text means by finite. Every type with a `Fintype` instance is `Finite`.
@description
Let `α` be a finite type and `f : α → α` injective. Show that `f` is a bijection. Then show that doubling, `fun x : Fin 5 => x + x`, is a bijection of `Fin 5`.
-/
theorem bijective_of_injective {α : Type u} [Finite α] {f : α → α} (hf : Function.Injective f) :
    Function.Bijective f :=
  ⟨hf, Finite.injective_iff_surjective.mp hf⟩

theorem double_bijective : Function.Bijective (fun x : Fin 5 => x + x) := by
  apply bijective_of_injective
  decide

/-! @end -/

/--
@problem pigeonhole
@title The Pigeonhole Principle
@concept finite_types

@preamble
A function from a larger finite type to a smaller one sends two elements to one value: the pigeonhole principle. Its contrapositive, that an injective function does not increase cardinality, is Mathlib's
```lean
theorem Fintype.card_le_of_injective (f : α → β) (hf : Function.Injective f) :
    Fintype.card α ≤ Fintype.card β
```
This problem produces the two elements. A function that is not injective fails the definition at some `a` and `b`, and extracting them from the negated statement is logic; `not_forall` applies to the binders `⦃a b⦄` of `Function.Injective` as to any `∀`.
@description
Let `f : α → β` be a function between finite types with `Fintype.card β < Fintype.card α`. Show that there are `a ≠ b` with `f a = f b`. Mathlib provides these laws, the first of which Logic proved:
```lean
theorem not_forall : (¬∀ x, p x) ↔ ∃ x, ¬p x
theorem Classical.not_imp : ¬(a → b) ↔ a ∧ ¬b
```
-/
theorem Fintype.exists_ne_map_eq_of_card_lt {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (f : α → β) (h : Fintype.card β < Fintype.card α) : ∃ a b, a ≠ b ∧ f a = f b := by
  have hf : ¬Function.Injective f := by
    intro hinj
    have hle := Fintype.card_le_of_injective f hinj
    omega
  obtain ⟨a, ha⟩ := not_forall.mp hf
  obtain ⟨b, hb⟩ := not_forall.mp ha
  obtain ⟨hab, hne⟩ := Classical.not_imp.mp hb
  exact ⟨a, b, hne, hab⟩

/--
@problem exists_injective_fin
@title A Finite Type Has an Injection into Some Fin n
@concept finite_types

@preamble
A `Finite` type is in bijection with some `Fin n`, and Mathlib's theorem produces the bijection, wrapped:
```lean
theorem Finite.exists_equiv_fin (α : Type u) [Finite α] : ∃ n, Nonempty (α ≃ Fin n)
```
`Nonempty α` is the proposition that `α` has an element:
```lean
class inductive Nonempty (α : Sort u) : Prop
  | intro (val : α) : Nonempty α
```
so `⟨e⟩` proves `Nonempty (α ≃ Fin n)`. Since `Finite α` is a proposition, the bijection it holds comes wrapped in `Nonempty`, and it can be unwrapped only in the proof of a proposition, as here. Mathlib's `e.injective` says that the function of an equivalence is injective.
@description
Show that a finite type `α` has an injective function into some `Fin n`.
-/
theorem Finite.exists_injective_fin (α : Type u) [Finite α] :
    ∃ n, ∃ f : α → Fin n, Function.Injective f := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  exact ⟨n, e, e.injective⟩

/-!
@concept integers_and_remainders
@title The Integers and Remainders
@kind theorem

The integers under addition are the subject's first infinite group, and the remainders modulo `n` its first finite ones. So the integers are needed with their induction, and remainders with the rules for adding them. The least number with a property and coprime numbers are met here too, for the order of an element and for primes.
-/

/--
@problem int_cases
@title An Integer is a Difference of Natural Numbers
@concept integers_and_remainders

@preamble
Lean's integers are an inductive type with two constructors, the natural numbers and the negative numbers counted from `-1`:
```lean
inductive Int where
  | ofNat   : Nat → Int
  | negSucc : Nat → Int
```
`Int.ofNat n` is the natural number `n` as an integer, written `(n : ℤ)` or `↑n`, and `Int.negSucc n` is `-(n + 1)`. Every integer has exactly one of the two forms, and `cases z with` takes an integer `z` apart into them.

The tactic `omega` proves linear arithmetic over `ℤ` as over `ℕ`; it reads `Int.negSucc n` as `-(n + 1)`, but it fails on `Int.ofNat n = ↑n`. The two are equal by definition, so `rfl` proves that equation.
@description
Show that every integer is the difference of two natural numbers: for each `z : ℤ` there are `m n : ℕ` with `z = m - n`. Here `m - n` is subtraction in `ℤ`, of the two natural numbers cast there; the goal writes it `↑m - ↑n`.
-/
theorem int_eq_sub_natCast (z : ℤ) : ∃ m n : ℕ, z = m - n := by
  cases z with
  | ofNat n => exact ⟨n, 0, rfl⟩
  | negSucc n => exact ⟨0, n + 1, by omega⟩

/--
@problem eq_zero_of_add_one
@title A Function Unchanged by a Step of One Vanishes Everywhere
@concept integers_and_remainders

@preamble
The induction of The Natural Numbers starts at `0` and steps up. An integer is reached from `0` by steps up or by steps down, so induction over `ℤ` has two steps. Mathlib's principle is
```lean
theorem Int.induction_on {p : ℤ → Prop} (z : ℤ) (zero : p 0)
    (succ : ∀ k : ℕ, p k → p (k + 1))
    (pred : ∀ k : ℕ, p (-k) → p (-k - 1)) : p z
```
and `induction z with` uses it by itself on an integer `z`: the cases are `zero`, `succ k ih` and `pred k ih`, where `k : ℕ`, and the goal of the last two is about `↑k + 1` or `-↑k - 1`.
@description
Let `f : ℤ → ℤ` take the value `0` at `0`, and the same value at `k + 1` as at `k` for every integer `k`. Show that `f` is `0` everywhere. Core Lean provides `Int.sub_add_cancel`, which you may find useful:
```lean
theorem Int.sub_add_cancel (a b : ℤ) : a - b + b = a
```
-/
theorem eq_zero_of_add_one (f : ℤ → ℤ) (h0 : f 0 = 0) (hf : ∀ k, f (k + 1) = f k) (z : ℤ) :
    f z = 0 := by
  induction z with
  | zero => exact h0
  | succ k ih =>
    rw [hf]
    exact ih
  | pred k ih =>
    rw [← hf, Int.sub_add_cancel]
    exact ih

/-!
@problem mod_add_mod
@title Adding Remainders
@concept integers_and_remainders

@preamble
For natural numbers `a` and `n`, `a % n` is the remainder of `a` on division by `n` and `a / n` the quotient. A remainder of numerals is computed by `decide` or `rfl`, as `17 % 5 = 2`. Core Lean's laws of remainders include these:
```lean
theorem Nat.mod_add_div (a n : ℕ) : a % n + n * (a / n) = a
theorem Nat.mod_lt (a : ℕ) (h : 0 < n) : a % n < n
theorem Nat.mod_eq_of_lt (h : a < n) : a % n = a
theorem Nat.mod_self (n : ℕ) : n % n = 0
```
Arithmetic modulo `n` rests on one fact: it makes no difference whether a summand is reduced before the addition or after it. Core Lean has the two halves of this:
```lean
theorem Nat.mod_add_mod (a n b : ℕ) : (a % n + b) % n = (a + b) % n
theorem Nat.add_mod_mod (a b n : ℕ) : (a + b % n) % n = (a + b) % n
```
@description
Show that a remainder modulo a positive `n` is its own remainder, and that reducing the summands modulo `n` and then adding gives the same remainder as adding first, for two summands and then for three.
-/

theorem mod_mod_of_pos (a n : ℕ) (h : 0 < n) : a % n % n = a % n := by
  apply Nat.mod_eq_of_lt
  exact Nat.mod_lt a h

theorem mod_add_mod_eq_add_mod (a b n : ℕ) : (a % n + b % n) % n = (a + b) % n := by
  rw [Nat.mod_add_mod, Nat.add_mod_mod]

theorem mod_add_mod_add_mod (a b c n : ℕ) :
    (a % n + b % n + c % n) % n = (a + b + c) % n := by
  rw [← mod_add_mod_eq_add_mod (a + b), ← mod_add_mod_eq_add_mod a b, Nat.mod_add_mod]

/-! @end -/

/-!
@problem find_least
@title The Least Number With a Property
@concept integers_and_remainders

@preamble
If some natural number has a property, a least one has it: this is the well-ordering of `ℕ`, which The Natural Numbers proved by strong induction. Mathlib's `Nat.find h`, for `h : ∃ k, p k`, is that least number, found by testing `p 0`, `p 1`, … in turn. So `p` must be decidable: the hypothesis `[DecidablePred p]` says so, and holds for a property made of equations and inequalities between numbers. Its laws are
```lean
theorem Nat.find_spec (h : ∃ n, p n) : p (Nat.find h)
theorem Nat.find_min' (h : ∃ n, p n) (hm : p m) : Nat.find h ≤ m
theorem Nat.find_eq_iff (h : ∃ n, p n) :
    Nat.find h = m ↔ p m ∧ ∀ n < m, ¬p n
```
The least multiple of `3` above `10`, for instance, is
```lean
Nat.find (p := fun k => 10 < k ∧ k % 3 = 0) ⟨12, by decide⟩
```
where `(p := …)` names the property, which Lean cannot read off the witness.
@description
Let `p` be a decidable property that some natural number has. Show that `Nat.find h` has the property and is at most every number that has it. Show also that the least number whose square exceeds `50` is `8`. `decide` cannot evaluate `Nat.find`, so work from its laws.
-/

theorem find_spec_and_min (p : ℕ → Prop) [DecidablePred p] (h : ∃ k, p k) :
    p (Nat.find h) ∧ ∀ m, p m → Nat.find h ≤ m :=
  ⟨Nat.find_spec h, fun _ hm => Nat.find_min' h hm⟩

theorem find_sqrt_fifty : Nat.find (p := fun k => 50 < k * k) ⟨8, by decide⟩ = 8 := by
  rw [Nat.find_eq_iff]
  exact ⟨by decide, by decide⟩

/-! @end -/

/-!
@problem coprime
@title Coprime Numbers
@concept integers_and_remainders

@preamble
A prime is a number whose only divisors are `1` and itself, so a prime that does not divide `m` has no common divisor with `m` but `1`: the two are *coprime*.

`a ∣ b`, "`a` divides `b`", means that `b = a * c` for some `c`, on `ℕ` as on the naturals of The Natural Numbers. `Nat.gcd a b` is the greatest common divisor, computed by Euclid's algorithm. Two numbers are coprime when their greatest common divisor is `1`: `Nat.Coprime a b` is `Nat.gcd a b = 1`, so `decide` settles it for numerals.

A number coprime to `m` that divides a product `m * n` divides `n`:
```lean
theorem Nat.Coprime.dvd_of_dvd_mul_left (hc : Nat.Coprime k m) (h : k ∣ m * n) : k ∣ n
```
@description
Show that `4` and `9` are coprime, and that a number coprime to `4` which divides `4 * n` divides `n`.
-/

theorem coprime_four_nine : Nat.Coprime 4 9 := by
  decide

theorem dvd_of_coprime_four (k n : ℕ) (hc : Nat.Coprime k 4) (h : k ∣ 4 * n) : k ∣ n :=
  hc.dvd_of_dvd_mul_left h

/-! @end -/

/-!
@concept relations
@title Equivalence Relations
@kind definition

A relation on a type is a predicate of two arguments, and an equivalence relation is one that is reflexive, symmetric and transitive: it says which elements count as the same. Cosets, conjugacy classes and orbits are the classes of equivalence relations, so the subject needs them.
-/

/--
@problem ker_equivalence
@title Equal Values Under a Function
@concept relations

@preamble
Set Theory proved `⊆` reflexive and transitive, and Logic proved `↔` symmetric and transitive. An equivalence relation is one with all three laws, which Lean collects in a structure:
```lean
structure Equivalence (r : α → α → Prop) : Prop where
  refl  : ∀ x, r x x
  symm  : ∀ {x y}, r x y → r y x
  trans : ∀ {x y z}, r x y → r y z → r x z
```
The elements in `symm` and `trans` are implicit, so in a term the last two fields are functions of the hypotheses alone. In tactic form, `constructor` leaves one goal per field, and `intro x y h` names the implicit elements as well.

Equality is the basic equivalence relation, and every function `f` carries it back to its domain: two elements are related when `f` takes the same value at them. This relation is called the *kernel* of `f`.
@description
Let `f : α → β`. Show that the relation "`f a = f b`" is an equivalence relation on `α`.
-/
theorem ker_equivalence {α : Type u} {β : Type v} (f : α → β) :
    Equivalence (fun a b => f a = f b) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h h' => h.trans h'⟩

/--
@problem same_parity
@title Same Parity on the Integers
@concept relations

@preamble
Not every equivalence relation is given by equal values of a function. Two integers have the same parity when they differ by an even number, `b = a + 2 * k` for some integer `k`: `3` and `-5` have the same parity, since `-5 = 3 + 2 * (-4)`. Each of the three laws is now the existence of an integer, and a proof of it names one.
@description
Show that having the same parity, "`b = a + 2 * k` for some `k : ℤ`", is an equivalence relation on `ℤ`.
-/
theorem same_parity_equivalence :
    Equivalence (fun a b : ℤ => ∃ k : ℤ, b = a + 2 * k) := by
  constructor
  · intro a
    exact ⟨0, by omega⟩
  · intro a b ⟨k, hk⟩
    exact ⟨-k, by omega⟩
  · intro a b c ⟨k, hk⟩ ⟨l, hl⟩
    exact ⟨k + l, by omega⟩

/--
@problem near_not_equivalence
@title Nearness is Not an Equivalence Relation
@concept relations

@preamble
The three laws are separate conditions, and a relation may have some of them without the others. Call two natural numbers *near* when they differ by at most `1`: `a ≤ b + 1` and `b ≤ a + 1`. To show that a relation is not an equivalence relation is to derive `False` from a proof `h : Equivalence r`, whose fields are used as `h.refl`, `h.symm` and `h.trans`, as `hf.1` was for a bijection; the implicit elements of `h.trans` are read off the two hypotheses it is given.
@description
Show that nearness is not an equivalence relation on `ℕ`.
-/
theorem near_not_equivalence :
    ¬Equivalence (fun a b : ℕ => a ≤ b + 1 ∧ b ≤ a + 1) := by
  intro h
  have h01 : 0 ≤ 1 + 1 ∧ 1 ≤ 0 + 1 := by omega
  have h12 : 1 ≤ 2 + 1 ∧ 2 ≤ 1 + 1 := by omega
  have h02 : 0 ≤ 2 + 1 ∧ 2 ≤ 0 + 1 := h.trans h01 h12
  omega

/-!
@problem mod_setoid
@title Congruence Modulo n as a Setoid
@concept relations

@preamble
Lean bundles a relation together with the proof that it is an equivalence, as a class:
```lean
class Setoid (α : Sort u) where
  r : α → α → Prop
  iseqv : Equivalence r
```
A setoid `s` is applied like its relation, `s a b`, and a quotient is formed from a setoid. Since `ℕ` has a congruence for every `n`, `modSetoid n` is an ordinary `def`, not an instance, built by `where` with its two fields and passed by name. A field that is a function may take its arguments before `:=`, as `r a b := …`.
@description
Define `modSetoid n`, the setoid on `ℕ` whose relation is congruence modulo `n`: `a` is related to `b` when `a % n = b % n`.
-/

def modSetoid (n : ℕ) : Setoid ℕ where
  r a b := a % n = b % n
  iseqv := ker_equivalence (· % n)

/-- @spec -/
example (n a b : ℕ) : (modSetoid n) a b ↔ a % n = b % n := by
  constructor
  · intro h
    change _ = _ at h
    grind
  · intro h
    change _ = _
    grind

/-! @end -/

/-!
@concept equivalence_classes
@title Equivalence Classes and Quotients
@kind definition

The class of an element under an equivalence relation is the set of elements related to it, and the classes partition the type: each element lies in exactly one. The classes form a new type, the quotient. Cosets, quotient groups and sets of orbits are all quotients, so the subject needs to form a quotient, define a function on one, and count one.
-/

/--
@problem quotient_eq_iff_mod
@title When Two Classes Are Equal
@concept equivalence_classes

@preamble
For a setoid `s` on `α`, `Quotient s` is the type of equivalence classes, and `Quotient.mk s a` is the class of `a`, which Lean prints as `⟦a⟧`. A class is an element of a new type, standing for the set of elements related to `a` without being that set. Two classes are equal exactly when their representatives are related, and these two laws are all there is to say about it:
```lean
theorem Quotient.sound : a ≈ b → ⟦a⟧ = ⟦b⟧
theorem Quotient.exact : ⟦a⟧ = ⟦b⟧ → a ≈ b
```
Here `a ≈ b` means `s a b`, so for the classes modulo `n` it is `a % n = b % n` by definition, and `exact` accepts the one for the other.
@description
Show that the classes of `a` and `b` modulo `n` are equal exactly when `a` and `b` have the same remainder.
-/
theorem quotient_eq_iff_mod (n a b : ℕ) :
    Quotient.mk (modSetoid n) a = Quotient.mk (modSetoid n) b ↔ a % n = b % n := by
  constructor
  · intro h
    exact Quotient.exact h
  · intro h
    exact Quotient.sound h

/-!
@problem to_fin
@title The Remainder as an Element of Fin n
@concept equivalence_classes

@preamble
A class modulo `n` is to be sent to the remainder its members share, as an element of `Fin n`, and the first step is the remainder of a number. The remainder `a % n` is below `n` when `n` is positive, by `Nat.mod_lt`, met earlier in this section.

The positivity of `n` is carried as an instance: the hypothesis `[NeZero n]` says `n ≠ 0` in a form Lean finds by itself. The numerals of `Fin n` need it, and so does the proof that `a % n < n`, through `Nat.pos_of_neZero n : 0 < n`, which reads it back as a proof.
@description
Define `toFin n`, which sends a natural number `a` to its remainder `a % n` as an element of `Fin n`.
-/

def toFin (n : ℕ) [NeZero n] (a : ℕ) : Fin n := ⟨a % n, Nat.mod_lt a (Nat.pos_of_neZero n)⟩

/-- @spec -/
example (n : ℕ) [NeZero n] (a : ℕ) : (toFin n a).val = a % n := rfl

/-! @end -/

/--
@problem to_fin_mod
@title A Number and Its Remainder Give the Same Element of Fin n
@concept equivalence_classes

@preamble
Equality in `Fin n` is equality of values, so an equation in `Fin n` comes down to an equation of numbers:
```lean
theorem Fin.ext {i j : Fin n} (h : i.val = j.val) : i = j
```
The value of `toFin n a` is `a % n` by definition, but a goal shows it as `↑(toFin n a)`, as Lean prints a value `i.val`. The tactic `change t` restates the goal as `t` when the two are equal by definition. `rw` cannot rewrite `a % n` inside `⟨a % n % n, _⟩`, because the proof component depends on the value; the error says the motive is not type correct. Rewrite the values instead.
@description
Show that `toFin n (a % n) = toFin n a`. The context holds `mod_mod_of_pos`, proved earlier in this section, which says `a % n % n = a % n` for `0 < n`.
-/
theorem toFin_mod (n : ℕ) [NeZero n] (a : ℕ) : toFin n (a % n) = toFin n a := by
  apply Fin.ext
  change a % n % n = a % n
  exact mod_mod_of_pos a n (Nat.pos_of_neZero n)

/-!
@problem residue
@title The Remainder of a Class
@concept equivalence_classes

@preamble
A function out of a quotient is defined on representatives. A function `f : α → β` that takes equal values on related elements descends to the classes:
```lean
def Quotient.lift (f : α → β) (h : ∀ a b, a ≈ b → f a = f b) : Quotient s → β
```
and its value at the class `⟦a⟧` is `f a` by `rfl`. The *residue* of a class is the remainder its members share, as an element of `Fin n`: `toFin n` takes the same value on congruent numbers, by the definition of congruence, so it descends to the classes.
@description
Define `residue n`, the function sending the class of `a` modulo `n` to `toFin n a`.
-/

def residue (n : ℕ) [NeZero n] : Quotient (modSetoid n) → Fin n :=
  Quotient.lift (toFin n) (fun _ _ h => Fin.ext h)

/-- @spec -/
example (n : ℕ) [NeZero n] (a : ℕ) : (residue n (Quotient.mk _ a)).val = a % n := rfl

/-! @end -/

/--
@problem quotient_mk_surjective
@title Every Class Has a Representative
@concept equivalence_classes

@preamble
Lean states that every class has a representative as a principle of induction: to prove something about every class, it is enough to prove it about the class of every element. This replaces a class `q` by `Quotient.mk s a` for an arbitrary `a`:
```lean
induction q using Quotient.inductionOn with
| h a => …
```
Here `h` names the single case of `Quotient.inductionOn`, not a hypothesis.
@description
Show that `Quotient.mk s` is surjective.
-/
theorem quotient_mk_surjective {α : Type u} (s : Setoid α) :
    Function.Surjective (Quotient.mk s) := by
  intro q
  induction q using Quotient.inductionOn with
  | h a => exact ⟨a, rfl⟩

/--
@problem residue_bijective
@title The Classes Modulo n Are the Remainders
@concept equivalence_classes

@preamble
The residue map is a bijection: a class is determined by its remainder, and every remainder occurs. Statements about classes are reduced to representatives, as in the previous problem.
@description
Show that `residue n` is a bijection between the classes modulo `n` and `Fin n`. The context holds `quotient_eq_iff_mod`, this concept's first problem, which says that two classes modulo `n` are equal exactly when the remainders agree. `Fin.ext_iff`, which turns an equation in `Fin n` into an equation of values, and `Nat.mod_eq_of_lt`, met earlier in this section, may be useful.
-/
theorem residue_bijective (n : ℕ) [NeZero n] : Function.Bijective (residue n) := by
  constructor
  · intro q₁ q₂ h
    induction q₁ using Quotient.inductionOn with
    | h a =>
      induction q₂ using Quotient.inductionOn with
      | h b => exact (quotient_eq_iff_mod n a b).mpr (Fin.ext_iff.mp h)
  · intro i
    exact ⟨Quotient.mk _ i.val, Fin.ext (Nat.mod_eq_of_lt i.isLt)⟩

/-!
@problem card_quotient_le
@title A Quotient Has No More Classes Than Elements
@concept equivalence_classes

@preamble
A finite type has finitely many classes, and no more than it has elements. Mathlib provides the instance `Fintype (Quotient s)` for a finite type when the relation is decidable, as `Quotient.fintype`.

Lean cannot decide an arbitrary setoid's relation by itself. `open Classical` makes every proposition decidable, through the law of the excluded middle, at the price that nothing so decided can be computed. Writing `open Classical in` before a declaration opens it for that declaration alone.

An onto map does not increase cardinality:
```lean
theorem Fintype.card_le_of_surjective (f : α → β) (h : Function.Surjective f) :
    Fintype.card β ≤ Fintype.card α
```
@description
Show that a quotient of a finite type has at most as many classes as the type has elements.
-/

open Classical in
theorem card_quotient_le {α : Type u} [Fintype α] (s : Setoid α) :
    Fintype.card (Quotient s) ≤ Fintype.card α :=
  Fintype.card_le_of_surjective (Quotient.mk s) (quotient_mk_surjective s)

/-! @end -/

end GroupTheory
