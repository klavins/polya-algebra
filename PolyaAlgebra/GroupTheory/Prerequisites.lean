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

Set Theory built sets as predicates and proved their laws by hand. Mathlib's `Set α` is the same object under its own names, and it is the one this subject uses: a subgroup is a set of group elements, a coset is a set, an orbit is a set. This concept matches the names, and shows how a set is used as a type, which is how a subgroup will be a group in its own right.
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
`{x | p x}` is `fun x => p x`, so `x ∈ S` unfolds to `S x`; `f '' S` is `Set.image f S`; and `∃ x ∈ S, …` abbreviates `∃ x, x ∈ S ∧ …`, so a membership in an image is taken apart by the pattern `⟨x, hx, hy⟩`, as in Set Theory.

Two sets with the same members are equal: Set Theory's `setext` is Mathlib's `Set.ext : (∀ x, x ∈ S ↔ x ∈ T) → S = T`. Most laws Set Theory proved are in Mathlib under the same names with the prefix `Set.`, as `Set.union_comm`; `subset_antisym` is `Set.Subset.antisymm`, with `Set.Subset.refl` and `Set.Subset.trans` beside it.
@description
Show that the image of a union is the union of the images, as Set Theory proved for its own sets. Mathlib has the fact as `Set.image_union`; the exercise is to prove it again from the definitions, so that each membership has been taken apart by hand once under Mathlib's notation.
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
@problem restrict_mem_image
@title A Set as a Type
@concept mathlib_sets

@preamble
A set `S : Set α` can stand where a type is expected, and then it means the type of its elements: Mathlib writes it `↥S`, and usually just `S`. An element of that type is a pair `⟨x, hx⟩` of a point `x : α` and a proof `hx : x ∈ S`; from `a : S`, `a.1` is the point and `a.2` the proof, and `(a : α)` is the point again, by coercion, which Lean prints as `↑a` in a goal. Where a point of `α` is expected and an element of `S` is given, as in `f a`, Lean inserts the coercion by itself. This is how a subgroup, a set of group elements, will carry a group structure of its own.
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
The set of all values of a function `g : ι → β` is its range, `Set.range g`, the set `{y | ∃ i, g i = y}`; `Set.mem_range : y ∈ Set.range g ↔ ∃ i, g i = y` states the membership, and an `intro` pattern sees it directly, as it does for the image. Restricting `f : α → β` to the set `S` gives a function on `S` as a type, `fun x : S => f x`, whose values are the values of `f` at the points of `S`: its range is the image of `S`.
@description
Show that the image of `S` under `f` is the range of the restriction of `f` to `S`, the function `fun x : S => f x`.
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

A function is injective when distinct inputs have distinct values, surjective when every value is taken, and bijective when both; Mathlib writes `Function.Injective f`, `Function.Surjective f` and `Function.Bijective f`. Homomorphisms are functions, kernels measure how far they are from injective, and the subject's counting rests on injections and surjections.
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
The binders `⦃a₁ a₂⦄` are strict implicit: from `hf : Function.Injective f` and `h : f a = f b`, the term `hf h` proves `a = b`, the two points being read off `h`. They are introduced like any other binders: `intro a b h` brings in the two points and the equation, and a surjectivity goal opens on `intro b`.

The composite `g ∘ f` is `fun x => g (f x)`, and `(g ∘ f) x` unfolds to `g (f x)`: `exact` accepts either form for the other, but `rw` sees only what is written, and `Function.comp_apply : (g ∘ f) x = g (f x)` is the rewrite that unfolds it.
@description
Show that the composite of two injective functions is injective, and that the composite of two surjective functions is surjective. Mathlib has these as `Function.Injective.comp` and `Function.Surjective.comp`.
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
A function is often shown injective or surjective not from the definition but from a second function that undoes it, in one direction or the other. A *left inverse* of `f : α → β` is a function `g : β → α` with `g (f x) = x` for every `x`; a *right inverse* is a `g` with `f (g y) = y` for every `y`. A function may have one without the other: doubling on `ℕ` has a left inverse, halving, and no right inverse. Mathlib names the two conditions `Function.LeftInverse g f` and `Function.RightInverse g f`; here they are written out as the statements they abbreviate.
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

A bijection between two types, packaged with its inverse, is an equivalence, written `α ≃ β`: Mathlib's way of saying that two types are the same up to renaming, and this subject's way of saying that two groups are the same, once the equivalence respects the operation. A permutation of `X` is an equivalence `X ≃ X`, and the permutations of three points are the first non-commutative group met.
-/

/-!
@problem not_equiv
@title Negation as an Equivalence
@concept bijections

@preamble
An equivalence between `α` and `β` is a function in each direction, with the two laws saying that they undo each other:
```lean
structure Equiv (α : Sort u) (β : Sort v) where
  toFun : α → β
  invFun : β → α
  left_inv : Function.LeftInverse invFun toFun
  right_inv : Function.RightInverse invFun toFun
```
(`Sort u` is Lean's word for a universe of types or propositions; read it as `Type u`.) `α ≃ β` is the type of equivalences, and for `e : α ≃ β` we write `e x` for `e.toFun x`, by coercion, and `e.symm : β ≃ α` for the inverse equivalence. A structure is built field by field with `where` in place of `:=`: `def e : α ≃ β where`, then `toFun := …` on the next line, and so on through the four fields; the anonymous constructor `⟨toFun, invFun, left_inv, right_inv⟩` after `:=` builds the same thing. An inverse law of an equivalence between finite types is a statement about finitely many cases, which `decide` settles.
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
`Fin n` is the type of natural numbers below `n`: an element `i` is a pair of a value `i.val : ℕ` and a proof `i.isLt : i.val < n`, written `⟨k, h⟩`, and the numerals `0`, `1`, … of `Fin n` are the numbers they name. `Fin 2` has two elements, and so does `Bool`, so the two types are in bijection, and an equivalence between them says so: the shape of the previous problem serves again, with `Fin 2` in place of the second `Bool`.
@description
Define `boolEquivFinTwo : Bool ≃ Fin 2`, sending `false` to `0` and `true` to `1`. Each of the two inverse laws is a statement about finitely many cases, which `decide` settles.
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
The two laws of an equivalence `e : α ≃ β` are used under Mathlib's names: `e.symm_apply_apply x : e.symm (e x) = x` and `e.apply_symm_apply y : e (e.symm y) = y`. They say that `e.symm` is a left inverse and a right inverse of `e`, so by the two theorems of the previous concept `e` is injective and surjective. A bijection is the conjunction of the two:
```lean
def Function.Bijective (f : α → β) : Prop :=
  Function.Injective f ∧ Function.Surjective f
```
so a proof of it is `constructor` with a half for each, and `hf.1` and `hf.2` are the halves of `hf : Function.Bijective f`.
@description
Show that the function of an equivalence is a bijection. The context holds `injective_of_left_inverse` and `surjective_of_right_inverse`, the two theorems of the previous concept. Once this is proved, Mathlib's own `e.bijective`, `e.injective` and `e.surjective` state the same facts and may be used in later problems.
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

The three points `0`, `1`, `2` of `Fin 3` are rotated by `i ↦ i + 1`: addition in `Fin n` wraps around, so `2 + 1 = 0`, and so does subtraction. A closed statement about `Fin 3`, such as `rot3 2 = 0`, is settled by `decide`, which computes both sides; so is an equation between two permutations of `Fin 3`, since there are only three points at which to compare them.
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
@concept finite_types
@title Finite Types and Counting
@kind theorem

A type is finite when its elements can be listed; Mathlib packages the list as an instance `Fintype α`, with `Fintype.card α` its length. Every finite group has an order, every subgroup and coset a size, and Lagrange's theorem compares them, so the subject counts with `Fintype.card`. On a finite type a statement about every element is checked by running through the list, as `decide` does.
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
`Fintype.card α` is the number of elements, and Mathlib provides the instances for `Bool`, `Unit` and `Fin n`, with `Fintype.card_fin : Fintype.card (Fin n) = n`.

A statement `∀ x : α, p x` over a finite type `α` is decided by checking `p` at each element of the list, and `∃ x : α, p x` by finding one. So `decide` settles such statements when `p` is decidable, as it settles statements about numerals; that is why it settled the laws of `notEquiv` and the cube of `rot3`, and it is how this subject checks small facts about its examples. It needs the type fixed: it cannot run through `Fin n` for a variable `n`.
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
Two finite types in bijection have the same number of elements: `Fintype.card_congr (e : α ≃ β) : Fintype.card α = Fintype.card β`. So to count a type it is enough to label its elements by the elements of a type already counted. `Fintype.equivFin α : α ≃ Fin (Fintype.card α)` labels the elements of any finite type by the numbers below its cardinality, and `finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)` labels pairs by single numbers.

This is how the subject will count a group whose elements are given by pairs, a coset and a position in it. The product `Fin m × Fin n` carries no `Fintype` instance in the part of Mathlib this subject imports, so a count passes through `Fin (m * n)`, which has one, with `Fintype.card_fin`.
@description
Let `α` be a finite type whose elements are labelled by pairs, through an equivalence `e : α ≃ Fin m × Fin n`. Show that `α` has `m * n` elements. Mathlib provides `Fintype.card_congr`, `finProdFinEquiv` and `Fintype.card_fin`, which you may find useful.
-/
theorem card_of_equiv_prod {α : Type u} [Fintype α] {m n : ℕ} (e : α ≃ Fin m × Fin n) :
    Fintype.card α = m * n := by
  rw [Fintype.card_congr (e.trans finProdFinEquiv), Fintype.card_fin]

/--
@problem bijective_of_injective
@title An Injective Self-Map of a Finite Type is a Bijection
@concept finite_types

@preamble
On a finite type an injective function into the type itself must take every value. The argument is a count: an injective `f` has as many values as the type has elements, and a set of that many elements of a finite type is the whole type. Mathlib has done the count, and the result is taken from it here under its name, `Finite.injective_iff_surjective`. It is stated for a second class of finite types, which asks for no list, only for a bijection with some `Fin n`, which is what a mathematics text means by finite:
```lean
class inductive Finite (α : Sort u) : Prop
  | intro {n : ℕ} : α ≃ Fin n → Finite α
```
A type with a `Fintype` instance is `Finite`, through `Fintype.equivFin`, and Lean finds the instance by itself, so the result applies to every type this subject counts.
@description
Let `α` be a finite type and `f : α → α` injective. Show that `f` is a bijection. Mathlib provides `Finite.injective_iff_surjective`, which you may find useful.
-/
theorem bijective_of_injective {α : Type u} [Finite α] {f : α → α} (hf : Function.Injective f) :
    Function.Bijective f :=
  ⟨hf, Finite.injective_iff_surjective.mp hf⟩

/-!
@concept integers_and_remainders
@title The Integers and Remainders
@kind theorem

The integers under addition are the subject's first infinite group, and the remainders modulo `n` under addition its first finite ones, so `ℤ` and `%` are needed with their laws under Lean's names: `ℤ` with its two constructors, `%` with the rules for adding remainders. The least number with a property and coprime numbers are met here too, for the order of an element and for primes.
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
`Int.ofNat n` is the natural number `n` as an integer, written `(n : ℤ)` or `↑n` (Mathlib's name for the cast is `Nat.cast`, `natCast` in theorem names), and `Int.negSucc n` is `-(n + 1)`, so that every integer has exactly one of the two forms. A proof about an integer `z` can therefore begin `cases z with` and treat `ofNat n` and `negSucc n` in turn. The tactic `omega` proves linear arithmetic over `ℤ` as over `ℕ`; it reads `Int.negSucc n` as `-(n + 1)`, but it does not read `Int.ofNat n` as `(n : ℤ)`, though the two are equal by definition, so a goal that shows `Int.ofNat n` and holds by definition is closed by `rfl`.
@description
Show that every integer is the difference of two natural numbers: for each `z : ℤ` there are `m n : ℕ` with `z = m - n`. Here `m - n` is subtraction in `ℤ`, of the two natural numbers cast there; the goal writes it `↑m - ↑n`.
-/
theorem int_eq_sub_natCast (z : ℤ) : ∃ m n : ℕ, z = m - n := by
  cases z with
  | ofNat n => exact ⟨n, 0, rfl⟩
  | negSucc n => exact ⟨0, n + 1, by omega⟩

/-!
@problem mod_add_mod
@title Adding Remainders
@concept integers_and_remainders

@preamble
For natural numbers `a` and `n`, `a % n` is the remainder of `a` on division by `n` and `a / n` the quotient, with `Nat.mod_add_div : a % n + n * (a / n) = a`. The remainder is below `n` when `n` is positive, `Nat.mod_lt a h : a % n < n` for `h : 0 < n`, with the dividend `a` given explicitly; a number below `n` is its own remainder, `Nat.mod_eq_of_lt : a < n → a % n = a`; and `Nat.mod_self : n % n = 0`. A remainder of numerals is computed by `decide` or `rfl`, as `17 % 5 = 2`.

Arithmetic modulo `n` rests on one fact: it makes no difference whether a summand is reduced before the addition or after it. Core Lean has the two halves of this as `Nat.mod_add_mod : (a % n + b) % n = (a + b) % n` and `Nat.add_mod_mod : (a + b % n) % n = (a + b) % n`.
@description
Show that a remainder modulo a positive `n` is its own remainder, and that reducing both summands modulo `n` and then adding gives the same remainder as adding first. Core Lean provides `Nat.mod_add_mod` and `Nat.add_mod_mod`, which you may find useful; Mathlib has the second result, the other way round, as `Nat.add_mod`, and later sections use the form proved here.
-/

theorem mod_mod_of_pos (a n : ℕ) (h : 0 < n) : a % n % n = a % n := by
  apply Nat.mod_eq_of_lt
  exact Nat.mod_lt a h

theorem mod_add_mod_eq_add_mod (a b n : ℕ) : (a % n + b % n) % n = (a + b) % n := by
  rw [Nat.mod_add_mod, Nat.add_mod_mod]

/-! @end -/

/-!
@problem find_least
@title The Least Number With a Property
@concept integers_and_remainders

@preamble
The order of an element of a group will be the least power that returns to the identity, so the subject needs the least natural number with a property. Such a number exists: this is the well-ordering of `ℕ`, which The Natural Numbers proved by strong induction. Mathlib's `Nat.find h`, for `h : ∃ k, p k`, is that least number, computed by testing `p 0`, `p 1`, … in turn. The test needs `p` to be decidable: the hypothesis `[DecidablePred p]` says so, and holds for a property made of equations and inequalities between numbers. Its laws are `Nat.find_spec h : p (Nat.find h)`, `Nat.find_min' h : p m → Nat.find h ≤ m`, and `Nat.find_eq_iff`, which says that `Nat.find h = m` exactly when `m` has the property and no smaller number does. The least multiple of `3` above `10`, for instance, is `Nat.find (p := fun k => 10 < k ∧ k % 3 = 0) ⟨12, by decide⟩`, where `(p := …)` names the property, which Lean cannot read off the witness.
@description
Let `p` be a decidable property that some natural number has. Show that `Nat.find h` has the property and is at most every number that has it; Mathlib provides `Nat.find_spec` and `Nat.find_min'`. Show also that the least number whose square exceeds `50` is `8`: `decide` cannot compute `Nat.find` itself, and Mathlib provides `Nat.find_eq_iff`.
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
A prime is a number whose only divisors are `1` and itself, so a prime that does not divide `m` has no divisor in common with `m`: the two are *coprime*. The subject's arguments about groups of prime order rest on this. `a ∣ b`, "`a` divides `b`", means that `b = a * c` for some `c`, on `ℕ` as on the naturals of The Natural Numbers, and `Nat.gcd a b` is the greatest common divisor, computed by Euclid's algorithm. Two numbers are coprime when their greatest common divisor is `1`: `Nat.Coprime a b` is `Nat.gcd a b = 1`, so `decide` settles it for numerals. The fact about coprime numbers that the subject uses is that a number coprime to `m` which divides a product `m * n` divides `n`: `Nat.Coprime.dvd_of_dvd_mul_left : Nat.Coprime k m → k ∣ m * n → k ∣ n`, used as `hc.dvd_of_dvd_mul_left` for a proof `hc : Nat.Coprime k m`.
@description
Show that `4` and `9` are coprime, and that `3` divides `k` whenever it divides `4 * k`.
-/

theorem coprime_four_nine : Nat.Coprime 4 9 := by
  decide

theorem three_dvd_of_dvd_four_mul (k : ℕ) (h : 3 ∣ 4 * k) : 3 ∣ k :=
  (by decide : Nat.Coprime 3 4).dvd_of_dvd_mul_left h

/-! @end -/

/-!
@concept relations
@title Equivalence Relations
@kind definition

A relation on a type is a predicate of two arguments, and an equivalence relation is one that is reflexive, symmetric and transitive: it says which elements count as the same. Lean bundles the three laws as `Equivalence r`, and a relation with its laws as a `Setoid`. Cosets, conjugacy classes and orbits are the classes of equivalence relations, which is the form the subject needs.
-/

/--
@problem ker_equivalence
@title Equal Values Under a Function
@concept relations

@preamble
Set Theory proved `⊆` reflexive and transitive, and Logic proved `↔` symmetric and transitive as well; an equivalence relation is one with all three laws, which Lean collects in a structure:
```lean
structure Equivalence (r : α → α → Prop) : Prop where
  refl  : ∀ x, r x x
  symm  : ∀ {x y}, r x y → r y x
  trans : ∀ {x y z}, r x y → r y z → r x z
```
The elements in `symm` and `trans` are implicit, so a proof of `Equivalence r` is `⟨fun x => …, fun h => …, fun h h' => …⟩`, the last two functions of the hypotheses alone; in tactic form, `intro x y h` names the implicit elements as well.

Equality is the first equivalence relation, and every function `f` carries it back to its domain: two elements are related when `f` takes the same value at them. This relation is the *kernel* of `f`, which names the theorem. Congruence modulo `n` is the case `f = (· % n)`, Lean's short form of `fun a => a % n`. `h.symm` reverses an equation and `h.trans h'` chains two, as Lean names the laws of equality.
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
Not every equivalence relation compares the values of a function in hand. Two integers have the same parity when they differ by an even number, `b = a + 2 * k` for some integer `k`: `3` and `-5` have the same parity, since `-5 = 3 + 2 * (-4)`. Each of the three laws is now the existence of an integer, and a proof of it names one: the relations the subject forms later, between elements of a group reached from one another by some element, have this shape. Parity is also congruence modulo `2`, with a witness in place of a remainder.
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
A setoid `s` is applied like its relation, `s a b`. The setoid is what a quotient is formed from, so each equivalence relation the subject uses is packaged as one, by `where` with its two fields; a setoid that is not the instance on its type is an ordinary `def`, passed by name.
@description
Define `modSetoid n`, the setoid on `ℕ` whose relation is congruence modulo `n`: `a` is related to `b` when `a % n = b % n`. The context holds `ker_equivalence`, which says that equal values under any function give an equivalence relation.
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

The class of `a` under an equivalence relation is the set of elements related to it, and the classes partition the type: each element lies in exactly one. Lean has a type whose elements are the classes, the quotient `Quotient s` of a setoid `s`. Cosets, quotient groups and sets of orbits are all quotients, so the subject needs to form a quotient, to define a function on one, and to count one.
-/

/--
@problem quotient_eq_iff_mod
@title When Two Classes Are Equal
@concept equivalence_classes

@preamble
For a setoid `s` on `α`, `Quotient s` is the type of equivalence classes, and `Quotient.mk s a` is the class of `a`. Two classes are equal exactly when their representatives are related, and the two directions are `Quotient.sound : s a b → Quotient.mk s a = Quotient.mk s b` and `Quotient.exact : Quotient.mk s a = Quotient.mk s b → s a b`, each applied to a hypothesis, as `Quotient.sound h`. Nothing else is known about a class: it is an element of a new type, not a set, and these two laws are its whole interface. Lean prints `Quotient.mk s a` as `⟦a⟧` and `s a b` as `a ≈ b` whatever `s` is, so the classes modulo `n` appear in a goal as `⟦a⟧`, and a goal `a ≈ b` is `a % n = b % n` up to unfolding, which `exact` sees through.

The classes modulo `n` correspond to the remainders: the class of `a` is the set of numbers with the remainder `a % n`, one class for each remainder.
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
The residue map of the next problem sends a class modulo `n` to the remainder its members share, as an element of `Fin n`; this problem builds that element from a number. The remainder `a % n` is below `n` when `n` is positive, by `Nat.mod_lt a h` of the previous concept, so `⟨a % n, _⟩ : Fin n`, with that proof in the second component, is the element; Lean prints its value `i.val` as `↑i`. The positivity of `n` is carried as an instance: the hypothesis `[NeZero n]` says `n ≠ 0` in a form Lean finds by itself whenever `Fin n` or a remainder needs it, and `Nat.pos_of_neZero n : 0 < n` reads it back as a proof.
@description
Define `toFin n`, which sends a natural number `a` to its remainder `a % n` as an element of `Fin n`. Core Lean has the same function as `Fin.ofNat n a`.
-/

def toFin (n : ℕ) [NeZero n] (a : ℕ) : Fin n := ⟨a % n, Nat.mod_lt a (Nat.pos_of_neZero n)⟩

/-- @spec -/
example (n : ℕ) [NeZero n] (a : ℕ) : (toFin n a).val = a % n := rfl

/-! @end -/

/-!
@problem residue
@title The Remainder of a Class
@concept equivalence_classes

@preamble
A function out of a quotient is defined on representatives: a function `f` on `α` that takes equal values on related elements descends to the classes, as `Quotient.lift f h : Quotient s → β` where `h : ∀ a b, s a b → f a = f b`, and `Quotient.lift f h (Quotient.mk s a)` is `f a` by `rfl`. The *residue* of a class is the remainder its members share, as an element of `Fin n`: `toFin n` takes the same value on congruent numbers, by the definition of congruence, so it descends to the classes.

Equality in `Fin n` is equality of values, `Fin.ext : i.val = j.val → i = j`. A hypothesis about `a % n` cannot be rewritten inside `⟨a % n, _⟩`, whose proof component depends on it (`rw` reports that the motive is not type correct); it is passed to `Fin.ext` as a term.
@description
Define `residue n`, the function sending the class of `a` modulo `n` to `toFin n a`.
-/

def residue (n : ℕ) [NeZero n] : Quotient (modSetoid n) → Fin n :=
  Quotient.lift (toFin n) (fun _ _ h => Fin.ext h)

/-- @spec -/
example (n : ℕ) [NeZero n] (a : ℕ) : (residue n (Quotient.mk _ a)).val = a % n := rfl

/-! @end -/

/--
@problem residue_bijective
@title The Classes Modulo n Are the Remainders
@concept equivalence_classes

@preamble
To prove something about every class, it is enough to prove it about the class of every element, since every class is one: `induction q using Quotient.inductionOn with | h a => …` replaces a class `q` by `Quotient.mk s a` for an arbitrary `a`. Here `h` names the single case of `Quotient.inductionOn`, not a hypothesis, and a statement about two classes is reduced by applying it to each in turn. With that, the residue map is seen to be a bijection: a class is told by its remainder, and every remainder occurs.
@description
Show that `residue n` is a bijection between the classes modulo `n` and `Fin n`. `Fin.ext_iff` turns an equation in `Fin n` into an equation of values; the context holds `quotient_eq_iff_mod`, this concept's first problem; and `Nat.mod_eq_of_lt`, from the previous concept, may be useful.
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
A finite type has finitely many classes, and no more than it has elements, since `Quotient.mk s` maps the type onto its classes. Mathlib provides the instance `Fintype (Quotient s)` for a finite type when the relation is decidable, as `Quotient.fintype`. A relation given by a definition is not decidable by instance search, and `open Classical` supplies the missing instance by fiat, through the law of the excluded middle: every proposition becomes decidable, at the price that nothing so decided can be computed. Writing `open Classical in` before a declaration opens it for that declaration alone, and this subject does so whenever a quotient is counted. An onto map does not increase cardinality: `Fintype.card_le_of_surjective (f : α → β) : Function.Surjective f → Fintype.card β ≤ Fintype.card α`.
@description
Show that a quotient of a finite type has at most as many classes as the type has elements.
-/

open Classical in
theorem card_quotient_le {α : Type u} [Fintype α] (s : Setoid α) :
    Fintype.card (Quotient s) ≤ Fintype.card α := by
  apply Fintype.card_le_of_surjective (Quotient.mk s)
  intro q
  induction q using Quotient.inductionOn with
  | h a => exact ⟨a, rfl⟩

/-! @end -/

end GroupTheory
