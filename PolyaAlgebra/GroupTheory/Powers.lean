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
import PolyaAlgebra.GroupTheory.Examples

/-! @section Powers and the Order of an Element -/

universe u v

namespace GroupTheory

set_option linter.translateGenerateName false

/-!
@concept natural_powers
@title Natural Powers
@kind definition

The `n`th power of an element is the product of `n` copies of it, and in an additive group the `n`th multiple is the sum of `n` copies. In every group, exponents add when powers are multiplied, and multiply when a power is raised to a power. Powers are defined by recursion, and the laws are proved from the definition.
-/

/-!
@problem npow
@title The Definition of a Power
@concept natural_powers

@preamble
The *power* `g ^ n` is the product of `n` copies of `g`: `g ^ 0` is `1` and `g ^ (n + 1)` is `g ^ n * g`. It is a definition by recursion on `n`, as The Natural Numbers defined addition, with a line `| 0, _ => …` and a line `| n + 1, g => …`. The exponent comes first, `Group.npow n g`. Inside the definition the recursive call is `npow n g`, since `^` does not exist yet. The notation comes from an instance of Lean's class
```lean
class Pow (α : Type u) (β : Type v) where
  pow : α → β → α
```
`Pow` takes the base first; the instance is built by `⟨…⟩`, as `Add MyNat` was.

A numeral exponent, as in `rot3 ^ 3`, is read through Lean's default instances alone, so this instance must be one of them; the line `@[default_instance high]` above it makes it one.
@description
Define `Group.npow n g` by the two equations, with the factor order `npow n g * g` for the power `n + 1`. Supply the instance `Group.toPow : Pow G ℕ` under that line, and check by `decide` that `rot3 ^ 3 = 1` and `reflect3 ^ 2 = 1`.
-/

def Group.npow {G : Type u} [Group G] : ℕ → G → G
  | 0, _ => 1
  | n + 1, g => npow n g * g

@[default_instance high]
instance Group.toPow {G : Type u} [Group G] : Pow G ℕ := ⟨fun g n => Group.npow n g⟩

/-- @spec -/
example {G : Type u} [Group G] (g : G) (n : ℕ) : g ^ 0 = 1 ∧ g ^ (n + 1) = g ^ n * g := ⟨rfl, rfl⟩

theorem s3_pow_check : rot3 ^ 3 = 1 ∧ reflect3 ^ 2 = 1 := by
  decide

/-! @end -/

/-!
@problem nsmul
@title Multiples in an Additive Group
@concept natural_powers

@preamble
In an additive group the power becomes the *multiple* `n • a`, the sum of `n` copies of `a`: `0 • a = 0` and `(n + 1) • a = n • a + a`. The textbook writes it *na*; Lean writes `n • a` (typed `\smul`), the symbol of the class
```lean
class SMul (M : Type u) (α : Type v) where
  smul : M → α → α
```
which takes the number first. The definition is the previous one with `+` and `0`, as `AddGroup` was `Group` with them. The two definitions correspond, so every theorem about powers has an additive version about multiples.
@description
Define `AddGroup.nsmul n a` by the two equations, with `nsmul n a + a` for the multiple `n + 1`; supply the instance `AddGroup.toSMul : SMul ℕ A`; and check that `3 • (2 : ℤ) = 6` by `decide`. This instance needs no `@[default_instance]` line, since a bare numeral such as `3` is read as a natural number by default.
-/

def AddGroup.nsmul {A : Type u} [AddGroup A] : ℕ → A → A
  | 0, _ => 0
  | n + 1, a => nsmul n a + a

instance AddGroup.toSMul {A : Type u} [AddGroup A] : SMul ℕ A := ⟨AddGroup.nsmul⟩

/-- @spec -/
example {A : Type u} [AddGroup A] (a : A) (n : ℕ) : 0 • a = 0 ∧ (n + 1) • a = n • a + a :=
  ⟨rfl, rfl⟩

theorem int_three_nsmul_two : 3 • (2 : ℤ) = 6 := by
  decide

/-! @end -/

attribute [to_additive existing AddGroup.nsmul] Group.npow

attribute [to_additive existing AddGroup.toSMul] Group.toPow

/-!
@problem pow_one
@title The First Laws of Powers
@concept natural_powers

@preamble
The two equations of the definition hold by `rfl`; their additive versions are `zero_nsmul` and `succ_nsmul`:
```lean
pow_zero : g ^ 0 = 1
pow_succ : g ^ (n + 1) = g ^ n * g
```
Anything more is a theorem. Even `g ^ 1 = g` is not an equation of the definition, and it needs a law of groups as well as of powers. `rw [pow_succ]` matches `g ^ 1`, since Lean reads the numeral `1` as `0 + 1`.
@description
Show that `g ^ 0 = 1` and `g ^ (n + 1) = g ^ n * g`, which hold by definition, and that `g ^ 1 = g`.
-/

@[to_additive zero_nsmul]
theorem pow_zero {G : Type u} [Group G] (g : G) : g ^ 0 = 1 := rfl

@[to_additive succ_nsmul]
theorem pow_succ {G : Type u} [Group G] (g : G) (n : ℕ) : g ^ (n + 1) = g ^ n * g := rfl

@[to_additive one_nsmul]
theorem pow_one {G : Type u} [Group G] (g : G) : g ^ 1 = g := by
  rw [pow_succ, pow_zero, one_mul]

/-! @end -/

/-!
@problem one_pow
@title A Law of Powers by Induction
@concept natural_powers

@preamble
`1 ^ n = 1` is not an equation of the definition either, since the exponent is unknown; it is proved by induction on `n`, as The Natural Numbers proved `0 + a = a`. Here is the proof, the step as a `calc` chain:
```lean
theorem one_pow (n : ℕ) : (1 : G) ^ n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc (1 : G) ^ (n + 1) = 1 ^ n * 1 := by rw [pow_succ]
      _ = 1 * 1 := by rw [ih]
      _ = 1 := by rw [one_mul]
```
The zero case is the definition. In the step, `ih : 1 ^ n = 1`, the definition peels off one factor, the hypothesis replaces the rest, and a law finishes. When a rewrite leaves the left side of `ih` on both sides of the goal, `rw [ih]` rewrites both; a `calc` step rewrites only the expression it names.
@description
Show that `g ^ (n + 1) = g * g ^ n`, under the name `pow_succ'`. The context holds `pow_zero`, `pow_succ`, `pow_one`, `one_mul`, `mul_one`, `mul_assoc` and `one_pow`.
-/

/-- @given -/
@[to_additive nsmul_zero]
theorem one_pow {G : Type u} [Group G] (n : ℕ) : (1 : G) ^ n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc (1 : G) ^ (n + 1) = 1 ^ n * 1 := by rw [pow_succ]
      _ = 1 * 1 := by rw [ih]
      _ = 1 := by rw [one_mul]

@[to_additive succ_nsmul']
theorem pow_succ' {G : Type u} [Group G] (g : G) (n : ℕ) : g ^ (n + 1) = g * g ^ n := by
  induction n with
  | zero => rw [pow_one, pow_zero, mul_one]
  | succ n ih =>
    calc g ^ (n + 1 + 1) = g ^ (n + 1) * g := by rw [pow_succ]
      _ = g * g ^ n * g := by rw [ih]
      _ = g * (g ^ n * g) := by rw [mul_assoc]
      _ = g * g ^ (n + 1) := by rw [pow_succ]

/-! @end -/

/-!
@problem pow_add
@title The Laws of Exponents
@concept natural_powers

@preamble
A product of `m` copies of `g` followed by `n` copies is `m + n` copies, and `n` blocks of `m` copies make `m * n` copies. These are the laws of exponents, `pow_add` and `pow_mul`:
```lean
g ^ (m + n) = g ^ m * g ^ n
g ^ (m * n) = (g ^ m) ^ n
```
In the exponents, `+` and `*` are the arithmetic of `ℕ`; the `*` between two powers is the group's operation. Their additive versions are `add_nsmul` and `mul_nsmul'`. Core Lean has `Nat.add_zero`, `Nat.add_assoc`, `Nat.mul_zero` and `Nat.mul_add_one` for the arithmetic in the exponents:
```lean
theorem Nat.mul_add_one (n m : ℕ) : n * (m + 1) = n * m + n
```
@description
Prove the two laws of exponents. The context holds `pow_zero`, `pow_succ`, `mul_one` and `mul_assoc`.
-/

@[to_additive add_nsmul]
theorem pow_add {G : Type u} [Group G] (g : G) (m n : ℕ) : g ^ (m + n) = g ^ m * g ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, pow_zero, mul_one]
  | succ n ih => rw [← Nat.add_assoc, pow_succ, pow_succ, ih, mul_assoc]

@[to_additive mul_nsmul']
theorem pow_mul {G : Type u} [Group G] (g : G) (m n : ℕ) : g ^ (m * n) = (g ^ m) ^ n := by
  induction n with
  | zero => rw [Nat.mul_zero, pow_zero, pow_zero]
  | succ n ih => rw [Nat.mul_add_one, pow_add, ih, pow_succ]

/-! @end -/

/-!
@problem int_pow
@title Multiples in the Integers
@concept natural_powers

@preamble
In the integers a multiple is a repeated sum: `2 • 3` is `0 + 3 + 3`, which is `6`, and in general `k • a` is the product `k * a`. In particular every natural number `k` is the multiple `k • 1`. `omega` knows that `↑(k + 1)` is `↑k + 1`, but it treats a multiple such as `(k + 1) • 1` as an unknown number.
@description
Show that `k • 1 = k` in `ℤ` for every natural number `k`. The context holds `zero_nsmul` and `succ_nsmul`.
-/

theorem int_nsmul_one (k : ℕ) : k • (1 : ℤ) = k := by
  induction k with
  | zero =>
    rw [zero_nsmul]
    rfl
  | succ k ih =>
    rw [succ_nsmul, ih]
    omega

/-! @end -/

/-!
@concept integer_powers
@title Integer Powers
@kind definition

A negative power is the inverse of a positive one, so that every integer is an exponent, and the laws of exponents hold for all integers. The subject needs them because every element reached from an element by multiplying and inverting is one of its integer powers.
-/

/-!
@problem zpow
@title The Definition of an Integer Power
@concept integer_powers

@preamble
As the first section showed, an integer is either `Int.ofNat n`, a natural number, or `Int.negSucc n`, which is `-(n + 1)`. So a power with an integer exponent is defined by the two cases: `g ^ Int.ofNat n` is the natural power `g ^ n`, and `g ^ Int.negSucc n` is `(g ^ (n + 1))⁻¹`, the inverse of a natural power.

The definition matches on the two constructors, with the exponent first as before. The notation comes from a second instance, `Pow G ℤ`, so `g ^ k` is the natural power when `k : ℕ` and this one when `k : ℤ`. A negative numeral needs its type, as in `g ^ (-1 : ℤ)`.
@description
Define `Group.zpow k g` by the two cases, and supply the instance `Group.toZPow : Pow G ℤ`. Check by `decide` that in the symmetric group on three points the inverse of the rotation is the rotation twice:
```lean
rot3 ^ (-1 : ℤ) = rot3 * rot3
```
-/

def Group.zpow {G : Type u} [Group G] : ℤ → G → G
  | Int.ofNat n, g => g ^ n
  | Int.negSucc n, g => (g ^ (n + 1))⁻¹

instance Group.toZPow {G : Type u} [Group G] : Pow G ℤ := ⟨fun g k => Group.zpow k g⟩

/-- @spec -/
example {G : Type u} [Group G] (g : G) (n : ℕ) :
    g ^ (n : ℤ) = g ^ n ∧ g ^ Int.negSucc n = (g ^ (n + 1))⁻¹ := ⟨rfl, rfl⟩

theorem s3_zpow_check : rot3 ^ (-1 : ℤ) = rot3 * rot3 := by
  decide

/-! @end -/

/-!
@problem zsmul
@title Integer Multiples
@concept integer_powers

@preamble
The additive version of the integer power is the integer multiple `k • a`: `Int.ofNat n • a` is the natural multiple `n • a`, and `Int.negSucc n • a` is `-((n + 1) • a)`, the negative of a natural multiple. It is the previous definition with `+`, `0` and `-` for `*`, `1` and `⁻¹`, through a second instance of `SMul`, now `SMul ℤ A`. The numeral `-3` needs its type, since a bare `3` in `3 • a` is read as a natural number.
@description
Define `AddGroup.zsmul k a` by the two cases, supply the instance `AddGroup.toZSMul : SMul ℤ A`, and check that `(-3 : ℤ) • (2 : ℤ) = -6`.
-/

def AddGroup.zsmul {A : Type u} [AddGroup A] : ℤ → A → A
  | Int.ofNat n, a => n • a
  | Int.negSucc n, a => -((n + 1) • a)

instance AddGroup.toZSMul {A : Type u} [AddGroup A] : SMul ℤ A := ⟨AddGroup.zsmul⟩

/-- @spec -/
example {A : Type u} [AddGroup A] (a : A) (n : ℕ) :
    (n : ℤ) • a = n • a ∧ Int.negSucc n • a = -((n + 1) • a) := ⟨rfl, rfl⟩

theorem int_neg_three_zsmul_two : (-3 : ℤ) • (2 : ℤ) = -6 := by
  decide

/-! @end -/

attribute [to_additive existing AddGroup.zsmul] Group.zpow

attribute [to_additive existing AddGroup.toZSMul] Group.toZPow

/-!
@problem zpow_zero_one
@title The Integer Powers Zero and One
@concept integer_powers

@preamble
The two equations of the definition, `zpow_natCast` and `zpow_negSucc`, hold by `rfl`, since the cast `(n : ℤ)` is `Int.ofNat n` by definition. The exponents `0` and `1` are `Int.ofNat 0` and `Int.ofNat 1`, so the integer powers `0` and `1` are the natural ones.

As in the first section, `change` restates a goal in a form equal to it by definition, here in natural powers and inverses. A numeral in the restated goal takes its type from the goal unless it is written with one. The context holds `pow_one`.
@description
Show that the two equations of the definition hold,
```lean
g ^ (n : ℤ) = g ^ n
g ^ Int.negSucc n = (g ^ (n + 1))⁻¹
```
and that `g ^ (0 : ℤ) = 1` and `g ^ (1 : ℤ) = g`.
-/

@[to_additive natCast_zsmul]
theorem zpow_natCast {G : Type u} [Group G] (g : G) (n : ℕ) : g ^ (n : ℤ) = g ^ n := rfl

@[to_additive negSucc_zsmul]
theorem zpow_negSucc {G : Type u} [Group G] (g : G) (n : ℕ) :
    g ^ Int.negSucc n = (g ^ (n + 1))⁻¹ := rfl

@[to_additive zero_zsmul]
theorem zpow_zero {G : Type u} [Group G] (g : G) : g ^ (0 : ℤ) = 1 := rfl

@[to_additive one_zsmul]
theorem zpow_one {G : Type u} [Group G] (g : G) : g ^ (1 : ℤ) = g := by
  change g ^ (1 : ℕ) = g
  rw [pow_one]

/-! @end -/

/-!
@problem zpow_neg
@title Negative Exponents
@concept integer_powers

@preamble
A negative exponent inverts: `g ^ (-n) = (g ^ n)⁻¹` for every integer `n`. Negation exchanges the two forms of an integer by definition. The context holds `inv_one` and `inv_inv`.
@description
Show that `g ^ (-n) = (g ^ n)⁻¹` for every integer `n`.
-/

@[to_additive neg_zsmul]
theorem zpow_neg {G : Type u} [Group G] (g : G) (n : ℤ) : g ^ (-n) = (g ^ n)⁻¹ := by
  cases n with
  | ofNat k =>
    cases k with
    | zero =>
      change (1 : G) = 1⁻¹
      rw [inv_one]
    | succ k => rfl
  | negSucc k =>
    change g ^ (k + 1) = (g ^ (k + 1))⁻¹⁻¹
    rw [inv_inv]

/-! @end -/

/-!
@problem zpow_add_one
@title Adding and Subtracting One in the Exponent
@concept integer_powers

@preamble
For a natural exponent, `g ^ (n + 1) = g ^ n * g` is the definition; for an integer exponent it is a theorem, `zpow_add_one`. Adding one to a negative integer `Int.negSucc (j + 1)` gives `Int.negSucc j`, and that case is the subtle one. There the right side reduces as follows:
```lean
(g ^ (j + 1 + 1))⁻¹ * g = (g * g ^ (j + 1))⁻¹ * g
  = (g ^ (j + 1))⁻¹ * g⁻¹ * g = (g ^ (j + 1))⁻¹
```
A bare `rw` with a law about powers rewrites the first power it matches, which need not be the one meant; naming the law's arguments picks it. The context holds `pow_one`, `pow_succ'`, `mul_inv_rev` and the adjacent cancellations.

The companion law, `g ^ (n - 1) = g ^ n * g⁻¹`, follows from the first; core Lean's `Int.sub_add_cancel`, met in the first section, helps.
@description
Show that `g ^ (n + 1) = g ^ n * g` and that `g ^ (n - 1) = g ^ n * g⁻¹` for every integer `n`.
-/

@[to_additive add_one_zsmul]
theorem zpow_add_one {G : Type u} [Group G] (g : G) (n : ℤ) : g ^ (n + 1) = g ^ n * g := by
  cases n with
  | ofNat k => rfl
  | negSucc k =>
    cases k with
    | zero =>
      change 1 = (g ^ 1)⁻¹ * g
      rw [pow_one, inv_mul_cancel]
    | succ j =>
      change (g ^ (j + 1))⁻¹ = (g ^ (j + 1 + 1))⁻¹ * g
      rw [pow_succ' g (j + 1), mul_inv_rev, inv_mul_cancel_right]

@[to_additive sub_one_zsmul]
theorem zpow_sub_one {G : Type u} [Group G] (g : G) (n : ℤ) : g ^ (n - 1) = g ^ n * g⁻¹ := by
  have h := zpow_add_one g (n - 1)
  rw [Int.sub_add_cancel] at h
  rw [h, mul_inv_cancel_right]

/-! @end -/

/--
@problem one_zpow
@title Integer Powers of the Neutral Element
@concept integer_powers

@preamble
`1 ^ n = 1` holds for an integer exponent too, and the integers admit the induction of the first section. The context holds `zpow_add_one`, `zpow_sub_one`, `inv_one` and `mul_one`.
@description
Show that `1 ^ n = 1` for every integer `n`.
-/
@[to_additive zsmul_zero]
theorem one_zpow {G : Type u} [Group G] (n : ℤ) : (1 : G) ^ n = 1 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [zpow_add_one, ih, mul_one]
  | pred k ih => rw [zpow_sub_one, ih, inv_one, mul_one]

/-!
@problem zpow_add
@title The Laws of Exponents for Integer Powers
@concept integer_powers

@preamble
The law of exponents for a sum holds for integer exponents too, and so does the law for a difference, `zpow_add` and `zpow_sub`:
```lean
g ^ (m + n) = g ^ m * g ^ n
g ^ (m - n) = g ^ m * (g ^ n)⁻¹
```
The proof follows that of the law for natural exponents. The additive version of the first is `add_zsmul`. For the exponents core Lean has `Int.add_zero`, `Int.add_assoc` and
```lean
theorem Int.add_sub_assoc (a b c : ℤ) : a + b - c = a + (b - c)
theorem Int.sub_eq_add_neg {a b : ℤ} : a - b = a + -b
```
@description
Prove the two laws for all integers `m` and `n`. The context holds `zpow_zero`, `zpow_neg`, `zpow_add_one`, `zpow_sub_one`, `mul_one` and `mul_assoc`.
-/

@[to_additive add_zsmul]
theorem zpow_add {G : Type u} [Group G] (g : G) (m n : ℤ) : g ^ (m + n) = g ^ m * g ^ n := by
  induction n with
  | zero => rw [Int.add_zero, zpow_zero, mul_one]
  | succ k ih => rw [← Int.add_assoc, zpow_add_one, zpow_add_one, ih, mul_assoc]
  | pred k ih => rw [← Int.add_sub_assoc, zpow_sub_one, zpow_sub_one, ih, mul_assoc]

@[to_additive sub_zsmul]
theorem zpow_sub {G : Type u} [Group G] (g : G) (m n : ℤ) : g ^ (m - n) = g ^ m * (g ^ n)⁻¹ := by
  rw [Int.sub_eq_add_neg, zpow_add, zpow_neg]

/-! @end -/

/--
@problem int_zsmul_one
@title Integer Multiples in the Integers
@concept integer_powers

@preamble
An earlier problem showed that `k • 1 = k` in `ℤ` for a natural number `k`. The same holds for every integer `k`, so every integer is a multiple of `1`. As with natural multiples, `omega` treats a multiple it has not expanded as an unknown number.
@description
Show that `k • 1 = k` in `ℤ` for every integer `k`. The context holds the additive versions of the two laws of adding and subtracting one in the exponent:
```lean
add_one_zsmul : (n + 1) • a = n • a + a
sub_one_zsmul : (n - 1) • a = n • a + -a
```
-/
theorem int_zsmul_one (k : ℤ) : k • (1 : ℤ) = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [add_one_zsmul, ih]
  | pred k ih =>
    rw [sub_one_zsmul, ih]
    omega

/-!
@concept order_of_element
@title The Order of an Element
@kind definition

The order of an element is the least positive exponent that gives the neutral element, and `0` when there is none, so an element has infinite order exactly when its order is `0`. The powers of an element repeat with this period, and an exponent gives the neutral element exactly when the order divides it.
-/

/-!
@problem is_of_fin_order
@title Elements of Finite Order
@concept order_of_element

@preamble
A positive power of `rot3` is `1`: `rot3 ^ 3 = 1`, since three turns of the triangle bring every vertex home. No positive multiple of `1` in `ℤ` is `0`, since `k • 1 = k`. An element `g` has *finite order* when `g ^ n = 1` for some `n > 0`, a question about natural exponents. We write `IsOfFinOrder g`, and `IsOfFinAddOrder a` for its additive version.

`IsOfFinOrder g` is a `def` whose type is `Prop`, a proposition with a name, as a set in Set Theory was a function into `Prop` with a name. A proof of it is a witness with its two facts, `⟨n, _, _⟩`. The context holds `int_nsmul_one`, and `s3_pow_check` of the definition of a power, whose first half is `rot3 ^ 3 = 1`.
@description
Define `IsOfFinOrder g` as `∃ n, 0 < n ∧ g ^ n = 1`, keeping the `@[to_additive]` line; show that `rot3` has finite order, and that `1` in `ℤ` does not, `¬IsOfFinAddOrder (1 : ℤ)`.
-/

@[to_additive IsOfFinAddOrder]
def IsOfFinOrder {G : Type u} [Group G] (g : G) : Prop := ∃ n, 0 < n ∧ g ^ n = 1

/-- @spec -/
example {G : Type u} [Group G] (g : G) : IsOfFinOrder g ↔ ∃ n, 0 < n ∧ g ^ n = 1 := Iff.rfl

theorem rot3_isOfFinOrder : IsOfFinOrder rot3 :=
  ⟨3, by decide, s3_pow_check.1⟩

theorem int_one_not_isOfFinAddOrder : ¬ IsOfFinAddOrder (1 : ℤ) := by
  intro ⟨n, hn, h⟩
  rw [int_nsmul_one] at h
  omega

/-! @end -/

/-!
@problem to_fin_or_zero
@title A Definition That Uses Its Condition
@concept order_of_element

@preamble
A definition by cases sometimes needs, in one case, the proof that the case holds. A number `a` names an element of `Fin (n + 1)` only when `a < n + 1`, and the anonymous constructor `⟨a, h⟩` asks for that proof `h`. Lean's *dependent* `if` names it:
```lean
if h : c then x else y
```
is `x` when `c` holds and `y` when it does not, and the branch `x` may use `h : c`, the branch `y` the proof `h : ¬c`. The condition must be decidable, as an inequality between numbers is, so that Lean can compute which branch applies. The plain `if c then x else y` of Programming in Lean is the same with the proof left unnamed.
@description
Define `toFinOrZero n a`, the element of `Fin (n + 1)` with value `a` when `a < n + 1` and `0` otherwise, and check by `decide` that `toFinOrZero 4 3 = 3` and `toFinOrZero 4 7 = 0`.
-/

def toFinOrZero (n a : ℕ) : Fin (n + 1) :=
  if h : a < n + 1 then ⟨a, h⟩ else 0

/-- @spec -/
example : toFinOrZero 4 0 = 0 ∧ toFinOrZero 4 3 = 3 ∧ toFinOrZero 4 4 = 4 ∧
    toFinOrZero 4 5 = 0 ∧ toFinOrZero 2 9 = 0 ∧ toFinOrZero 0 0 = 0 := by
  decide

theorem toFinOrZero_check : toFinOrZero 4 3 = 3 ∧ toFinOrZero 4 7 = 0 := by
  decide

/-! @end -/

/-!
@problem order_of
@title The Definition of the Order
@concept order_of_element

@preamble
The *order* of an element `g` is the least `n > 0` with `g ^ n = 1`, when there is one. We write it `orderOf g`, and set it to `0` when there is none. The least such `n` is `Nat.find h` for a proof `h : IsOfFinOrder g`, as in the first section. The definition is a dependent `if`, as in the previous problem, on whether such a proof exists.

Whether an element has finite order is not a question Lean can settle by computation, so the definition opens `Classical`, as the first section did to count a quotient, and is a `noncomputable def`. The keyword records the price the first section named: Lean will reason about `orderOf g` but never compute it.
@description
Define `orderOf g` as `Nat.find h` when there is a proof `h` that `g` has finite order, and as `0` otherwise, keeping the `@[to_additive]` line. Its additive version is `addOrderOf a`.
-/

open Classical in
@[to_additive addOrderOf]
noncomputable def orderOf {G : Type u} [Group G] (g : G) : ℕ :=
  if h : IsOfFinOrder g then Nat.find h else 0

/-- @spec -/
example {G : Type u} [Group G] (g : G) (h : ¬ IsOfFinOrder g) : orderOf g = 0 := by
  unfold orderOf
  rw [dif_neg h]

/-- @spec -/
example {G : Type u} [Group G] (g : G) (h : IsOfFinOrder g) :
    (0 < orderOf g ∧ g ^ orderOf g = 1) ∧ ∀ m, 0 < m → g ^ m = 1 → orderOf g ≤ m := by
  classical
  unfold orderOf
  rw [dif_pos h]
  exact ⟨Nat.find_spec h, fun _ hm h' => Nat.find_min' h ⟨hm, h'⟩⟩

/-! @end -/

/-!
@problem order_of_cases
@title The Two Cases of the Order
@concept order_of_element

@preamble
A definition by `if` is used through its two cases. Core Lean's `dif_pos h` says that `if h : c then a else b` is `a` when `h : c`, and `dif_neg h` that it is `b` when `h : ¬c`. `unfold orderOf` replaces `orderOf g` by its definition. A statement that mentions `Nat.find h` needs the decidability instance the definition had, so it stands under `open Classical in` too; without that line Lean rejects `Nat.find h`. The context holds `int_one_not_isOfFinAddOrder`.
@description
Show that `orderOf g = Nat.find h` for `h : IsOfFinOrder g`, that `orderOf g = 0` for `h : ¬IsOfFinOrder g`, and that `addOrderOf (1 : ℤ) = 0`.
-/

open Classical in
@[to_additive addOrderOf_of_isOfFinAddOrder]
theorem orderOf_of_isOfFinOrder {G : Type u} [Group G] {g : G} (h : IsOfFinOrder g) :
    orderOf g = Nat.find h := by
  unfold orderOf
  rw [dif_pos h]

@[to_additive addOrderOf_of_not_isOfFinAddOrder]
theorem orderOf_of_not_isOfFinOrder {G : Type u} [Group G] {g : G} (h : ¬ IsOfFinOrder g) :
    orderOf g = 0 := by
  unfold orderOf
  rw [dif_neg h]

theorem addOrderOf_int_one : addOrderOf (1 : ℤ) = 0 :=
  addOrderOf_of_not_isOfFinAddOrder int_one_not_isOfFinAddOrder

/-! @end -/

/-!
@problem pow_order_of_eq_one
@title The Order Is the Least Exponent
@concept order_of_element

@preamble
Three facts make the order useful. First, `g ^ orderOf g = 1` in every case, since `g ^ 0 = 1` covers infinite order. Second, no smaller positive exponent gives `1`. Third, the order is positive exactly when `g` has finite order. The context holds the two equations of the previous problem, and `Nat.find_spec` and `Nat.find_min'` were met in the first section.

The tactic `by_cases h : p` splits a goal into a case with `h : p` and a case with `h : ¬p`.
@description
Show that `g ^ orderOf g = 1`, that `orderOf g ≤ n` when `0 < n` and `g ^ n = 1`, and that `0 < orderOf g` exactly when `g` has finite order.
-/

open Classical in
@[to_additive addOrderOf_nsmul_eq_zero]
theorem pow_orderOf_eq_one {G : Type u} [Group G] (g : G) : g ^ orderOf g = 1 := by
  by_cases h : IsOfFinOrder g
  · rw [orderOf_of_isOfFinOrder h]
    exact (Nat.find_spec h).2
  · rw [orderOf_of_not_isOfFinOrder h, pow_zero]

open Classical in
@[to_additive addOrderOf_le_of_nsmul_eq_zero]
theorem orderOf_le_of_pow_eq_one {G : Type u} [Group G] {g : G} {n : ℕ} (hn : 0 < n)
    (h : g ^ n = 1) : orderOf g ≤ n := by
  have hf : IsOfFinOrder g := ⟨n, hn, h⟩
  rw [orderOf_of_isOfFinOrder hf]
  exact Nat.find_min' hf ⟨hn, h⟩

open Classical in
@[to_additive addOrderOf_pos_iff]
theorem orderOf_pos_iff {G : Type u} [Group G] {g : G} : 0 < orderOf g ↔ IsOfFinOrder g := by
  constructor
  · intro hpos
    by_cases h : IsOfFinOrder g
    · exact h
    · rw [orderOf_of_not_isOfFinOrder h] at hpos
      omega
  · intro h
    rw [orderOf_of_isOfFinOrder h]
    exact (Nat.find_spec h).1

/-! @end -/

/-!
@problem order_of_eq_iff
@title Recognizing the Order
@concept order_of_element

@preamble
To show that the order of `g` is `n`, for a positive `n`, it is enough to check that `g ^ n = 1` and that no smaller positive exponent gives `1`. This is `orderOf_eq_iff`, an equivalence under the hypothesis `0 < n`. It follows from the three facts of the previous problem, which the context holds, without returning to the definition.

In `ZMod 6`, `2 + 2 = 4` and `2 + 2 + 2 = 0`, so `2` has order `3`. `decide` cannot evaluate `addOrderOf 2`, as it could not evaluate `Nat.find` in the first section, but it can check a statement about the finitely many numbers below `3`.
@description
Show that for `0 < n`, `orderOf g = n` exactly when `g ^ n = 1` and `g ^ m ≠ 1` for every `m` with `m < n` and `0 < m`; and conclude that `2` has order `3` in `ZMod 6`.
-/

@[to_additive addOrderOf_eq_iff]
theorem orderOf_eq_iff {G : Type u} [Group G] {g : G} {n : ℕ} (hn : 0 < n) :
    orderOf g = n ↔ g ^ n = 1 ∧ ∀ m, m < n → 0 < m → g ^ m ≠ 1 := by
  constructor
  · intro h
    constructor
    · rw [← h]
      exact pow_orderOf_eq_one g
    · intro m hm hm0 hgm
      have := orderOf_le_of_pow_eq_one hm0 hgm
      omega
  · intro ⟨h, hmin⟩
    have hle := orderOf_le_of_pow_eq_one hn h
    have hpos := orderOf_pos_iff.mpr ⟨n, hn, h⟩
    by_cases hlt : orderOf g < n
    · exact absurd (pow_orderOf_eq_one g) (hmin (orderOf g) hlt hpos)
    · omega

theorem addOrderOf_zmod_six_two : addOrderOf (2 : ZMod 6) = 3 := by
  rw [addOrderOf_eq_iff (by decide)]
  decide

/-! @end -/

/-!
@problem pow_mod_order_of
@title The Powers Repeat With the Order
@concept order_of_element

@preamble
The powers of `g` repeat with the order as their period: `g ^ (n % d) = g ^ n` for the order `d`, which is `pow_mod_orderOf`. The argument is division of `n` by `d`, through the first section's
```lean
theorem Nat.mod_add_div (n d : ℕ) : n % d + d * (n / d) = n
```
and it holds in every case, since `n % 0 = n`. Rewriting with that equation directly would replace every `n`, the one inside `n % d` included. The context holds `pow_orderOf_eq_one`, `one_pow`, `pow_add`, `pow_mul` and `mul_one`.
@description
Show that `g ^ (n % orderOf g) = g ^ n`.
-/

@[to_additive mod_addOrderOf_nsmul]
theorem pow_mod_orderOf {G : Type u} [Group G] (g : G) (n : ℕ) :
    g ^ (n % orderOf g) = g ^ n := by
  have h := Nat.mod_add_div n (orderOf g)
  have h' : g ^ n = g ^ (n % orderOf g + orderOf g * (n / orderOf g)) := by
    rw [h]
  rw [h', pow_add, pow_mul, pow_orderOf_eq_one, one_pow, mul_one]

/-! @end -/

/-!
@problem order_of_dvd_iff_pow_eq_one
@title The Exponents That Give the Neutral Element
@concept order_of_element

@preamble
An exponent `n` gives `1` exactly when the order divides `n`. By the previous problem, `g ^ n = 1` gives `g ^ (n % orderOf g) = 1`, and a nonzero remainder below the order cannot do that. We name the hard direction `orderOf_dvd_of_pow_eq_one` and the equivalence `orderOf_dvd_iff_pow_eq_one`. On `ℕ`, `a ∣ b` is `∃ c, b = a * c`, which `intro ⟨k, hk⟩` opens. Core Lean has `Nat.mod_lt`, `Nat.pos_of_ne_zero` and
```lean
theorem Nat.dvd_of_mod_eq_zero {m n : ℕ} (h : n % m = 0) : m ∣ n
```
@description
Show that `orderOf g ∣ n` whenever `g ^ n = 1`, and that `orderOf g ∣ n` exactly when `g ^ n = 1`. The context holds `pow_mod_orderOf`, `pow_orderOf_eq_one`, `orderOf_le_of_pow_eq_one`, `orderOf_pos_iff`, `one_pow` and `pow_mul`.
-/

@[to_additive addOrderOf_dvd_of_nsmul_eq_zero]
theorem orderOf_dvd_of_pow_eq_one {G : Type u} [Group G] {g : G} {n : ℕ} (h : g ^ n = 1) :
    orderOf g ∣ n := by
  apply Nat.dvd_of_mod_eq_zero
  by_cases hr : n % orderOf g = 0
  · exact hr
  · have hg : g ^ (n % orderOf g) = 1 := by
      rw [pow_mod_orderOf, h]
    have hpos := orderOf_pos_iff.mpr ⟨n % orderOf g, Nat.pos_of_ne_zero hr, hg⟩
    have h1 := orderOf_le_of_pow_eq_one (Nat.pos_of_ne_zero hr) hg
    have h2 := Nat.mod_lt n hpos
    omega

@[to_additive addOrderOf_dvd_iff_nsmul_eq_zero]
theorem orderOf_dvd_iff_pow_eq_one {G : Type u} [Group G] {g : G} {n : ℕ} :
    orderOf g ∣ n ↔ g ^ n = 1 := by
  constructor
  · intro ⟨k, hk⟩
    rw [hk, pow_mul, pow_orderOf_eq_one, one_pow]
  · exact orderOf_dvd_of_pow_eq_one

/-! @end -/

/-!
@problem order_of_eq_one_iff
@title The Elements of Order One
@concept order_of_element

@preamble
The neutral element is the only element of order `1`: the order of `1` is `1`, and conversely an element of order `1` is `1`. We name the two facts `orderOf_one` and `orderOf_eq_one_iff`. The context holds `orderOf_dvd_iff_pow_eq_one`, `pow_orderOf_eq_one` and `pow_one`, and core Lean has
```lean
theorem Nat.dvd_one {n : ℕ} : n ∣ 1 ↔ n = 1
```
@description
Show that `orderOf 1 = 1`, and that `orderOf g = 1` exactly when `g = 1`.
-/

@[to_additive addOrderOf_zero]
theorem orderOf_one {G : Type u} [Group G] : orderOf (1 : G) = 1 := by
  have h : orderOf (1 : G) ∣ 1 := orderOf_dvd_iff_pow_eq_one.mpr (pow_one 1)
  exact Nat.dvd_one.mp h

@[to_additive addOrderOf_eq_one_iff]
theorem orderOf_eq_one_iff {G : Type u} [Group G] {g : G} : orderOf g = 1 ↔ g = 1 := by
  constructor
  · intro h
    rw [← pow_one g, ← h, pow_orderOf_eq_one]
  · intro h
    rw [h, orderOf_one]

/-! @end -/

/-!
@problem order_of_eq_two_iff
@title The Elements of Order Two
@concept order_of_element

@preamble
An element of order `2` is one that is its own inverse without being `1`: `g * g = 1` and `g ≠ 1`. Through the characterization of the order, the square appears as `g ^ 2`, which is `1 * g * g` by the definition of a power, not `g * g`. The context holds `orderOf_eq_iff`, `pow_succ` and `pow_one`.
@description
Show that `orderOf g = 2` exactly when `g * g = 1` and `g ≠ 1`.
-/

@[to_additive addOrderOf_eq_two_iff]
theorem orderOf_eq_two_iff {G : Type u} [Group G] {g : G} : orderOf g = 2 ↔ g * g = 1 ∧ g ≠ 1 := by
  rw [orderOf_eq_iff (by decide), pow_succ, pow_one]
  constructor
  · intro ⟨h1, h2⟩
    constructor
    · exact h1
    · have h := h2 1 (by decide) (by decide)
      rw [pow_one] at h
      exact h
  · intro ⟨h1, h2⟩
    constructor
    · exact h1
    · intro m hm hm0 h
      have hm1 : m = 1 := by omega
      rw [hm1, pow_one] at h
      exact h2 h

/-! @end -/

/-!
@problem order_of_sr
@title The Reflections Have Order Two
@concept order_of_element

@preamble
In the dihedral group every reflection `sr i` has order `2`, since a reflection is its own inverse: `(sr i)⁻¹` is `sr i` by the definition of the instance. And a reflection is not `1`, which is the rotation `r 0`. Two different constructors of an inductive type never give equal values, and Lean knows it: `cases h` on a hypothesis `h : sr i = 1` finds no way for the two sides to agree and closes the goal, as it would on `h : true = false`. The context holds `orderOf_eq_two_iff`.
@description
Show that no reflection `sr i` of `DihedralGroup n` is `1`, and that every reflection has order `2`.
-/

open DihedralGroup in
theorem sr_ne_one {n : ℕ} [NeZero n] (i : ZMod n) : sr i ≠ 1 := by
  intro h
  cases h

open DihedralGroup in
theorem orderOf_sr {n : ℕ} [NeZero n] (i : ZMod n) : orderOf (sr i) = 2 := by
  rw [orderOf_eq_two_iff]
  constructor
  · exact mul_inv_cancel (sr i)
  · exact sr_ne_one i

/-! @end -/

/-!
@concept orders_in_finite_groups
@title Orders in a Finite Group
@kind theorem

In a finite group every element has finite order: by the pigeonhole principle two of its powers coincide, and the power that leads from one to the other is the neutral element. The order is then positive, and the inverse of an element is one of its powers.
-/

/--
@problem exists_pow_eq_of_finite
@title Two Powers of an Element of a Finite Group Coincide
@concept orders_in_finite_groups

@preamble
In a group with `n` elements the `n + 1` powers `g ^ 0, …, g ^ n` cannot all differ: by the pigeonhole principle two of them coincide. The hypothesis is `[Finite G]`, and the pigeonhole principle is stated for a function between two `Fintype`s, which `Fin (n + 1)` and `Fin n` are.
@description
Show that in a finite group there are `i ≠ j` with `g ^ i = g ^ j`. The context holds `Fintype.exists_ne_map_eq_of_card_lt` and `Finite.exists_injective_fin` of the first section, which also met `Fintype.card_fin` and `Fin.ext`.
-/
@[to_additive exists_nsmul_eq_of_finite]
theorem exists_pow_eq_of_finite {G : Type u} [Group G] [Finite G] (g : G) :
    ∃ i j : ℕ, i ≠ j ∧ g ^ i = g ^ j := by
  obtain ⟨n, f, hf⟩ := Finite.exists_injective_fin G
  have hcard : Fintype.card (Fin n) < Fintype.card (Fin (n + 1)) := by
    rw [Fintype.card_fin, Fintype.card_fin]
    omega
  obtain ⟨i, j, hne, hij⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (n + 1) => f (g ^ i.val)) hcard
  exact ⟨i.val, j.val, fun h => hne (Fin.ext h), hf hij⟩

/-!
@problem finite_order_of_finite
@title Every Element of a Finite Group Has Finite Order
@concept orders_in_finite_groups

@preamble
Two equal powers `g ^ i = g ^ j` with `i < j` give `g ^ (j - i) = 1`, since `g ^ i` times that power is `g ^ j`. With the previous problem, every element of a finite group has finite order, and its order is positive. Core Lean has `Nat.le_of_lt` and
```lean
theorem Nat.add_sub_of_le {a b : ℕ} (h : a ≤ b) : a + (b - a) = b
```
@description
Show that `g ^ (j - i) = 1` whenever `i < j` and `g ^ i = g ^ j`; that every element of a finite group has finite order; and that its order is positive. The context holds `pow_add`, `mul_eq_left`, `orderOf_pos_iff` and `exists_pow_eq_of_finite`.
-/

@[to_additive nsmul_sub_eq_zero_of_nsmul_eq]
theorem pow_sub_eq_one_of_pow_eq {G : Type u} [Group G] {g : G} {i j : ℕ} (hij : i < j)
    (h : g ^ i = g ^ j) : g ^ (j - i) = 1 := by
  have h' : g ^ i * g ^ (j - i) = g ^ i := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hij), h]
  exact mul_eq_left.mp h'

@[to_additive isOfFinAddOrder_of_finite]
theorem isOfFinOrder_of_finite {G : Type u} [Group G] [Finite G] (g : G) : IsOfFinOrder g := by
  obtain ⟨i, j, hne, hpow⟩ := exists_pow_eq_of_finite g
  by_cases hlt : i < j
  · exact ⟨j - i, by omega, pow_sub_eq_one_of_pow_eq hlt hpow⟩
  · exact ⟨i - j, by omega, pow_sub_eq_one_of_pow_eq (by omega) hpow.symm⟩

@[to_additive addOrderOf_pos]
theorem orderOf_pos {G : Type u} [Group G] [Finite G] (g : G) : 0 < orderOf g :=
  orderOf_pos_iff.mpr (isOfFinOrder_of_finite g)

/-! @end -/

/-!
@problem inv_eq_pow
@title The Inverse as a Power
@concept orders_in_finite_groups

@preamble
In a finite group the inverse of `g` is a power of `g`: with `d` the order, `g * g ^ (d - 1)` is `g ^ d`, which is `1`. The exponent `d - 1` steps back up to `d` only because the order is positive; `0 < d` is `1 ≤ d` by the definition of `<` on `ℕ`, and core Lean has
```lean
theorem Nat.sub_add_cancel {n m : ℕ} (h : m ≤ n) : n - m + m = n
```
In `ZMod 6` the residue `2` has order `3`, so `-2 = 2 • 2 = 4`. The context holds `pow_orderOf_eq_one`, `inv_eq_of_mul_eq_one_right`, `pow_succ'`, `orderOf_pos` and `addOrderOf_zmod_six_two`.
@description
Show that `g⁻¹ = g ^ (orderOf g - 1)` in a finite group, and that in `ZMod 6` every negative is a multiple:
```lean
-a = (addOrderOf a - 1) • a
```
Check that both `-2` and `(addOrderOf 2 - 1) • 2` are `4`.
-/

@[to_additive neg_eq_addOrderOf_sub_one_nsmul]
theorem inv_eq_pow_orderOf_sub_one {G : Type u} [Group G] [Finite G] (g : G) :
    g⁻¹ = g ^ (orderOf g - 1) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos g), pow_orderOf_eq_one]

theorem zmod_six_neg_eq_nsmul (a : ZMod 6) : -a = (addOrderOf a - 1) • a :=
  neg_eq_addOrderOf_sub_one_nsmul a

theorem zmod_six_two_neg :
    -(2 : ZMod 6) = 4 ∧ (addOrderOf (2 : ZMod 6) - 1) • (2 : ZMod 6) = 4 := by
  rw [addOrderOf_zmod_six_two]
  decide

/-! @end -/

end GroupTheory
