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

`g ^ n` is the product of `n` copies of `g`, and the laws of exponents, `g ^ (m + n) = g ^ m * g ^ n` and `g ^ (m * n) = (g ^ m) ^ n`, hold in every group, by associativity alone. The order of an element is the first power that returns to `1`, and the elements reached from `g` by multiplying it by itself are its powers, so the subject defines powers by recursion and proves the laws once.
-/

/-!
@problem npow
@title The Definition of a Power
@concept natural_powers

@preamble
The *power* `g ^ n` is the product of `n` copies of `g`: `g ^ 0` is `1` and `g ^ (n + 1)` is `g ^ n * g`. It is a definition by recursion on `n`, as The Natural Numbers defined addition, with a line `| 0, _ => …` and a line `| n + 1, g => …`; the exponent comes first, `Group.npow n g`, and inside the definition the recursive call is `npow n g`, since `^` does not exist yet. The notation comes from an instance of Lean's class
```lean
class Pow (α : Type u) (β : Type v) where
  pow : α → β → α
```
built by `⟨…⟩` as `Add MyNat` was, which takes the base first.

A numeral exponent, as in `rot3 ^ 3`, has to be read as a natural number: the mark `@[default_instance high]` above the instance tells Lean to read it through this instance, as Mathlib's own power instance carries the same mark.
@description
Define `Group.npow n g` by the two equations, with `npow n g * g` for the power `n + 1`, in that order; supply the instance `Group.toPow : Pow G ℕ` under the mark; and check that `rot3 ^ 3 = 1` and `reflect3 ^ 2 = 1` by `decide`.
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
In an additive group the power `g ^ n` becomes the *multiple* `n • g`, the sum of `n` copies of `g`: `0 • g = 0` and `(n + 1) • g = n • g + g`. The textbook writes it `ng`; Lean writes `n • g` (typed `\smul`), the symbol of the class
```lean
class SMul (M : Type u) (α : Type v) where
  smul : M → α → α
```
which takes the number first. On the integers `n • a` is the product `n * a`, a multiple in the everyday sense. The definition is the previous one copied with `+` and `0`, as `AddGroup` copied `Group`, and the lines `attribute [to_additive existing AddGroup.nsmul] Group.npow` and the like after this problem pair the two, so that a theorem about powers under its mark has a copy about multiples.
@description
Define `AddGroup.nsmul n a` by the two equations, with `nsmul n a + a` for the multiple `n + 1`; supply the instance `AddGroup.toSMul : SMul ℕ A`; and check that `3 • (2 : ℤ) = 6` by `decide`.
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
The two equations of the definition, `pow_zero : g ^ 0 = 1` and `pow_succ : g ^ (n + 1) = g ^ n * g`, hold by `rfl`, and later proofs rewrite with them; their copies are `zero_nsmul` and `succ_nsmul`. `g ^ 1` is `g ^ 0 * g`, which is `1 * g`, and the definition does not say that this is `g`: that is the law `one_mul`. Nor is `1 ^ n = 1` an equation of the definition, which recurses on an exponent that is here unknown; it is proved by induction, as The Natural Numbers proved `0 + a = a`. On Lean's `ℕ` the tactic `induction n with` has the cases `zero` and `succ n ih`, and the goal of the step is written with `n + 1`, the form `pow_succ` takes; `rw [pow_succ]` matches `g ^ 1` as well, since Lean reads the numeral `1` as `0 + 1`. The last law puts the new factor on the left: `g ^ (n + 1) = g * g ^ n`, Mathlib's `pow_succ'`, again an induction.
@description
Show that `g ^ 0 = 1` and `g ^ (n + 1) = g ^ n * g`, which hold by definition; that `g ^ 1 = g`; that `1 ^ n = 1`; and that `g ^ (n + 1) = g * g ^ n`.
-/

@[to_additive zero_nsmul]
theorem pow_zero {G : Type u} [Group G] (g : G) : g ^ 0 = 1 := rfl

@[to_additive succ_nsmul]
theorem pow_succ {G : Type u} [Group G] (g : G) (n : ℕ) : g ^ (n + 1) = g ^ n * g := rfl

@[to_additive one_nsmul]
theorem pow_one {G : Type u} [Group G] (g : G) : g ^ 1 = g := by
  rw [pow_succ, pow_zero, one_mul]

@[to_additive nsmul_zero]
theorem one_pow {G : Type u} [Group G] (n : ℕ) : (1 : G) ^ n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ih, one_mul]

@[to_additive succ_nsmul']
theorem pow_succ' {G : Type u} [Group G] (g : G) (n : ℕ) : g ^ (n + 1) = g * g ^ n := by
  induction n with
  | zero => rw [pow_one, pow_zero, mul_one]
  | succ n ih => rw [pow_succ, ih, mul_assoc, ← ih, ← pow_succ]

/-! @end -/

/-!
@problem pow_add
@title The Laws of Exponents
@concept natural_powers

@preamble
A product of `m` copies of `g` followed by `n` copies is `m + n` copies: `g ^ (m + n) = g ^ m * g ^ n`. And `n` blocks of `m` copies make `m * n` copies: `g ^ (m * n) = (g ^ m) ^ n`. These are the laws of exponents, Mathlib's `pow_add` and `pow_mul`, and they hold in every group, commutative or not, since each is a regrouping of one product; their copies are `add_nsmul` and `mul_nsmul'`. Each is proved by induction on `n`, the variable the definition recurses on, with `m` fixed, and the second uses the first. In the exponents, `+` and `*` are the arithmetic of `ℕ`; the `*` between two powers is the group's operation. Core Lean has `Nat.add_zero`, `Nat.add_assoc`, `Nat.mul_zero` and `Nat.mul_add_one : n * (m + 1) = n * m + n` for the arithmetic in the exponents.
@description
Show that `g ^ (m + n) = g ^ m * g ^ n` and that `g ^ (m * n) = (g ^ m) ^ n`. The context holds `pow_zero`, `pow_succ`, `mul_one` and `mul_assoc`.
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
In the integers a multiple is a repeated sum: `2 • 3` is `0 + 3 + 3`, which is `6`, and in general `k • a` is the product `k * a`. The case the subject needs is `a = 1`: every natural number is a multiple of `1`, which is how the integers will turn out to be generated by a single element. The statement casts `k : ℕ` into `ℤ`, written `(k : ℤ)` and printed `↑k`; `omega` knows that `↑(k + 1)` is `↑k + 1`, once `succ_nsmul` has opened the multiple, and the base case, `0 = ↑0` once `zero_nsmul` has opened it, holds by `rfl`.
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

A negative power is the inverse of a positive one, `g ^ (-n) = (g ^ n)⁻¹`, so that `g ^ k` makes sense for every integer `k`, and the law `g ^ (m + n) = g ^ m * g ^ n` holds for all integers. Every element reached from `g` by multiplying and inverting is an integer power of `g`, and `ℤ` itself is the multiples of `1`, so the subject extends the exponent to `ℤ` and proves the laws again there.
-/

/-!
@problem zpow
@title The Definition of an Integer Power
@concept integer_powers

@preamble
An integer is a natural number or a negative one, `Int.ofNat n` or `Int.negSucc n`, which is `-(n + 1)`, as the first section took them apart. So a power with an integer exponent is defined by the two cases: `g ^ Int.ofNat n` is the natural power `g ^ n`, and `g ^ Int.negSucc n` is `(g ^ (n + 1))⁻¹`, the inverse of a natural power. The definition matches on the two constructors, as `cases` does, with the exponent first as before, and the notation comes from a second instance, `Pow G ℤ`, so that `g ^ k` is the natural power when `k : ℕ` and this one when `k : ℤ`; a negative numeral needs its type, `g ^ (-1 : ℤ)`. In the symmetric group on three points the inverse of the rotation is the rotation twice, `rot3 ^ (-1 : ℤ) = rot3 * rot3`, which `decide` computes.
@description
Define `Group.zpow k g` by the two cases, supply the instance `Group.toZPow : Pow G ℤ`, and check that `rot3 ^ (-1 : ℤ) = rot3 * rot3`.
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
The copy of the integer power is the integer multiple `k • a`: `Int.ofNat n • a` is the natural multiple `n • a`, and `Int.negSucc n • a` is `-((n + 1) • a)`, the negative of a natural multiple. It is the previous definition with `+`, `0` and `-` for `*`, `1` and `⁻¹`, through a second instance of `SMul`, now `SMul ℤ A`, and the lines `attribute [to_additive existing AddGroup.zsmul] Group.zpow` and the like after this problem pair the two. On the integers, `(-3 : ℤ) • 2 = -6`, which `decide` computes; the numeral needs its type, since a bare `3` in `3 • a` is read as a natural number.
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
@problem zpow_neg
@title The Powers Zero, One and Minus n
@concept integer_powers

@preamble
The two equations of the definition hold by `rfl`, Mathlib's `zpow_natCast : g ^ (n : ℤ) = g ^ n`, for the natural number `n` cast into `ℤ`, which is `Int.ofNat n` by definition, and `zpow_negSucc`. The exponents `0` and `1` are `Int.ofNat 0` and `Int.ofNat 1`, so `g ^ (0 : ℤ)` is `g ^ 0`, which is `1`, and `g ^ (1 : ℤ)` is `g ^ 1`, which `pow_one` says is `g`. A goal is put into the natural powers and inverses it unfolds to by `change t`, which restates it as `t` when the two are equal by definition; a numeral in `t` takes its type from the goal unless written with one, so `g ^ (1 : ℤ)` is restated as `g ^ (1 : ℕ)`.

The law of the sign is `g ^ (-n) = (g ^ n)⁻¹` for every integer `n`, Mathlib's `zpow_neg`. Negation exchanges the two forms of an integer by definition, `-(Int.ofNat (k + 1))` is `Int.negSucc k` and back, except that `0` is its own negative; so a case on an integer opens into a case on the natural number inside it. The context holds `pow_one`, `inv_one` and `inv_inv`.
@description
Show that `g ^ (n : ℤ) = g ^ n` and `g ^ Int.negSucc n = (g ^ (n + 1))⁻¹`; that `g ^ (0 : ℤ) = 1` and `g ^ (1 : ℤ) = g`; and that `g ^ (-n) = (g ^ n)⁻¹` for every integer `n`.
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
For a natural exponent, `g ^ (n + 1) = g ^ n * g` is the definition; for an integer exponent it is a theorem, Mathlib's `zpow_add_one`, proved by cases on `n`. For `Int.ofNat k`, the sum `Int.ofNat k + 1` is `Int.ofNat (k + 1)` by definition, and both sides unfold to the same natural power. For `Int.negSucc k` the exponent steps up towards zero, in two cases: `Int.negSucc 0 + 1 = 0`, and `Int.negSucc (j + 1) + 1 = Int.negSucc j`, again by definition; a `change` puts each case into natural powers and inverses, where both sides carry a power of a successor, so a rewrite with `pow_succ'` names its exponent. The context holds `pow_one`, `pow_succ'`, `mul_inv_rev` and the adjacent cancellations.

The mirror image, `g ^ (n - 1) = g ^ n * g⁻¹`, follows from the first law; core Lean has `Int.sub_add_cancel : a - b + b = a`.
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
`1 ^ n = 1` for an integer `n` is a small fact, and the place to learn the induction that the law of exponents to come needs: an induction over the integers. The induction of The Natural Numbers does not fit, since an integer has no first element. Mathlib's `Int.induction_on` is the principle that does: a property that holds at `0`, that passes from `k` to `k + 1`, and that passes from `-k` to `-k - 1`, holds for every integer. Under this subject's imports `induction n with` uses it by itself on an integer: the cases are `zero`, `succ k ih` and `pred k ih`, where `k : ℕ`, and the goal is about `↑k + 1` or `-↑k - 1`. The context holds `zpow_add_one`, `zpow_sub_one`, `inv_one` and `mul_one`.
@description
Show that `1 ^ n = 1` for every integer `n`, by induction on `n`.
-/
@[to_additive zsmul_zero]
theorem one_zpow {G : Type u} [Group G] (n : ℤ) : (1 : G) ^ n = 1 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [zpow_add_one, ih, mul_one]
  | pred k ih => rw [zpow_sub_one, ih, inv_one, mul_one]

/-!
@problem zpow_add
@title An Integer Power of a Sum
@concept integer_powers

@preamble
The law of exponents `g ^ (m + n) = g ^ m * g ^ n` holds for integer exponents too, and the proof is an induction on `n` in both directions, as in the previous problem, with `m` fixed throughout. Its copy, `add_zsmul : (m + n) • a = m • a + n • a`, is the distributive law on the integers. Core Lean has `Int.add_zero`, `Int.add_assoc`, `Int.add_sub_assoc : a + b - c = a + (b - c)` and `Int.sub_eq_add_neg : a - b = a + -b` for the exponents. The law for a difference, `g ^ (m - n) = g ^ m * (g ^ n)⁻¹`, follows from the law for a sum and `zpow_neg`, since a difference is a sum with a negative, Mathlib's `zpow_sub`.
@description
Show that `g ^ (m + n) = g ^ m * g ^ n` and `g ^ (m - n) = g ^ m * (g ^ n)⁻¹` for all integers `m` and `n`. The context holds `zpow_zero`, `zpow_neg`, `zpow_add_one` and `zpow_sub_one`.
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

/-!
@concept order_of_element
@title The Order of an Element
@kind definition

The order of an element `g` is the least positive `n` with `g ^ n = 1`, and `0` when there is none, so that an element of infinite order is told by its order being `0`. The powers of `g` repeat with this period: `g ^ n = 1` exactly when the order divides `n`. It is the first invariant of an element, and the number the subject's counting arguments turn on.
-/

/-!
@problem is_of_fin_order
@title Elements of Finite Order
@concept order_of_element

@preamble
Some positive power of `rot3` is the identity, `rot3 ^ 3 = 1`, since three turns of the triangle bring every vertex home; no positive multiple of `1` in `ℤ` is `0`, since `k • 1 = k`: the steps never return. An element `g` has *finite order* when `g ^ n = 1` for some `n > 0`, a question about natural exponents; Mathlib writes `IsOfFinOrder g`, and its copy for an additive group is `IsOfFinAddOrder a`, `∃ n, 0 < n ∧ n • a = 0`. It is a proposition, `∃ n, 0 < n ∧ g ^ n = 1`: a `def` whose type is `Prop`, a proposition with a name, as a set in Set Theory was a function into `Prop` with a name, and a proof of it is a witness with the two facts, `⟨n, _, _⟩`. The integer `1` is the subject's standing element of infinite order. The context holds `s3_pow_check`, that `rot3 ^ 3 = 1`, from the definition of a power, and `int_nsmul_one`.
@description
Define `IsOfFinOrder g` as `∃ n, 0 < n ∧ g ^ n = 1`, under its mark; show that `rot3` has finite order, and that `1` in `ℤ` does not, `¬IsOfFinAddOrder (1 : ℤ)`.
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
@problem order_of
@title The Definition of the Order
@concept order_of_element

@preamble
The *order* of an element `g` is the least `n > 0` with `g ^ n = 1`, when there is one; Mathlib writes it `orderOf g`, and sets it to `0` when there is none, so that an element of infinite order has order `0`. The least such `n` is `Nat.find h` for a proof `h : IsOfFinOrder g`, as in the first section, and the definition branches on whether such a proof exists. The shape, on the first section's example: `if h : ∃ k, 10 < k ∧ k % 3 = 0 then Nat.find h else 0` is the least multiple of `3` above `10`, and would be `0` if there were none; naming the proof of the condition, `h`, in the `if` itself lets the first branch use it.

Whether an element has finite order is not a question Lean can settle by computation, so the definition opens `Classical`, as the first section did to count a quotient, and is a `noncomputable def`: the keyword acknowledges the price the first section named, that Lean will reason about `orderOf g` and never compute it.
@description
Define `orderOf g`, the order of `g`, as `Nat.find h` for a proof `h` that `g` has finite order and as `0` otherwise, under `open Classical in` and as a `noncomputable def`, under its mark; the copy is `addOrderOf a`, the order of an element of an additive group.
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
A definition by `if` is used through its two cases. Core Lean's `dif_pos h` says that `if h : c then a else b` is `a` when `h : c`, and `dif_neg h` that it is `b` when `h : ¬c`; each is a rewrite rule, applied once `unfold orderOf` has exposed the `if`, and the two equations here are to be proved by them. They say that `orderOf g = Nat.find h` when `g` has finite order and `orderOf g = 0` when it does not, and later proofs rewrite with them rather than unfolding the definition again. A statement that mentions `Nat.find h` needs the decidability instance the definition had, so it stands under `open Classical in` too; without that line, `Nat.find h` does not elaborate. With the copy of the second equation the order of `1` in `ℤ` is read off, `addOrderOf (1 : ℤ) = 0`; the context holds `int_one_not_isOfFinAddOrder`.
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
What the order is for: `g ^ orderOf g = 1` in every case, since `g ^ 0 = 1` covers infinite order; no smaller positive exponent does it, `orderOf g ≤ n` whenever `0 < n` and `g ^ n = 1`; and the order is positive exactly when `g` has finite order. These are the first section's `Nat.find_spec` and `Nat.find_min'` read through the two equations of the previous problem, which the context holds, and the elements of the second and third statements are implicit, since each is applied to hypotheses that fix them.

A proof about the order begins by asking which case holds: the tactic `by_cases h : IsOfFinOrder g`, new here, splits the goal in two, with `h : IsOfFinOrder g` in the first and `h : ¬IsOfFinOrder g` in the second. A proof that uses `Nat.find_spec` or `Nat.find_min'` needs the classical instance and stands under `open Classical in`.
@description
Show that `g ^ orderOf g = 1`, that `orderOf g ≤ n` when `0 < n` and `g ^ n = 1`, and that `0 < orderOf g` exactly when `g` has finite order. Mathlib names them `pow_orderOf_eq_one`, `orderOf_le_of_pow_eq_one` and `orderOf_pos_iff`.
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
To show that the order of `g` is `n`, for a positive `n`, it is enough to check that `g ^ n = 1` and that no smaller positive exponent gives `1`: Mathlib's `orderOf_eq_iff`, an equivalence under the hypothesis `0 < n`. It follows from the three facts of the previous problem, which the context holds, with no case on the definition left to make.

In `ZMod 6`, `2 + 2 = 4` and `2 + 2 + 2 = 0`, so `2` has order `3`, `addOrderOf (2 : ZMod 6) = 3`. `decide` cannot compute `addOrderOf 2` itself, as it could not compute `Nat.find` in the first section; through the copy of the equivalence, `addOrderOf_eq_iff`, the claim becomes one about the multipliers `1`, `2` and `3`, and `decide` runs through them: `∀ m, m < 3 → …` is a statement about finitely many numbers, decided as a statement about `Fin 4` was.
@description
Show that for `0 < n`, `orderOf g = n` exactly when `g ^ n = 1` and `g ^ m ≠ 1` for every `m` with `0 < m` and `m < n`; and conclude that `2` has order `3` in `ZMod 6`.
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
@problem order_of_dvd_iff_pow_eq_one
@title The Exponents That Give the Neutral Element
@concept order_of_element

@preamble
The powers of `g` repeat with the order as their period: dividing `n` by the order, `n = n % orderOf g + orderOf g * (n / orderOf g)`, the first section's `Nat.mod_add_div`, and the laws of exponents reduce `g ^ n` to `g ^ (n % orderOf g)`, Mathlib's `pow_mod_orderOf`, in every case, since `n % 0 = n`. Rewriting a goal with that equation backwards replaces every `n`, the one inside `n % orderOf g` included; restate `g ^ n` alone first.

It follows that `g ^ n = 1` exactly when the order divides `n`, with the element of infinite order as a case of its own. Mathlib names the hard direction `orderOf_dvd_of_pow_eq_one` and the equivalence `orderOf_dvd_iff_pow_eq_one`. On `ℕ`, `a ∣ b` is `∃ c, b = a * c`, which `intro ⟨k, hk⟩` opens. Core Lean has `Nat.dvd_of_mod_eq_zero : n % m = 0 → m ∣ n`, `Nat.mod_lt`, `Nat.pos_of_ne_zero` and `Nat.mod_zero`.
@description
Show that `g ^ (n % orderOf g) = g ^ n`; that `orderOf g ∣ n` whenever `g ^ n = 1`; and that `orderOf g ∣ n` exactly when `g ^ n = 1`. The context holds `pow_orderOf_eq_one`, `orderOf_le_of_pow_eq_one`, `orderOf_pos_iff` and `orderOf_of_not_isOfFinOrder`, `one_pow`, `pow_add` and `pow_mul` of this section, and `mul_one`.
-/

@[to_additive mod_addOrderOf_nsmul]
theorem pow_mod_orderOf {G : Type u} [Group G] (g : G) (n : ℕ) :
    g ^ (n % orderOf g) = g ^ n := by
  have h := Nat.mod_add_div n (orderOf g)
  have h' : g ^ n = g ^ (n % orderOf g + orderOf g * (n / orderOf g)) := by
    rw [h]
  rw [h', pow_add, pow_mul, pow_orderOf_eq_one, one_pow, mul_one]

@[to_additive addOrderOf_dvd_of_nsmul_eq_zero]
theorem orderOf_dvd_of_pow_eq_one {G : Type u} [Group G] {g : G} {n : ℕ} (h : g ^ n = 1) :
    orderOf g ∣ n := by
  apply Nat.dvd_of_mod_eq_zero
  by_cases hf : IsOfFinOrder g
  · rw [← pow_mod_orderOf] at h
    by_cases hr : n % orderOf g = 0
    · exact hr
    · have h1 := orderOf_le_of_pow_eq_one (Nat.pos_of_ne_zero hr) h
      have h2 := Nat.mod_lt n (orderOf_pos_iff.mpr hf)
      omega
  · rw [orderOf_of_not_isOfFinOrder hf, Nat.mod_zero]
    by_cases hn : n = 0
    · exact hn
    · exact absurd ⟨n, Nat.pos_of_ne_zero hn, h⟩ hf

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
The neutral element is the only element of order `1`: the order of `1` is `1`, and conversely an element of order `1` is `1`. Each half is read off the characterization of the previous problem or off `pow_orderOf_eq_one`, which the context holds together with `pow_one`; Mathlib names the two facts `orderOf_one` and `orderOf_eq_one_iff`, and the elements of a group of order `1` have, of course, order `1`. With it the orders of the running examples can be tabulated: in `ZMod 6` the elements `0, 1, 2, 3, 4, 5` have orders `1, 6, 3, 2, 3, 6`; in `ℤ` only `0` has finite order; in `Dₙ` the rotation `r 1` has order `n`, and every reflection order `2`, the case the next problem settles.
@description
Show that `orderOf 1 = 1`, and that `orderOf g = 1` exactly when `g = 1`.
-/

@[to_additive addOrderOf_zero]
theorem orderOf_one {G : Type u} [Group G] : orderOf (1 : G) = 1 := by
  rw [orderOf_eq_iff (by decide)]
  constructor
  · exact pow_one 1
  · intro m hm hm0
    omega

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
An element of order `2` is one that is its own inverse without being `1`: `g * g = 1` and `g ≠ 1`. In the dihedral group every reflection `sr i` is such an element, since a reflection undone is the same reflection, and the general fact instantiates there. Through the characterization of the order the square appears as `g ^ 2`, which is `1 * g * g` by the definition of a power, not `g * g`; `pow_succ` and `pow_one` bring it to `g * g`. For a reflection, `(sr i)⁻¹` is `sr i` by the definition of the instance, so `mul_inv_cancel (sr i)`, which reads `sr i * (sr i)⁻¹ = 1`, closes the goal `sr i * sr i = 1` by `exact`, which sees through the unfolding; and `sr i ≠ 1` because `1` is the rotation `r 0` and the two constructors of `DihedralGroup n` never agree: `cases h` on a hypothesis `h : sr i = 1` closes the goal, as it would on `h : true = false`. The context holds `orderOf_eq_iff`, `pow_succ` and `pow_one`.
@description
Show that `orderOf g = 2` exactly when `g * g = 1` and `g ≠ 1`, and that every reflection `sr i` of `DihedralGroup n` has order `2`.
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

open DihedralGroup in
theorem orderOf_sr {n : ℕ} [NeZero n] (i : ZMod n) : orderOf (sr i) = 2 := by
  rw [orderOf_eq_two_iff]
  constructor
  · exact mul_inv_cancel (sr i)
  · intro h
    cases h

/-! @end -/

/-!
@concept orders_in_finite_groups
@title Orders in a Finite Group
@kind theorem

In a finite group every element has finite order: by the pigeonhole principle two of its powers coincide, and their quotient is `1`. The order is then positive, and the inverse of `g` is itself a power of `g`. These facts are what Lagrange's theorem and the counting arguments to come rest on, and they are the first place where the finiteness of a group enters a proof.
-/

/--
@problem pigeonhole
@title The Pigeonhole Principle
@concept orders_in_finite_groups

@preamble
A function from a larger finite set to a smaller one sends two elements to one value: the pigeonhole principle. Mathlib has its contrapositive, `Fintype.card_le_of_injective f hf : Fintype.card α ≤ Fintype.card β` for `hf : Function.Injective f`, that an injective function does not increase cardinality, and the first section counted with it in words; here the two elements are produced. A function that is not injective fails `∀ a b, f a = f b → a = b` at some `a` and `b`, and extracting them from the negated statement is the logic that Logic proved, under Mathlib's names: `not_forall : (¬∀ x, p x) ↔ ∃ x, ¬p x` and `Classical.not_imp : ¬(a → b) ↔ a ∧ ¬b`; the binders `⦃a b⦄` of `Function.Injective` come apart as `∀` does. An injective `f` contradicts the count, which `omega` sees once both inequalities are in hand. The name is Mathlib's.
@description
Let `f : α → β` be a function between finite types with `Fintype.card β < Fintype.card α`. Show that there are `a ≠ b` with `f a = f b`.
-/
theorem Fintype.exists_ne_map_eq_of_card_lt {α : Type u} {β : Type v} [Fintype α] [Fintype β]
    (f : α → β) (h : Fintype.card β < Fintype.card α) : ∃ a b, a ≠ b ∧ f a = f b := by
  by_cases hf : Function.Injective f
  · have hle := Fintype.card_le_of_injective f hf
    omega
  · obtain ⟨a, ha⟩ := not_forall.mp hf
    obtain ⟨b, hb⟩ := not_forall.mp ha
    obtain ⟨hab, hne⟩ := Classical.not_imp.mp hb
    exact ⟨a, b, hne, hab⟩

/--
@problem exists_pow_eq_of_finite
@title Two Powers of an Element of a Finite Group Coincide
@concept orders_in_finite_groups

@preamble
In a group with `n` elements the `n + 1` powers `g ^ 0, …, g ^ n` cannot all differ: by the pigeonhole principle two of them coincide. The hypothesis is `[Finite G]`, the class the first section showed, and `Finite.exists_equiv_fin G : ∃ n, Nonempty (G ≃ Fin n)` produces its bijection; `Nonempty α` is the proposition that `α` has an element, a structure whose one field holds one, so `⟨e⟩` proves it and `⟨n, ⟨e⟩⟩` takes the statement apart. The pigeonhole principle wants a function between types it can count, so the powers are indexed by `Fin (n + 1)` and compared through their labels in `Fin n`, counted by `Fintype.card_fin`; `e.injective` returns from equal labels to equal powers, and `Fin.ext` turns an equation of values into one of `Fin`.
@description
Show that in a finite group there are `i ≠ j` with `g ^ i = g ^ j`. The context holds the pigeonhole principle.
-/
@[to_additive exists_nsmul_eq_of_finite]
theorem exists_pow_eq_of_finite {G : Type u} [Group G] [Finite G] (g : G) :
    ∃ i j : ℕ, i ≠ j ∧ g ^ i = g ^ j := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin G
  have hcard : Fintype.card (Fin n) < Fintype.card (Fin (n + 1)) := by
    rw [Fintype.card_fin, Fintype.card_fin]
    omega
  obtain ⟨i, j, hne, hij⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (n + 1) => e (g ^ i.val)) hcard
  exact ⟨i.val, j.val, fun h => hne (Fin.ext h), e.injective hij⟩

/-!
@problem finite_order_of_finite
@title Every Element of a Finite Group Has Finite Order
@concept orders_in_finite_groups

@preamble
Two equal powers `g ^ i = g ^ j` with `i < j` give `g ^ (j - i) = 1`: by `pow_add`, `g ^ j` is `g ^ i * g ^ (j - i)`, and `mul_eq_left` of the second section reads the second factor off. With the previous problem, every element of a finite group has finite order, and its order is positive by `orderOf_pos_iff`. This is the first place where the finiteness of a group enters a proof; nothing before it asked a group to be finite. Core Lean has `Nat.add_sub_of_le : a ≤ b → a + (b - a) = b` and `Nat.le_of_lt`, and `omega` orders two distinct naturals; the two orders are symmetric cases.
@description
Show that `g ^ (j - i) = 1` whenever `i < j` and `g ^ i = g ^ j`; that every element of a finite group has finite order; and that its order is positive. The context holds `pow_add`, `mul_eq_left`, `orderOf_pos_iff` and `exists_pow_eq_of_finite`, and not the cancellation laws.
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
In a finite group the inverse of `g` is a power of `g`: with `d` the order, `g * g ^ (d - 1)` is `g ^ d`, which is `1` by `pow_orderOf_eq_one` of the previous concept, so `g ^ (d - 1)` is the inverse of `g` by the uniqueness of inverses, `inv_eq_of_mul_eq_one_right` of the second section. The exponent `d - 1` steps back up to `d` only because the order is positive, the previous problem's `orderOf_pos`; `0 < d` is `1 ≤ d` by the definition of `<` on `ℕ`, so `orderOf_pos g` is accepted where core Lean's `Nat.sub_add_cancel : m ≤ n → n - m + m = n` asks for `1 ≤ d`. In `ZMod 6` the residue `2` has order `3`, so by the copy `-2 = 2 • 2 = 4`; `decide` cannot evaluate `addOrderOf 2` itself, and computes both sides once the order is rewritten. The context holds `pow_orderOf_eq_one`, `inv_eq_of_mul_eq_one_right`, `pow_succ'`, `orderOf_pos` and `addOrderOf_zmod_six_two`.
@description
Show that `g⁻¹ = g ^ (orderOf g - 1)` in a finite group, and check that in `ZMod 6` both `-2` and `(addOrderOf 2 - 1) • 2` are `4`.
-/

@[to_additive neg_eq_addOrderOf_sub_one_nsmul]
theorem inv_eq_pow_orderOf_sub_one {G : Type u} [Group G] [Finite G] (g : G) :
    g⁻¹ = g ^ (orderOf g - 1) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos g), pow_orderOf_eq_one]

theorem zmod_six_two_neg :
    -(2 : ZMod 6) = 4 ∧ (addOrderOf (2 : ZMod 6) - 1) • (2 : ZMod 6) = 4 := by
  rw [addOrderOf_zmod_six_two]
  decide

/-! @end -/

end GroupTheory
