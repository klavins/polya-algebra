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
import PolyaAlgebra.GroupTheory.Cosets

/-! @section Cyclic Groups and Groups of Prime Order -/

universe u

namespace GroupTheory

set_option linter.translateGenerateName false

/-!
@concept cyclic_subgroups
@title Cyclic Subgroups
@kind theorem

The powers of one element form a subgroup, the cyclic subgroup it generates. In a finite group it has exactly as many elements as the order of the element, so by Lagrange's theorem the order of every element divides the order of the group. That divisibility is what settles the groups of prime order.
-/

/-!
@problem zpow_mod_order_of
@title Integer Powers Repeat With the Order
@concept cyclic_subgroups

@preamble
Integer powers repeat with the order as their period, as natural powers did in the section on powers, by the same division, now of integers:
```lean
theorem Int.emod_add_mul_ediv (a b : ℤ) :
    a % b + b * (a / b) = a
```
where `a / b` is the integer quotient. Write `d` for `orderOf g`, a natural number, and `(d : ℤ)` for it read as an integer. A rewrite with this identity changes every `k` of the goal, the one inside `k % (d : ℤ)` too. What is new is that a power whose exponent is a multiple of the order is `1`: `g ^ ((d : ℤ) * q) = 1` for every integer `q`.

The context holds the section on powers' `zpow_natCast`, `zpow_zero`, `zpow_add`, `zpow_sub` and `pow_orderOf_eq_one`, the second section's `inv_one`, and core's `Int.mul_add`, `Int.mul_sub`, `Int.mul_one` and `Int.mul_zero`.
@description
Show that a power of `g` whose exponent is a multiple of the order of `g` is `1`, under the name `zpow_orderOf_mul_eq_one`. Then show that the integer powers of `g` repeat with the order as their period, under the name `zpow_mod_orderOf`.
-/

@[to_additive addOrderOf_mul_zsmul_eq_zero]
theorem zpow_orderOf_mul_eq_one {G : Type u} [Group G] (g : G) (q : ℤ) :
    g ^ ((orderOf g : ℤ) * q) = 1 := by
  induction q with
  | zero => rw [Int.mul_zero, zpow_zero]
  | succ k ih =>
    rw [Int.mul_add, Int.mul_one, zpow_add, ih, one_mul, zpow_natCast, pow_orderOf_eq_one]
  | pred k ih =>
    rw [Int.mul_sub, Int.mul_one, zpow_sub, ih, one_mul, zpow_natCast, pow_orderOf_eq_one,
      inv_one]

@[to_additive mod_addOrderOf_zsmul]
theorem zpow_mod_orderOf {G : Type u} [Group G] (g : G) (k : ℤ) :
    g ^ (k % (orderOf g : ℤ)) = g ^ k := by
  have h := Int.emod_add_mul_ediv k (orderOf g)
  have h' : g ^ k = g ^ (k % (orderOf g : ℤ) + (orderOf g : ℤ) * (k / (orderOf g : ℤ))) := by
    rw [h]
  rw [h', zpow_add, zpow_orderOf_mul_eq_one, mul_one]

/-! @end -/

/--
@problem pow_inj_of_lt_order_of
@title Powers Below the Order Are Distinct
@concept cyclic_subgroups

@preamble
The powers of `g` with exponents below its order are all different. An equation between two of them would give a positive exponent smaller than the order whose power is `1`, and the order is the least such exponent. The context holds two theorems of the section on powers:
```lean
theorem pow_sub_eq_one_of_pow_eq {i j : ℕ}
    (hij : i < j) (h : g ^ i = g ^ j) :
    g ^ (j - i) = 1
theorem orderOf_le_of_pow_eq_one {n : ℕ}
    (hn : 0 < n) (h : g ^ n = 1) : orderOf g ≤ n
```
@description
Show that two natural numbers below the order of `g` whose powers of `g` are equal are themselves equal.
-/
@[to_additive nsmul_inj_of_lt_addOrderOf]
theorem pow_inj_of_lt_orderOf {G : Type u} [Group G] {g : G} {i j : ℕ} (hi : i < orderOf g)
    (hj : j < orderOf g) (h : g ^ i = g ^ j) : i = j := by
  by_cases hlt : i < j
  · have h1 := orderOf_le_of_pow_eq_one (by omega) (pow_sub_eq_one_of_pow_eq hlt h)
    omega
  · by_cases hgt : j < i
    · have h1 := orderOf_le_of_pow_eq_one (by omega) (pow_sub_eq_one_of_pow_eq hgt h.symm)
      omega
    · omega

/--
@problem exists_pow_of_mem_zpowers
@title Every Power Is a Power Below the Order
@concept cyclic_subgroups

@preamble
In a finite group every power of `g`, with any integer as exponent, is a natural power below the order: the exponent may be replaced by its remainder on division by the order. That remainder is an integer, though, and the exponent wanted is a natural number. Core Lean has
```lean
theorem Int.emod_nonneg (a : ℤ) {b : ℤ} :
    b ≠ 0 → 0 ≤ a % b
theorem Int.emod_lt_of_pos (a : ℤ) {b : ℤ} :
    0 < b → a % b < b
theorem Int.eq_ofNat_of_zero_le {a : ℤ} :
    0 ≤ a → ∃ n : ℕ, a = ↑n
```
`omega` passes between an inequality of natural numbers and the same inequality of their values as integers. The context holds `zpow_mod_orderOf` of this section, `zpow_natCast` and `orderOf_pos` of the section on powers, and `Subgroup.mem_zpowers_iff` of the section on subgroups.
@description
Show that in a finite group every element of `zpowers g` is `g ^ i` for some natural number `i` below the order of `g`.
-/
@[to_additive exists_nsmul_lt_addOrderOf_of_mem_zmultiples]
theorem exists_pow_lt_orderOf_of_mem_zpowers {G : Type u} [Group G] [Finite G] {g x : G}
    (hx : x ∈ Subgroup.zpowers g) : ∃ i, i < orderOf g ∧ g ^ i = x := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hpos := orderOf_pos g
  have h0 : 0 ≤ k % (orderOf g : ℤ) := Int.emod_nonneg k (by omega)
  have hlt : k % (orderOf g : ℤ) < orderOf g := Int.emod_lt_of_pos k (by omega)
  obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le h0
  apply Exists.intro i
  constructor
  · omega
  · rw [← zpow_natCast, ← hi, zpow_mod_orderOf, hk]

/-!
@problem card_zpowers
@title The Order of an Element Counts Its Powers
@concept cyclic_subgroups

@preamble
The order of `g` counts its powers: in a finite group, `zpowers g` has exactly `orderOf g` elements. This is why the order of an element and the order of a group share a word. The rotations of Dₙ were counted in the previous section through Mathlib's
```lean
theorem Fintype.card_of_bijective {f : α → β}
    (hf : Function.Bijective f) :
    Fintype.card α = Fintype.card β
```

A power `g ^ i` with `i : ℕ` lies in `zpowers g` with the exponent `(i : ℤ)`, since `g ^ (i : ℤ) = g ^ i` holds by definition. The context holds the two previous theorems of this section, `Fintype.card_fin`, `Fin.ext` and `Subtype.ext`.
@description
Show that in a finite group the subgroup `zpowers g` has as many elements as the order of `g`, under the name `Fintype.card_zpowers`.
-/

open Classical in
@[to_additive Fintype.card_zmultiples]
theorem Fintype.card_zpowers {G : Type u} [Group G] [Fintype G] (g : G) :
    Fintype.card (Subgroup.zpowers g).carrier = orderOf g := by
  have hf : Function.Bijective
      (fun i : Fin (orderOf g) => (⟨g ^ i.val, i.val, rfl⟩ : (Subgroup.zpowers g).carrier)) := by
    constructor
    · intro i j h
      have h' : g ^ i.val = g ^ j.val := congrArg Subtype.val h
      exact Fin.ext (pow_inj_of_lt_orderOf i.isLt j.isLt h')
    · intro ⟨x, hx⟩
      obtain ⟨i, hi, e⟩ := exists_pow_lt_orderOf_of_mem_zpowers hx
      exact ⟨⟨i, hi⟩, Subtype.ext e⟩
  rw [← Fintype.card_of_bijective hf, Fintype.card_fin]

/-! @end -/

/-!
@problem order_of_dvd_card
@title The Order of an Element Divides the Order of the Group
@concept cyclic_subgroups

@preamble
Lagrange's theorem applied to `zpowers g` says that the number of powers of `g` divides the order of the group, and that number is the order of `g`. So in a finite group the order of every element divides the order of the group, and every element raised to the order of the group is `1`.

The context holds `Fintype.card_zpowers` of this section, `Subgroup.card_subgroup_dvd_card` of the previous section, and `orderOf_dvd_iff_pow_eq_one` of the section on powers.
@description
Show that the order of every element of a finite group divides the number of elements of the group, under the name `orderOf_dvd_card`, and that every element raised to that number is `1`, under the name `pow_card_eq_one`.
-/

open Classical in
@[to_additive addOrderOf_dvd_card]
theorem orderOf_dvd_card {G : Type u} [Group G] [Fintype G] (g : G) :
    orderOf g ∣ Fintype.card G := by
  rw [← Fintype.card_zpowers]
  exact (Subgroup.zpowers g).card_subgroup_dvd_card

@[to_additive card_nsmul_eq_zero]
theorem pow_card_eq_one {G : Type u} [Group G] [Fintype G] (g : G) :
    g ^ Fintype.card G = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_card g)

/-! @end -/

/-!
@problem zmod_add_order_of_one
@title The Order of One in the Integers Modulo n
@concept cyclic_subgroups

@preamble
In `ZMod n` the residue `1` has order `n`. Its multiples are all the residues, as the section on subgroups showed in proving `ZMod n` cyclic with `1` as generator, and the order counts them. The context holds the facts of that proof: `AddSubgroup.mem_zmultiples_iff` and `ZMod.val_nsmul_one` of the section on subgroups, `natCast_zsmul` of the section on powers, and `Fin.ext` and `Nat.mod_eq_of_lt`. `ZMod.val_nsmul_one` says that the value of `k • (1 : ZMod n)` is `k % n` for a natural number `k`. The context also holds `Fintype.card_zmultiples`, the additive version of this section's count, `card_zmod` of the section on examples, and `Fintype.card_of_bijective`, shown two problems before, and `Subtype.val_injective` of the section on subgroups.

Rewriting the `n` of the goal as the number of elements of `ZMod n` fails with `motive is not type correct`, since `n` appears in the type `ZMod n` as well; rewrite the count instead.
@description
Show that the residue `1` has order `n` in `ZMod n`, under the name `ZMod.addOrderOf_one`.
-/

open Classical in
theorem ZMod.addOrderOf_one (n : ℕ) [NeZero n] : addOrderOf (1 : ZMod n) = n := by
  rw [← Fintype.card_zmultiples]
  have hb : Function.Bijective
      (fun a : (AddSubgroup.zmultiples (1 : ZMod n)).carrier => (a : ZMod n)) := by
    constructor
    · exact Subtype.val_injective
    · intro x
      have hx : x ∈ AddSubgroup.zmultiples (1 : ZMod n) := by
        rw [AddSubgroup.mem_zmultiples_iff]
        apply Exists.intro (x.val : ℤ)
        rw [natCast_zsmul]
        apply Fin.ext
        rw [ZMod.val_nsmul_one, Nat.mod_eq_of_lt x.isLt]
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [Fintype.card_of_bijective hb, card_zmod]

/-! @end -/

/-!
@concept primes
@title Prime Numbers
@kind definition

A prime is a natural number at least 2 whose only divisors are 1 and itself. A prime that does not divide a number is coprime to it, and a divisor of a power of a prime other than 1 is divisible by the prime. Primes enter group theory through Lagrange's theorem, which ties the orders of subgroups to the divisors of the group's order.
-/

/-!
@problem nat_prime
@title Prime Numbers
@concept primes

@preamble
A natural number `p` is *prime* when `2 ≤ p` and its only divisors are `1` and `p`. We write `Nat.Prime p`, a proposition with a name, as `IsCyclic G` was. Mathlib's `Nat.Prime` has a different definition, which says the same of natural numbers; the one here is the textbook's.

A statement about every divisor of a numeral is not something `decide` can check as it stands, since the divisors range over all natural numbers. A divisor of a positive number is at most that number, core Lean's `Nat.le_of_dvd`, and `decide` checks the bounded statement, as it did for the subgroups of `ZMod 6`.
@description
Define `Nat.Prime p`. Show that a prime is at least `2`, under the name `Nat.Prime.two_le`, and that a divisor of a prime is `1` or the prime itself, under the name `Nat.Prime.eq_one_or_self_of_dvd`. Then show that `5` is prime, under the name `Nat.prime_five`.
-/

def Nat.Prime (p : ℕ) : Prop := 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p

/-- @spec -/
example (p : ℕ) : Nat.Prime p ↔ 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p := by
  unfold Nat.Prime
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨by omega, fun m hm => by have := h2 m hm; omega⟩
  · intro ⟨h1, h2⟩
    exact ⟨by omega, fun m hm => by have := h2 m hm; omega⟩

theorem Nat.Prime.two_le {p : ℕ} (hp : Nat.Prime p) : 2 ≤ p := hp.1

theorem Nat.Prime.eq_one_or_self_of_dvd {p : ℕ} (hp : Nat.Prime p) (a : ℕ) (h : a ∣ p) :
    a = 1 ∨ a = p := hp.2 a h

theorem Nat.prime_five : Nat.Prime 5 := by
  constructor
  · decide
  · intro m hm
    have hle : m ≤ 5 := Nat.le_of_dvd (by decide) hm
    have key : ∀ d ≤ 5, d ∣ 5 → d = 1 ∨ d = 5 := by
      decide
    exact key m hle hm

/-! @end -/

/--
@problem prime_coprime
@title A Prime Is Coprime to What It Does Not Divide
@concept primes

@preamble
A prime `p` is coprime to every number it does not divide, and to no number it divides. `Nat.Coprime p n` is `Nat.gcd p n = 1` by definition, as the first section said. Core Lean has
```lean
theorem Nat.gcd_dvd_left (m n : ℕ) :
    Nat.gcd m n ∣ m
theorem Nat.gcd_dvd_right (m n : ℕ) :
    Nat.gcd m n ∣ n
theorem Nat.Coprime.eq_one_of_dvd {k m : ℕ} :
    Nat.Coprime k m → k ∣ m → k = 1
```
The context holds `Nat.Prime.two_le` and `Nat.Prime.eq_one_or_self_of_dvd` of the previous problem.
@description
Show that a prime `p` is coprime to `n` exactly when it does not divide `n`, under the name `Nat.Prime.coprime_iff_not_dvd`.
-/
theorem Nat.Prime.coprime_iff_not_dvd {p n : ℕ} (hp : Nat.Prime p) :
    Nat.Coprime p n ↔ ¬ p ∣ n := by
  constructor
  · intro hc hd
    have h1 := Nat.Coprime.eq_one_of_dvd hc hd
    have h2 := hp.two_le
    omega
  · intro hn
    cases hp.eq_one_or_self_of_dvd (Nat.gcd p n) (Nat.gcd_dvd_left p n) with
    | inl h => exact h
    | inr h =>
      have hd := Nat.gcd_dvd_right p n
      rw [h] at hd
      exact absurd hd hn

/--
@problem prime_dvd_of_dvd_pow
@title A Divisor of a Prime Power Is One or a Multiple of the Prime
@concept primes

@preamble
A divisor of a power of a prime shares the prime as a factor, unless it is `1`. Core Lean has
```lean
theorem Nat.Coprime.pow_left {m k : ℕ} (n : ℕ) :
    Nat.Coprime m k → Nat.Coprime (m ^ n) k
theorem Nat.Coprime.symm {n m : ℕ} :
    Nat.Coprime n m → Nat.Coprime m n
```
The context holds `Nat.Prime.coprime_iff_not_dvd` of this section and core Lean's `Nat.Coprime.eq_one_of_dvd`, shown in the previous problem.
@description
Show that a divisor `m` of `p ^ n`, for a prime `p`, is divisible by `p` unless `m = 1`, under the name `Nat.Prime.dvd_of_dvd_pow_of_ne_one`.
-/
theorem Nat.Prime.dvd_of_dvd_pow_of_ne_one {p m n : ℕ} (hp : Nat.Prime p) (hm : m ∣ p ^ n)
    (h1 : m ≠ 1) : p ∣ m := by
  by_cases hd : p ∣ m
  · exact hd
  · have hc : Nat.Coprime m (p ^ n) :=
      (Nat.Coprime.pow_left n (hp.coprime_iff_not_dvd.mpr hd)).symm
    exact absurd (Nat.Coprime.eq_one_of_dvd hc hm) h1

/-!
@concept prime_order
@title Groups of Prime Order
@kind theorem

A group whose order is a prime is cyclic, generated by any of its elements other than the neutral element. Its only subgroups are the trivial subgroup and the whole group. Both follow from Lagrange's theorem, since a divisor of a prime is 1 or the prime itself.
-/

/-!
@problem eq_top_of_card_eq
@title A Subgroup as Large as the Group Is the Group
@concept prime_order

@preamble
The theorems on groups of prime order recognize a subgroup by its number of elements alone. A subgroup with as many elements as the group is the whole group. The inclusion of `H.carrier` into `G`, `a ↦ (a : G)`, is injective, `Subtype.val_injective`, and Mathlib has
```lean
theorem Fintype.bijective_iff_injective_and_card
    (f : α → β) : Function.Bijective f ↔
      Function.Injective f ∧
        Fintype.card α = Fintype.card β
```
The context holds `Subgroup.ext`, `Subgroup.mem_top` and `Subgroup.coe_mem` of the section on subgroups.
@description
Show that a subgroup of a finite group with as many elements as the group is `⊤`, under the name `Subgroup.eq_top_of_card_eq`.
-/

open Classical in
@[to_additive AddSubgroup.eq_top_of_card_eq]
theorem Subgroup.eq_top_of_card_eq {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    (h : Fintype.card H.carrier = Fintype.card G) : H = ⊤ := by
  have hb : Function.Bijective (fun a : H.carrier => (a : G)) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨Subtype.val_injective, h⟩
  apply Subgroup.ext
  intro x
  constructor
  · intro _
    exact Subgroup.mem_top x
  · intro _
    obtain ⟨a, ha⟩ := hb.2 x
    rw [← ha]
    exact Subgroup.coe_mem a

/-! @end -/

/-!
@problem eq_bot_of_card_eq
@title A Subgroup With One Element Is Trivial
@concept prime_order

@preamble
A subgroup with one element is the trivial subgroup, since `1` is always one of its elements. Mathlib has
```lean
theorem Fintype.card_eq_one_iff :
    Fintype.card α = 1 ↔ ∃ x, ∀ y : α, y = x
```
An element of `H.carrier` is a pair `⟨x, hx⟩` of an element of `G` and a proof that it lies in `H`, as in the section on subgroups. The context holds `Subgroup.ext`, `Subgroup.mem_bot` and `Subgroup.one_mem`.
@description
Show that a subgroup of a finite group with exactly one element is `⊥`, under the name `Subgroup.eq_bot_of_card_eq`.
-/

open Classical in
@[to_additive AddSubgroup.eq_bot_of_card_eq]
theorem Subgroup.eq_bot_of_card_eq {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    (h : Fintype.card H.carrier = 1) : H = ⊥ := by
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp h
  apply Subgroup.ext
  intro x
  rw [Subgroup.mem_bot]
  constructor
  · intro hx
    have e : (⟨x, hx⟩ : H.carrier) = ⟨1, H.one_mem⟩ := by
      rw [ha ⟨x, hx⟩, ha ⟨1, H.one_mem⟩]
    exact congrArg Subtype.val e
  · intro hx
    rw [hx]
    exact H.one_mem

/-! @end -/

/-!
@problem prime_card_cyclic
@title An Element Other Than One Generates a Group of Prime Order
@concept prime_order

@preamble
In a group of prime order, the powers of an element other than `1` are the whole group. The context holds `Fintype.card_zpowers` and `orderOf_dvd_card` of this section's first concept, `Nat.Prime.eq_one_or_self_of_dvd` of the previous concept, `Subgroup.eq_top_of_card_eq` of this concept, and `orderOf_eq_one_iff` of the section on powers.
@description
Show that in a group of prime order every element other than `1` generates the whole group, under the name `Subgroup.zpowers_eq_top_of_prime_card`.
-/

open Classical in
@[to_additive AddSubgroup.zmultiples_eq_top_of_prime_card]
theorem Subgroup.zpowers_eq_top_of_prime_card {G : Type u} [Group G] [Fintype G] {p : ℕ}
    (hp : Nat.Prime p) (hG : Fintype.card G = p) {g : G} (hg : g ≠ 1) :
    Subgroup.zpowers g = ⊤ := by
  apply Subgroup.eq_top_of_card_eq
  rw [Fintype.card_zpowers, hG]
  have hd := orderOf_dvd_card g
  rw [hG] at hd
  cases hp.eq_one_or_self_of_dvd (orderOf g) hd with
  | inl h => exact absurd (orderOf_eq_one_iff.mp h) hg
  | inr h => exact h

/-! @end -/

/-!
@problem is_cyclic_of_prime_card
@title A Group of Prime Order Is Cyclic
@concept prime_order

@preamble
A group of prime order is cyclic, since it has an element other than `1`: it has at least two elements. `IsCyclic G`, from the section on subgroups, asks for an element `g` with every `x` in `zpowers g`. Mathlib has
```lean
theorem Fintype.exists_ne_of_one_lt_card
    (h : 1 < Fintype.card α) (a : α) : ∃ b, b ≠ a
```
The integers modulo `5` are the running example. The context holds `Subgroup.zpowers_eq_top_of_prime_card` of the previous problem with its additive version `AddSubgroup.zmultiples_eq_top_of_prime_card`, `Nat.Prime.two_le` and `Nat.prime_five` of the previous concept, `Subgroup.mem_top`, and `card_zmod` of the section on examples.
@description
Show that a group of prime order is cyclic, under the name `isCyclic_of_prime_card`, and that every nonzero residue of `ZMod 5` generates `ZMod 5`.
-/

@[to_additive isAddCyclic_of_prime_card]
theorem isCyclic_of_prime_card {G : Type u} [Group G] [Fintype G] {p : ℕ} (hp : Nat.Prime p)
    (hG : Fintype.card G = p) : IsCyclic G := by
  have h1 : 1 < Fintype.card G := by
    have h2 := hp.two_le
    omega
  obtain ⟨g, hg⟩ := Fintype.exists_ne_of_one_lt_card h1 (1 : G)
  apply Exists.intro g
  intro x
  rw [Subgroup.zpowers_eq_top_of_prime_card hp hG hg]
  exact Subgroup.mem_top x

theorem zmultiples_eq_top_zmod_five {a : ZMod 5} (ha : a ≠ 0) :
    AddSubgroup.zmultiples a = ⊤ :=
  AddSubgroup.zmultiples_eq_top_of_prime_card Nat.prime_five (card_zmod 5) ha

/-! @end -/

/-!
@problem prime_card_subgroups
@title The Subgroups of a Group of Prime Order
@concept prime_order

@preamble
A group of prime order has only the two subgroups every group has. The context holds `Subgroup.card_subgroup_dvd_card` of the previous section, `Nat.Prime.eq_one_or_self_of_dvd` of the previous concept, and `Subgroup.eq_bot_of_card_eq` and `Subgroup.eq_top_of_card_eq` of this one.
@description
Show that every subgroup of a group of prime order is `⊥` or `⊤`, under the name `Subgroup.eq_bot_or_eq_top_of_prime_card`.
-/

open Classical in
@[to_additive AddSubgroup.eq_bot_or_eq_top_of_prime_card]
theorem Subgroup.eq_bot_or_eq_top_of_prime_card {G : Type u} [Group G] [Fintype G] {p : ℕ}
    (H : Subgroup G) (hp : Nat.Prime p) (hG : Fintype.card G = p) : H = ⊥ ∨ H = ⊤ := by
  have hd := H.card_subgroup_dvd_card
  rw [hG] at hd
  cases hp.eq_one_or_self_of_dvd _ hd with
  | inl h => exact Or.inl (H.eq_bot_of_card_eq h)
  | inr h =>
    apply Or.inr
    apply H.eq_top_of_card_eq
    rw [h, hG]

/-! @end -/

end GroupTheory
