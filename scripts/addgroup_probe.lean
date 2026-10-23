-- The probe behind the plan's Decision 4 of 2026-10-23 (the student's `AddGroup`): a student
-- `AddGroup ℤ` from the integers' own operations lets the additive laws reach `3 + x` as written,
-- and `@[to_additive]` copies the student's theorems once each class, structure and recursive
-- definition has a hand-written twin (`to_additive existing`). Run with
-- `lake env lean scripts/addgroup_probe.lean`; it compiles without errors.
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Init
import Mathlib.Data.Set.Basic

universe u
namespace GroupTheory

class AddGroup (A : Type u) where
  add : A → A → A
  zero : A
  neg : A → A
  add_assoc : ∀ a b c : A, add (add a b) c = add a (add b c)
  zero_add : ∀ a : A, add zero a = a
  add_zero : ∀ a : A, add a zero = a
  neg_add_cancel : ∀ a : A, add (neg a) a = zero
  add_neg_cancel : ∀ a : A, add a (neg a) = zero

@[to_additive]
class Group (G : Type u) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : G, mul one a = a
  mul_one : ∀ a : G, mul a one = a
  inv_mul_cancel : ∀ a : G, mul (inv a) a = one
  mul_inv_cancel : ∀ a : G, mul a (inv a) = one

@[to_additive]
instance instMulG {G : Type u} [Group G] : Mul G := ⟨Group.mul⟩
@[to_additive]
instance instOneG {G : Type u} [Group G] : One G := ⟨Group.one⟩
@[to_additive]
instance instInvG {G : Type u} [Group G] : Inv G := ⟨Group.inv⟩

@[to_additive]
theorem one_mul {G : Type u} [Group G] (a : G) : 1 * a = a := Group.one_mul a
@[to_additive]
theorem inv_mul_cancel {G : Type u} [Group G] (a : G) : a⁻¹ * a = 1 := Group.inv_mul_cancel a
@[to_additive]
theorem mul_assoc {G : Type u} [Group G] (a b c : G) : a * b * c = a * (b * c) := Group.mul_assoc a b c
@[to_additive]
theorem mul_left_cancel {G : Type u} [Group G] {a b c : G} (h : a * b = a * c) : b = c := by
  rw [← one_mul b, ← inv_mul_cancel a, mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]

#check @zero_add
#check @add_left_cancel

instance : AddGroup ℤ where
  add a b := a + b
  zero := 0
  neg a := -a
  add_assoc := Int.add_assoc
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  neg_add_cancel := Int.add_left_neg
  add_neg_cancel := Int.add_right_neg

example (x : ℤ) (h : 3 + x = 3 + 4) : x = 4 := add_left_cancel h
example : (0 : ℤ) + 3 = 3 := by rw [zero_add]

structure AddSubgroup (A : Type u) [AddGroup A] where
  carrier : Set A
  zero_mem' : (0 : A) ∈ carrier
  add_mem' {a b : A} : a ∈ carrier → b ∈ carrier → a + b ∈ carrier
  neg_mem' {a : A} : a ∈ carrier → -a ∈ carrier

@[to_additive]
structure Subgroup (G : Type u) [Group G] where
  carrier : Set G
  one_mem' : (1 : G) ∈ carrier
  mul_mem' {a b : G} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  inv_mem' {a : G} : a ∈ carrier → a⁻¹ ∈ carrier

@[to_additive]
instance {G : Type u} [Group G] : Membership G (Subgroup G) := ⟨fun H g => g ∈ H.carrier⟩

@[to_additive]
theorem Subgroup.mul_mem {G : Type u} [Group G] (H : Subgroup G) {a b : G} (ha : a ∈ H) (hb : b ∈ H) :
    a * b ∈ H := H.mul_mem' ha hb

#check @AddSubgroup.add_mem

def evens : AddSubgroup ℤ where
  carrier := {x | 2 ∣ x}
  zero_mem' := ⟨0, rfl⟩
  add_mem' := fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a + b, by omega⟩
  neg_mem' := fun ⟨a, ha⟩ => ⟨-a, by omega⟩

example : (4 : ℤ) + 6 ∈ evens := evens.add_mem ⟨2, rfl⟩ ⟨3, rfl⟩

-- powers
def nsmulRec {A : Type u} [AddGroup A] : ℕ → A → A
  | 0, _ => 0
  | n + 1, a => nsmulRec n a + a

@[to_additive existing]
def npowRec {G : Type u} [Group G] : ℕ → G → G
  | 0, _ => 1
  | n + 1, g => npowRec n g * g

@[to_additive]
instance instPowG {G : Type u} [Group G] : Pow G ℕ := ⟨fun g n => npowRec n g⟩

@[to_additive succ_nsmul]
theorem pow_succ {G : Type u} [Group G] (g : G) (n : ℕ) : g ^ (n + 1) = g ^ n * g := rfl

#check @succ_nsmul
example : (3 : ℕ) • (2 : ℤ) = 6 := by decide
example (k : ℕ) : k • (1 : ℤ) = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [succ_nsmul, ih]; omega
