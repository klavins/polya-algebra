-- The second probe of 2026-10-23: the student defines `Group` first and `AddGroup` after it, and
-- `attribute [to_additive existing] …` pairs them afterwards; `@[to_additive]` then copies a theorem
-- (`add_left_cancel` from `mul_left_cancel`). Run with `lake env lean scripts/addgroup_order_probe.lean`.
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Init
universe u
namespace GroupTheory
-- Group first, as the student meets it; AddGroup after, then the two are linked
class Group (G : Type u) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : G, mul one a = a
  mul_one : ∀ a : G, mul a one = a
  inv_mul_cancel : ∀ a : G, mul (inv a) a = one
  mul_inv_cancel : ∀ a : G, mul a (inv a) = one
instance instMulG {G : Type u} [Group G] : Mul G := ⟨Group.mul⟩
instance instOneG {G : Type u} [Group G] : One G := ⟨Group.one⟩
instance instInvG {G : Type u} [Group G] : Inv G := ⟨Group.inv⟩
class AddGroup (A : Type u) where
  add : A → A → A
  zero : A
  neg : A → A
  add_assoc : ∀ a b c : A, add (add a b) c = add a (add b c)
  zero_add : ∀ a : A, add zero a = a
  add_zero : ∀ a : A, add a zero = a
  neg_add_cancel : ∀ a : A, add (neg a) a = zero
  add_neg_cancel : ∀ a : A, add a (neg a) = zero
instance instAddG {A : Type u} [AddGroup A] : Add A := ⟨AddGroup.add⟩
instance instZeroG {A : Type u} [AddGroup A] : Zero A := ⟨AddGroup.zero⟩
instance instNegG {A : Type u} [AddGroup A] : Neg A := ⟨AddGroup.neg⟩
attribute [to_additive existing] Group instMulG instOneG instInvG
theorem one_mul {G : Type u} [Group G] (a : G) : 1 * a = a := Group.one_mul a
-- a theorem proved before the link, linked afterwards
theorem zero_add {A : Type u} [AddGroup A] (a : A) : 0 + a = a := AddGroup.zero_add a
attribute [to_additive existing] one_mul
@[to_additive]
theorem inv_mul_cancel {G : Type u} [Group G] (a : G) : a⁻¹ * a = 1 := Group.inv_mul_cancel a
@[to_additive]
theorem mul_assoc {G : Type u} [Group G] (a b c : G) : a * b * c = a * (b * c) := Group.mul_assoc a b c
@[to_additive]
theorem mul_left_cancel {G : Type u} [Group G] {a b c : G} (h : a * b = a * c) : b = c := by
  rw [← one_mul b, ← inv_mul_cancel a, mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
#check @add_left_cancel
