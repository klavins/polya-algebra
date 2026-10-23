import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Algebra.Quotient
import Mathlib.Order.Notation
import Mathlib.Data.Nat.Find
import Mathlib.Data.Int.Init

/-!
The second probe behind the plan's Decision 4 (2026-10-22): what the subject looks like if the
student's `Group` writes `*` and `1` through `Mul` and `One` instances and the additive examples
are wrapped, Mathlib's way. Compile it from the repository root with

    lake env lean scripts/wrapper_probe.lean

It imports the fence and nothing of this repository; the group laws of the two toy instances
are `sorry`, since only elaboration is probed. The expected outcome is in the comment on each
line: `ok` compiles, `ERROR` is an error Lean must report, and a `#synth`/`#check` line says what
it must print. What it shows: (A) under the fence `Unit`, `Bool`, `Equiv.Perm`, a subtype and
the student's own structures carry no `Mul` or `One`, while `Fin n` carries both; (B) the
student's `Multiplicative ℤ` works, `ofAdd 3 * ofAdd 4 = ofAdd 7` by `rfl` and by `decide`, has
no numerals, and `omega` is blind through it until a `show` or a rewrite; (C) `ZMod n` directly
under `*`, with its numerals, has two different ones, `one_mul 1 : 1 * 1 = 1`; (D) on `G × H`
the fence's `Prod.instMul` wins the elaboration of `*` and the group's laws still apply to it.
-/

universe u

-- A. which example types already carry Mul or One under the fence 
#synth Mul Unit  -- ERROR: failed to synthesize
#synth One Unit  -- ERROR: failed to synthesize
#synth Mul Bool  -- ERROR: failed to synthesize
#synth One Bool  -- ERROR: failed to synthesize
#synth Mul (Equiv.Perm (Fin 3))  -- ERROR: failed to synthesize
#synth One (Equiv.Perm (Fin 3))  -- ERROR: failed to synthesize
#synth Mul {x : ℤ // 0 < x}  -- ERROR: failed to synthesize
#synth One {x : ℤ // 0 < x}  -- ERROR: failed to synthesize
#synth Mul (Fin 3)  -- prints Fin.instMul
#synth One (Fin 3)  -- prints One.ofOfNat1
#synth Mul (ℤ × ℤ)  -- prints Prod.instMul
#check @Multiplicative  -- ERROR: unknown identifier, so the student may define it

class Group (G : Type u) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : G, mul one a = a
  mul_one : ∀ a : G, mul a one = a
  inv_mul_cancel : ∀ a : G, mul (inv a) a = one
  mul_inv_cancel : ∀ a : G, mul a (inv a) = one

instance {G : Type u} [Group G] : Mul G := ⟨Group.mul⟩
instance {G : Type u} [Group G] : One G := ⟨Group.one⟩
instance {G : Type u} [Group G] : Inv G := ⟨Group.inv⟩

theorem mul_assoc {G : Type u} [Group G] (a b c : G) : a * b * c = a * (b * c) := Group.mul_assoc a b c
theorem one_mul {G : Type u} [Group G] (a : G) : 1 * a = a := Group.one_mul a

-- B. the wrapper, Mathlib's Multiplicative written by the student
def Multiplicative (α : Type u) := α
def ofAdd {α : Type u} (a : α) : Multiplicative α := a
def toAdd {α : Type u} (a : Multiplicative α) : α := a
instance {α : Type u} [DecidableEq α] : DecidableEq (Multiplicative α) := inferInstanceAs (DecidableEq α)

instance : Group (Multiplicative ℤ) where
  mul a b := ofAdd (toAdd a + toAdd b)
  one := ofAdd 0
  inv a := ofAdd (-toAdd a)
  mul_assoc a b c := Int.add_assoc (toAdd a) (toAdd b) (toAdd c)
  one_mul a := Int.zero_add (toAdd a)
  mul_one a := Int.add_zero (toAdd a)
  inv_mul_cancel a := Int.add_left_neg (toAdd a)
  mul_inv_cancel a := Int.add_right_neg (toAdd a)

example : ofAdd (3 : ℤ) * ofAdd 4 = ofAdd 7 := rfl  -- ok
example : ofAdd (3 : ℤ) * ofAdd 4 = ofAdd 7 := by decide  -- ok
example : (ofAdd (3 : ℤ))⁻¹ = ofAdd (-3) := rfl  -- ok
example : (1 : Multiplicative ℤ) = ofAdd 0 := rfl  -- ok
example : (3 : Multiplicative ℤ) = ofAdd 3 := rfl  -- ERROR: no numerals on the wrapper
theorem ofAdd_mul (a b : ℤ) : ofAdd a * ofAdd b = ofAdd (a + b) := rfl
example (x : Multiplicative ℤ) : ofAdd 3 * x = ofAdd 7 ↔ x = ofAdd 4 := by
  constructor
  · intro h
    have h' : (3 : ℤ) + toAdd x = 7 := h                            -- the defeq step a student must write
    show toAdd x = 4
    omega
  · intro h
    rw [h]
    rfl  -- rw leaves ofAdd 3 * ofAdd 4 = ofAdd 7, and rfl closes it
example (x : Multiplicative ℤ) (h : ofAdd 3 * x = ofAdd 7) : x = ofAdd 4 := by omega  -- ERROR: omega does not see through the wrapper
example (a b : ℤ) : ofAdd a * ofAdd b = ofAdd b * ofAdd a := by
  rw [ofAdd_mul, ofAdd_mul, Int.add_comm]  -- ok

-- C. ZMod n directly as a `*`-group, with the student's numerals: the two ones
structure ZMod (n : ℕ) where
  val : ℕ
  val_lt : val < n
deriving DecidableEq
instance (n : ℕ) [NeZero n] (k : ℕ) : OfNat (ZMod n) k := ⟨⟨k % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩⟩
instance (n : ℕ) [NeZero n] : Group (ZMod n) where
  mul a b := ⟨(a.val + b.val) % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩
  one := ⟨0, Nat.pos_of_neZero n⟩
  inv a := ⟨(n - a.val) % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  inv_mul_cancel := sorry
  mul_inv_cancel := sorry
example : (3 : ZMod 5) * 4 = 2 := by decide  -- ok: `*` on ZMod 5 is addition
example : (1 : ZMod 5) * 1 = 2 := by decide  -- ok: the numeral 1 is the residue 1
example : (One.one : ZMod 5) ≠ (1 : ZMod 5) := by decide  -- ok: the group's 1 is the residue 0
#check one_mul (1 : ZMod 5)  -- prints `1 * 1 = 1`, two different ones

-- D. the product diamond: Prod.instMul from the fence against the group's Mul (G × H)
instance {G H : Type u} [Group G] [Group H] : Group (G × H) where
  mul a b := (a.1 * b.1, a.2 * b.2)
  one := (1, 1)
  inv a := (a.1⁻¹, a.2⁻¹)
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  inv_mul_cancel := sorry
  mul_inv_cancel := sorry
set_option pp.explicit false in
#synth Mul (Multiplicative ℤ × Multiplicative ℤ)  -- prints Prod.instMul: the fence's instance wins
example {G H : Type u} [Group G] [Group H] (a b c : G × H) : a * b * c = a * (b * c) := by
  rw [mul_assoc]  -- ok: the group's law rewrites the fence's `*`
example {G H : Type u} [Group G] [Group H] (a b c : G × H) : a * b * c = a * (b * c) :=
  mul_assoc a b c  -- ok
example {G H : Type u} [Group G] [Group H] (a b : G × H) : a * b = (a.1 * b.1, a.2 * b.2) := rfl  -- ok
