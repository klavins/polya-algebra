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
The probe behind the plan's Decision 4, reopened 2026-10-22: could the student's `Group` write
its operation `*` and its neutral element `1` through instances of Mathlib's notation classes
`Mul` and `One`, as it writes `a⁻¹` through an `Inv G` instance, without the class extending
them? Compile it from the repository root with

    lake env lean scripts/notation_probe.lean

It imports the fence and nothing of this repository. The expected outcome is in the comment on
each line: `ok` compiles, `ERROR` is an error Lean must report, and a `#eval`/`#synth` line says
what it must print. What it shows: the obstacle is `ℤ`, not the shape of the class. `ℤ` already
carries `Mul ℤ` and `One ℤ` with their usual meanings and no `Inv ℤ`; with a second `Mul ℤ`
through the group, Lean keeps the integers' own `*` (a concrete instance beats a generic one),
so the group's laws, stated in `*`, never reach the integers' `*`, and `(One.one : ℤ)` is `0`
while `(1 : ℤ)` is `1`. A second `⁻¹` notation beside Mathlib's `Inv` is ambiguous, which is
why `⁻¹` goes through `Inv` while `∗` and `𝟙`, whose symbols are free, are notation commands on
the class's own fields.
-/

universe u

-- A. What ℤ carries under the fence.
#synth Mul ℤ          -- prints Int.instMul
#synth One ℤ          -- prints One.ofOfNat1
#synth Inv ℤ          -- ERROR: failed to synthesize

class Group (G : Type u) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : G, mul one a = a
  mul_one : ∀ a : G, mul a one = a
  inv_mul_cancel : ∀ a : G, mul (inv a) a = one
  mul_inv_cancel : ∀ a : G, mul a (inv a) = one

-- B. The proposal: the three symbols through notation instances derived from the class.
instance {G : Type u} [Group G] : Mul G := ⟨Group.mul⟩
instance {G : Type u} [Group G] : One G := ⟨Group.one⟩
instance {G : Type u} [Group G] : Inv G := ⟨Group.inv⟩

theorem one_mul {G : Type u} [Group G] (a : G) : 1 * a = a := Group.one_mul a

instance : Group ℤ where
  mul := (· + ·)
  one := 0
  inv := (- ·)
  mul_assoc := by intros; omega
  one_mul := by intros; omega
  mul_one := by intros; omega
  inv_mul_cancel := by intros; omega
  mul_inv_cancel := by intros; omega

-- C. What the symbols now mean on ℤ.
#eval (3 : ℤ) * 4                                  -- prints 12: the integers' own `*` wins
example : (3 : ℤ) * 4 = 12 := rfl                  -- ok
example : (3 : ℤ) * 4 = 7 := rfl                   -- ERROR: the group's operation is not `*` on ℤ
example (m : ℤ) : 2 * m = m + m := by omega        -- ok: `*` on ℤ is still what omega knows
#eval (1 : ℤ)                                      -- prints 1
example : (1 : ℤ) = 0 := rfl                       -- ERROR
example : (One.one : ℤ) = 0 := rfl                 -- ok: the group's `One ℤ` beats One.ofOfNat1
#check one_mul (3 : ℤ)                             -- prints `1 * 3 = 3`, and means 0 + 3 = 3
example : (1 : ℤ) * 3 = 3 := one_mul 3             -- ERROR: the law does not reach ℤ's `*`
example : (1 : ℤ) * 3 = 3 := by rw [one_mul]       -- ERROR: did not find `1 * ?a` in `1 * 3 = 3`
example : (3 : ℤ)⁻¹ = -3 := rfl                    -- ok: `Inv` has no collision

-- D. Why `⁻¹` is not a notation command of its own: the symbol already belongs to `Inv`.
postfix:max "⁻¹" => Group.inv
example {G : Type u} [Group G] (a : G) : a⁻¹ = Group.inv a := rfl   -- ERROR: Ambiguous term a⁻¹
