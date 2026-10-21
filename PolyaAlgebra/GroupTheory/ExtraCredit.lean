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
import PolyaAlgebra.GroupTheory.Groups

/-! @section Extra Credit -/

universe u

namespace GroupTheory

/-!
@concept one_sided_axioms
@title The One-Sided Axioms
@kind definition

The definition asks for a neutral element on both sides and an inverse on both sides, and the left half of each is enough: a left neutral element and left inverses already satisfy all five laws. Nothing later depends on this, but checking it is a good exercise in the axioms, and it shortens the verification that a structure is a group from five laws to three.
-/

/-!
@problem left_axioms_laws
@title The Left Axioms Give the Right Laws
@concept one_sided_axioms

@preamble
Suppose a set `G` has an operation `op`, an element `e` and a function `inv` satisfying three of the five laws: associativity, `op e a = a`, and `op (inv a) a = e`. Then the other two laws hold as well. The trick for `op a (inv a) = e` is to write `e` as a product `op (inv b) b` for a well-chosen `b`, so that `op (inv a) a` can be brought together by reassociating and cancelled; `op a e = a` then follows from it in a few steps. Without a class to hold them, the operation and the laws are explicit arguments of each theorem, and the statements are written with the bare functions, `op (op a b) c`.
@description
From the three left laws alone, show that `op a (inv a) = e` and then that `op a e = a`.
-/

theorem op_inv_of_left_axioms {G : Type u} (op : G → G → G) (e : G) (inv : G → G)
    (assoc : ∀ a b c : G, op (op a b) c = op a (op b c))
    (e_op : ∀ a : G, op e a = a) (inv_op : ∀ a : G, op (inv a) a = e) (a : G) :
    op a (inv a) = e := by
  calc op a (inv a) = op e (op a (inv a)) := by rw [e_op]
    _ = op (op (inv (inv a)) (inv a)) (op a (inv a)) := by rw [inv_op]
    _ = op (inv (inv a)) (op (op (inv a) a) (inv a)) := by rw [assoc, assoc]
    _ = op (inv (inv a)) (inv a) := by rw [inv_op, e_op]
    _ = e := inv_op (inv a)

theorem op_e_of_left_axioms {G : Type u} (op : G → G → G) (e : G) (inv : G → G)
    (assoc : ∀ a b c : G, op (op a b) c = op a (op b c))
    (e_op : ∀ a : G, op e a = a) (inv_op : ∀ a : G, op (inv a) a = e) (a : G) :
    op a e = a := by
  calc op a e = op a (op (inv a) a) := by rw [inv_op]
    _ = op (op a (inv a)) a := by rw [assoc]
    _ = op e a := by rw [op_inv_of_left_axioms op e inv assoc e_op inv_op]
    _ = a := e_op a

/-! @end -/

/-!
@problem group_of_left_axioms
@title A Group From the Left Axioms
@concept one_sided_axioms

@preamble
With the two missing laws proved, the three left laws determine a group: a construction that takes the three laws and returns the instance, under Mathlib's name for it. It is an `abbrev`, a definition Lean unfolds wherever it appears, so that the group it returns is seen to have the operation it was given. A definition that returns an instance of a class is built like an instance, with `where` and a line per field: the arguments supply the three pieces of data and three of the laws, and the previous problem's two theorems, which the context holds, supply the other two.
@description
Define `Group.ofLeftAxioms`, which builds the instance `Group G` from `op`, `e`, `inv` and the three left laws.
-/

abbrev Group.ofLeftAxioms {G : Type u} (op : G → G → G) (e : G) (inv : G → G)
    (assoc : ∀ a b c : G, op (op a b) c = op a (op b c))
    (e_op : ∀ a : G, op e a = a) (inv_op : ∀ a : G, op (inv a) a = e) : Group G where
  mul := op
  one := e
  inv := inv
  mul_assoc := assoc
  one_mul := e_op
  mul_one := op_e_of_left_axioms op e inv assoc e_op inv_op
  inv_mul_cancel := inv_op
  mul_inv_cancel := op_inv_of_left_axioms op e inv assoc e_op inv_op

/-- @spec -/
example {G : Type u} (op : G → G → G) (e : G) (inv : G → G)
    (assoc : ∀ a b c : G, op (op a b) c = op a (op b c))
    (e_op : ∀ a : G, op e a = a) (inv_op : ∀ a : G, op (inv a) a = e) :
    @Group.mul G (Group.ofLeftAxioms op e inv assoc e_op inv_op) = op ∧
    @Group.one G (Group.ofLeftAxioms op e inv assoc e_op inv_op) = e ∧
    @Group.inv G (Group.ofLeftAxioms op e inv assoc e_op inv_op) = inv :=
  ⟨rfl, rfl, rfl⟩

/-! @end -/

/-!
@problem int_group_of_left_axioms
@title The Integers From the Left Axioms
@concept one_sided_axioms

@preamble
What the construction buys is visible on the integers. The instance of the first concept checked five laws of addition; three suffice, `Int.add_assoc`, `Int.zero_add` and `Int.add_left_neg : -a + a = 0`, and the group they determine is the same group, with the same operation. A `def` holding a `Group ℤ` is a value, not an instance Lean finds by itself, so its operation is reached through the field, as `intGroupLeft.mul 3 4`, which is `3 + 4` once the definition unfolds.
@description
Define `intGroupLeft : Group ℤ` by `Group.ofLeftAxioms`, from addition, `0`, negation and the three laws, and check that its operation on `3` and `4` gives `7`.
-/

def intGroupLeft : Group ℤ :=
  Group.ofLeftAxioms (· + ·) 0 (- ·) Int.add_assoc Int.zero_add Int.add_left_neg

theorem intGroupLeft_mul : intGroupLeft.mul 3 4 = 7 := rfl

/-! @end -/

end GroupTheory
