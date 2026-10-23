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
import PolyaAlgebra.GroupTheory.Subgroups

/-! @section Extra Credit -/

universe u

namespace GroupTheory

set_option linter.translateGenerateName false

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
With the two missing laws proved, the three left laws determine a group: a construction that takes the three laws and returns the instance, under Mathlib's name for it. It is an `abbrev`, a definition Lean unfolds wherever it appears, so that the group it returns is seen to have the operation it was given. A definition that returns an instance of a class is built like an instance, with `where` and a line per field: the arguments supply the three pieces of data and three of the laws, and the previous problem's two theorems, which the context holds, supply the other two. Under its mark the construction comes with its copy, `AddGroup.ofLeftAxioms`, which builds an additive group the same way.
@description
Define `Group.ofLeftAxioms`, under its mark, which builds the instance `Group G` from `op`, `e`, `inv` and the three left laws.
-/

@[to_additive AddGroup.ofLeftAxioms]
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
What the construction buys is visible on the integers. The instance `AddGroup ℤ` of the second section checked five laws of addition; three suffice, `Int.add_assoc`, `Int.zero_add` and `Int.add_left_neg : -a + a = 0`, and the copy of the construction, `AddGroup.ofLeftAxioms`, builds from them the same group. A `def` holding an `AddGroup ℤ` is a value, not an instance Lean finds by itself, so its operation is reached through the field, as `intGroupLeft.add 3 4`, which is `3 + 4` once the definition unfolds.
@description
Define `intGroupLeft : AddGroup ℤ` by `AddGroup.ofLeftAxioms`, from the integers' addition, zero and negation and the three laws, and check that its addition on `3` and `4` gives `7`.
-/

def intGroupLeft : AddGroup ℤ :=
  AddGroup.ofLeftAxioms (fun a b => a + b) 0 (fun a => -a) Int.add_assoc Int.zero_add
    Int.add_left_neg

theorem intGroupLeft_add : intGroupLeft.add 3 4 = 7 := rfl

/-! @end -/

/-!
@concept subgroup_criterion
@title The Subgroup Criterion
@kind theorem

A subset is a subgroup as soon as it is nonempty and contains `a * b⁻¹` with any `a` and `b` it contains: one closure condition in place of three. Nothing later depends on it, but it is the test most books state, and proving it is an exercise in getting the neutral element and the inverses out of a single condition.
-/

/-!
@problem subgroup_of_div
@title A Subgroup From One Closure Condition
@concept subgroup_criterion

@preamble
A nonempty subset `s` of `G` that contains `a * b⁻¹` whenever it contains `a` and `b` is a subgroup. The one condition only ever produces elements of the form `a * b⁻¹`, so the test is to recognize each of `1`, `a⁻¹` and `a * b` as such a product of two elements already in `s`, through a law of the second section read as an equation between the two; the nonemptiness supplies the first element to start from, and each step uses the one before it. Mathlib's `Subgroup.ofDiv` is the construction, and under the marks its copy is `AddSubgroup.ofSub`; the two theorems before it carry the first two steps, so that each proof stays short, and the third step uses the second. The context holds `mul_inv_cancel`, `one_mul` and `inv_inv`.
@description
Show from the two hypotheses that `1 ∈ s`, and that `a⁻¹ ∈ s` for every `a ∈ s`; then define `Subgroup.ofDiv s hne hs`, the subgroup with carrier `s`.
-/

@[to_additive zero_mem_of_sub]
theorem one_mem_of_div {G : Type u} [Group G] {s : Set G} (hne : ∃ x, x ∈ s)
    (hs : ∀ a b, a ∈ s → b ∈ s → a * b⁻¹ ∈ s) : 1 ∈ s := by
  obtain ⟨x, hx⟩ := hne
  rw [← mul_inv_cancel x]
  exact hs x x hx hx

@[to_additive neg_mem_of_sub]
theorem inv_mem_of_div {G : Type u} [Group G] {s : Set G} (hne : ∃ x, x ∈ s)
    (hs : ∀ a b, a ∈ s → b ∈ s → a * b⁻¹ ∈ s) {a : G} (ha : a ∈ s) : a⁻¹ ∈ s := by
  rw [← one_mul a⁻¹]
  exact hs 1 a (one_mem_of_div hne hs) ha

@[to_additive AddSubgroup.ofSub]
def Subgroup.ofDiv {G : Type u} [Group G] (s : Set G) (hne : ∃ x, x ∈ s)
    (hs : ∀ a b, a ∈ s → b ∈ s → a * b⁻¹ ∈ s) : Subgroup G where
  carrier := s
  one_mem' := one_mem_of_div hne hs
  mul_mem' := by
    intro a b ha hb
    rw [← inv_inv b]
    exact hs a b⁻¹ ha (inv_mem_of_div hne hs hb)
  inv_mem' := by
    intro a ha
    exact inv_mem_of_div hne hs ha

/-- @spec -/
example {G : Type u} [Group G] (s : Set G) (hne : ∃ x, x ∈ s)
    (hs : ∀ a b, a ∈ s → b ∈ s → a * b⁻¹ ∈ s) : (Subgroup.ofDiv s hne hs).carrier = s := rfl

/-! @end -/

end GroupTheory
