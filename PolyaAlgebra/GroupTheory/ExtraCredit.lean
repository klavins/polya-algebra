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

The definition asks for a neutral element on both sides and an inverse on both sides, and the left half of each is enough: with associativity, a left neutral element and left inverses already give all five laws. It shortens the verification that a structure is a group from five laws to three.
-/

/-!
@problem left_axioms_laws
@title The Left Axioms Give the Right Laws
@concept one_sided_axioms

@preamble
Suppose a set `G` has an operation `op`, an element `e` and a function `inv` satisfying three of the five laws: associativity, `op e a = a`, and `op (inv a) a = e`. Then the other two laws hold as well. In the chain below we write `a * b` for `op a b`, `1` for `e` and `a⁻¹` for `inv a`. The chain of expressions for `a * a⁻¹ = 1` is
```lean
a * a⁻¹ = 1 * (a * a⁻¹) = a⁻¹⁻¹ * a⁻¹ * (a * a⁻¹)
  = a⁻¹⁻¹ * (a⁻¹ * a * a⁻¹) = a⁻¹⁻¹ * a⁻¹ = 1
```
Finding the left law behind each step is the exercise, and a step may take more than one. Without a class to hold them, the operation and the laws are explicit arguments of each theorem, and the statements are written with the bare functions, `op (op a b) c`.
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
With the two missing laws proved, the three left laws determine a group: a construction takes the data and the three laws, as plain arguments as in the previous problem, and returns the instance. It is an `abbrev`, as Lean expects of a definition whose value is an instance of a class. A definition that returns an instance of a class is built like an instance, with `where` and a line per field. The context holds the previous problem's two theorems. The construction comes with its additive version, `AddGroup.ofLeftAxioms`.
@description
Define `Group.ofLeftAxioms`, keeping the `@[to_additive]` line, which builds the instance `Group G` from `op`, `e`, `inv` and the three left laws.
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
What the construction buys is visible on the integers. The instance `AddGroup ℤ` of the second section needed five laws of addition; three suffice, `Int.add_assoc`, `Int.zero_add` and `Int.add_left_neg`, and the additive version of the construction, `AddGroup.ofLeftAxioms`, builds from them the same group. Like the construction, the definition holding it is an `abbrev`. It is a value, not an instance Lean finds by itself, so its pieces are reached through the fields, as `intGroupLeft.add 3 4`, which is `3 + 4` by definition. Its `add_zero` field is one of the two laws no argument supplied. `inferInstance` names the instance Lean finds, here that of the second section, written `(inferInstance : AddGroup ℤ)`.
@description
Define `intGroupLeft : AddGroup ℤ` by `AddGroup.ofLeftAxioms`, from the integers' addition, zero and negation and the three laws. Check that its addition on `3` and `4` gives `7`, that its `add_zero` gives `a + 0 = a`, and that it is the instance of the second section.
-/

abbrev intGroupLeft : AddGroup ℤ :=
  AddGroup.ofLeftAxioms (fun a b => a + b) 0 (fun a => -a) Int.add_assoc Int.zero_add
    Int.add_left_neg

theorem intGroupLeft_add : intGroupLeft.add 3 4 = 7 := rfl

theorem intGroupLeft_add_zero (a : ℤ) : intGroupLeft.add a intGroupLeft.zero = a :=
  intGroupLeft.add_zero a

theorem intGroupLeft_eq : intGroupLeft = (inferInstance : AddGroup ℤ) := rfl

/-! @end -/

/-!
@concept subgroup_criterion
@title The Subgroup Criterion
@kind theorem

A subset is a subgroup as soon as it is nonempty and contains, with any two of its elements, not necessarily distinct, the first times the inverse of the second: one closure condition in place of three. It is the test most books state.
-/

/-!
@problem subgroup_of_div
@title A Subgroup From One Closure Condition
@concept subgroup_criterion

@preamble
A nonempty subset `s` of `G` that contains `a * b⁻¹` whenever it contains `a` and `b` is a subgroup. We name the construction `Subgroup.ofDiv`, reading `a * b⁻¹` as the quotient of `a` by `b`, and its additive version is `AddSubgroup.ofSub`. The context holds `inv_inv`, `mul_inv_cancel` and `one_mul` of the second section.
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

/-!
@problem add_subgroup_of_sub_threes
@title The Multiples of Three by the Criterion
@concept subgroup_criterion

@preamble
What the criterion saves shows on the multiples of `3` in the integers, the subgroup `intMultiples 3` of the previous section, built from three closure conditions. The additive version `AddSubgroup.ofSub` asks for one element of the set and for the one condition, which written additively reads `a + -b ∈ s`: there is no subtraction in the condition, only a sum with a negative. Core Lean provides `Int.dvd_zero`, `Int.dvd_add` and `Int.dvd_neg`, which you may find useful. A membership `a ∈ {x | 3 ∣ x}` is the statement `3 ∣ a` by definition; `exact` accepts the one for the other, but `omega` does not. The context holds `intMultiples` with `mem_intMultiples`, the additive version `AddSubgroup.ext`, and the instance `AddGroup ℤ` of the second section.
@description
Define `threeMultiples : AddSubgroup ℤ` by `AddSubgroup.ofSub`, with carrier `{x | 3 ∣ x}`, and show that it is `intMultiples 3`.
-/

def threeMultiples : AddSubgroup ℤ :=
  AddSubgroup.ofSub {x | 3 ∣ x} ⟨0, Int.dvd_zero 3⟩ (by
    intro a b ha hb
    exact Int.dvd_add ha (Int.dvd_neg.mpr hb))

theorem threeMultiples_eq : threeMultiples = intMultiples 3 := by
  apply AddSubgroup.ext
  intro x
  rw [mem_intMultiples]
  rfl

/-! @end -/

end GroupTheory
