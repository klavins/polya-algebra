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

/-! @section Examples -/

universe u v

namespace GroupTheory

set_option linter.translateGenerateName false

/-!
@concept integers_mod_n
@title The Integers Modulo n
@kind definition

The integers modulo `n` are the remainders `0, …, n - 1`, added by adding and reducing. They are the commutative finite groups every course computes in: one for each `n`, among them a group of each prime order. This concept builds the type `ZMod n` from a remainder and its bound, adds its residues, makes it an additive group, counts it, and matches `ZMod 2` with the group of order two.
-/

/-!
@problem zmod
@title The Integers Modulo n
@concept integers_mod_n

@preamble
The first section showed that the classes of congruence modulo `n` correspond to the remainders `0, …, n - 1`. Arithmetic modulo `n` is arithmetic on these remainders, and we take the remainders themselves as the elements, as `Fin n` does: an element of `ZMod n` is a natural number `val` together with a proof `val_lt` that it is below `n`, built as `⟨2, by decide⟩` or `⟨a % n, Nat.mod_lt a h⟩`. Lean's `Fin n` already adds this way, and Mathlib has a `ZMod n` of another shape; `ZMod n` is defined afresh here, so that its operation is the one written in this concept, under Mathlib's name for the integers modulo `n`.

A numeral in `ZMod n` is the remainder of the number it names, so `(7 : ZMod 5)` is `2`. The Natural Numbers gave `MyNat` its numerals through instances of `OfNat`; one instance `OfNat (ZMod n) k` for every `k` gives `ZMod n` all of them, and the hypothesis `[NeZero n]`, met at `toFin` in the first section, keeps `n` positive so that `k % n` is a remainder below it. Closing the structure with `deriving DecidableEq` lets `decide` compare two of its elements.
@description
Define the structure `ZMod n` with the fields `val : ℕ` and `val_lt : val < n`, closed by `deriving DecidableEq`, and supply the instance `OfNat (ZMod n) k` that reads a numeral as its remainder modulo `n`.
-/

structure ZMod (n : ℕ) where
  val : ℕ
  val_lt : val < n
  deriving DecidableEq

instance (n : ℕ) [NeZero n] (k : ℕ) : OfNat (ZMod n) k :=
  ⟨⟨k % n, Nat.mod_lt k (Nat.pos_of_neZero n)⟩⟩

/-- @spec -/
example (n : ℕ) (a : ZMod n) : a.val < n := a.val_lt

/-- @spec -/
example (n k : ℕ) (h : k < n) : ZMod n := ⟨k, h⟩

/-- @spec -/
example : (7 : ZMod 5).val = 2 ∧ (3 : ZMod 6) ≠ 4 := by decide

/-! @end -/

/-!
@problem zmod_add_neg
@title Addition and Negation Modulo n
@concept integers_mod_n

@preamble
Remainders are added by adding and reducing: the sum of `a` and `b` in `ZMod n` has the value `(a.val + b.val) % n`, which `Nat.mod_lt` keeps below `n`. The negative of `a` is the remainder that returns the sum to `0`, which is `n - a.val`, except that `n - 0 = n` is not a remainder; reducing once more, `(n - a.val) % n`, covers that case too, since `n % n = 0`. Each operation returns a remainder together with its proof of being one, with `Nat.mod_lt` and `Nat.pos_of_neZero n` as `toFin` used them in the first section. The symbols `+` and `-a` belong to the classes `Add` and `Neg`, as `*` belongs to `Mul`, and two instances hand them the operations.

The two equations that read the values back, `(a + b).val = (a.val + b.val) % n` and `(-a).val = (n - a.val) % n`, hold by definition, and later proofs rewrite with them: a goal that mentions `(a + b).val` is not touched by the lemmas about `%` until it is unfolded to the arithmetic it stands for.
@description
Define `ZMod.add` and `ZMod.neg`, supply the instances `Add (ZMod n)` and `Neg (ZMod n)`, and prove the two equations `ZMod.val_add` and `ZMod.val_neg` that unfold them, each of which holds by definition.
-/

def ZMod.add {n : ℕ} [NeZero n] (a b : ZMod n) : ZMod n :=
  ⟨(a.val + b.val) % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩

def ZMod.neg {n : ℕ} [NeZero n] (a : ZMod n) : ZMod n :=
  ⟨(n - a.val) % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩

instance {n : ℕ} [NeZero n] : Add (ZMod n) := ⟨ZMod.add⟩

instance {n : ℕ} [NeZero n] : Neg (ZMod n) := ⟨ZMod.neg⟩

/-- @spec -/
example : (3 : ZMod 5) + 4 = 2 ∧ -(2 : ZMod 5) = 3 := by decide

theorem ZMod.val_add {n : ℕ} [NeZero n] (a b : ZMod n) :
    (a + b).val = (a.val + b.val) % n := rfl

theorem ZMod.val_neg {n : ℕ} [NeZero n] (a : ZMod n) : (-a).val = (n - a.val) % n := rfl

/-! @end -/

/-!
@problem zmod_add_laws
@title The Laws of Addition Modulo n
@concept integers_mod_n

@preamble
Addition modulo `n` is associative and commutative, `0` is neutral, and `-a` cancels `a` on either side: the six laws an additive group has, each an equation of remainders. Two elements of `ZMod n` are equal when their values are, by `ZMod.ext : a.val = b.val → a = b`, given in the context; the two equations of the previous problem turn the value of a sum or a negative into arithmetic of remainders, and `ZMod.val_zero`, also given, says that the numeral `0` has the value `0 % n`, which `Nat.zero_mod` reduces. The first section's facts about `%` settle the arithmetic: `Nat.mod_add_mod` and `Nat.add_mod_mod` let a summand be reduced before or after the addition, `Nat.mod_eq_of_lt` for a number below `n`, and `Nat.mod_self`. Core Lean also has `Nat.add_assoc`, `Nat.add_comm`, `Nat.zero_add`, `Nat.add_zero`, `Nat.le_of_lt`, `Nat.sub_add_cancel` and `Nat.add_sub_of_le`.
@description
Prove the six laws `ZMod.add_assoc`, `ZMod.zero_add`, `ZMod.add_zero`, `ZMod.neg_add_cancel : -a + a = 0`, `ZMod.add_neg_cancel : a + -a = 0` and `ZMod.add_comm`, under Mathlib's names.
-/

/-- @given -/
theorem ZMod.ext {n : ℕ} {a b : ZMod n} (h : a.val = b.val) : a = b := by
  cases a
  cases b
  subst h
  rfl

/-- @given -/
theorem ZMod.val_zero {n : ℕ} [NeZero n] : (0 : ZMod n).val = 0 % n := rfl

theorem ZMod.add_assoc {n : ℕ} [NeZero n] (a b c : ZMod n) : a + b + c = a + (b + c) := by
  apply ZMod.ext
  simp only [ZMod.val_add]
  rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

theorem ZMod.zero_add {n : ℕ} [NeZero n] (a : ZMod n) : 0 + a = a := by
  apply ZMod.ext
  rw [ZMod.val_add, ZMod.val_zero, Nat.zero_mod, Nat.zero_add, Nat.mod_eq_of_lt a.val_lt]

theorem ZMod.add_zero {n : ℕ} [NeZero n] (a : ZMod n) : a + 0 = a := by
  apply ZMod.ext
  rw [ZMod.val_add, ZMod.val_zero, Nat.zero_mod, Nat.add_zero, Nat.mod_eq_of_lt a.val_lt]

theorem ZMod.neg_add_cancel {n : ℕ} [NeZero n] (a : ZMod n) : -a + a = 0 := by
  apply ZMod.ext
  rw [ZMod.val_add, ZMod.val_neg, ZMod.val_zero, Nat.mod_add_mod,
    Nat.sub_add_cancel (Nat.le_of_lt a.val_lt), Nat.mod_self, Nat.zero_mod]

theorem ZMod.add_neg_cancel {n : ℕ} [NeZero n] (a : ZMod n) : a + -a = 0 := by
  apply ZMod.ext
  rw [ZMod.val_add, ZMod.val_neg, ZMod.val_zero, Nat.add_mod_mod,
    Nat.add_sub_of_le (Nat.le_of_lt a.val_lt), Nat.mod_self, Nat.zero_mod]

theorem ZMod.add_comm {n : ℕ} [NeZero n] (a b : ZMod n) : a + b = b + a := by
  apply ZMod.ext
  rw [ZMod.val_add, ZMod.val_add, Nat.add_comm]

/-! @end -/

/-!
@problem zmod_group
@title The Group of Integers Modulo n
@concept integers_mod_n

@preamble
`ZMod n` under `+` is an additive group for every positive `n`: the instance takes the addition, the numeral `0` and the negation of the previous problems as its data, and the laws of the previous problem as its five laws, so that `add_assoc := ZMod.add_assoc` is accepted as it stands. As for the integers, the instance's `+` is the residues' own, so every theorem about additive groups applies to residues as they are written, with no new proof: `-(-a) = a` is `neg_neg a`, and `-(a + b) = -b + -a` is `neg_add_rev a b`, the additive copies of two theorems of the previous section, which the context holds. In `ZMod 5`, `3 + 4 = 2` and `-2 = 3`, which `decide` settles.
@description
Supply the instance `AddGroup (ZMod n)` for positive `n`, and show that `-(-a) = a` and `-(a + b) = -b + -a` for all residues `a` and `b`.
-/

instance (n : ℕ) [NeZero n] : AddGroup (ZMod n) where
  add a b := a + b
  zero := 0
  neg a := -a
  add_assoc := ZMod.add_assoc
  zero_add := ZMod.zero_add
  add_zero := ZMod.add_zero
  neg_add_cancel := ZMod.neg_add_cancel
  add_neg_cancel := ZMod.add_neg_cancel

/-- @spec -/
example : AddGroup.add (4 : ZMod 6) 5 = 3 ∧ (AddGroup.zero : ZMod 6) = 0 ∧
    AddGroup.neg (4 : ZMod 6) = 2 := by decide

theorem zmod_neg_neg {n : ℕ} [NeZero n] (a : ZMod n) : -(-a) = a :=
  neg_neg a

theorem zmod_neg_add_rev {n : ℕ} [NeZero n] (a b : ZMod n) : -(a + b) = -b + -a :=
  neg_add_rev a b

/-! @end -/

/-!
@problem zmod_fintype
@title Counting the Integers Modulo n
@concept integers_mod_n

@preamble
`ZMod n` has `n` elements, one for each remainder. To count it in Lean is to give it a `Fintype` instance, and the first section's way of counting, by labelling, gives one. The elements of `ZMod n` are labelled by `Fin n` through the equivalence that keeps the value and carries the bound across, under the name each side gives its proof, `isLt` in `Fin n` and `val_lt` in `ZMod n`; each inverse law says that an element rebuilt from its own fields is itself, which holds by `rfl`. `Fintype.ofEquiv α (e : α ≃ β) : Fintype β` makes the labelled type finite from its labels, and `Fintype.card_congr` of the same equivalence counts it.
@description
Define `finEquivZMod n : Fin n ≃ ZMod n`, supply the instance `Fintype (ZMod n)` from it, and show that `ZMod n` has `n` elements. Mathlib provides `Fintype.ofEquiv`, `Fintype.card_congr` and `Fintype.card_fin`.
-/

def finEquivZMod (n : ℕ) : Fin n ≃ ZMod n where
  toFun i := ⟨i.val, i.isLt⟩
  invFun a := ⟨a.val, a.val_lt⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- @spec -/
example (n : ℕ) (i : Fin n) (a : ZMod n) :
    (finEquivZMod n i).val = i.val ∧ ((finEquivZMod n).symm a).val = a.val := ⟨rfl, rfl⟩

instance (n : ℕ) : Fintype (ZMod n) := Fintype.ofEquiv (Fin n) (finEquivZMod n)

theorem card_zmod (n : ℕ) : Fintype.card (ZMod n) = n := by
  rw [← Fintype.card_congr (finEquivZMod n), Fintype.card_fin]

/-! @end -/

/-!
@problem zmod_two_equiv_bool
@title The Integers Modulo 2 and the Booleans
@concept integers_mod_n

@preamble
`ZMod 2` has the two elements `0` and `1`, with `1 + 1 = 0`, and so has the group of order two of the previous section, `Bool` under `xor`, with `true + true = false`. The two are the same group under different names: the renaming `0 ↦ false`, `1 ↦ true` is a bijection that carries the one table to the other, `e (a + b) = e a + e b` for all `a` and `b`. The equivalence is written as `boolEquivFinTwo` was in the first section, with `if c then x else y`, which branches on a decidable condition `c`, in each direction: a test of `a.val` on one side, and the numerals `1` and `0` on the other. Each of its laws, like the equation of the tables, is a statement about the finitely many elements of `ZMod 2` and `Bool`, which `decide` settles through the instance of the previous problem.
@description
Define `zmodTwoEquivBool : ZMod 2 ≃ Bool`, sending `0` to `false` and `1` to `true`, and show that it carries the addition of `ZMod 2` to the addition of `Bool`.
-/

def zmodTwoEquivBool : ZMod 2 ≃ Bool where
  toFun a := if a.val = 1 then true else false
  invFun b := if b then ⟨1, by decide⟩ else ⟨0, by decide⟩
  left_inv := by decide
  right_inv := by decide

/-- @spec -/
example : zmodTwoEquivBool 0 = false ∧ zmodTwoEquivBool 1 = true := by decide

theorem zmodTwoEquivBool_add :
    ∀ a b : ZMod 2, zmodTwoEquivBool (a + b) = zmodTwoEquivBool a + zmodTwoEquivBool b := by
  decide

/-! @end -/

/-!
@concept symmetric_groups
@title The Symmetric Groups
@kind definition

The permutations of a set form a group under composition, the symmetric group of the set; on `n` points it is `Sₙ`. It is the first group in which the order of the factors matters, and the one every finite group lives inside. This concept makes `Equiv.Perm X` an instance of the class and shows, on three points, that a rotation and a reflection do not commute.
-/

/-!
@problem perm_group
@title The Symmetric Group
@concept symmetric_groups

@preamble
A permutation of `X` is a bijection from `X` to itself, an element of `Equiv.Perm X`, and permutations compose: `g` and then `f` is `g.trans f`. We take `f * g` to be `g.trans f`, the permutation that applies `g` first, so that `(f * g) x = f (g x)`, as for functions; the identity `Equiv.refl X` is neutral, and the inverse of `f` is `f.symm`. Associativity and the two laws of the identity hold by `rfl`: both sides apply the same functions in the same order, and the proof fields of an equivalence do not matter to its equality.

The two inverse laws say that `f` followed by `f.symm`, and `f.symm` followed by `f`, are the identity, which is true at every point: `f.symm (f x) = x` and `f (f.symm x) = x`, the laws `f.symm_apply_apply` and `f.apply_symm_apply` of the first section. Two equivalences that agree at every point are equal, `Equiv.ext : (∀ x, e x = e' x) → e = e'`; after `apply Equiv.ext` the goal at a point `x` reads `(f.trans f.symm) x = (Equiv.refl X) x`, which unfolds to `f.symm (f x) = x`, and `exact` sees through the unfolding.
@description
Supply the instance `Group (Equiv.Perm X)` with `f * g = g.trans f` (not `f.trans g`, which applies `f` first), so that `(f * g) x = f (g x)`. Mathlib provides `Equiv.ext`.
-/

instance (X : Type u) : Group (Equiv.Perm X) where
  mul f g := g.trans f
  one := Equiv.refl X
  inv f := f.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel f := Equiv.ext f.symm_apply_apply
  mul_inv_cancel f := Equiv.ext f.apply_symm_apply

/-- @spec -/
example (X : Type u) (f g : Equiv.Perm X) (x : X) :
    (f * g) x = f (g x) ∧ (1 : Equiv.Perm X) x = x ∧ f⁻¹ (f x) = x :=
  ⟨rfl, rfl, f.symm_apply_apply x⟩

/-! @end -/

/-!
@problem reflect3
@title A Reflection of Three Points
@concept symmetric_groups

@preamble
The symmetric group on three points, `Equiv.Perm (Fin 3)`, is the group of symmetries of a triangle with vertices `0`, `1` and `2`. The rotation `rot3` of the first section, `i ↦ i + 1`, turns it; the reflection through the vertex `0` fixes `0` and exchanges `1` and `2`, which is `i ↦ -i`, since `-1 = 2` and `-2 = 1` in `Fin 3`. A reflection is its own inverse, so the same function serves in both directions, and applied twice it is the identity, `reflect3 * reflect3 = 1`. `decide` settles the laws and the equation, as it settled the cube of `rot3`, which in the group's symbols is `rot3 * rot3 * rot3 = 1`: `rot3` of the first section is an element of this group as it stands.
@description
Define `reflect3 : Equiv.Perm (Fin 3)`, the permutation sending `i` to `-i`, and show that `reflect3 * reflect3 = 1` and `rot3 * rot3 * rot3 = 1`.
-/

def reflect3 : Equiv.Perm (Fin 3) where
  toFun i := -i
  invFun i := -i
  left_inv := by decide
  right_inv := by decide

/-- @spec -/
example : reflect3 0 = 0 ∧ reflect3 1 = 2 ∧ reflect3 2 = 1 := by decide

theorem reflect3_mul_self : reflect3 * reflect3 = 1 := by
  decide

theorem rot3_cube_mul : rot3 * rot3 * rot3 = 1 := by
  decide

/-! @end -/

/-!
@problem s3_not_comm
@title The Symmetric Group on Three Points is Not Commutative
@concept symmetric_groups

@preamble
In every group met so far, `a * b = b * a`. Not here: reflecting and then rotating is not rotating and then reflecting. At the vertex `0`, `(rot3 * reflect3) 0 = rot3 (reflect3 0) = 1`, while `(reflect3 * rot3) 0 = reflect3 1 = 2`; the two products differ at a point, so they differ, and `decide` compares the two permutations at all three points.

What the order does is a rule: reflecting after a rotation is rotating the other way after the reflection, `reflect3 * rot3 = rot3⁻¹ * reflect3`, again a check at three points. The laws of the previous section hold all the same, since they were proved from the axioms, so an equal factor cancels in S₃ as it does in the integers. There `decide` is no help: the goal has a free variable `x`, and to run through its values `decide` would need a list of all permutations of three points, which the part of Mathlib this subject imports does not provide.
@description
Show that `rot3 * reflect3 ≠ reflect3 * rot3`, that `reflect3 * rot3 = rot3⁻¹ * reflect3`, and that `rot3 * x = rot3 * reflect3` forces `x = reflect3`. The context holds `mul_left_cancel` of the previous section, and not the `↔` form beside it.
-/

theorem rot3_reflect3_ne : rot3 * reflect3 ≠ reflect3 * rot3 := by
  decide

theorem reflect3_mul_rot3 : reflect3 * rot3 = rot3⁻¹ * reflect3 := by
  decide

theorem s3_cancel (x : Equiv.Perm (Fin 3)) (h : rot3 * x = rot3 * reflect3) : x = reflect3 :=
  mul_left_cancel h

/-! @end -/

/-!
@concept commutative_groups
@title Commutative Groups
@kind definition

A group is commutative when `a * b = b * a` for all its elements. The integers, the integers modulo `n`, and the groups of order one and two are commutative; the symmetric group on three points is not. In a commutative group the factors of a product may be freely rearranged, which the table of the dihedral groups relies on, and the subject's goal is that every group of order `p²` is commutative.
-/

/-!
@problem comm_group
@title The Definition of a Commutative Group
@concept commutative_groups

@preamble
A group is *commutative*, or abelian, when `a * b = b * a` for all `a` and `b`. Lean expresses "a group with one more law" as a class that extends the first: the head `class CommGroup (G : Type u) extends Group G where` is followed by the new field alone, `mul_comm`, which says that `a * b = b * a` for all `a` and `b`; the symbol is available inside the class because `extends Group G` puts a `Group G` in scope. An instance of `CommGroup G` then carries an instance of `Group G` inside it, as the field `toGroup`, which Lean finds whenever a law of groups is used on `G`; and an instance is built from an existing `Group G` by supplying the one new field. The additive copy is `AddCommGroup A`, extending `AddGroup A` by `add_comm`, and the line `attribute [to_additive existing AddCommGroup] CommGroup` after the problem records the correspondence. The names are Mathlib's.
@description
Define the class `CommGroup G`, extending `Group G` by the law `mul_comm`, and its additive copy `AddCommGroup A`, extending `AddGroup A` by the law `add_comm`, each written with the elements as explicit arguments as in the preamble.
-/

class CommGroup (G : Type u) extends Group G where
  mul_comm : ∀ a b : G, a * b = b * a

class AddCommGroup (A : Type u) extends AddGroup A where
  add_comm : ∀ a b : A, a + b = b + a

/-- @spec -/
example (G : Type u) [CommGroup G] : Group G := CommGroup.toGroup

/-- @spec -/
example (G : Type u) [CommGroup G] (a b : G) : a * b = b * a := by
  have h := @CommGroup.mul_comm G _ a b
  grind

/-- @spec -/
example (A : Type u) [AddCommGroup A] : AddGroup A := AddCommGroup.toAddGroup

/-- @spec -/
example (A : Type u) [AddCommGroup A] (a b : A) : a + b = b + a := by
  have h := @AddCommGroup.add_comm A _ a b
  grind

/-! @end -/

attribute [to_additive existing AddCommGroup] CommGroup

/-!
@problem comm_instances
@title The Commutative Examples
@concept commutative_groups

@preamble
Addition commutes, on `ℤ` by `Int.add_comm`, on `ZMod n` by `ZMod.add_comm` of this section's first concept, and on `Bool` by `decide`, so the three are commutative additive groups. Each instance is an existing `AddGroup` instance, of the previous section or of this one, with the field `add_comm` added, which `where` with that one field builds, Lean supplying `toAddGroup` by itself. The restatement `mul_comm : a * b = b * a` of the new field, given in the starting code with its additive copy `add_comm`, is the form later proofs rewrite with. The trivial group is commutative too, by `decide` through the instance `Group Unit` of the previous section, which the context holds.
@description
Supply the instances `CommGroup Unit`, `AddCommGroup ℤ`, `AddCommGroup (ZMod n)` and `AddCommGroup Bool`.
-/

/-- @given -/
@[to_additive add_comm]
theorem mul_comm {G : Type u} [CommGroup G] (a b : G) : a * b = b * a :=
  CommGroup.mul_comm a b

instance : CommGroup Unit where
  mul_comm := by decide

instance : AddCommGroup ℤ where
  add_comm := Int.add_comm

instance (n : ℕ) [NeZero n] : AddCommGroup (ZMod n) where
  add_comm := ZMod.add_comm

instance : AddCommGroup Bool where
  add_comm := by decide

/-- @spec -/
example (a b : ℤ) : a + b = b + a := add_comm a b

/-- @spec -/
example (a b : Bool) : a + b = b + a := add_comm a b

/-- @spec -/
example (n : ℕ) [NeZero n] (a b : ZMod n) : a + b = b + a := add_comm a b

/-- @spec -/
example (a b : Unit) : a * b = b * a := mul_comm a b

/-! @end -/

/-!
@problem comm_rearrange
@title Rearranging a Product in a Commutative Group
@concept commutative_groups

@preamble
In a commutative group the factors of a product can be put in any order, and two rearrangements are used so often that Mathlib names them: `mul_left_comm : a * (b * c) = b * (a * c)` exchanges the first two factors of a product grouped to the right, and `mul_right_comm : a * b * c = a * c * b` exchanges the last two of one grouped to the left. Each is a consequence of associativity and a single commutation, and each is a rewrite rule, used on a product whose factors are in the wrong order, and each comes with its additive copy, `add_left_comm` and `add_right_comm`. `rw [mul_comm]` exchanges the first product it finds, the outer one; `rw [mul_comm x y]` names the product to exchange. The context holds `mul_assoc` and `mul_comm`.
@description
Show that in a commutative group `a * (b * c) = b * (a * c)` and `a * b * c = a * c * b`, under Mathlib's names `mul_left_comm` and `mul_right_comm`.
-/

@[to_additive add_left_comm]
theorem mul_left_comm {G : Type u} [CommGroup G] (a b c : G) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, mul_comm a b, mul_assoc]

@[to_additive add_right_comm]
theorem mul_right_comm {G : Type u} [CommGroup G] (a b c : G) : a * b * c = a * c * b := by
  rw [mul_assoc, mul_comm b c, ← mul_assoc]

/-! @end -/

/-!
@concept product_groups
@title Product Groups
@kind definition

Two groups `G` and `H` make a third, their product `G × H`: the pairs `(g, h)`, multiplied componentwise. It is how groups are assembled from smaller ones, and how a group is recognized as assembled: `ZMod 2 × ZMod 3` has six elements and commutes, as `ZMod 6` does, and the subject's goal needs the product, since the groups of order `p²` turn out to be `ZMod (p²)` and `ZMod p × ZMod p`.
-/

/-!
@problem prod_group
@title The Product of Two Groups
@concept product_groups

@preamble
The product of two groups `G` and `H` is the set of pairs `(g, h)` with the operation `(g, h) * (g', h') = (g * g', h * h')`, each component multiplied in its own group; the neutral element is `(1, 1)` and the inverse of `(g, h)` is `(g⁻¹, h⁻¹)`. The elements of `G × H` are Lean's pairs, with `a.1` and `a.2` the components of `a`, so the operation is `(a.1 * b.1, a.2 * b.2)`. Each law is an equation between two pairs, true when it is true in each component, where it is the same law in `G` or in `H`; a rewrite with a law fixes the law's elements at the first product it meets, so the two components take two rewrites. The equation `a * b = (a.1 * b.1, a.2 * b.2)` holds by definition, and later proofs rewrite with it. The instance carries its mark, so the product of two additive groups is an additive group, added componentwise: in `ZMod 2 × ZMod 3`, `(1, 2) + (1, 2) = (0, 1)`, which `decide` computes.
@description
Supply the instance `Group (G × H)`, state `prod_mul_def`, that `a * b = (a.1 * b.1, a.2 * b.2)`, and check that `(1, 2) + (1, 2) = (0, 1)` in `ZMod 2 × ZMod 3`.
-/

@[to_additive Prod.instAddGroup]
instance Prod.instGroup {G : Type u} {H : Type v} [Group G] [Group H] : Group (G × H) where
  mul a b := (a.1 * b.1, a.2 * b.2)
  one := (1, 1)
  inv a := (a.1⁻¹, a.2⁻¹)
  mul_assoc a b c := by
    rw [mul_assoc, mul_assoc]
  one_mul a := by
    rw [one_mul, one_mul]
  mul_one a := by
    rw [mul_one, mul_one]
  inv_mul_cancel a := by
    rw [inv_mul_cancel, inv_mul_cancel]
  mul_inv_cancel a := by
    rw [mul_inv_cancel, mul_inv_cancel]

/-- @spec -/
example {G : Type u} {H : Type v} [Group G] [Group H] (a c : G) (b d : H) :
    (a, b) * (c, d) = (a * c, b * d) ∧ (1 : G × H) = (1, 1) ∧ (a, b)⁻¹ = (a⁻¹, b⁻¹) :=
  ⟨rfl, rfl, rfl⟩

@[to_additive prod_add_def]
theorem prod_mul_def {G : Type u} {H : Type v} [Group G] [Group H] (a b : G × H) :
    a * b = (a.1 * b.1, a.2 * b.2) := rfl

theorem zmod_two_three_add : ((1 : ZMod 2), (2 : ZMod 3)) + (1, 2) = (0, 1) := by
  decide

/-! @end -/

/-!
@problem prod_fintype
@title Counting a Product
@concept product_groups

@preamble
A product of finite groups is finite, with as many elements as there are pairs: `ZMod 2 × ZMod 3` has `2 * 3 = 6`. The count is by labelling, as in the first section: `finProdFinEquiv` labels the pairs of `Fin 2 × Fin 3` by `Fin 6`, and `finEquivZMod` of this section's first concept labels each factor, so that `Fin 6 ≃ ZMod 2 × ZMod 3` is a composite of the three. Two equivalences combine componentwise, `e.prodCongr e' : α × β ≃ γ × δ` for `e : α ≃ γ` and `e' : β ≃ δ`, and `e.symm` and `e.trans` are as in the first section. The product `Fin 2 × Fin 3` carries no `Fintype` instance in the part of Mathlib this subject imports, and neither does `ZMod 2 × ZMod 3` until one is built, by `Fintype.ofEquiv` from `Fin 6` as the instance of `ZMod n` was built from `Fin n`; with it, `decide` runs through the six pairs.
@description
Define `finSixEquivZModTwoThree : Fin 6 ≃ ZMod 2 × ZMod 3`, supply the instance `Fintype (ZMod 2 × ZMod 3)`, and show that it has six elements. The context holds `finEquivZMod`; Mathlib provides `Equiv.prodCongr`, `finProdFinEquiv`, `Fintype.ofEquiv`, `Fintype.card_congr` and `Fintype.card_fin`.
-/

def finSixEquivZModTwoThree : Fin 6 ≃ ZMod 2 × ZMod 3 :=
  finProdFinEquiv.symm.trans ((finEquivZMod 2).prodCongr (finEquivZMod 3))

/-- @spec -/
example : Function.Bijective finSixEquivZModTwoThree := finSixEquivZModTwoThree.bijective

instance : Fintype (ZMod 2 × ZMod 3) :=
  Fintype.ofEquiv (Fin 6) finSixEquivZModTwoThree

theorem card_zmod_two_three : Fintype.card (ZMod 2 × ZMod 3) = 6 := by
  rw [← Fintype.card_congr finSixEquivZModTwoThree, Fintype.card_fin]

/-! @end -/

/-!
@problem prod_comm_group
@title The Product of Two Commutative Groups
@concept product_groups

@preamble
When `G` and `H` are commutative, so is `G × H`: the two components of `a * b` and of `b * a` are products in `G` and in `H`, which commute. The instance is built from the group instance of the product by supplying the one field `mul_comm`, and the law is an equation between two pairs once both products are unfolded by `prod_mul_def`. The instance carries its mark, so the product of two commutative additive groups is one: `ZMod 2 × ZMod 3` is a commutative group of order six, as `ZMod 6` is, and `decide` confirms its commutativity pair by pair, through the `Fintype` instance of the previous problem.
@description
Supply the instance `CommGroup (G × H)` for commutative `G` and `H`, and check that `ZMod 2 × ZMod 3` is commutative by running through its pairs. The context holds `prod_mul_def` and `mul_comm`; `mul_comm` is applied to the elements of each component, since a bare `rw [mul_comm]` turns the first product it finds, and a second bare one turns it back.
-/

@[to_additive Prod.instAddCommGroup]
instance Prod.instCommGroup {G : Type u} {H : Type v} [CommGroup G] [CommGroup H] :
    CommGroup (G × H) where
  mul_comm a b := by
    rw [prod_mul_def, prod_mul_def, mul_comm a.1 b.1, mul_comm a.2 b.2]

/-- @spec -/
example {G : Type u} {H : Type v} [CommGroup G] [CommGroup H] (a b : G × H) : a * b = b * a :=
  mul_comm a b

theorem zmod_two_three_comm : ∀ a b : ZMod 2 × ZMod 3, a + b = b + a := by
  decide

/-! @end -/

/-!
@concept dihedral_groups
@title The Dihedral Groups
@kind definition

The dihedral group Dₙ is the group of symmetries of a regular `n`-gon: `n` rotations and `n` reflections, `2n` elements in all, multiplied by composing symmetries. It is the subject's standard non-commutative example, small enough to compute in and rich enough to have subgroups of every kind; D₂ is the Klein four-group. This concept builds it over `ZMod n` from a four-line table and counts it.
-/

/-!
@problem dihedral_mul
@title The Elements and the Table of the Dihedral Group
@concept dihedral_groups

@preamble
The symmetries of a regular `n`-gon are the `n` rotations, through `i` steps of a full turn divided by `n`, and the `n` reflections, each the rotation through `i` steps followed by a fixed reflection `s`. So the elements are of two kinds, `r i` and `sr i`, each labelled by a residue `i : ZMod n`, so an inductive type with two constructors carrying an `i`. Composing symmetries gives the table, where in `mul a b` the symmetry `b` acts first, as for permutations. Two rotations add their steps, `mul (r i) (r j) = r (i + j)`; a reflection after a rotation is a reflection, `mul (sr i) (r j) = sr (i + j)`; a rotation after a reflection is a reflection with the rotation reversed, `mul (r i) (sr j) = sr (j + -i)`; and two reflections make a rotation, `mul (sr i) (sr j) = r (j + -i)`. The `+` and `-` on the right are `ZMod n`'s, so the table needs `[NeZero n]`; Mathlib writes `j - i`. In D₄, the square, reflecting, turning a quarter and reflecting again turns a quarter the other way: `sr 0` times `r 1` times `sr 0` is `r 3`, which `decide` computes.
@description
Define the inductive type `DihedralGroup n` with the constructors `r` and `sr`, each taking an `i : ZMod n`, closed by `deriving DecidableEq`; define `DihedralGroup.mul` by the four-line table; and check in `DihedralGroup 4` that `sr 0` times `r 1` times `sr 0` is `r 3`.
-/

inductive DihedralGroup (n : ℕ) where
  | r (i : ZMod n)
  | sr (i : ZMod n)
  deriving DecidableEq

def DihedralGroup.mul {n : ℕ} [NeZero n] : DihedralGroup n → DihedralGroup n → DihedralGroup n
  | r i, r j => r (i + j)
  | r i, sr j => sr (j + -i)
  | sr i, r j => sr (i + j)
  | sr i, sr j => r (j + -i)

/-- @spec -/
example {n : ℕ} [NeZero n] (i j : ZMod n) :
    DihedralGroup.mul (.r i) (.r j) = .r (i + j) ∧
    DihedralGroup.mul (.r i) (.sr j) = .sr (j + -i) ∧
    DihedralGroup.mul (.sr i) (.r j) = .sr (i + j) ∧
    DihedralGroup.mul (.sr i) (.sr j) = .r (j + -i) :=
  ⟨rfl, rfl, rfl, rfl⟩

open DihedralGroup in
theorem d4_table :
    DihedralGroup.mul (DihedralGroup.mul (sr 0) (r 1)) (sr 0) = (r 3 : DihedralGroup 4) := by
  decide

/-! @end -/

/-!
@problem dihedral_mul_assoc
@title The Dihedral Table is Associative
@concept dihedral_groups

@preamble
The table defines a group only if it is associative, which is a check on eight cases, one for each choice of kinds for `a`, `b` and `c`, opened by `cases` on each of them (`cases a <;> cases b <;> cases c` opens all eight at once, with the residues left unnamed, which the rewrite rules below do not need). In each case both sides are one constructor applied to two sums in `ZMod n`, equal because addition modulo `n` is associative and commutative: `add_assoc`, `neg_add_rev`, `neg_neg`, `add_left_comm` and `add_right_comm`, the additive copies of theorems of the previous section and of the previous concept, applied to residues, are the rewrite rules, and which of them a case needs is read off its two sums. A goal shows `mul` applied to constructors, which `rw` does not see through; the four equations of the table, given in the context as `DihedralGroup.r_mul_r` and its three companions, unfold it, and `simp only` with the four unfolds every product at once, as `simp only [ZMod.val_add]` unfolded sums. For a fixed `n`, `decide` would check all `(2n)³` cases instead; this is the general proof.
@description
Show that `DihedralGroup.mul` is associative. The context holds the four equations of the table and those five theorems.
-/

/-- @given -/
theorem DihedralGroup.r_mul_r {n : ℕ} [NeZero n] (i j : ZMod n) :
    DihedralGroup.mul (r i) (r j) = r (i + j) := rfl

/-- @given -/
theorem DihedralGroup.r_mul_sr {n : ℕ} [NeZero n] (i j : ZMod n) :
    DihedralGroup.mul (r i) (sr j) = sr (j + -i) := rfl

/-- @given -/
theorem DihedralGroup.sr_mul_r {n : ℕ} [NeZero n] (i j : ZMod n) :
    DihedralGroup.mul (sr i) (r j) = sr (i + j) := rfl

/-- @given -/
theorem DihedralGroup.sr_mul_sr {n : ℕ} [NeZero n] (i j : ZMod n) :
    DihedralGroup.mul (sr i) (sr j) = r (j + -i) := rfl

theorem dihedral_mul_assoc {n : ℕ} [NeZero n] (a b c : DihedralGroup n) :
    DihedralGroup.mul (DihedralGroup.mul a b) c = DihedralGroup.mul a (DihedralGroup.mul b c) := by
  cases a <;> cases b <;> cases c <;> simp only [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
    DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
  · rw [add_assoc]
  · rw [neg_add_rev, add_assoc]
  · rw [add_right_comm]
  · rw [neg_add_rev, neg_neg, add_left_comm]
  · rw [add_assoc]
  · rw [neg_add_rev, add_assoc]
  · rw [add_right_comm]
  · rw [neg_add_rev, neg_neg, add_left_comm]

/-! @end -/

/-!
@problem dihedral_group
@title The Dihedral Group
@concept dihedral_groups

@preamble
With the table as its operation, the trivial rotation `r 0` as its neutral element, and the inverse `(r i)⁻¹ = r (-i)`, `(sr i)⁻¹ = sr i`, since a rotation is undone by the opposite rotation and a reflection by itself, `DihedralGroup n` is a group, Dₙ. Associativity is the previous problem. Each of the other four laws is a check on the two kinds of element, opened by `cases`: a rewrite with the table's equation for the case turns the goal into `r x = r y` or `sr x = sr y`, and a law of the additive group `ZMod n` closes it, `zero_add`, `add_zero`, `neg_add_cancel` or `add_neg_cancel`, with `neg_zero`, `-0 = 0`, where the trivial rotation's step is negated. A function field is defined by cases, `inv | r i => … | sr i => …`. D₄, the symmetries of the square, is not commutative: `r 1 * sr 0 ≠ sr 0 * r 1`, by `decide`.
@description
Supply the instance `Group (DihedralGroup n)`, and show that in `DihedralGroup 4`, `r 1 * sr 0 ≠ sr 0 * r 1`. The context holds `dihedral_mul_assoc`, the four equations of the table, the laws of additive groups and `neg_zero`.
-/

open DihedralGroup in
instance (n : ℕ) [NeZero n] : Group (DihedralGroup n) where
  mul := DihedralGroup.mul
  one := r 0
  inv
    | r i => r (-i)
    | sr i => sr i
  mul_assoc := dihedral_mul_assoc
  one_mul a := by
    cases a with
    | r i => rw [r_mul_r, zero_add]
    | sr i => rw [r_mul_sr, neg_zero, add_zero]
  mul_one a := by
    cases a with
    | r i => rw [r_mul_r, add_zero]
    | sr i => rw [sr_mul_r, add_zero]
  inv_mul_cancel a := by
    cases a with
    | r i => rw [r_mul_r, neg_add_cancel]
    | sr i => rw [sr_mul_sr, add_neg_cancel]
  mul_inv_cancel a := by
    cases a with
    | r i => rw [r_mul_r, add_neg_cancel]
    | sr i => rw [sr_mul_sr, add_neg_cancel]

/-- @spec -/
example : (DihedralGroup.r 1 : DihedralGroup 4) * DihedralGroup.sr 0 = DihedralGroup.sr 3 ∧
    (DihedralGroup.sr 0 : DihedralGroup 4)⁻¹ = DihedralGroup.sr 0 ∧
    (1 : DihedralGroup 4) = DihedralGroup.r 0 := by decide

open DihedralGroup in
theorem d4_not_comm : (r 1 : DihedralGroup 4) * sr 0 ≠ sr 0 * r 1 := by
  decide

/-! @end -/

/-!
@problem dihedral_fintype
@title Counting the Dihedral Group
@concept dihedral_groups

@preamble
Dₙ has `2n` elements, `n` of each kind, and the count is by labelling, as in the first section: an element is a kind, `0` for a rotation and `1` for a reflection, together with a residue, so `DihedralGroup n` is in bijection with `Fin 2 × Fin n`, the residue `i` passing to `⟨i.val, i.val_lt⟩` and back. The inverse function is defined by matching on the pair, `| (0, k) => …` and `| (1, k) => …`, and Lean sees that `Fin 2` leaves no third case; one law is checked by cases on the element, the other by the same match on the pair, each case holding by `rfl`. `card_of_equiv_prod` of the first section then counts `DihedralGroup n` as `2 * n`, once the type has a `Fintype` instance, which `Fintype.ofEquiv` makes from a bijection out of `Fin (2 * n)`: the one built here runs the other way, continued by `finProdFinEquiv`, and `.symm` turns it round. With the instance, `decide` runs through D₄.
@description
Define `DihedralGroup.equivProd n : DihedralGroup n ≃ Fin 2 × Fin n`, supply the instance `Fintype (DihedralGroup n)`, and show that `DihedralGroup n` has `2 * n` elements. The context holds `card_of_equiv_prod` of the first section; Mathlib provides `Fintype.ofEquiv` and `finProdFinEquiv`.
-/

def DihedralGroup.equivProd (n : ℕ) : DihedralGroup n ≃ Fin 2 × Fin n where
  toFun
    | r i => (0, ⟨i.val, i.val_lt⟩)
    | sr i => (1, ⟨i.val, i.val_lt⟩)
  invFun
    | (0, k) => r ⟨k.val, k.isLt⟩
    | (1, k) => sr ⟨k.val, k.isLt⟩
  left_inv a := by
    cases a with
    | r i => rfl
    | sr i => rfl
  right_inv p := by
    match p with
    | (0, k) => rfl
    | (1, k) => rfl

/-- @spec -/
example (n : ℕ) (i : ZMod n) :
    DihedralGroup.equivProd n (DihedralGroup.r i) = (0, ⟨i.val, i.val_lt⟩) ∧
    DihedralGroup.equivProd n (DihedralGroup.sr i) = (1, ⟨i.val, i.val_lt⟩) := ⟨rfl, rfl⟩

instance (n : ℕ) : Fintype (DihedralGroup n) :=
  Fintype.ofEquiv (Fin (2 * n)) ((DihedralGroup.equivProd n).trans finProdFinEquiv).symm

theorem card_dihedral (n : ℕ) : Fintype.card (DihedralGroup n) = 2 * n :=
  card_of_equiv_prod (DihedralGroup.equivProd n)

/-! @end -/

/-!
@problem klein_four
@title The Klein Four-Group
@concept dihedral_groups

@preamble
D₂, the symmetries of a segment, has four elements, `r 0`, `r 1`, `sr 0` and `sr 1`, and is the *Klein four-group* V₄. Each of its elements is its own inverse, a fact about four elements that `decide` checks through the instance of the previous problem; and a group in which every element is its own inverse is commutative, by the theorem of the previous section, so V₄ is a commutative group, unlike D₄. The product of two groups of order two, `ZMod 2 × ZMod 2`, is the Klein four-group as well: the two are the same group under different names, as `ZMod 2` and `Bool` were. `ZMod 4` also has four elements, but its residue `1` is not its own negative, since `1 + 1 = 2`: the two groups of order four differ.
@description
Show that every element of `DihedralGroup 2` is its own inverse, supply the instance `CommGroup (DihedralGroup 2)`, and check that in `ZMod 4` the residue `1` is not its own negative. The context holds `mul_comm_of_inv_eq_self` of the previous section.
-/

theorem klein_inv_self : ∀ x : DihedralGroup 2, x⁻¹ = x := by
  decide

instance : CommGroup (DihedralGroup 2) where
  mul_comm := mul_comm_of_inv_eq_self klein_inv_self

theorem zmod_four_neg_one : -(1 : ZMod 4) ≠ 1 := by
  decide

/-- @spec -/
example (a b : DihedralGroup 2) : a * b = b * a := mul_comm a b

/-! @end -/

end GroupTheory
