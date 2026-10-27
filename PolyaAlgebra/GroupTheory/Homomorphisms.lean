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

/-! @section Homomorphisms -/

universe u v w

namespace GroupTheory

set_option linter.translateGenerateName false

/-!
@concept homomorphisms
@title Homomorphisms
@kind definition

A homomorphism is a function between groups that carries products to products. It is how one group is compared with another, and it carries the neutral element and inverses across as well. Reducing integers modulo `n` and recording whether a symmetry reverses orientation are the first examples.
-/

/-!
@problem group_hom
@title The Definition of a Homomorphism
@concept homomorphisms

@preamble
A *homomorphism* from a group `G` to a group `H` is a function `f : G → H` that carries products to products:
f(ab) = f(a) f(b)

for all `a` and `b`, the product on the left taken in `G` and the one on the right in `H`. Reducing integers modulo `n` is one: the residue of a sum is the sum of the residues.

A homomorphism is a function together with a law, so we make it a structure, as a subgroup was, with the fields `toFun` and `map_mul'`. A homomorphism `f` is applied through its field, `f.toFun a`. We write `G →* H` for `GroupHom G H`, with Mathlib's arrow; Mathlib applies `f` as `f a`, and its definition also asks that `1` go to `1`, which for groups follows from the law.
@description
Define the structure `GroupHom G H` for groups `G` and `H`, with the function `toFun` and the law `map_mul'`, its elements explicit:
```lean
∀ a b : G, toFun (a * b) = toFun a * toFun b
```
-/

structure GroupHom (G : Type u) (H : Type v) [Group G] [Group H] where
  toFun : G → H
  map_mul' : ∀ a b : G, toFun (a * b) = toFun a * toFun b

/-- @spec -/
example {G : Type u} {H : Type v} [Group G] [Group H] (f : GroupHom G H) : G → H := f.toFun

/-- @spec -/
example {G : Type u} {H : Type v} [Group G] [Group H] (f : GroupHom G H) (a b : G) :
    f.toFun (a * b) = f.toFun a * f.toFun b := by
  have h := @GroupHom.map_mul' G H _ _ f a b
  grind

/-! @end -/

/-- `G →* H`: the homomorphisms from the group `G` to the group `H`, as Mathlib writes them. -/
infixr:25 " →* " => GroupHom

/-!
@problem add_group_hom
@title Additive Homomorphisms
@concept homomorphisms

@preamble
A homomorphism of additive groups carries sums to sums, f(a + b) = f(a) + f(b). We write `AddGroupHom A B`, or `A →+ B`, with the fields `toFun` and `map_add'`. It is the previous definition written additively, as `AddSubgroup` was `Subgroup`. Lean is told that `AddGroupHom` is the additive version of `GroupHom`, so each theorem about homomorphisms below comes with its additive version.
@description
Define the structure `AddGroupHom A B` with the fields `toFun` and `map_add'`, written as those of `GroupHom` are.
-/

structure AddGroupHom (A : Type u) (B : Type v) [AddGroup A] [AddGroup B] where
  toFun : A → B
  map_add' : ∀ a b : A, toFun (a + b) = toFun a + toFun b

/-- @spec -/
example {A : Type u} {B : Type v} [AddGroup A] [AddGroup B] (f : AddGroupHom A B) : A → B :=
  f.toFun

/-- @spec -/
example {A : Type u} {B : Type v} [AddGroup A] [AddGroup B] (f : AddGroupHom A B) (a b : A) :
    f.toFun (a + b) = f.toFun a + f.toFun b := by
  have h := @AddGroupHom.map_add' A B _ _ f a b
  grind

/-! @end -/

/-- `A →+ B`: the homomorphisms from the additive group `A` to the additive group `B`. -/
infixr:25 " →+ " => AddGroupHom

attribute [to_additive existing AddGroupHom] GroupHom

/-!
@problem map_one
@title A Homomorphism Preserves the Neutral Element and Inverses
@concept homomorphisms

@preamble
The definition asks only about products, but a homomorphism also carries `1` to `1` and inverses to inverses. For `1`, the element `f 1` satisfies `f 1 * f 1 = f (1 * 1) = f 1`, and an element `b` with `a * b = a` is `1`, by `mul_eq_left` of the second section:
```lean
theorem GroupHom.map_one (f : G →* H) : f.toFun 1 = 1 := by
  have h : f.toFun 1 * f.toFun 1 = f.toFun 1 := by
    calc f.toFun 1 * f.toFun 1 = f.toFun (1 * 1) := by rw [f.map_mul]
      _ = f.toFun 1 := by rw [one_mul]
  exact mul_eq_left.mp h
```
Here `f.map_mul` is the law `map_mul'` restated. For inverses, the uniqueness of inverses does the work: to show that an element is the inverse of `f a`, it is enough to multiply it by `f a`. The additive versions are `AddGroupHom.map_zero` and `AddGroupHom.map_neg`.
@description
Show that the value `f.toFun a⁻¹` at `a⁻¹` is `(f.toFun a)⁻¹`, for every homomorphism `f`, under the name `GroupHom.map_inv`. The context holds `GroupHom.map_one`, `GroupHom.map_mul`, `inv_eq_of_mul_eq_one_right` and `mul_inv_cancel`.
-/

/-- @given -/
@[to_additive AddGroupHom.map_add]
theorem GroupHom.map_mul {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) (a b : G) :
    f.toFun (a * b) = f.toFun a * f.toFun b :=
  f.map_mul' a b

/-- @given -/
@[to_additive AddGroupHom.map_zero]
theorem GroupHom.map_one {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) :
    f.toFun 1 = 1 := by
  have h : f.toFun 1 * f.toFun 1 = f.toFun 1 := by
    calc f.toFun 1 * f.toFun 1 = f.toFun (1 * 1) := by rw [f.map_mul]
      _ = f.toFun 1 := by rw [one_mul]
  exact mul_eq_left.mp h

@[to_additive AddGroupHom.map_neg]
theorem GroupHom.map_inv {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) (a : G) :
    f.toFun a⁻¹ = (f.toFun a)⁻¹ := by
  apply Eq.symm
  apply inv_eq_of_mul_eq_one_right
  rw [← f.map_mul, mul_inv_cancel, f.map_one]

/-! @end -/

/-!
@problem map_pow
@title A Homomorphism Preserves Powers
@concept homomorphisms

@preamble
A homomorphism carries powers to powers: f(aⁿ) = f(a)ⁿ. For a natural exponent the power is a product of `n` copies, and `f` carries each product across. For an integer exponent a negative power is the inverse of a natural one, and `f` carries inverses across too; a non-negative integer power is the natural power by definition, though Lean prints it `a ^ Int.ofNat n`. The additive versions, `AddGroupHom.map_nsmul` and `AddGroupHom.map_zsmul`, say that a homomorphism of additive groups carries multiples to multiples. The context holds `pow_zero`, `pow_succ` and `zpow_negSucc` of the section on powers, and `GroupHom.map_one`, `GroupHom.map_mul` and `GroupHom.map_inv`.
@description
Show that `f.toFun (a ^ n) = f.toFun a ^ n` for every natural number `n`, and the same for every integer exponent, under the names `GroupHom.map_pow` and `GroupHom.map_zpow`.
-/

@[to_additive AddGroupHom.map_nsmul]
theorem GroupHom.map_pow {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) (a : G)
    (n : ℕ) : f.toFun (a ^ n) = f.toFun a ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, f.map_one]
  | succ n ih => rw [pow_succ, pow_succ, f.map_mul, ih]

@[to_additive AddGroupHom.map_zsmul]
theorem GroupHom.map_zpow {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) (a : G)
    (k : ℤ) : f.toFun (a ^ k) = f.toFun a ^ k := by
  cases k with
  | ofNat n => exact f.map_pow a n
  | negSucc n => rw [zpow_negSucc, zpow_negSucc, f.map_inv, f.map_pow]

/-! @end -/

/-!
@problem comp
@title The Standard Homomorphisms
@concept homomorphisms

@preamble
Some homomorphisms exist for every group. Two homomorphisms `f : G →* H` and `g : H →* K` compose to `g.comp f : G →* K`, which applies `f` first, as the composite `g ∘ f` of two functions does: `f` carries a product to a product, and `g` carries that one on. The identity function of `G` is a homomorphism, `GroupHom.id G`. The projection of a product onto its first factor is one too, `GroupHom.fst G H : G × H →* G`, since the first component of a product of pairs is the product of the first components, which holds by definition. A definition whose value is a structure is written with `where`, one line per field, as the subgroups were.
@description
Define `GroupHom.comp g f`, `GroupHom.id G` and `GroupHom.fst G H`, keeping the `@[to_additive]` lines.
-/

@[to_additive AddGroupHom.comp]
def GroupHom.comp {G : Type u} {H : Type v} {K : Type w} [Group G] [Group H] [Group K]
    (g : H →* K) (f : G →* H) : G →* K where
  toFun x := g.toFun (f.toFun x)
  map_mul' a b := by
    rw [f.map_mul, g.map_mul]

@[to_additive AddGroupHom.id]
def GroupHom.id (G : Type u) [Group G] : G →* G where
  toFun x := x
  map_mul' _ _ := rfl

@[to_additive AddGroupHom.fst]
def GroupHom.fst (G : Type u) (H : Type v) [Group G] [Group H] : G × H →* G where
  toFun a := a.1
  map_mul' _ _ := rfl

/-- @spec -/
example {G : Type u} {H : Type v} {K : Type w} [Group G] [Group H] [Group K] (g : H →* K)
    (f : G →* H) (x : G) (y : G × H) :
    (g.comp f).toFun x = g.toFun (f.toFun x) ∧ (GroupHom.id G).toFun x = x ∧
    (GroupHom.fst G H).toFun y = y.1 :=
  ⟨rfl, rfl, rfl⟩

/-! @end -/

/-!
@problem zmod_reductions
@title Reduction Modulo n
@concept homomorphisms

@preamble
Reducing a residue modulo `6` to a residue modulo `2` is a homomorphism `ZMod 6 →+ ZMod 2`: the parity of a sum is determined by the parities of its terms. It works because `2` divides `6`; reducing modulo `5` to modulo `2` would not, since `4 + 3 = 2` in `ZMod 5`. The residue with value `a.val % 2` is `toFin 2 a.val`, with `toFin` of the first section.
Reducing an integer modulo `n` is a homomorphism `ℤ →+ ZMod n`. We send the integer `k` to the multiple `k • 1` of the residue `1`, which is the residue of `k`, since `k • 1` adds `k` copies of `1`. In `ZMod 6` the integer `-1` goes to `5`. The context holds `add_zsmul` of the section on powers:
```lean
theorem add_zsmul (g : A) (m n : ℤ) : (m + n) • g = m • g + n • g
```
@description
Define `zmodSixToTwo`, the homomorphism `ZMod 6 →+ ZMod 2` sending `a` to `toFin 2 a.val`; and define `intToZMod n : ℤ →+ ZMod n`, sending `k` to `k • 1`. Check that `zmodSixToTwo` sends `5` to `1`, and that `intToZMod 6` sends `-1` to `5`.
-/

def zmodSixToTwo : AddGroupHom (ZMod 6) (ZMod 2) where
  toFun a := toFin 2 a.val
  map_add' := by decide

def intToZMod (n : ℕ) [NeZero n] : ℤ →+ ZMod n where
  toFun k := k • 1
  map_add' a b := add_zsmul 1 a b

/-- @spec -/
example : ∀ a : ZMod 6, (zmodSixToTwo.toFun a).val = a.val % 2 := by decide

/-- @spec -/
example (n : ℕ) [NeZero n] (k : ℤ) : (intToZMod n).toFun k = k • 1 := rfl

theorem zmodSixToTwo_five : zmodSixToTwo.toFun 5 = 1 := by
  decide

theorem intToZMod_six_neg_one : (intToZMod 6).toFun (-1) = 5 := by
  decide

/-! @end -/

/-!
@problem orientation
@title The Orientation of a Symmetry
@concept homomorphisms

@preamble
A symmetry of the `n`-gon either keeps the orientation of the `n`-gon, as a rotation does, or reverses it, as a reflection does. Composing two symmetries composes these effects, and two reversals make a keeping. We record the effect in the symmetric group on two points, `Equiv.Perm (Fin 2)`: a rotation goes to `1`, and a reflection to the permutation `swap2` that exchanges `0` and `1`. The context holds `swap2`, with `swap2 * swap2 = 1` as `swap2_mul_self`, and `swap2 ≠ 1` as `swap2_ne_one`.

A function on `DihedralGroup n` is defined by its two cases, as the inverse of the dihedral group was. A product in `DihedralGroup n` is given by the four lines of the table, so the law is a statement about each line; Lean computes a product of two symmetries written as constructors, and the value of the orientation at it.
@description
Define the homomorphism `DihedralGroup.orientation n` from Dₙ to the permutations of `Fin 2`, sending each rotation to `1` and each reflection to `swap2`.
-/

/-- @given -/
def swap2 : Equiv.Perm (Fin 2) where
  toFun i := i + 1
  invFun i := i + 1
  left_inv := by decide
  right_inv := by decide

/-- @given -/
theorem swap2_mul_self : swap2 * swap2 = 1 := by
  decide

/-- @given -/
theorem swap2_ne_one : swap2 ≠ 1 := by
  decide

open DihedralGroup in
def DihedralGroup.orientation (n : ℕ) [NeZero n] : DihedralGroup n →* Equiv.Perm (Fin 2) where
  toFun
    | r _ => 1
    | sr _ => swap2
  map_mul' a b := by
    cases a <;> cases b
    · rfl
    · rfl
    · rfl
    · exact swap2_mul_self.symm

/-- @spec -/
example (n : ℕ) [NeZero n] (i : ZMod n) :
    (DihedralGroup.orientation n).toFun (DihedralGroup.r i) = 1 ∧
    (DihedralGroup.orientation n).toFun (DihedralGroup.sr i) = swap2 :=
  ⟨rfl, rfl⟩

/-! @end -/

/-!
@concept isomorphisms
@title Isomorphisms
@kind definition

An isomorphism is a homomorphism that is a bijection, and its inverse is a homomorphism too. Isomorphic groups differ only in the names of their elements: they have the same number of elements and share every property stated through the operation. It is the subject's notion of sameness of groups.
-/

/-!
@problem group_iso
@title The Definition of an Isomorphism
@concept isomorphisms

@preamble
An *isomorphism* from `G` to `H` is a homomorphism that is a bijection. It matches the elements of `G` with those of `H` so that the two tables agree, as the matching of `ZMod 2` with `Bool` did in the third section.

The first section packaged a bijection with its inverse as an equivalence `G ≃ H`, with the fields `toFun`, `invFun`, `left_inv` and `right_inv`. An isomorphism is an equivalence with one more field, `map_mul'`, as a commutative group was a group with one more law. So the structure extends the structure of equivalences:
```lean
structure GroupIso (G : Type u) (H : Type v) [Group G] [Group H]
    extends G ≃ H where
```
followed by the new field alone. The fields of the equivalence are reached directly, as `e.toFun` and `e.invFun`, and the equivalence itself is `e.toEquiv`. We write `G ≃* H`, Mathlib's notation.
@description
Define the structure `GroupIso G H`, extending `G ≃ H` by the law `map_mul'`, with the elements explicit as in `GroupHom`.
-/

structure GroupIso (G : Type u) (H : Type v) [Group G] [Group H] extends G ≃ H where
  map_mul' : ∀ a b : G, toFun (a * b) = toFun a * toFun b

/-- @spec -/
example {G : Type u} {H : Type v} [Group G] [Group H] (e : GroupIso G H) : G ≃ H := e.toEquiv

/-- @spec -/
example {G : Type u} {H : Type v} [Group G] [Group H] (e : GroupIso G H) (a b : G) :
    e.toFun (a * b) = e.toFun a * e.toFun b := by
  have h := @GroupIso.map_mul' G H _ _ e a b
  first
  | exact h
  | exact h.symm
  | grind

/-! @end -/

/-- `G ≃* H`: the isomorphisms from the group `G` to the group `H`, as Mathlib writes them. -/
infixl:25 " ≃* " => GroupIso

/-!
@problem add_group_iso
@title Additive Isomorphisms
@concept isomorphisms

@preamble
An isomorphism of additive groups carries sums to sums: `AddGroupIso A B`, written `A ≃+ B`, extends `A ≃ B` by the law `map_add'`. It is the previous definition written additively, as `AddGroupHom` was `GroupHom`. Lean is told that `AddGroupIso` is the additive version of `GroupIso`, so each theorem about isomorphisms below comes with its additive version.
@description
Define the structure `AddGroupIso A B`, extending `A ≃ B` by `map_add'`, written as `GroupIso` is.
-/

structure AddGroupIso (A : Type u) (B : Type v) [AddGroup A] [AddGroup B] extends A ≃ B where
  map_add' : ∀ a b : A, toFun (a + b) = toFun a + toFun b

/-- @spec -/
example {A : Type u} {B : Type v} [AddGroup A] [AddGroup B] (e : AddGroupIso A B) : A ≃ B :=
  e.toEquiv

/-- @spec -/
example {A : Type u} {B : Type v} [AddGroup A] [AddGroup B] (e : AddGroupIso A B) (a b : A) :
    e.toFun (a + b) = e.toFun a + e.toFun b := by
  have h := @AddGroupIso.map_add' A B _ _ e a b
  first
  | exact h
  | exact h.symm
  | grind

/-! @end -/

/-- `A ≃+ B`: the isomorphisms from the additive group `A` to the additive group `B`. -/
infixl:25 " ≃+ " => AddGroupIso

attribute [to_additive existing AddGroupIso] GroupIso

attribute [to_additive existing AddGroupIso.toEquiv] GroupIso.toEquiv

/-!
@problem zmod_two_iso_bool
@title The Groups of Order Two Are Isomorphic
@concept isomorphisms

@preamble
The first isomorphism is already half built. The third section matched `ZMod 2` with `Bool` by the equivalence `zmodTwoEquivBool`, which sends `0` to `false` and `1` to `true`, and proved that it carries the addition of the one to the addition of the other, as `zmodTwoEquivBool_add`. Together the two are an isomorphism `ZMod 2 ≃+ Bool`: the two groups of order two are one group under two sets of names. Its inverse function `invFun` renames the Booleans back as residues.

A value of a structure that extends another is written with `where` and a line for the structure it extends, `toEquiv := …`, beside the new field.
@description
Define `zmodTwoIsoBool : ZMod 2 ≃+ Bool` from `zmodTwoEquivBool` and its law, and check that its inverse function sends `true` to `1`.
-/

def zmodTwoIsoBool : ZMod 2 ≃+ Bool where
  toEquiv := zmodTwoEquivBool
  map_add' := zmodTwoEquivBool_add

/-- @spec -/
example : zmodTwoIsoBool.toFun 0 = false ∧ zmodTwoIsoBool.toFun 1 = true := by
  decide

theorem zmodTwoIsoBool_invFun_true : zmodTwoIsoBool.invFun true = 1 := by
  decide

/-! @end -/

/-!
@problem group_iso_symm
@title The Inverse of an Isomorphism
@concept isomorphisms

@preamble
An isomorphism is a homomorphism once its inverse function is forgotten: `e.toGroupHom : G →* H`, with the same function. Its inverse function `e.invFun` is a homomorphism too, so that `e.symm : H ≃* G` is an isomorphism with the roles of `toFun` and `invFun` exchanged. Its law holds because `e.toFun` sends both `e.invFun (a * b)` and `e.invFun a * e.invFun b` to `a * b`, and two elements with the same image under `e.toFun` are equal. The laws of the equivalence read
```lean
e.left_inv x : e.invFun (e.toFun x) = x
e.right_inv y : e.toFun (e.invFun y) = y
```
and `rw` uses them as equations. The additive versions are `AddGroupIso.toAddGroupHom` and `AddGroupIso.symm`.
@description
Define `GroupIso.toGroupHom e` and `GroupIso.symm e`, keeping the `@[to_additive]` lines.
-/

@[to_additive AddGroupIso.toAddGroupHom]
def GroupIso.toGroupHom {G : Type u} {H : Type v} [Group G] [Group H] (e : G ≃* H) : G →* H where
  toFun := e.toFun
  map_mul' := e.map_mul'

@[to_additive AddGroupIso.symm]
def GroupIso.symm {G : Type u} {H : Type v} [Group G] [Group H] (e : G ≃* H) : H ≃* G where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv
  map_mul' a b := by
    have h : e.toFun (e.invFun a * e.invFun b) = a * b := by
      rw [e.map_mul', e.right_inv a, e.right_inv b]
    rw [← h, e.left_inv]

/-- @spec -/
example {G : Type u} {H : Type v} [Group G] [Group H] (e : G ≃* H) (x : G) (y : H) :
    e.toGroupHom.toFun x = e.toFun x ∧ e.symm.toFun y = e.invFun y ∧ e.symm.invFun x = e.toFun x :=
  ⟨rfl, rfl, rfl⟩

/-! @end -/

/-!
@problem group_iso_invariants
@title Isomorphic Groups Share Their Properties
@concept isomorphisms

@preamble
Isomorphic groups differ only in the names of their elements, so whatever is said through the operation holds in both. Isomorphic finite groups have the same number of elements, since an equivalence matches their elements one for one, as `Fintype.card_congr` of the first section counts. And a group isomorphic to a commutative group is commutative: two elements `x` and `y` of `H` are the images of `e.invFun x` and `e.invFun y`, and those commute in `G`. The additive versions are `AddGroupIso.card_eq` and `AddGroupIso.add_comm`.
@description
Show that isomorphic finite groups have the same number of elements, under the name `GroupIso.card_eq`, and that if `a * b = b * a` for all `a` and `b` in `G`, then `x * y = y * x` for all `x` and `y` in `H`, under the name `GroupIso.mul_comm`.
-/

@[to_additive AddGroupIso.card_eq]
theorem GroupIso.card_eq {G : Type u} {H : Type v} [Group G] [Group H] [Fintype G] [Fintype H]
    (e : G ≃* H) : Fintype.card G = Fintype.card H :=
  Fintype.card_congr e.toEquiv

@[to_additive AddGroupIso.add_comm]
theorem GroupIso.mul_comm {G : Type u} {H : Type v} [Group G] [Group H] (e : G ≃* H)
    (h : ∀ a b : G, a * b = b * a) (x y : H) : x * y = y * x := by
  rw [← e.right_inv x, ← e.right_inv y, ← e.map_mul', ← e.map_mul', h]

/-! @end -/

/-!
@problem klein_not_zmod_four
@title Two Groups of Order Four
@concept isomorphisms

@preamble
`ZMod 2 × ZMod 2` and `ZMod 4` both have four elements, but they are not isomorphic. In the first, every element added to itself gives `0`. In the second, `1 + 1 = 2`. An isomorphism would carry the first property to the second group. The first group is isomorphic to the Klein four-group of the third section, written additively.

We write that no isomorphism exists as
```lean
¬ Nonempty (ZMod 2 × ZMod 2 ≃+ ZMod 4)
```
with `Nonempty` met in the first section, and `intro ⟨e⟩` takes a supposed isomorphism out. `decide` cannot range over `ZMod 2 × ZMod 2`, which has no count, but it can range over residues `x` and `y` in `ZMod 2`. The context holds `GroupHom.map_one` and `GroupIso.toGroupHom`; a theorem about homomorphisms applies to `e` through `e.toGroupHom`, whose function is `e.toFun` only by definition, so `exact` matches it where `rw` does not.
@description
Show that if `a * a = 1` for every `a` in `G`, and `G ≃* H`, then `y * y = 1` for every `y` in `H`, under the name `GroupIso.mul_self_eq_one`. Show that `(x, y) + (x, y) = 0` for all `x` and `y` in `ZMod 2`, and that `ZMod 2 × ZMod 2` is not isomorphic to `ZMod 4`.
-/

@[to_additive AddGroupIso.add_self_eq_zero]
theorem GroupIso.mul_self_eq_one {G : Type u} {H : Type v} [Group G] [Group H] (e : G ≃* H)
    (h : ∀ a : G, a * a = 1) (y : H) : y * y = 1 := by
  rw [← e.right_inv y, ← e.map_mul', h]
  exact e.toGroupHom.map_one

theorem zmod_two_prod_add_self : ∀ x y : ZMod 2, ((x, y) + (x, y) : ZMod 2 × ZMod 2) = 0 := by
  decide

theorem not_nonempty_addGroupIso_zmod_four : ¬ Nonempty (ZMod 2 × ZMod 2 ≃+ ZMod 4) := by
  intro ⟨e⟩
  have h := e.add_self_eq_zero (fun a => zmod_two_prod_add_self a.1 a.2) 1
  exact absurd h (by decide)

/-! @end -/

/-!
@concept kernels_and_images
@title Kernels and Images
@kind definition

The kernel of a homomorphism is the set of elements it sends to the neutral element, and its image is the set of values it takes; both are subgroups. A homomorphism is injective exactly when its kernel is trivial, and surjective exactly when its image is everything, so the two subgroups say what a homomorphism forgets and what it reaches.
-/

/-!
@problem ker
@title The Kernel of a Homomorphism
@concept kernels_and_images

@preamble
The *kernel* of a homomorphism `f : G →* H` is the set of elements it sends to `1`:
```lean
{x | f.toFun x = 1}
```
It is a subgroup of `G`: `f` sends `1` to `1`, and it sends products and inverses of elements of the kernel to products and inverses of `1`. We write it `f.ker`, for `GroupHom.ker f`, and its additive version, the elements sent to `0`, is `AddGroupHom.ker`. A hypothesis `ha : a ∈ f.ker` is the equation it abbreviates, and `change` restates a goal `a * b ∈ f.ker` as the equation `f.toFun (a * b) = 1`. The context holds `GroupHom.map_one`, `GroupHom.map_mul`, `GroupHom.map_inv`, `one_mul` and `inv_one`.
@description
Define `GroupHom.ker f`, the subgroup with that carrier, and prove `GroupHom.mem_ker`, which says that `x ∈ f.ker` exactly when `f.toFun x = 1`; it holds by definition.
-/

@[to_additive AddGroupHom.ker]
def GroupHom.ker {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) : Subgroup G where
  carrier := {x | f.toFun x = 1}
  one_mem' := f.map_one
  mul_mem' := by
    intro a b ha hb
    change f.toFun (a * b) = 1
    rw [f.map_mul, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    change f.toFun a⁻¹ = 1
    rw [f.map_inv, ha, inv_one]

/-- @spec -/
example {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) (x : G) :
    x ∈ f.ker ↔ f.toFun x = 1 := by
  constructor
  · intro h
    change _ = _ at h
    grind
  · intro h
    change _ = _
    grind

@[to_additive AddGroupHom.mem_ker]
theorem GroupHom.mem_ker {G : Type u} {H : Type v} [Group G] [Group H] {f : G →* H} {x : G} :
    x ∈ f.ker ↔ f.toFun x = 1 :=
  Iff.rfl

/-! @end -/

/-!
@problem range
@title The Image of a Homomorphism
@concept kernels_and_images

@preamble
The *image* of a homomorphism `f : G →* H` is the set of its values, a subgroup of `H`:
```lean
{y | ∃ x, f.toFun x = y}
```
Mathlib calls it the range, `f.range`, as it called the set of values of a function `Set.range` in the first section; its additive version is `AddGroupHom.range`. A homomorphism is surjective exactly when its image is the whole group `⊤`. The context holds `GroupHom.map_one`, `GroupHom.map_mul`, `GroupHom.map_inv`, `Subgroup.ext` and `Subgroup.mem_top`.
@description
Define `GroupHom.range f`, the subgroup with that carrier, and prove `GroupHom.mem_range`, which holds by definition. Show that `f.range = ⊤` exactly when `f.toFun` is surjective, under the name `GroupHom.range_eq_top`.
-/

@[to_additive AddGroupHom.range]
def GroupHom.range {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) : Subgroup H where
  carrier := {y | ∃ x, f.toFun x = y}
  one_mem' := ⟨1, f.map_one⟩
  mul_mem' := by
    intro a b ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x * y, by rw [f.map_mul, hx, hy]⟩
  inv_mem' := by
    intro a ⟨x, hx⟩
    exact ⟨x⁻¹, by rw [f.map_inv, hx]⟩

/-- @spec -/
example {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) (y : H) :
    y ∈ f.range ↔ ∃ x, f.toFun x = y := by
  constructor
  · intro ⟨x, hx⟩
    exact ⟨x, by grind⟩
  · intro ⟨x, hx⟩
    exact ⟨x, by grind⟩

@[to_additive AddGroupHom.mem_range]
theorem GroupHom.mem_range {G : Type u} {H : Type v} [Group G] [Group H] {f : G →* H} {y : H} :
    y ∈ f.range ↔ ∃ x, f.toFun x = y :=
  Iff.rfl

@[to_additive AddGroupHom.range_eq_top]
theorem GroupHom.range_eq_top {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) :
    f.range = ⊤ ↔ Function.Surjective f.toFun := by
  constructor
  · intro h y
    have hy : y ∈ f.range := by
      rw [h]
      exact Subgroup.mem_top y
    exact GroupHom.mem_range.mp hy
  · intro h
    apply Subgroup.ext
    intro y
    constructor
    · intro _
      exact Subgroup.mem_top y
    · intro _
      exact h y

/-! @end -/

/-!
@problem ker_eq_bot_iff
@title A Homomorphism With Trivial Kernel Is Injective
@concept kernels_and_images

@preamble
To test whether a homomorphism is injective, it is enough to look at what it sends to `1`. If `f a = f b`, then `f` sends `a * b⁻¹` to `f a * (f b)⁻¹`, which is `1`: so `a * b⁻¹` is in the kernel. When the kernel is `⊥`, that makes `a * b⁻¹ = 1`, and then `a = b`. Conversely, an injective homomorphism sends nothing but `1` to `1`, since it already sends `1` there. The additive version is `AddGroupHom.ker_eq_bot_iff`. The context holds `Subgroup.ext`, `Subgroup.mem_bot`, `GroupHom.mem_ker`, `GroupHom.map_one`, `GroupHom.map_mul`, `GroupHom.map_inv`, `mul_inv_cancel`, `inv_mul_cancel_right` and `one_mul`.
@description
Show that `f.ker = ⊥` exactly when `f.toFun` is injective, under the name `GroupHom.ker_eq_bot_iff`.
-/

@[to_additive AddGroupHom.ker_eq_bot_iff]
theorem GroupHom.ker_eq_bot_iff {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) :
    f.ker = ⊥ ↔ Function.Injective f.toFun := by
  constructor
  · intro h a b hab
    have hk : a * b⁻¹ ∈ f.ker := by
      rw [GroupHom.mem_ker, f.map_mul, f.map_inv, hab, mul_inv_cancel]
    rw [h, Subgroup.mem_bot] at hk
    rw [← inv_mul_cancel_right a b, hk, one_mul]
  · intro h
    apply Subgroup.ext
    intro x
    rw [GroupHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hx
      apply h
      rw [hx, f.map_one]
    · intro hx
      rw [hx, f.map_one]

/-! @end -/

/-!
@problem kernel_examples
@title The Kernels of the Reduction and the Orientation
@concept kernels_and_images

@preamble
The reduction `zmodSixToTwo` sends a residue modulo `6` to `0` exactly when it is even, so its kernel is the subgroup `zmodSixEvens` of the previous section. The orientation of Dₙ sends a symmetry to `1` exactly when it keeps the orientation, so its kernel is the subgroup of rotations. The image of `zmodSixToTwo` is the whole of `ZMod 2`, since `1` is the residue of `1`.

A statement about membership in the kernel of a map of `ZMod 6` is a statement about finitely many residues once the memberships are written out as what they say, as for the centres of D₃ and D₄: `decide` refuses a goal about a variable named by `intro`, and `simp only` rewrites the memberships under the `∀` instead. The context holds `AddGroupHom.range_eq_top`, `AddSubgroup.ext`, `Subgroup.ext`, `AddGroupHom.mem_ker`, `GroupHom.mem_ker`, `mem_zmodSixEvens`, `r_mem_rotations`, `sr_not_mem_rotations` and `swap2_ne_one`.
@description
Show that the kernel of `zmodSixToTwo` is `zmodSixEvens` and its image is `⊤`, and that the kernel of `DihedralGroup.orientation n` is `DihedralGroup.rotations n`.
-/

theorem ker_zmodSixToTwo : zmodSixToTwo.ker = zmodSixEvens := by
  apply AddSubgroup.ext
  simp only [AddGroupHom.mem_ker, mem_zmodSixEvens]
  decide

theorem range_zmodSixToTwo : zmodSixToTwo.range = ⊤ := by
  rw [AddGroupHom.range_eq_top]
  decide

open DihedralGroup in
theorem ker_orientation (n : ℕ) [NeZero n] : (orientation n).ker = rotations n := by
  apply Subgroup.ext
  intro x
  rw [GroupHom.mem_ker]
  cases x with
  | r i =>
    constructor
    · intro _
      exact r_mem_rotations i
    · intro _
      rfl
  | sr i =>
    constructor
    · intro h
      exact absurd h swap2_ne_one
    · intro h
      exact absurd h (sr_not_mem_rotations i)

/-! @end -/

/-!
@problem int_to_zmod_nat_mem_ker
@title The Natural Numbers in the Kernel of Reduction
@concept kernels_and_images

@preamble
An integer reduces to `0` modulo `n` exactly when `n` divides it. For a natural number `m` this is a fact about remainders: `intToZMod n` sends `m` to `m • 1`, whose value is `m % n`, by `ZMod.val_nsmul_one` of the previous section, and a remainder is `0` exactly when `n` divides. The integer `m` is written `(m : ℤ)`, the cast of the first section, and `natCast_zsmul` of the section on powers turns its multiple into a natural one. A membership in a kernel is an equation of residues, and two residues are equal when their values are. Core Lean has
```lean
theorem Nat.dvd_of_mod_eq_zero {m n : ℕ} (h : n % m = 0) : m ∣ n
theorem Nat.mod_eq_zero_of_dvd {m n : ℕ} (h : m ∣ n) : n % m = 0
```
The context holds `AddGroupHom.mem_ker`, `ZMod.val_zero` and `Fin.ext`.
@description
Show that `(m : ℤ) ∈ (intToZMod n).ker` exactly when `n ∣ m`, for every natural number `m`.
-/

theorem intToZMod_natCast_mem_ker {n : ℕ} [NeZero n] (m : ℕ) :
    (m : ℤ) ∈ (intToZMod n).ker ↔ n ∣ m := by
  rw [AddGroupHom.mem_ker]
  change (m : ℤ) • (1 : ZMod n) = 0 ↔ n ∣ m
  rw [natCast_zsmul]
  constructor
  · intro h
    apply Nat.dvd_of_mod_eq_zero
    rw [← ZMod.val_nsmul_one, h, ZMod.val_zero, Nat.zero_mod]
  · intro h
    apply Fin.ext
    rw [ZMod.val_nsmul_one, ZMod.val_zero, Nat.zero_mod]
    exact Nat.mod_eq_zero_of_dvd h

/-! @end -/

/-!
@problem ker_int_to_zmod
@title The Kernel of Reduction Modulo n
@concept kernels_and_images

@preamble
The kernel of reduction modulo `n` is `nℤ`, the subgroup `intMultiples n` of the previous section. The previous problem settles the natural numbers. A negative integer is the negative of a natural number, and two facts carry the question across: a subgroup contains an element exactly when it contains its inverse, and `n` divides an integer exactly when it divides its negative. Core Lean has `Int.dvd_neg : a ∣ -b ↔ a ∣ b` and
```lean
theorem Int.negSucc_eq (n : ℕ) : Int.negSucc n = -(↑n + 1)
theorem Int.natCast_add_one (n : ℕ) : ((n + 1 : ℕ) : ℤ) = ↑n + 1
theorem Int.natCast_dvd_natCast {m n : ℕ} : (↑m ∣ ↑n) ↔ m ∣ n
```
and `Int.ofNat_eq_natCast : Int.ofNat m = ↑m`. The context holds `intToZMod_natCast_mem_ker`, `mem_intMultiples`, `AddSubgroup.ext`, `Subgroup.inv_mem`, `neg_neg` and `inv_inv`.
@description
Show that `x⁻¹ ∈ H` exactly when `x ∈ H`, for a subgroup `H`, under the name `Subgroup.inv_mem_iff`, and that the kernel of `intToZMod n` is `intMultiples n`.
-/

@[to_additive AddSubgroup.neg_mem_iff]
theorem Subgroup.inv_mem_iff {G : Type u} [Group G] (H : Subgroup G) {x : G} : x⁻¹ ∈ H ↔ x ∈ H := by
  constructor
  · intro h
    rw [← inv_inv x]
    exact H.inv_mem h
  · intro h
    exact H.inv_mem h

theorem ker_intToZMod (n : ℕ) [NeZero n] : (intToZMod n).ker = intMultiples n := by
  apply AddSubgroup.ext
  intro k
  rw [mem_intMultiples]
  cases k with
  | ofNat m =>
    rw [Int.ofNat_eq_natCast, intToZMod_natCast_mem_ker, Int.natCast_dvd_natCast]
  | negSucc m =>
    rw [Int.negSucc_eq, ← AddSubgroup.neg_mem_iff, neg_neg, Int.dvd_neg, ← Int.natCast_add_one,
      intToZMod_natCast_mem_ker, Int.natCast_dvd_natCast]

/-! @end -/

/-!
@problem to_perm3
@title The Symmetries of the Triangle as Permutations
@concept kernels_and_images

@preamble
A symmetry of the triangle moves its vertices `0`, `1` and `2`. The rotation `r i` turns them `i` steps, `rot3 ^ i.val`; the reflection `sr i` turns them `i` steps and then reflects through the vertex `0`, `reflect3 * rot3 ^ i.val`, with the right factor acting first. This is a homomorphism from D₃ to the symmetric group on three points, and its law is a statement about the thirty-six pairs of symmetries.

Its kernel is `⊥`: different symmetries move the vertices differently. So D₃ is isomorphic to its image. The image has six elements, and so has the symmetric group on three points, `3! = 6`, a count this subject does not make; the image is therefore the whole of it, and D₃ is S₃ under other names. On a finite type, `decide` checks that a function is injective.
@description
Define the homomorphism `DihedralGroup.toPerm3` from D₃ to the permutations of `Fin 3`, sending `r i` to `rot3 ^ i.val` and `sr i` to `reflect3 * rot3 ^ i.val`, and show that its kernel is `⊥`. The context holds `GroupHom.ker_eq_bot_iff`.
-/

open DihedralGroup in
def DihedralGroup.toPerm3 : DihedralGroup 3 →* Equiv.Perm (Fin 3) where
  toFun
    | r i => rot3 ^ i.val
    | sr i => reflect3 * rot3 ^ i.val
  map_mul' := by
    decide

/-- @spec -/
example : DihedralGroup.toPerm3.toFun (DihedralGroup.r 1) = rot3 ∧
    DihedralGroup.toPerm3.toFun (DihedralGroup.sr 0) = reflect3 := by
  decide

theorem ker_toPerm3 : DihedralGroup.toPerm3.ker = ⊥ := by
  rw [GroupHom.ker_eq_bot_iff]
  decide

/-! @end -/

/-!
@concept cayley
@title Cayley's Theorem
@kind theorem

Every group is a group of permutations. An element acts on the group by multiplying on the left, which permutes the elements, and this gives an injective homomorphism from the group into the permutations of its elements. So the symmetric groups contain every group, each finite group inside one of finite order.
-/

/-!
@problem mul_left
@title Left Multiplication as a Permutation
@concept cayley

@preamble
The second section showed that `x ↦ g * x` is a bijection of `G`, and `x ↦ g⁻¹ * x` undoes it. As an equivalence it is a permutation of `G`, `Equiv.mulLeft g : Equiv.Perm G`, and its additive version `Equiv.addLeft a` adds `a`. In `ZMod 3`, adding `1` moves `0` to `1`, `1` to `2` and `2` to `0`: it is the rotation `rot3` of the first section, since `ZMod 3` is `Fin 3`. The context holds
```lean
theorem inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
theorem mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
```
@description
Define `Equiv.mulLeft g`, keeping the `@[to_additive]` line, and show that `Equiv.addLeft (1 : ZMod 3) = rot3`.
-/

@[to_additive Equiv.addLeft]
def Equiv.mulLeft {G : Type u} [Group G] (g : G) : Equiv.Perm G where
  toFun x := g * x
  invFun x := g⁻¹ * x
  left_inv x := inv_mul_cancel_left g x
  right_inv x := mul_inv_cancel_left g x

/-- @spec -/
example {G : Type u} [Group G] (g x : G) : Equiv.mulLeft g x = g * x ∧ (Equiv.mulLeft g).symm x = g⁻¹ * x :=
  ⟨rfl, rfl⟩

theorem addLeft_one_zmod_three : Equiv.addLeft (1 : ZMod 3) = rot3 := by
  decide

/-! @end -/

/-!
@problem cayley
@title Cayley's Theorem
@concept cayley

@preamble
Sending `g` to the permutation `Equiv.mulLeft g` is a homomorphism `G →* Equiv.Perm G`. Multiplying on the left by `a * b` is multiplying by `b` and then by `a`, and that is the product `Equiv.mulLeft a * Equiv.mulLeft b` of the symmetric group, where the right factor acts first. It is injective, since `Equiv.mulLeft g` sends `1` to `g`. So every group is isomorphic to a group of permutations, its image: this is *Cayley's theorem*. A finite group with `n` elements thus sits inside `Sₙ`, once its elements are labelled `0, …, n - 1`. The permutations of an additive group form a multiplicative group all the same, so this homomorphism has no additive version.

Two permutations are equal when they agree at every point, `Equiv.ext`, and `congrArg` applies a function to both sides of an equation. The goals that arise hold up to unfolding definitions, so `rw` may not find its pattern until `change` restates the goal as what it says. The context holds `mul_assoc` and `mul_one`.
@description
Define `cayley G : G →* Equiv.Perm G`, sending `g` to `Equiv.mulLeft g`, and show that its function is injective.
-/

def cayley (G : Type u) [Group G] : G →* Equiv.Perm G where
  toFun := Equiv.mulLeft
  map_mul' a b := by
    apply Equiv.ext
    intro x
    exact mul_assoc a b x

/-- @spec -/
example {G : Type u} [Group G] (g x : G) : (cayley G).toFun g x = g * x := rfl

theorem cayley_injective (G : Type u) [Group G] : Function.Injective (cayley G).toFun := by
  intro a b h
  have h1 : a * 1 = b * 1 := congrArg (fun p : Equiv.Perm G => p 1) h
  rw [mul_one, mul_one] at h1
  exact h1

/-! @end -/

end GroupTheory
