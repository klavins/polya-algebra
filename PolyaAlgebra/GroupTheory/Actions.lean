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
import PolyaAlgebra.GroupTheory.Isomorphisms

/-! @section Group Actions -/

universe u v

namespace GroupTheory

set_option linter.translateGenerateName false

/-!
@concept actions
@title Group Actions
@kind definition

A group acts on a set when each of its elements moves the points of the set, the neutral element moving nothing and a product moving them as its two factors do, one after the other. Groups arise this way, as the symmetries of something, and an action turns a question about a group into one about the set it moves.
-/

/-!
@problem mul_action
@title The Definition of a Group Action
@concept actions

@preamble
A group `G` acts on a set `X` through an operation we write `g • x`, with two laws:
```lean
(1 : G) • x = x
(g * h) • x = g • h • x
```
Here `g • h • x` is `g • (h • x)`, and `•` is the notation of the class `SMul` of the section on powers. The class of actions extends `SMul`, as `CommGroup` extends `Group`:
```lean
class MulAction (G : Type u) (X : Type v) [Group G]
    extends SMul G X where
```
The additive version is written `a +ᵥ x` (typed `+\_v`), the notation of Mathlib's class `VAdd`, whose one field is `vadd : A → X → X`.
@description
Define the class `MulAction G X`, extending `SMul G X` by the laws `one_smul` and `mul_smul` above, and its additive version `AddAction A X`, extending `VAdd A X` by `zero_vadd` and `add_vadd`. Write each law with its points and elements as explicit arguments, as in `∀ x : X, (1 : G) • x = x`.
-/

class MulAction (G : Type u) (X : Type v) [Group G] extends SMul G X where
  one_smul : ∀ x : X, (1 : G) • x = x
  mul_smul : ∀ (g h : G) (x : X), (g * h) • x = g • h • x

class AddAction (A : Type u) (X : Type v) [AddGroup A] extends VAdd A X where
  zero_vadd : ∀ x : X, (0 : A) +ᵥ x = x
  add_vadd : ∀ (a b : A) (x : X), (a + b) +ᵥ x = a +ᵥ b +ᵥ x

/-- @spec -/
example (G : Type u) (X : Type v) [Group G] [MulAction G X] : SMul G X := MulAction.toSMul

/-- @spec -/
example (G : Type u) (X : Type v) [Group G] [MulAction G X] (x : X) : (1 : G) • x = x := by
  have h := @MulAction.one_smul G X _ _ x
  grind

/-- @spec -/
example (G : Type u) (X : Type v) [Group G] [MulAction G X] (g h : G) (x : X) :
    (g * h) • x = g • h • x := by
  have e := @MulAction.mul_smul G X _ _ g h x
  grind

/-- @spec -/
example (A : Type u) (X : Type v) [AddGroup A] [AddAction A X] : VAdd A X := AddAction.toVAdd

/-- @spec -/
example (A : Type u) (X : Type v) [AddGroup A] [AddAction A X] (x : X) : (0 : A) +ᵥ x = x := by
  have h := @AddAction.zero_vadd A X _ _ x
  grind

/-- @spec -/
example (A : Type u) (X : Type v) [AddGroup A] [AddAction A X] (a b : A) (x : X) :
    (a + b) +ᵥ x = a +ᵥ b +ᵥ x := by
  have e := @AddAction.add_vadd A X _ _ a b x
  grind

/-! @end -/

attribute [to_additive existing AddAction] MulAction

attribute [to_additive existing AddAction.toVAdd] MulAction.toSMul

/-!
@problem perm_action
@title The Symmetric Group Acts on Its Points
@concept actions

@preamble
The permutations of a type `X` act on `X`: a permutation `f` sends the point `x` to `f x`. Both laws hold by definition, since the neutral permutation is the identity and `f * g` applies `g` first, by the instance making `Equiv.Perm X` a group in the section on examples.

When `•` already has an instance, an instance of `MulAction` needs only its two laws, written with `where`; Lean finds the operation, as it found the group of an instance of `CommGroup`.
@description
Supply the instance `Equiv.Perm.instSMul`, the operation `f • x = f x` of a permutation on a point, and the instance `Equiv.Perm.applyMulAction X`, which makes it an action. Then check that the rotation `rot3` of the first section moves the point `0` of `Fin 3` to `1`.
-/

instance Equiv.Perm.instSMul {X : Type u} : SMul (Equiv.Perm X) X := ⟨fun f x => f x⟩

instance Equiv.Perm.applyMulAction (X : Type u) : MulAction (Equiv.Perm X) X where
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- @spec -/
example (X : Type u) (f : Equiv.Perm X) (x : X) : f • x = f x := rfl

theorem rot3_smul_zero : rot3 • (0 : Fin 3) = 1 := by
  decide

/-! @end -/

/-!
@problem self_action
@title A Group Acts on Itself
@concept actions

@preamble
Every group acts on itself by multiplication on the left, `g • x = g * x`, and the two laws of the action are laws of the group. The additive version, `a +ᵥ x = a + x`, makes `ZMod n` act on its own `n` residues. Read as the vertices `0`, `1`, …, `n - 1` of a regular polygon, the residue `1` turns each vertex to the next: `ZMod n` acts by rotation.

The context holds `one_mul` and `mul_assoc` of the second section.
@description
Supply the instances `Group.toSMulSelf`, with `g • x = g * x`, and `Group.toMulAction`, keeping their `@[to_additive]` lines. Then check that in `ZMod 4` the rotation `1` carries the vertex `3` to `0`.
-/

@[to_additive AddGroup.toVAddSelf]
instance Group.toSMulSelf {G : Type u} [Group G] : SMul G G := ⟨fun g x => g * x⟩

@[to_additive AddGroup.toAddAction]
instance Group.toMulAction {G : Type u} [Group G] : MulAction G G where
  one_smul := one_mul
  mul_smul := mul_assoc

/-- @spec -/
example {G : Type u} [Group G] (g x : G) : g • x = g * x := rfl

theorem zmod_four_one_vadd_three : (1 : ZMod 4) +ᵥ (3 : ZMod 4) = 0 := by
  decide

/-! @end -/

/-!
@problem dihedral_smul
@title The Dihedral Group Moves the Vertices
@concept actions

@preamble
`DihedralGroup n` acts on the `n` vertices of the polygon, numbered by `ZMod n` so that the rotation `r 1` carries each vertex to the next. The rotation `r i` carries the vertex `v` to `i + v`. The reflection `s = sr 0` fixes the vertex `0` and carries `v` to `-v`. By the table of the section on examples, `sr i` is the rotation `r i` followed by `s`, so it carries `v` to `-(i + v)`.

The operation is defined by cases on the symmetry, as the inverse of `DihedralGroup n` was. `rw` does not compute such a definition, so the two rules are stated as theorems, which hold by definition, for later proofs to rewrite with.
@description
Supply the instance `DihedralGroup.instSMul n`, the operation of `DihedralGroup n` on `ZMod n` by the two rules; prove them under the names `DihedralGroup.r_smul` and `DihedralGroup.sr_smul`; and check that in `DihedralGroup 4` the reflection `sr 1` carries the vertex `0` to `3`.
-/

open DihedralGroup in
instance DihedralGroup.instSMul (n : ℕ) [NeZero n] : SMul (DihedralGroup n) (ZMod n) where
  smul
    | r i, v => i + v
    | sr i, v => -(i + v)

/-- @spec -/
example {n : ℕ} [NeZero n] (i v : ZMod n) :
    DihedralGroup.r i • v = i + v ∧ DihedralGroup.sr i • v = -(i + v) :=
  ⟨rfl, rfl⟩

theorem DihedralGroup.r_smul {n : ℕ} [NeZero n] (i v : ZMod n) : r i • v = i + v :=
  rfl

theorem DihedralGroup.sr_smul {n : ℕ} [NeZero n] (i v : ZMod n) : sr i • v = -(i + v) :=
  rfl

open DihedralGroup in
theorem d4_sr_one_smul_zero : (sr 1 : DihedralGroup 4) • (0 : ZMod 4) = 3 := by
  decide

/-! @end -/

/-!
@problem dihedral_action
@title The Dihedral Group Acts on the Vertices
@concept actions

@preamble
The two rules make an action. Its law `mul_smul` reduces, through the table, to equations in `ZMod n`. The table's equations rewrite `DihedralGroup.mul`, not `*`, so the law is proved for `DihedralGroup.mul`, as `dihedral_mul_assoc` was in the section on examples. The instance takes it as it stands, since `g * h` is `DihedralGroup.mul g h` by definition. The neutral element is `r 0`, by definition.

The context holds `DihedralGroup.r_smul` and `DihedralGroup.sr_smul` of the previous problem; the four equations of the table, `DihedralGroup.r_mul_r` and its companions, of the section on examples; and the additive versions `zero_add`, `add_assoc`, `neg_add_rev` and `neg_neg` of laws of the second section and `add_left_comm` and `add_right_comm` of the section on examples.
@description
Show that the action respects the table, under the name `dihedral_mul_smul`, and supply the instance `DihedralGroup.instMulAction n`, which makes the operation an action.
-/

open DihedralGroup in
theorem dihedral_mul_smul {n : ℕ} [NeZero n] (g h : DihedralGroup n) (v : ZMod n) :
    DihedralGroup.mul g h • v = g • h • v := by
  cases g with
  | r i =>
    cases h with
    | r j => rw [r_mul_r, r_smul, r_smul, r_smul, add_assoc]
    | sr j =>
      rw [r_mul_sr, sr_smul, sr_smul, r_smul, neg_add_rev, neg_add_rev, neg_neg, add_left_comm,
        neg_add_rev j v]
  | sr i =>
    cases h with
    | r j => rw [sr_mul_r, sr_smul, sr_smul, r_smul, add_assoc]
    | sr j => rw [sr_mul_sr, r_smul, sr_smul, sr_smul, neg_add_rev, neg_neg, add_right_comm]

instance DihedralGroup.instMulAction (n : ℕ) [NeZero n] :
    MulAction (DihedralGroup n) (ZMod n) where
  one_smul v := zero_add v
  mul_smul := dihedral_mul_smul

/-- @spec -/
example {n : ℕ} [NeZero n] (g h : DihedralGroup n) (v : ZMod n) : (g * h) • v = g • h • v :=
  MulAction.mul_smul g h v

/-! @end -/

/-!
@problem quotient_action
@title A Group Acts on the Cosets of a Subgroup
@concept actions

@preamble
A group acts on the left cosets of any subgroup `H`, normal or not, by multiplication on the left: `g` carries the class of `a` in `G ⧸ H` to the class of `g * a`. The operation is defined on representatives through core Lean's `Quotient.lift`, met in the first section, which applies to `G ⧸ H` for any subgroup `H`. Representatives related by `a ≈ b`, which is `a⁻¹ * b ∈ H` by definition, must give the same class. The laws are then proved on representatives, as the laws of the quotient group were.

The context holds `QuotientGroup.mk_surjective` and
```lean
QuotientGroup.eq : (QuotientGroup.mk a : G ⧸ H) =
    QuotientGroup.mk b ↔ a⁻¹ * b ∈ H
```
of the section on cosets, and `inv_mul_cancel_left`, `mul_assoc`, `mul_inv_rev` and `one_mul` of the second section.
@description
Supply the instance `QuotientGroup.instSMul H`, the operation of `G` on `G ⧸ H` that carries `g` and the class of `a` to the class of `g * a`; prove that equation, which holds by definition, under the name `QuotientGroup.smul_mk`; and supply the instance `MulAction.quotient H`, which makes the operation an action. Keep the `@[to_additive]` lines.
-/

@[to_additive QuotientAddGroup.instVAdd]
instance QuotientGroup.instSMul {G : Type u} [Group G] (H : Subgroup G) : SMul G (G ⧸ H) where
  smul g := Quotient.lift (fun a => (QuotientGroup.mk (g * a) : G ⧸ H)) (by
    intro a b h
    apply QuotientGroup.eq.mpr
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    exact h)

/-- @spec -/
example {G : Type u} [Group G] (H : Subgroup G) (g a : G) :
    g • (QuotientGroup.mk a : G ⧸ H) = QuotientGroup.mk (g * a) :=
  rfl

@[to_additive QuotientAddGroup.vadd_mk]
theorem QuotientGroup.smul_mk {G : Type u} [Group G] {H : Subgroup G} (g a : G) :
    g • (QuotientGroup.mk a : G ⧸ H) = QuotientGroup.mk (g * a) :=
  rfl

@[to_additive AddAction.quotient]
instance MulAction.quotient {G : Type u} [Group G] (H : Subgroup G) : MulAction G (G ⧸ H) where
  one_smul q := by
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective q
    rw [← ha, QuotientGroup.smul_mk, one_mul]
  mul_smul g h q := by
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective q
    rw [← ha, QuotientGroup.smul_mk, QuotientGroup.smul_mk, QuotientGroup.smul_mk, mul_assoc]

/-! @end -/

/-!
@problem inv_smul_smul
@title Acting by an Inverse Undoes the Action
@concept actions

@preamble
The two laws of an action, restated below as the theorems `one_smul` and `mul_smul`, are all that is known about a general action. Acting by `g` and then by `g⁻¹` returns every point to its place, in three steps:
```lean
theorem inv_smul_smul (g : G) (x : X) :
    g⁻¹ • g • x = x :=
  calc g⁻¹ • g • x = (g⁻¹ * g) • x :=
        (mul_smul g⁻¹ g x).symm
    _ = (1 : G) • x := by rw [inv_mul_cancel]
    _ = x := one_smul x
```
The same steps are one rewrite,
```lean
rw [← mul_smul, inv_mul_cancel, one_smul]
```
with `mul_smul` read from right to left: the two actions are combined into one, the product cancels, and the neutral element is removed.
@description
Show the mirror image, that acting by `g⁻¹` and then by `g` returns every point to its place, under the name `smul_inv_smul`, keeping the `@[to_additive]` line. The context holds `mul_inv_cancel` of the second section.
-/

/-- @given -/
@[to_additive zero_vadd]
theorem one_smul {G : Type u} {X : Type v} [Group G] [MulAction G X] (x : X) : (1 : G) • x = x :=
  MulAction.one_smul x

/-- @given -/
@[to_additive add_vadd]
theorem mul_smul {G : Type u} {X : Type v} [Group G] [MulAction G X] (g h : G) (x : X) :
    (g * h) • x = g • h • x :=
  MulAction.mul_smul g h x

/-- @given -/
@[to_additive neg_vadd_vadd]
theorem inv_smul_smul {G : Type u} {X : Type v} [Group G] [MulAction G X] (g : G) (x : X) :
    g⁻¹ • g • x = x :=
  calc g⁻¹ • g • x = (g⁻¹ * g) • x := (mul_smul g⁻¹ g x).symm
    _ = (1 : G) • x := by rw [inv_mul_cancel]
    _ = x := one_smul x

@[to_additive vadd_neg_vadd]
theorem smul_inv_smul {G : Type u} {X : Type v} [Group G] [MulAction G X] (g : G) (x : X) :
    g • g⁻¹ • x = x := by
  rw [← mul_smul, mul_inv_cancel, one_smul]

/-! @end -/

/-!
@problem to_perm_hom
@title An Action Is a Homomorphism to the Permutations
@concept actions

@preamble
Each element `g` permutes `X`: the function `x ↦ g • x` has the inverse `x ↦ g⁻¹ • x`. We write `MulAction.toPerm g` for this permutation, an element of `Equiv.Perm X`. Sending each `g` to it is a homomorphism from `G` to `Equiv.Perm X`, which we write `MulAction.toPermHom G X`. An action of `G` on `X` is a way of reading each element of `G` as a permutation of `X`, compatibly with products. The homomorphism has no additive version, since the permutations form a multiplicative group, as for `cayley` of the section on homomorphisms.

The context holds `inv_smul_smul` and `smul_inv_smul` of the previous problem, `mul_smul`, and Mathlib's `Equiv.ext`, shown in the section on examples.
@description
Define the permutation `MulAction.toPerm g`, keeping its `@[to_additive]` line, and the homomorphism `MulAction.toPermHom G X` that sends `g` to it.
-/

@[to_additive AddAction.toPerm]
def MulAction.toPerm {G : Type u} {X : Type v} [Group G] [MulAction G X] (g : G) :
    Equiv.Perm X where
  toFun x := g • x
  invFun x := g⁻¹ • x
  left_inv x := inv_smul_smul g x
  right_inv x := smul_inv_smul g x

def MulAction.toPermHom (G : Type u) (X : Type v) [Group G] [MulAction G X] :
    G →* Equiv.Perm X where
  toFun := MulAction.toPerm
  map_mul' g h := by
    apply Equiv.ext
    intro x
    exact mul_smul g h x

/-- @spec -/
example {G : Type u} {X : Type v} [Group G] [MulAction G X] (g : G) (x : X) :
    MulAction.toPerm g x = g • x ∧ (MulAction.toPermHom G X).toFun g = MulAction.toPerm g :=
  ⟨rfl, rfl⟩

/-! @end -/

/-!
@concept orbits
@title Orbits
@kind definition

The orbit of a point is the set of points the group can move it to, and lying in one orbit is an equivalence relation. A point alone in its orbit is a fixed point, and an action with only one orbit is transitive. Orbits are how an action sorts the points of a set.
-/

/-!
@problem orbit
@title The Orbit of a Point
@concept orbits

@preamble
The *orbit* of a point `x` is the set of the points that the elements of the group carry it to:
```lean
{y | ∃ g : G, g • x = y}
```
We write it `MulAction.orbit G x`. A member of an orbit opens into `⟨g, hg⟩` with `hg : g • x = y`, as a member of the range of a homomorphism did in the section on homomorphisms.

The context holds `one_smul`.
@description
Define `MulAction.orbit G x`, keeping the `@[to_additive]` line; prove `MulAction.mem_orbit_iff`, which holds by definition,
```lean
y ∈ MulAction.orbit G x ↔ ∃ g : G, g • x = y
```
and show that `x` lies in its own orbit, under the name `MulAction.mem_orbit_self`.
-/

@[to_additive AddAction.orbit]
def MulAction.orbit (G : Type u) {X : Type v} [Group G] [MulAction G X] (x : X) : Set X :=
  {y | ∃ g : G, g • x = y}

/-- @spec -/
example (G : Type u) {X : Type v} [Group G] [MulAction G X] (x y : X) :
    y ∈ MulAction.orbit G x ↔ ∃ g : G, g • x = y := by
  constructor
  · intro ⟨g, e⟩
    exact ⟨g, by grind⟩
  · intro ⟨g, e⟩
    exact ⟨g, by grind⟩

@[to_additive AddAction.mem_orbit_iff]
theorem MulAction.mem_orbit_iff {G : Type u} {X : Type v} [Group G] [MulAction G X] {x y : X} :
    y ∈ MulAction.orbit G x ↔ ∃ g : G, g • x = y :=
  Iff.rfl

@[to_additive AddAction.mem_orbit_self]
theorem MulAction.mem_orbit_self {G : Type u} {X : Type v} [Group G] [MulAction G X] (x : X) :
    x ∈ MulAction.orbit G x :=
  ⟨1, one_smul x⟩

/-! @end -/

/-!
@problem orbit_rel
@title Lying in One Orbit Is an Equivalence
@concept orbits

@preamble
Being in the orbit of another point is an equivalence relation on `X`. We make it a setoid, as the coset relation was in the section on cosets, and call it `MulAction.orbitRel G X`, Mathlib's name: it relates `x` to `y` when `x ∈ MulAction.orbit G y`. In the proof of `iseqv`, a goal stating the relation shows as the membership it is.

The context holds `MulAction.mem_orbit_iff` and `MulAction.mem_orbit_self` of the previous problem, and `inv_smul_smul` and `mul_smul` of the previous concept.
@description
Define `MulAction.orbitRel G X`, the setoid on `X` relating `x` and `y` when `x` lies in the orbit of `y`, keeping the `@[to_additive]` line.
-/

@[to_additive AddAction.orbitRel]
def MulAction.orbitRel (G : Type u) (X : Type v) [Group G] [MulAction G X] : Setoid X where
  r x y := x ∈ MulAction.orbit G y
  iseqv := by
    constructor
    · intro x
      exact MulAction.mem_orbit_self x
    · intro x y ⟨g, hg⟩
      exact MulAction.mem_orbit_iff.mpr ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
    · intro x y z ⟨g, hg⟩ ⟨h, hh⟩
      exact MulAction.mem_orbit_iff.mpr ⟨g * h, by rw [mul_smul, hh, hg]⟩

/-- @spec -/
example (G : Type u) (X : Type v) [Group G] [MulAction G X] (x y : X) :
    (MulAction.orbitRel G X) x y ↔ x ∈ MulAction.orbit G y := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-! @end -/

/--
@problem orbit_eq_iff
@title When Two Orbits Are Equal
@concept orbits

@preamble
An orbit is the orbit of each of its points.

The context holds `MulAction.mem_orbit_iff` and `MulAction.mem_orbit_self` of this concept's first problem; `inv_smul_smul` and `mul_smul` of the previous concept; and Mathlib's `Set.ext`, met in the first section.
@description
Show that the orbits of `x` and `y` are equal exactly when `x` lies in the orbit of `y`, under the name `MulAction.orbit_eq_iff`.
-/
@[to_additive AddAction.orbit_eq_iff]
theorem MulAction.orbit_eq_iff {G : Type u} {X : Type v} [Group G] [MulAction G X] {x y : X} :
    MulAction.orbit G x = MulAction.orbit G y ↔ x ∈ MulAction.orbit G y := by
  constructor
  · intro h
    rw [← h]
    exact MulAction.mem_orbit_self x
  · intro hx
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hx
    apply Set.ext
    intro z
    rw [MulAction.mem_orbit_iff, MulAction.mem_orbit_iff]
    constructor
    · intro ⟨h, hh⟩
      exact ⟨h * g, by rw [mul_smul, hg, hh]⟩
    · intro ⟨h, hh⟩
      exact ⟨h * g⁻¹, by rw [mul_smul, ← hg, inv_smul_smul, hh]⟩

/-!
@problem fixed_points
@title Fixed Points
@concept orbits

@preamble
A point that every element of the group leaves in its place, `g • x = x` for every `g`, is a *fixed point* of the action. We write `MulAction.fixedPoints G X` for the set of them.

The context holds `MulAction.mem_orbit_iff` and `MulAction.mem_orbit_self` of this concept's first problem, and Mathlib's `Set.ext`, met in the first section, and `Set.mem_singleton_iff`, met in the section on subgroups.
@description
Define `MulAction.fixedPoints G X`, keeping the `@[to_additive]` line, and prove `MulAction.mem_fixedPoints`, which holds by definition,
```lean
x ∈ MulAction.fixedPoints G X ↔ ∀ g : G, g • x = x
```
Then show that the orbit of `x` is `{x}` exactly when `x` is a fixed point, under the name `MulAction.orbit_eq_singleton_iff`.
-/

@[to_additive AddAction.fixedPoints]
def MulAction.fixedPoints (G : Type u) (X : Type v) [Group G] [MulAction G X] : Set X :=
  {x | ∀ g : G, g • x = x}

/-- @spec -/
example (G : Type u) (X : Type v) [Group G] [MulAction G X] (x : X) :
    x ∈ MulAction.fixedPoints G X ↔ ∀ g : G, g • x = x := by
  constructor
  · intro h g
    have e := h g
    grind
  · intro h g
    have e := h g
    grind

@[to_additive AddAction.mem_fixedPoints]
theorem MulAction.mem_fixedPoints {G : Type u} {X : Type v} [Group G] [MulAction G X] {x : X} :
    x ∈ MulAction.fixedPoints G X ↔ ∀ g : G, g • x = x :=
  Iff.rfl

@[to_additive AddAction.orbit_eq_singleton_iff]
theorem MulAction.orbit_eq_singleton_iff {G : Type u} {X : Type v} [Group G] [MulAction G X]
    {x : X} : MulAction.orbit G x = {x} ↔ x ∈ MulAction.fixedPoints G X := by
  constructor
  · intro h
    rw [MulAction.mem_fixedPoints]
    intro g
    have hg : g • x ∈ MulAction.orbit G x := MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩
    rw [h] at hg
    exact hg
  · intro h
    rw [MulAction.mem_fixedPoints] at h
    apply Set.ext
    intro y
    rw [MulAction.mem_orbit_iff, Set.mem_singleton_iff]
    constructor
    · intro ⟨g, hg⟩
      rw [← hg, h g]
    · intro hy
      rw [hy]
      exact MulAction.mem_orbit_self x

/-! @end -/

/-!
@problem is_pretransitive
@title Transitive Actions
@concept orbits

@preamble
An action is *transitive* when every point can be carried to every other, so that a nonempty set is a single orbit. Mathlib's name is `MulAction.IsPretransitive G X`, "pre" because the condition holds of the empty set too, which has no orbit. Like `Subgroup.Normal` in the section on quotient groups, it is a class whose type is `Prop`, so that Lean finds it when it is needed, and its one field is
```lean
exists_smul_eq : ∀ x y : X, ∃ g : G, g • x = y
```
The additive version `AddAction.IsPretransitive A X` has the field `exists_vadd_eq`, and Lean is told that the two correspond.
@description
Define the class `MulAction.IsPretransitive G X`, with the field `exists_smul_eq` above, and its additive version `AddAction.IsPretransitive A X`, with the field `exists_vadd_eq`.
-/

class MulAction.IsPretransitive (G : Type u) (X : Type v) [Group G] [MulAction G X] : Prop where
  exists_smul_eq : ∀ x y : X, ∃ g : G, g • x = y

class AddAction.IsPretransitive (A : Type u) (X : Type v) [AddGroup A] [AddAction A X] :
    Prop where
  exists_vadd_eq : ∀ x y : X, ∃ a : A, a +ᵥ x = y

/-- @spec -/
example (G : Type u) (X : Type v) [Group G] [MulAction G X] [MulAction.IsPretransitive G X]
    (x y : X) : ∃ g : G, g • x = y := by
  apply MulAction.IsPretransitive.exists_smul_eq

/-- @spec -/
example (A : Type u) (X : Type v) [AddGroup A] [AddAction A X] [AddAction.IsPretransitive A X]
    (x y : X) : ∃ a : A, a +ᵥ x = y := by
  apply AddAction.IsPretransitive.exists_vadd_eq

/-! @end -/

attribute [to_additive existing AddAction.IsPretransitive] MulAction.IsPretransitive

/-!
@problem orbit_eq_univ
@title The One Orbit of a Transitive Action
@concept orbits

@preamble
The theorem `MulAction.exists_smul_eq G x y`, given below, restates the field of a transitive action with the group explicit and the instance found by Lean. In a transitive action the orbit of every point is the whole of `X`, which Mathlib writes `Set.univ`.

The context holds `MulAction.mem_orbit_iff` of this concept's first problem, and Mathlib's `Set.ext`, met in the first section, and `Set.mem_univ`, met in the section on subgroups.
@description
Show that every orbit of a transitive action is `Set.univ`, under the name `MulAction.orbit_eq_univ`.
-/

/-- @given -/
@[to_additive AddAction.exists_vadd_eq]
theorem MulAction.exists_smul_eq (G : Type u) {X : Type v} [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] (x y : X) : ∃ g : G, g • x = y :=
  MulAction.IsPretransitive.exists_smul_eq x y

@[to_additive AddAction.orbit_eq_univ]
theorem MulAction.orbit_eq_univ (G : Type u) {X : Type v} [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] (x : X) : MulAction.orbit G x = Set.univ := by
  apply Set.ext
  intro y
  constructor
  · intro _
    exact Set.mem_univ y
  · intro _
    exact MulAction.mem_orbit_iff.mpr (MulAction.exists_smul_eq G x y)

/-! @end -/

/-!
@problem dihedral_transitive
@title Two Transitive Actions
@concept orbits

@preamble
A group acting on itself is transitive, and so is the dihedral group acting on the vertices of the polygon: every vertex can be carried to every other. An instance of a class of type `Prop` with one field is written with `where` and that field, as the normality of a subgroup was. For a group acting on itself, `g • x` is `g * x` only by definition: `rw` finds no product in it, while a term whose type is the equation with `*` is accepted as it stands.

The context holds `DihedralGroup.r_smul` of the previous concept; `inv_mul_cancel_right` of the second section; and the additive versions `add_assoc`, `add_zero` and `neg_add_cancel` of laws of the second section.
@description
Supply the instance `Group.isPretransitive_self`, which makes the action of a group on itself transitive, keeping its `@[to_additive]` line, and the instance `DihedralGroup.isPretransitive n`, which makes the action of `DihedralGroup n` on `ZMod n` transitive.
-/

@[to_additive AddGroup.isPretransitive_self]
instance Group.isPretransitive_self {G : Type u} [Group G] : MulAction.IsPretransitive G G where
  exists_smul_eq x y := ⟨y * x⁻¹, inv_mul_cancel_right y x⟩

instance DihedralGroup.isPretransitive (n : ℕ) [NeZero n] :
    MulAction.IsPretransitive (DihedralGroup n) (ZMod n) where
  exists_smul_eq v w := ⟨DihedralGroup.r (w + -v), by
    rw [DihedralGroup.r_smul, add_assoc, neg_add_cancel, add_zero]⟩

/-- @spec -/
example {G : Type u} [Group G] : MulAction.IsPretransitive G G := inferInstance

/-- @spec -/
example (n : ℕ) [NeZero n] : MulAction.IsPretransitive (DihedralGroup n) (ZMod n) := inferInstance

/-! @end -/

/-!
@concept stabilizers
@title Stabilizers
@kind definition

The stabilizer of a point is the subgroup of the elements that leave it in its place. The elements that leave every point in its place form the kernel of the action. An action is faithful when only the neutral element does, and then the group is a group of permutations of the set.
-/

/-!
@problem stabilizer
@title The Stabilizer of a Point
@concept stabilizers

@preamble
The *stabilizer* of a point `x` is the set of the elements that leave `x` in its place,
```lean
{g | g • x = x}
```
and it is a subgroup of `G`, Mathlib's `MulAction.stabilizer G x`. A membership in a set written `{g | p g}` is `p g` by definition, and `change` writes it out.

The context holds `one_smul`, `mul_smul` and `inv_smul_smul` of the first concept.
@description
Define the subgroup `MulAction.stabilizer G x` with that carrier, keeping the `@[to_additive]` line, and prove `MulAction.mem_stabilizer_iff`, which holds by definition:
```lean
g ∈ MulAction.stabilizer G x ↔ g • x = x
```
-/

@[to_additive AddAction.stabilizer]
def MulAction.stabilizer (G : Type u) {X : Type v} [Group G] [MulAction G X] (x : X) :
    Subgroup G where
  carrier := {g | g • x = x}
  one_mem' := one_smul x
  mul_mem' := by
    intro g h hg hh
    change (g * h) • x = x
    change h • x = x at hh
    rw [mul_smul, hh]
    exact hg
  inv_mem' := by
    intro g hg
    change g • x = x at hg
    change g⁻¹ • x = x
    rw [← hg, inv_smul_smul, hg]

/-- @spec -/
example (G : Type u) {X : Type v} [Group G] [MulAction G X] (x : X) (g : G) :
    g ∈ MulAction.stabilizer G x ↔ g • x = x := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

@[to_additive AddAction.mem_stabilizer_iff]
theorem MulAction.mem_stabilizer_iff {G : Type u} {X : Type v} [Group G] [MulAction G X] {x : X}
    {g : G} : g ∈ MulAction.stabilizer G x ↔ g • x = x :=
  Iff.rfl

/-! @end -/

/--
@problem stabilizer_smul
@title The Stabilizer of a Moved Point
@concept stabilizers

@preamble
Moving a point moves its stabilizer with it: the elements fixing `g • x` are the conjugates `g * k * g⁻¹` of the elements `k` fixing `x`.

The context holds `MulAction.mem_stabilizer_iff` of the previous problem, and `mul_smul`, `inv_smul_smul` and `smul_inv_smul` of the first concept.
@description
Show that `h` lies in the stabilizer of `g • x` exactly when `g⁻¹ * h * g` lies in the stabilizer of `x`, under the name `MulAction.mem_stabilizer_smul_iff`.
-/
@[to_additive AddAction.mem_stabilizer_vadd_iff]
theorem MulAction.mem_stabilizer_smul_iff {G : Type u} {X : Type v} [Group G] [MulAction G X]
    {x : X} {g h : G} :
    h ∈ MulAction.stabilizer G (g • x) ↔ g⁻¹ * h * g ∈ MulAction.stabilizer G x := by
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, mul_smul, mul_smul]
  constructor
  · intro e
    rw [e, inv_smul_smul]
  · intro e
    have e2 : g • g⁻¹ • h • g • x = g • x := by rw [e]
    rw [smul_inv_smul] at e2
    exact e2

/--
@problem ker_to_perm_hom
@title The Kernel of an Action
@concept stabilizers

@preamble
The *kernel* of an action is the kernel of `MulAction.toPermHom G X`, the elements whose permutation is the identity. The neutral element of `Equiv.Perm X` is the identity, by definition.

The context holds `GroupHom.mem_ker` of the section on homomorphisms, Mathlib's `Equiv.ext`, met in the section on examples, and core Lean's `congrArg`, met in the section on homomorphisms.
@description
Show that `g` lies in the kernel of `MulAction.toPermHom G X` exactly when `g • x = x` for every `x`, under the name `MulAction.mem_ker_toPermHom`.
-/
theorem MulAction.mem_ker_toPermHom {G : Type u} {X : Type v} [Group G] [MulAction G X] {g : G} :
    g ∈ (MulAction.toPermHom G X).ker ↔ ∀ x : X, g • x = x := by
  rw [GroupHom.mem_ker]
  constructor
  · intro h x
    exact congrArg (fun f : Equiv.Perm X => f x) h
  · intro h
    apply Equiv.ext
    exact h

/-!
@problem faithful_smul
@title Faithful Actions
@concept stabilizers

@preamble
An action is *faithful* when different elements act differently: if `g₁ • x = g₂ • x` at every point `x`, then `g₁ = g₂`. Mathlib's name is the class `FaithfulSMul G X`, of type `Prop`, with the field `eq_of_smul_eq_smul`; its `g₁` and `g₂` are explicit here and implicit in Mathlib. The class and its theorems have no additive version here; the theorems go through `MulAction.toPermHom`, which has none.

`X` occurs only in the field's hypothesis: when `apply` leaves that hypothesis as a goal, `X` stays unknown and Lean reports a stuck instance problem. A hypothesis whose type names `X` fixes it.

The context holds `MulAction.mem_ker_toPermHom` of the previous problem; `one_smul`, `mul_smul` and `inv_smul_smul` of the first concept; `Subgroup.ext` and `Subgroup.mem_bot` of the section on subgroups; and `mul_inv_cancel_left` and `mul_one` of the second section.
@description
Define the class `FaithfulSMul G X`, for an operation `•` of `G` on `X`. Then show that a faithful action has kernel `⊥`, under the name `MulAction.ker_eq_bot_of_faithful`, and that an action with kernel `⊥` is faithful, under the name `MulAction.faithful_of_ker_eq_bot`.
-/

class FaithfulSMul (G : Type u) (X : Type v) [SMul G X] : Prop where
  eq_of_smul_eq_smul : ∀ g₁ g₂ : G, (∀ x : X, g₁ • x = g₂ • x) → g₁ = g₂

/-- @spec -/
example (G : Type u) (X : Type v) [SMul G X] [FaithfulSMul G X] (g₁ g₂ : G)
    (h : ∀ x : X, g₁ • x = g₂ • x) : g₁ = g₂ := by
  apply FaithfulSMul.eq_of_smul_eq_smul (X := X)
  intro x
  have e := h x
  grind

theorem MulAction.ker_eq_bot_of_faithful {G : Type u} {X : Type v} [Group G] [MulAction G X]
    [FaithfulSMul G X] : (MulAction.toPermHom G X).ker = ⊥ := by
  apply Subgroup.ext
  intro g
  rw [MulAction.mem_ker_toPermHom, Subgroup.mem_bot]
  constructor
  · intro hg
    have e : ∀ x : X, g • x = (1 : G) • x := by
      intro x
      rw [hg x, one_smul]
    exact FaithfulSMul.eq_of_smul_eq_smul g 1 e
  · intro hg x
    rw [hg, one_smul]

theorem MulAction.faithful_of_ker_eq_bot {G : Type u} {X : Type v} [Group G] [MulAction G X]
    (h : (MulAction.toPermHom G X).ker = ⊥) : FaithfulSMul G X where
  eq_of_smul_eq_smul g₁ g₂ e := by
    have hk : g₂⁻¹ * g₁ ∈ (MulAction.toPermHom G X).ker := by
      rw [MulAction.mem_ker_toPermHom]
      intro x
      rw [mul_smul, e, inv_smul_smul]
    rw [h, Subgroup.mem_bot] at hk
    rw [← mul_inv_cancel_left g₂ g₁, hk, mul_one]

/-! @end -/

/-!
@problem dihedral_stabilizer
@title The Stabilizer of a Vertex of a Triangle
@concept stabilizers

@preamble
`DihedralGroup 3` acts on the three vertices of a triangle, numbered by `ZMod 3`. The section on cosets defined the subgroup `d3FixZero`. `decide` cannot see inside its definition, but it decides a statement about the elements of `DihedralGroup 3` written out in full.

The context holds `MulAction.mem_stabilizer_iff` of this concept, `mem_d3FixZero` of the section on cosets, and `Subgroup.ext` of the section on subgroups.
@description
Show that the stabilizer of the vertex `0` under `DihedralGroup 3` is `d3FixZero`.
-/

theorem stabilizer_d3_zero :
    MulAction.stabilizer (DihedralGroup 3) (0 : ZMod 3) = d3FixZero := by
  apply Subgroup.ext
  simp only [MulAction.mem_stabilizer_iff, mem_d3FixZero]
  decide

/-! @end -/

/-!
@problem d2_not_faithful
@title An Action That Is Not Faithful
@concept stabilizers

@preamble
`DihedralGroup 2` acts on `ZMod 2`, the two ends of a segment, and some symmetry other than the identity moves neither end.

The context holds `MulAction.mem_ker_toPermHom` and `MulAction.ker_eq_bot_of_faithful` of this concept; `sr_ne_one` of the section on powers; and `Subgroup.mem_bot` of the section on subgroups.
@description
Show that the action of `DihedralGroup 2` on `ZMod 2` is not faithful.
-/

open DihedralGroup in
theorem d2_not_faithful : ¬ FaithfulSMul (DihedralGroup 2) (ZMod 2) := by
  intro h
  have hk : sr 0 ∈ (MulAction.toPermHom (DihedralGroup 2) (ZMod 2)).ker := by
    rw [MulAction.mem_ker_toPermHom]
    decide
  rw [MulAction.ker_eq_bot_of_faithful, Subgroup.mem_bot] at hk
  exact sr_ne_one 0 hk

/-! @end -/

/-!
@concept conjugation
@title Conjugation
@kind definition

A group acts on itself by conjugation. The orbits of this action are the conjugacy classes, its stabilizers are centralizers, the elements that commute with a given one, and its fixed points are the centre. It is the action through which a group is studied by means of itself.
-/

/-!
@problem conj_act
@title A Second Name for a Group
@concept conjugation

@preamble
A group acts on itself a second way, by *conjugation*: `g` carries `x` to `g * x * g⁻¹`. But `g • x` already means `g * x` for `g x : G`, by an instance of this section's first concept, and a second instance of `SMul G G` would give one symbol two meanings. Lean tells the two actions apart through a *type synonym*, `ConjAct G`, defined to be `G`: a new name for the same type, on which instances are looked up afresh. The group structure of `ConjAct G` is that of `G`, copied: `inferInstanceAs (Group G)` finds the instance `Group G` and hands it over as an instance for the synonym. Two functions, `ConjAct.ofConjAct` from `ConjAct G` to `G` and `ConjAct.toConjAct` back, send each element to itself. Conjugation has no additive version here: every additive group the subject builds is commutative, and in a commutative group conjugation moves nothing.
@description
Define `ConjAct G` as `G`, the instance `ConjAct.instGroup` copying the group of `G`, and the functions `ConjAct.ofConjAct` and `ConjAct.toConjAct`.
-/

def ConjAct (G : Type u) : Type u := G

instance ConjAct.instGroup {G : Type u} [Group G] : Group (ConjAct G) := inferInstanceAs (Group G)

def ConjAct.ofConjAct {G : Type u} (g : ConjAct G) : G := g

def ConjAct.toConjAct {G : Type u} (g : G) : ConjAct G := g

/-- @spec -/
example {G : Type u} [Group G] (g h : ConjAct G) (a : G) :
    ConjAct.ofConjAct (g * h) = ConjAct.ofConjAct g * ConjAct.ofConjAct h ∧
    ConjAct.ofConjAct (1 : ConjAct G) = 1 ∧ ConjAct.ofConjAct (ConjAct.toConjAct a) = a :=
  ⟨rfl, rfl, rfl⟩

/-! @end -/

/-!
@problem conj_action
@title The Action by Conjugation
@concept conjugation

@preamble
Conjugation is an action of `ConjAct G` on `G`:
```lean
g • x = ConjAct.ofConjAct g * x *
    (ConjAct.ofConjAct g)⁻¹
```
The equations below hold by definition, for `rw`; the first two carry products and the neutral element through `ConjAct.ofConjAct`. The context also holds `inv_one`, `mul_assoc`, `mul_inv_rev`, `mul_one` and `one_mul` of the second section.
@description
Supply the instance `ConjAct.instSMul`, the operation of `ConjAct G` on `G` by conjugation; prove its equation, which holds by definition, under the name `ConjAct.smul_def`; and supply the instance `ConjAct.instMulAction`, which makes conjugation an action.
-/

/-- @given -/
theorem ConjAct.ofConjAct_mul {G : Type u} [Group G] (g h : ConjAct G) :
    ConjAct.ofConjAct (g * h) = ConjAct.ofConjAct g * ConjAct.ofConjAct h :=
  rfl

/-- @given -/
theorem ConjAct.ofConjAct_one {G : Type u} [Group G] : ConjAct.ofConjAct (1 : ConjAct G) = 1 :=
  rfl

/-- @given -/
theorem ConjAct.ofConjAct_toConjAct {G : Type u} (g : G) :
    ConjAct.ofConjAct (ConjAct.toConjAct g) = g :=
  rfl

instance ConjAct.instSMul {G : Type u} [Group G] : SMul (ConjAct G) G :=
  ⟨fun g x => ConjAct.ofConjAct g * x * (ConjAct.ofConjAct g)⁻¹⟩

/-- @spec -/
example {G : Type u} [Group G] (g : ConjAct G) (x : G) :
    g • x = ConjAct.ofConjAct g * x * (ConjAct.ofConjAct g)⁻¹ :=
  rfl

theorem ConjAct.smul_def {G : Type u} [Group G] (g : ConjAct G) (x : G) :
    g • x = ConjAct.ofConjAct g * x * (ConjAct.ofConjAct g)⁻¹ :=
  rfl

instance ConjAct.instMulAction {G : Type u} [Group G] : MulAction (ConjAct G) G where
  one_smul x := by
    rw [ConjAct.smul_def, ConjAct.ofConjAct_one, inv_one, mul_one, one_mul]
  mul_smul g h x := by
    rw [ConjAct.smul_def, ConjAct.smul_def, ConjAct.smul_def, ConjAct.ofConjAct_mul, mul_inv_rev,
      mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc]

/-! @end -/

/-!
@problem conj_orbit
@title Conjugacy Classes and the Centre
@concept conjugation

@preamble
The orbit of `x` under conjugation is its *conjugacy class*, the elements `g * x * g⁻¹` for `g : G`; two elements in one class are *conjugate*.

The context holds `ConjAct.smul_def` and `ConjAct.ofConjAct_toConjAct` of the previous problem; `MulAction.mem_fixedPoints` of the concept on orbits; `inv_mul_cancel_right` and `mul_inv_cancel_right` of the second section; and, of the section on subgroups,
```lean
Subgroup.mem_center_iff :
    z ∈ Subgroup.center G ↔ ∀ g, g * z = z * g
```
@description
Prove `ConjAct.mem_orbit_iff`, which holds by definition, since `ConjAct G` is `G`: `y` lies in the orbit of `x` under conjugation exactly when `g * x * g⁻¹ = y` for some `g : G`. Then show that `x` is a fixed point of conjugation exactly when it lies in the centre, under the name `ConjAct.mem_fixedPoints_iff`.
-/

theorem ConjAct.mem_orbit_iff {G : Type u} [Group G] {x y : G} :
    y ∈ MulAction.orbit (ConjAct G) x ↔ ∃ g : G, g * x * g⁻¹ = y :=
  Iff.rfl

theorem ConjAct.mem_fixedPoints_iff {G : Type u} [Group G] {x : G} :
    x ∈ MulAction.fixedPoints (ConjAct G) G ↔ x ∈ Subgroup.center G := by
  rw [MulAction.mem_fixedPoints, Subgroup.mem_center_iff]
  constructor
  · intro h g
    have e := h (ConjAct.toConjAct g)
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct] at e
    have e2 : g * x * g⁻¹ * g = x * g := by rw [e]
    rw [inv_mul_cancel_right] at e2
    exact e2
  · intro h g
    rw [ConjAct.smul_def, h, mul_inv_cancel_right]

/-! @end -/

/-!
@problem centralizer
@title The Centralizer of a Set
@concept conjugation

@preamble
The elements of `G` that commute with every element of a set `S` form a subgroup, the *centralizer* of `S`, Mathlib's `Subgroup.centralizer S`, with the carrier
```lean
{g | ∀ h ∈ S, h * g = g * h}
```
The centre of the section on subgroups is the same construction with every element of `G` in place of `S`.

The context holds `inv_mul_cancel_left`, `mul_assoc`, `mul_inv_cancel_right`, `mul_one` and `one_mul` of the second section.
@description
Define the subgroup `Subgroup.centralizer S` with that carrier, keeping the `@[to_additive]` line, and prove `Subgroup.mem_centralizer_iff`, which holds by definition:
```lean
g ∈ Subgroup.centralizer S ↔ ∀ h ∈ S, h * g = g * h
```
-/

@[to_additive AddSubgroup.centralizer]
def Subgroup.centralizer {G : Type u} [Group G] (S : Set G) : Subgroup G where
  carrier := {g | ∀ h ∈ S, h * g = g * h}
  one_mem' := by
    intro h _
    rw [mul_one, one_mul]
  mul_mem' := by
    intro a b ha hb h hh
    rw [← mul_assoc, ha h hh, mul_assoc, hb h hh, ← mul_assoc]
  inv_mem' := by
    intro a ha h hh
    have e : a⁻¹ * (h * a) * a⁻¹ = a⁻¹ * (a * h) * a⁻¹ := by rw [ha h hh]
    rw [inv_mul_cancel_left, ← mul_assoc, mul_inv_cancel_right] at e
    exact e.symm

/-- @spec -/
example {G : Type u} [Group G] (S : Set G) (g : G) :
    g ∈ Subgroup.centralizer S ↔ ∀ h ∈ S, h * g = g * h := by
  constructor
  · intro hg h hh
    have e := hg h hh
    grind
  · intro hg h hh
    have e := hg h hh
    grind

@[to_additive AddSubgroup.mem_centralizer_iff]
theorem Subgroup.mem_centralizer_iff {G : Type u} [Group G] {S : Set G} {g : G} :
    g ∈ Subgroup.centralizer S ↔ ∀ h ∈ S, h * g = g * h :=
  Iff.rfl

/-! @end -/

/--
@problem conj_stabilizer
@title Stabilizers Under Conjugation Are Centralizers
@concept conjugation

@preamble
A stabilizer under conjugation is a subgroup of `ConjAct G`, and a centralizer is a subgroup of `G`; `ConjAct.ofConjAct` passes from the one to the other.

The context holds `ConjAct.smul_def` of this concept; `MulAction.mem_stabilizer_iff` of the concept on stabilizers; `Subgroup.mem_centralizer_iff` of the previous problem; Mathlib's `Set.mem_singleton` and `Set.mem_singleton_iff`, met in the section on subgroups; and `inv_mul_cancel_right` and `mul_inv_cancel_right` of the second section.
@description
Show that `g` lies in the stabilizer of `x` under conjugation exactly when `ConjAct.ofConjAct g` lies in the centralizer of `{x}`, under the name `ConjAct.mem_stabilizer_iff`.
-/
theorem ConjAct.mem_stabilizer_iff {G : Type u} [Group G] {x : G} {g : ConjAct G} :
    g ∈ MulAction.stabilizer (ConjAct G) x ↔ ConjAct.ofConjAct g ∈ Subgroup.centralizer {x} := by
  rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def, Subgroup.mem_centralizer_iff]
  constructor
  · intro e h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have e2 : ConjAct.ofConjAct g * x * (ConjAct.ofConjAct g)⁻¹ * ConjAct.ofConjAct g =
        x * ConjAct.ofConjAct g := by rw [e]
    rw [inv_mul_cancel_right] at e2
    exact e2.symm
  · intro e
    rw [← e x (Set.mem_singleton x), mul_inv_cancel_right]

/-!
@problem d4_conj_classes
@title The Conjugacy Classes of D₄
@concept conjugation

@preamble
The eight symmetries of the square fall into five conjugacy classes: three of two elements, and two of one element each, the fixed points of conjugation.

On a membership in an orbit of `ConjAct (DihedralGroup 4)`, `decide` fails for want of a `Decidable` instance. The context holds `ConjAct.mem_orbit_iff` and `ConjAct.mem_fixedPoints_iff` of this concept, and of the section on subgroups
```lean
d4_center : ∀ x : DihedralGroup 4,
    x ∈ Subgroup.center (DihedralGroup 4) ↔
      x = r 0 ∨ x = r 2
```
@description
Show that the conjugacy classes of `r 1`, of `sr 0` and of `sr 1` in `DihedralGroup 4` have two elements each, as stated, and that the fixed points of conjugation in `DihedralGroup 4` are `r 0` and `r 2`.
-/

open DihedralGroup in
theorem d4_conj_classes :
    (∀ y : DihedralGroup 4,
      y ∈ MulAction.orbit (ConjAct (DihedralGroup 4)) (r 1) ↔ y = r 1 ∨ y = r 3) ∧
    (∀ y : DihedralGroup 4,
      y ∈ MulAction.orbit (ConjAct (DihedralGroup 4)) (sr 0) ↔ y = sr 0 ∨ y = sr 2) ∧
    (∀ y : DihedralGroup 4,
      y ∈ MulAction.orbit (ConjAct (DihedralGroup 4)) (sr 1) ↔ y = sr 1 ∨ y = sr 3) := by
  simp only [ConjAct.mem_orbit_iff]
  decide

open DihedralGroup in
theorem d4_conj_fixedPoints (x : DihedralGroup 4) :
    x ∈ MulAction.fixedPoints (ConjAct (DihedralGroup 4)) (DihedralGroup 4) ↔ x = r 0 ∨ x = r 2 := by
  rw [ConjAct.mem_fixedPoints_iff]
  exact d4_center x

/-! @end -/

end GroupTheory
