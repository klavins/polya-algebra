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
import PolyaAlgebra.GroupTheory.Actions

/-! @section Counting with Actions -/

universe u v

namespace GroupTheory

set_option linter.translateGenerateName false

/-!
@concept orbit_stabilizer
@title The Orbit–Stabilizer Theorem
@kind theorem

The points of an orbit correspond one for one with the cosets of the stabilizer, since two elements move a point to the same place exactly when they lie in one coset of its stabilizer. So the size of an orbit is the index of the stabilizer, and by Lagrange's theorem it divides the order of the group. It tells the size of an orbit without listing its points.
-/

/-!
@problem of_quotient_stabilizer
@title Acting on a Point Through the Cosets of Its Stabilizer
@concept orbit_stabilizer

@preamble
To count an orbit we match its points with cosets. Two elements `a` and `b` carry `x` to the same point when `a⁻¹ * b` fixes `x`, that is, when they lie in one left coset of the stabilizer of `x`. So acting on `x` is a function on the cosets, sending the class of `g` in `G ⧸ stabilizer G x` to `g • x`. We write it `MulAction.ofQuotientStabilizer G x`.

It is defined on representatives through core Lean's `Quotient.lift`, as the action of `G` on `G ⧸ H` was in the previous section. There `a ≈ b` is `a⁻¹ * b ∈ stabilizer G x` by definition.

The context holds `MulAction.mem_stabilizer_iff` and `mul_smul` of the previous section, and, of the second section,
```lean
mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
```
@description
Define `MulAction.ofQuotientStabilizer G x`, which sends the class of `g` to `g • x`, keeping the `@[to_additive]` line, and prove its equation, which holds by definition, under the name `MulAction.ofQuotientStabilizer_mk`.
-/

@[to_additive AddAction.ofQuotientStabilizer]
def MulAction.ofQuotientStabilizer (G : Type u) {X : Type v} [Group G] [MulAction G X] (x : X) :
    G ⧸ MulAction.stabilizer G x → X :=
  Quotient.lift (fun g => g • x) (by
    intro a b h
    have e : (a⁻¹ * b) • x = x := MulAction.mem_stabilizer_iff.mp h
    rw [← mul_inv_cancel_left a b, mul_smul, e])

/-- @spec -/
example (G : Type u) {X : Type v} [Group G] [MulAction G X] (x : X) (g : G) :
    MulAction.ofQuotientStabilizer G x (QuotientGroup.mk g) = g • x :=
  rfl

@[to_additive AddAction.ofQuotientStabilizer_mk]
theorem MulAction.ofQuotientStabilizer_mk {G : Type u} {X : Type v} [Group G] [MulAction G X]
    (x : X) (g : G) : MulAction.ofQuotientStabilizer G x (QuotientGroup.mk g) = g • x :=
  rfl

/-! @end -/

/-!
@problem injective_of_quotient_stabilizer
@title Different Cosets Move the Point Differently
@concept orbit_stabilizer

@preamble
A statement about every class of `G ⧸ H` reduces to representatives through `QuotientGroup.mk_surjective` of the section on cosets.

The context holds `MulAction.ofQuotientStabilizer_mk` of the previous problem; `MulAction.mem_stabilizer_iff`, `MulAction.mem_orbit_iff`, `mul_smul` and `inv_smul_smul` of the previous section; and `QuotientGroup.mk_surjective` and
```lean
QuotientGroup.eq : (QuotientGroup.mk a : G ⧸ H) =
    QuotientGroup.mk b ↔ a⁻¹ * b ∈ H
```
of the section on cosets.
@description
Show that `MulAction.ofQuotientStabilizer G x` is injective, under the name `MulAction.injective_ofQuotientStabilizer`, and that each of its values lies in the orbit of `x`, under the name `MulAction.ofQuotientStabilizer_mem_orbit`. Keep the `@[to_additive]` lines.
-/

@[to_additive AddAction.injective_ofQuotientStabilizer]
theorem MulAction.injective_ofQuotientStabilizer (G : Type u) {X : Type v} [Group G]
    [MulAction G X] (x : X) : Function.Injective (MulAction.ofQuotientStabilizer G x) := by
  intro p q h
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective p
  obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective q
  rw [← ha, ← hb, MulAction.ofQuotientStabilizer_mk, MulAction.ofQuotientStabilizer_mk] at h
  rw [← ha, ← hb, QuotientGroup.eq, MulAction.mem_stabilizer_iff, mul_smul, ← h, inv_smul_smul]

@[to_additive AddAction.ofQuotientStabilizer_mem_orbit]
theorem MulAction.ofQuotientStabilizer_mem_orbit {G : Type u} {X : Type v} [Group G]
    [MulAction G X] (x : X) (q : G ⧸ MulAction.stabilizer G x) :
    MulAction.ofQuotientStabilizer G x q ∈ MulAction.orbit G x := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective q
  rw [← hg, MulAction.ofQuotientStabilizer_mk, MulAction.mem_orbit_iff]
  exact ⟨g, rfl⟩

/-! @end -/

/-!
@problem orbit_equiv_quotient_stabilizer
@title The Orbit and the Cosets of the Stabilizer
@concept orbit_stabilizer

@preamble
Taken as a function into the orbit of `x`, a set used as a type as in the first section, the function of this concept's first problem is a bijection. So the orbit and the cosets of the stabilizer are matched by an equivalence, which we write `MulAction.orbitEquivQuotientStabilizer G x`. Mathlib's `Equiv.ofBijective`, met in the section on the isomorphism theorems, builds an equivalence from a bijection, running from its domain to its codomain; the equivalence asked for runs from the orbit.

A member of the orbit as a type is a pair `⟨y, hy⟩` of a point and a proof that it lies in the orbit. A goal about `fun q => ⟨…⟩` applied to a class shows the application unreduced; `exact` sees through it and `rw` does not.

The context holds the two theorems of the previous problem, `MulAction.mem_orbit_iff` of the previous section, and core Lean's `Subtype.ext` and `congrArg`.
@description
Define the equivalence `MulAction.orbitEquivQuotientStabilizer G x` between the orbit of `x` and `G ⧸ stabilizer G x`, keeping the `@[to_additive]` line.
-/

@[to_additive AddAction.orbitEquivQuotientStabilizer]
noncomputable def MulAction.orbitEquivQuotientStabilizer (G : Type u) {X : Type v} [Group G]
    [MulAction G X] (x : X) : MulAction.orbit G x ≃ G ⧸ MulAction.stabilizer G x :=
  (Equiv.ofBijective
    (fun q => ⟨MulAction.ofQuotientStabilizer G x q, MulAction.ofQuotientStabilizer_mem_orbit x q⟩)
    (by
      constructor
      · intro p q h
        exact MulAction.injective_ofQuotientStabilizer G x (congrArg Subtype.val h)
      · intro ⟨y, hy⟩
        obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hy
        exact ⟨QuotientGroup.mk g, Subtype.ext hg⟩)).symm

/-- @spec -/
example (G : Type u) {X : Type v} [Group G] [MulAction G X] (x : X) :
    Nonempty (MulAction.orbit G x ≃ G ⧸ MulAction.stabilizer G x) :=
  ⟨MulAction.orbitEquivQuotientStabilizer G x⟩

/-! @end -/

/-!
@problem card_orbit
@title The Orbit–Stabilizer Theorem
@concept orbit_stabilizer

@preamble
When `X` is finite, so is an orbit, a set used as a type, under `open Classical`, and `Fintype.card` counts it as it counts any finite type. The index is the number of elements of `G ⧸ H` by definition.

The context holds `MulAction.orbitEquivQuotientStabilizer` of the previous problem; Mathlib's `Fintype.card_congr`, met in the first section; and, of the section on cosets,
```lean
Subgroup.index_mul_card :
    H.index * Fintype.card H.carrier = Fintype.card G
theorem Nat.dvd_mul_right (a b : ℕ) : a ∣ a * b
```
the last core Lean's.
@description
Show that the size of the orbit of `x` is the index of its stabilizer, under the name `MulAction.card_orbit_eq_index`; that the size of the orbit times the order of the stabilizer is the order of `G`, under the name `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`; and that the size of the orbit divides the order of `G`, under the name `MulAction.card_orbit_dvd_card`. Keep the `open Classical in` and `@[to_additive]` lines.
-/

open Classical in
@[to_additive AddAction.card_orbit_eq_index]
theorem MulAction.card_orbit_eq_index {G : Type u} {X : Type v} [Group G] [MulAction G X]
    [Fintype G] [Fintype X] (x : X) :
    Fintype.card (MulAction.orbit G x) = (MulAction.stabilizer G x).index :=
  Fintype.card_congr (MulAction.orbitEquivQuotientStabilizer G x)

open Classical in
@[to_additive AddAction.card_orbit_mul_card_stabilizer_eq_card_addGroup]
theorem MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G : Type u) {X : Type v}
    [Group G] [MulAction G X] [Fintype G] [Fintype X] (x : X) :
    Fintype.card (MulAction.orbit G x) * Fintype.card (MulAction.stabilizer G x).carrier =
      Fintype.card G := by
  rw [MulAction.card_orbit_eq_index, Subgroup.index_mul_card]

open Classical in
@[to_additive AddAction.card_orbit_dvd_card]
theorem MulAction.card_orbit_dvd_card (G : Type u) {X : Type v} [Group G] [MulAction G X]
    [Fintype G] [Fintype X] (x : X) : Fintype.card (MulAction.orbit G x) ∣ Fintype.card G := by
  rw [← MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x]
  exact Nat.dvd_mul_right _ _

/-! @end -/

/-!
@problem card_stabilizer_dihedral
@title The Stabilizer of a Vertex Has Two Elements
@concept orbit_stabilizer

@preamble
The previous section found which symmetries of the triangle fix the vertex `0`; here they are counted for every `n`. A function from the orbit, as a type, needs the type of its binder written, since a bare `y` is taken as a residue. A rewrite of `n` inside `ZMod n` fails, as in the section on cyclic groups, since `n` is in the type too. Core Lean has
```lean
theorem Nat.eq_of_mul_eq_mul_left (hn : 0 < n)
    (h : n * m = n * k) : m = k
```
The context holds `MulAction.card_orbit_mul_card_stabilizer_eq_card_group` of the previous problem; `MulAction.mem_orbit_iff` and `MulAction.exists_smul_eq G x y` of the previous section, which applies by the instance `DihedralGroup.isPretransitive`; `card_zmod` and `card_dihedral` of the section on examples; Mathlib's `Fintype.card_of_bijective` and `Subtype.val_injective`; and core Lean's `Nat.mul_comm` and `Nat.pos_of_neZero`, which gives `0 < n` from `[NeZero n]`.
@description
Show that the orbit of the vertex `0` under `DihedralGroup n` has `n` points, under the name `card_orbit_dihedral`, and that its stabilizer has `2` elements, under the name `card_stabilizer_dihedral`.
-/

open Classical in
theorem card_orbit_dihedral (n : ℕ) [NeZero n] :
    Fintype.card (MulAction.orbit (DihedralGroup n) (0 : ZMod n)) = n := by
  have hb : Function.Bijective
      (fun y : MulAction.orbit (DihedralGroup n) (0 : ZMod n) => (y : ZMod n)) := by
    constructor
    · exact Subtype.val_injective
    · intro v
      exact ⟨⟨v, MulAction.mem_orbit_iff.mpr (MulAction.exists_smul_eq (DihedralGroup n) 0 v)⟩, rfl⟩
  rw [Fintype.card_of_bijective hb, card_zmod]

open Classical in
theorem card_stabilizer_dihedral (n : ℕ) [NeZero n] :
    Fintype.card (MulAction.stabilizer (DihedralGroup n) (0 : ZMod n)).carrier = 2 := by
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (DihedralGroup n) (0 : ZMod n)
  rw [card_orbit_dihedral, card_dihedral, Nat.mul_comm 2 n] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_neZero n) h

/-! @end -/

/-!
@concept block_counting
@title Counting by Blocks
@kind theorem

A function cuts a finite set into blocks, the elements it sends to each value, and a finite set is counted block by block. The orbits of an action are blocks. When the orbit of every point that is not fixed has a multiple of p points, counting by orbits gives as many points as fixed points, modulo p.
-/

/-!
@problem card_filter_mem_insert
@title Adding a Value Adds Its Block
@concept block_counting

@preamble
We count with Mathlib's `Finset α`, writing `s.card` for the number of elements of `s` and `s.filter p` for those with the property `p`, which Lean prints `{a ∈ s | p a}`. For `f : α → β`, the *block* of `b` and the elements sent into `S` are
```lean
s.filter (fun a => f a = b)   -- the block of b
s.filter (fun a => f a ∈ S)   -- sent into S
```
and `[DecidableEq β]` lets Lean test them. We write `insert b S` for `S` with `b` added. Mathlib has
```lean
Finset.card_union_of_disjoint (h : Disjoint s t) :
    (s ∪ t).card = s.card + t.card
Finset.disjoint_filter : Disjoint (s.filter p)
    (s.filter q) ↔ ∀ x ∈ s, p x → ¬q x
```
`Finset.filter_or`, which splits the filter by `p a ∨ q a` into a union, and `Finset.mem_insert`. `rw` cannot rewrite a term that mentions the `a` of `fun a => …`, such as `f a ∈ insert b S`, while `simp only` can.
@description
Show that when `b ∉ S`, the elements of `s` sent into `insert b S` number those of the block of `b` and those sent into `S` together, under the name `card_filter_mem_insert`, keeping the `open Classical in` line.
-/

/-- @given -/
theorem filter_mem_empty {α : Type u} {β : Type v} [DecidableEq β] (s : Finset α) (f : α → β) :
    s.filter (fun a => f a ∈ (∅ : Finset β)) = ∅ := by
  apply Finset.filter_false_of_mem
  intro a _
  exact Finset.notMem_empty (f a)

open Classical in
theorem card_filter_mem_insert {α : Type u} {β : Type v} [DecidableEq β] (s : Finset α)
    (f : α → β) {b : β} {S : Finset β} (hb : b ∉ S) :
    (s.filter (fun a => f a ∈ insert b S)).card =
      (s.filter (fun a => f a = b)).card + (s.filter (fun a => f a ∈ S)).card := by
  simp only [Finset.mem_insert]
  rw [Finset.filter_or, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_filter]
  intro a _ h1 h2
  rw [h1] at h2
  exact hb h2

/-! @end -/

/-!
@problem card_filter_mem_eq_zero
@title Empty Blocks Send Nothing Into a Set
@concept block_counting

@preamble
A statement about every finite set `S` is proved by induction: for the empty set, and for `insert b S` with `b ∉ S` from the statement for `S`. Mathlib's principle is `Finset.induction_on`, used as
```lean
induction S using Finset.induction_on with
| empty => sorry
| insert b S hb ih => sorry
```
with `hb : b ∉ S` and `ih` the statement for `S`. Mathlib's `Finset.card_empty` says that `∅` has no elements.

The context holds `card_filter_mem_insert` of the previous problem and `filter_mem_empty`, given there, by which nothing of `s` is sent into `∅`.
@description
Show that when every block of `f` in `s` is empty, no element of `s` is sent into `S`, under the name `card_filter_mem_eq_zero`.
-/

open Classical in
theorem card_filter_mem_eq_zero {α : Type u} {β : Type v} [DecidableEq β] (s : Finset α)
    (f : α → β) (h : ∀ b, (s.filter (fun a => f a = b)).card = 0) (S : Finset β) :
    (s.filter (fun a => f a ∈ S)).card = 0 := by
  induction S using Finset.induction_on with
  | empty => rw [filter_mem_empty, Finset.card_empty]
  | insert b S hb ih => rw [card_filter_mem_insert s f hb, h b, ih]

/-! @end -/

/-!
@problem card_filter_mem_eq_mul
@title Blocks of Equal Size Count by Multiplication
@concept block_counting

@preamble
When every block has `k` elements, the count goes by induction on `S` as in the previous problem. Mathlib has
```lean
theorem Finset.card_insert_of_notMem (h : a ∉ s) :
    (insert a s).card = s.card + 1
```
`omega` treats `k * (m + 1)` as an unknown of its own; core Lean has
```lean
theorem Nat.mul_add_one (n m : ℕ) :
    n * (m + 1) = n * m + n
```
and `Nat.mul_zero` and `Nat.add_comm`. The context holds `filter_mem_empty` and `card_filter_mem_insert` of this concept's first problem, and Mathlib's `Finset.card_empty`, which rewrites the empty set of one type at a time.
@description
Show that when every block of `f` in `s` has `k` elements, the elements of `s` sent into `S` number `k * S.card`, under the name `card_filter_mem_eq_mul`.
-/

open Classical in
theorem card_filter_mem_eq_mul {α : Type u} {β : Type v} [DecidableEq β] (s : Finset α)
    (f : α → β) (k : ℕ) (h : ∀ b, (s.filter (fun a => f a = b)).card = k) (S : Finset β) :
    (s.filter (fun a => f a ∈ S)).card = k * S.card := by
  induction S using Finset.induction_on with
  | empty => rw [filter_mem_empty, Finset.card_empty, Finset.card_empty, Nat.mul_zero]
  | insert b S hb ih =>
    rw [card_filter_mem_insert s f hb, ih, h b, Finset.card_insert_of_notMem hb, Nat.mul_add_one,
      Nat.add_comm]

/-! @end -/

/-!
@problem card_filter_mem_mod
@title Sets Whose Blocks Agree Modulo p Agree Modulo p
@concept block_counting

@preamble
Counting modulo a number `p` goes block by block too. Here two finite sets `s` and `t` are cut by the same function. Core Lean has
```lean
theorem Nat.add_mod (a b n : ℕ) :
    (a + b) % n = (a % n + b % n) % n
```
A bare `rw [Nat.add_mod]` rewrites the first sum of the right shape it finds. The context holds `filter_mem_empty` and `card_filter_mem_insert` of this concept's first problem.
@description
Show that if the blocks of `f` in `s` and in `t` have the same number of elements modulo `p` for every value, then so do the elements of `s` and of `t` sent into `S`, under the name `card_filter_mem_mod`.
-/

open Classical in
theorem card_filter_mem_mod {α : Type u} {β : Type v} [DecidableEq β] (s t : Finset α)
    (f : α → β) (p : ℕ)
    (h : ∀ b, (s.filter (fun a => f a = b)).card % p = (t.filter (fun a => f a = b)).card % p)
    (S : Finset β) :
    (s.filter (fun a => f a ∈ S)).card % p = (t.filter (fun a => f a ∈ S)).card % p := by
  induction S using Finset.induction_on with
  | empty => rw [filter_mem_empty, filter_mem_empty]
  | insert b S hb ih =>
    rw [card_filter_mem_insert s f hb, card_filter_mem_insert t f hb, Nat.add_mod, h b, ih,
      ← Nat.add_mod]

/-! @end -/

/-!
@problem card_block_eq_card_orbit
@title An Orbit Is a Block
@concept block_counting

@preamble
The orbits are the classes of the setoid `MulAction.orbitRel G X` of the previous section. The quotient by it has one element for each orbit, and `Quotient.mk _` sends each point to its class, printed `⟦a⟧` as in the first section. Its block over the class of `x` is the orbit of `x`; there `a ≈ x` is `a ∈ MulAction.orbit G x` by definition. Under `open Classical`, Lean can decide whether two classes are equal. `Finset.univ` is the finite set of all the elements of a finite type, and an orbit as a type is `{y // y ∈ MulAction.orbit G x}`. Mathlib has
```lean
theorem Fintype.card_of_subtype (s : Finset α)
    (H : ∀ x, x ∈ s ↔ p x) :
    Fintype.card {x // p x} = s.card
theorem Finset.mem_filter :
    a ∈ s.filter p ↔ a ∈ s ∧ p a
```
and `Finset.mem_univ a : a ∈ Finset.univ`. The context holds core Lean's `Quotient.sound` and `Quotient.exact`, met in the first section.
@description
Show that the points whose orbit is the orbit of `x` are as many as the points of the orbit of `x`, under the name `MulAction.card_block_eq_card_orbit`, keeping the `@[to_additive]` line.
-/

open Classical in
@[to_additive AddAction.card_block_eq_card_orbit]
theorem MulAction.card_block_eq_card_orbit {G : Type u} {X : Type v} [Group G] [MulAction G X]
    [Fintype X] (x : X) :
    (Finset.univ.filter (fun a : X => Quotient.mk (MulAction.orbitRel G X) a =
      Quotient.mk (MulAction.orbitRel G X) x)).card = Fintype.card (MulAction.orbit G x) := by
  apply Eq.symm
  apply Fintype.card_of_subtype
  intro a
  rw [Finset.mem_filter]
  constructor
  · intro ⟨_, h⟩
    exact Quotient.exact h
  · intro h
    exact ⟨Finset.mem_univ a, Quotient.sound h⟩

/-! @end -/

/--
@problem eq_of_mem_orbit_of_mem_fixed_points
@title A Fixed Point Is Alone in Its Orbit
@concept block_counting

@preamble
To count a block by its fixed points we first see where a fixed point can lie.

The context holds `MulAction.mem_orbit_iff`, `MulAction.mem_fixedPoints` and `inv_smul_smul` of the previous section.
@description
Show that if a fixed point `y` lies in the orbit of `x`, then `x = y`, under the name `MulAction.eq_of_mem_orbit_of_mem_fixedPoints`, keeping the `@[to_additive]` line.
-/
@[to_additive AddAction.eq_of_mem_orbit_of_mem_fixedPoints]
theorem MulAction.eq_of_mem_orbit_of_mem_fixedPoints {G : Type u} {X : Type v} [Group G]
    [MulAction G X] {x y : X} (hy : y ∈ MulAction.orbit G x) (hf : y ∈ MulAction.fixedPoints G X) :
    x = y := by
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hy
  rw [← inv_smul_smul g x, hg, MulAction.mem_fixedPoints.mp hf g⁻¹]

/-!
@problem filter_block_fixed_points
@title A Block Is All Fixed or Holds No Fixed Point
@concept block_counting

@preamble
Each finite set below keeps, of the block of `x`, the points `a` that are fixed. The previous problem's theorem reads
```lean
MulAction.eq_of_mem_orbit_of_mem_fixedPoints
    (hy : y ∈ MulAction.orbit G x)
    (hf : y ∈ MulAction.fixedPoints G X) : x = y
```
and core Lean's `Quotient.exact`, met in the first section, turns `⟦a⟧ = ⟦x⟧` into `a ≈ x`, that is, `a ∈ MulAction.orbit G x`. Mathlib has
```lean
theorem Finset.filter_false_of_mem
    (h : ∀ x ∈ s, ¬p x) : s.filter p = ∅
theorem Finset.filter_congr
    (H : ∀ x ∈ s, p x ↔ q x) :
    s.filter p = s.filter q
```
@description
Show that the fixed points in the block of a fixed point `x` are its whole block, under the name `MulAction.filter_block_of_mem_fixedPoints`, and that the block of a point `x` that is not fixed holds no fixed point, under the name `MulAction.filter_block_of_notMem_fixedPoints`. Keep the `open Classical in` and `@[to_additive]` lines.
-/

open Classical in
@[to_additive AddAction.filter_block_of_mem_fixedPoints]
theorem MulAction.filter_block_of_mem_fixedPoints {G : Type u} {X : Type v} [Group G]
    [MulAction G X] [Fintype X] {x : X} (hx : x ∈ MulAction.fixedPoints G X) :
    Finset.univ.filter (fun a : X => a ∈ MulAction.fixedPoints G X ∧
      Quotient.mk (MulAction.orbitRel G X) a = Quotient.mk (MulAction.orbitRel G X) x) =
    Finset.univ.filter (fun a : X =>
      Quotient.mk (MulAction.orbitRel G X) a = Quotient.mk (MulAction.orbitRel G X) x) := by
  apply Finset.filter_congr
  intro a _
  constructor
  · intro ⟨_, e⟩
    exact e
  · intro e
    have hax : a = x := MulAction.eq_of_mem_orbit_of_mem_fixedPoints (Quotient.exact e.symm) hx
    rw [hax]
    exact ⟨hx, rfl⟩

open Classical in
@[to_additive AddAction.filter_block_of_notMem_fixedPoints]
theorem MulAction.filter_block_of_notMem_fixedPoints {G : Type u} {X : Type v} [Group G]
    [MulAction G X] [Fintype X] {x : X} (hx : x ∉ MulAction.fixedPoints G X) :
    Finset.univ.filter (fun a : X => a ∈ MulAction.fixedPoints G X ∧
      Quotient.mk (MulAction.orbitRel G X) a = Quotient.mk (MulAction.orbitRel G X) x) = ∅ := by
  apply Finset.filter_false_of_mem
  intro a _ ⟨ha, e⟩
  have hxa : x = a := MulAction.eq_of_mem_orbit_of_mem_fixedPoints (Quotient.exact e) ha
  rw [hxa] at hx
  exact hx ha

/-! @end -/

/-!
@problem card_block_mod
@title A Block Has As Many Points as Fixed Points, Modulo p
@concept block_counting

@preamble
Here the block is over a class `b` of the quotient, not over the class of a named point. A statement about every class reduces to representatives through core Lean's `Quotient.inductionOn`, met in the first section. Mathlib has
```lean
theorem Finset.filter_filter :
    (s.filter p).filter q =
      s.filter (fun a => p a ∧ q a)
```
The context holds `MulAction.card_block_eq_card_orbit` and the two theorems of the previous problem, and core Lean's `Nat.zero_mod` and `Nat.mod_eq_zero_of_dvd`, met in the section on homomorphisms.
@description
Show that, when the orbit of every point that is not fixed has a multiple of `p` points, each block has as many points as fixed points modulo `p`, under the name `MulAction.card_block_mod`, keeping the `@[to_additive]` line.
-/

open Classical in
@[to_additive AddAction.card_block_mod]
theorem MulAction.card_block_mod {G : Type u} {X : Type v} [Group G] [MulAction G X] [Fintype X]
    {p : ℕ} (h : ∀ x : X, x ∉ MulAction.fixedPoints G X → p ∣ Fintype.card (MulAction.orbit G x))
    (b : Quotient (MulAction.orbitRel G X)) :
    (Finset.univ.filter (fun a : X => Quotient.mk (MulAction.orbitRel G X) a = b)).card % p =
    ((Finset.univ.filter (fun a : X => a ∈ MulAction.fixedPoints G X)).filter
      (fun a : X => Quotient.mk (MulAction.orbitRel G X) a = b)).card % p := by
  induction b using Quotient.inductionOn with
  | h x =>
    rw [Finset.filter_filter]
    by_cases hx : x ∈ MulAction.fixedPoints G X
    · rw [MulAction.filter_block_of_mem_fixedPoints hx]
    · rw [MulAction.filter_block_of_notMem_fixedPoints hx, Finset.card_empty, Nat.zero_mod,
        MulAction.card_block_eq_card_orbit, Nat.mod_eq_zero_of_dvd (h x hx)]

/-! @end -/

/-!
@problem card_mod_eq_card_fixed_points
@title The Fixed Points Count the Set Modulo p
@concept block_counting

@preamble
The whole of `X` is counted by the blocks of the function sending each point to its class. Under `open Classical` the quotient is a finite type too, so `Finset.univ` lists its classes. Mathlib has
```lean
theorem Finset.card_univ :
    Finset.univ.card = Fintype.card α
theorem Finset.filter_true_of_mem
    (h : ∀ x ∈ s, p x) : s.filter p = s
```
and `Fintype.card_of_subtype`, `Finset.mem_filter` and `Finset.mem_univ`, met in this concept. The context holds `card_filter_mem_mod` and `MulAction.card_block_mod` of this concept.
@description
Show that `X` has as many points as fixed points modulo `p` when the orbit of every point that is not fixed has a multiple of `p` points, under the name `MulAction.card_mod_eq_card_fixedPoints`, keeping the `@[to_additive]` line.
-/

open Classical in
@[to_additive AddAction.card_mod_eq_card_fixedPoints]
theorem MulAction.card_mod_eq_card_fixedPoints {G : Type u} {X : Type v} [Group G]
    [MulAction G X] [Fintype X] {p : ℕ}
    (h : ∀ x : X, x ∉ MulAction.fixedPoints G X → p ∣ Fintype.card (MulAction.orbit G x)) :
    Fintype.card X % p = Fintype.card (MulAction.fixedPoints G X) % p := by
  have e := card_filter_mem_mod Finset.univ
    (Finset.univ.filter (fun a : X => a ∈ MulAction.fixedPoints G X))
    (Quotient.mk (MulAction.orbitRel G X)) p (MulAction.card_block_mod h) Finset.univ
  rw [Finset.filter_true_of_mem (fun a _ => Finset.mem_univ _),
    Finset.filter_true_of_mem (fun a _ => Finset.mem_univ _), Finset.card_univ] at e
  rw [e, Fintype.card_of_subtype]
  intro a
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ a, h⟩⟩

/-! @end -/

/-!
@concept class_equation
@title p-Groups and Their Centres
@kind theorem

A group whose order is a power of a prime p is a p-group. Acting on a finite set, a p-group has as many points as fixed points, modulo p. Acting on itself by conjugation, a p-group other than the trivial group finds in this way an element of its centre other than the neutral one.
-/

/-!
@problem is_p_group
@title Groups of Prime Power Order
@concept class_equation

@preamble
A *`p`-group* is a finite group whose order is a power of `p`, and we write `IsPGroup p G`; the definition does not ask that `p` be prime. Mathlib's `IsPGroup` asks instead that each element `g` have `g ^ p ^ k = 1` for some `k`, which also makes sense for infinite groups.

The context holds `card_dihedral n` of the section on examples, by which `DihedralGroup n` has `2 * n` elements.
@description
Define `IsPGroup p G`, keeping the `@[to_additive]` line, and show that `DihedralGroup 4` is a `2`-group, under the name `isPGroup_dihedral_four`.
-/

@[to_additive IsAddPGroup]
def IsPGroup (p : ℕ) (G : Type u) [Group G] [Fintype G] : Prop :=
  ∃ n : ℕ, Fintype.card G = p ^ n

/-- @spec -/
example (p : ℕ) (G : Type u) [Group G] [Fintype G] :
    IsPGroup p G ↔ ∃ n : ℕ, Fintype.card G = p ^ n := by
  constructor
  · intro ⟨n, h⟩
    exact ⟨n, by grind⟩
  · intro ⟨n, h⟩
    exact ⟨n, by grind⟩

theorem isPGroup_dihedral_four : IsPGroup 2 (DihedralGroup 4) :=
  ⟨3, card_dihedral 4⟩

/-! @end -/

/-!
@problem mem_fixed_points_of_card_orbit_eq_one
@title A Point With a One-Point Orbit Is Fixed
@concept class_equation

@preamble
Mathlib has
```lean
theorem Fintype.card_eq_one_iff :
    Fintype.card α = 1 ↔ ∃ x, ∀ y : α, y = x
```
shown in the section on cyclic groups, where it found the subgroups with one element.

The context holds, of the previous section, `MulAction.mem_orbit_self` and
```lean
MulAction.mem_orbit_iff :
    y ∈ MulAction.orbit G x ↔ ∃ g, g • x = y
MulAction.mem_fixedPoints :
    x ∈ MulAction.fixedPoints G X ↔ ∀ g, g • x = x
```
and core Lean's `congrArg`.
@description
Show that a point whose orbit has one point is a fixed point, under the name `MulAction.mem_fixedPoints_of_card_orbit_eq_one`, keeping the `@[to_additive]` line.
-/

open Classical in
@[to_additive AddAction.mem_fixedPoints_of_card_orbit_eq_one]
theorem MulAction.mem_fixedPoints_of_card_orbit_eq_one {G : Type u} {X : Type v} [Group G]
    [MulAction G X] [Fintype X] {x : X}
    (h : Fintype.card (MulAction.orbit G x) = 1) : x ∈ MulAction.fixedPoints G X := by
  obtain ⟨y, hy⟩ := Fintype.card_eq_one_iff.mp h
  rw [MulAction.mem_fixedPoints]
  intro g
  have e : (⟨g • x, MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩⟩ : MulAction.orbit G x) =
      ⟨x, MulAction.mem_orbit_self x⟩ := by
    rw [hy ⟨g • x, _⟩, hy ⟨x, _⟩]
  exact congrArg Subtype.val e

/-! @end -/

/-!
@problem is_p_group_card_mod
@title A p-Group Counts a Set by Its Fixed Points
@concept class_equation

@preamble
The context holds `MulAction.card_mod_eq_card_fixedPoints` of the previous concept and `MulAction.mem_fixedPoints_of_card_orbit_eq_one` of the previous problem; of this section's first concept,
```lean
MulAction.card_orbit_dvd_card G x :
    Fintype.card (MulAction.orbit G x) ∣ Fintype.card G
```
and, of the section on cyclic groups,
```lean
theorem Nat.Prime.dvd_of_dvd_pow_of_ne_one
    (hp : Nat.Prime p) (hm : m ∣ p ^ n)
    (h1 : m ≠ 1) : p ∣ m
```
@description
Show that when a `p`-group acts on `X`, for a prime `p`, the orbit of a point that is not fixed has a multiple of `p` points, under the name `IsPGroup.dvd_card_orbit`, and that `X` has as many points as fixed points modulo `p`, under the name `IsPGroup.card_mod_eq_card_fixedPoints`. Keep the `@[to_additive]` lines.
-/

open Classical in
@[to_additive IsAddPGroup.dvd_card_orbit]
theorem IsPGroup.dvd_card_orbit {p : ℕ} {G : Type u} {X : Type v} [Group G] [MulAction G X]
    [Fintype G] [Fintype X] (hp : Nat.Prime p) (hG : IsPGroup p G) {x : X}
    (hx : x ∉ MulAction.fixedPoints G X) : p ∣ Fintype.card (MulAction.orbit G x) := by
  obtain ⟨n, hn⟩ := hG
  have hd := MulAction.card_orbit_dvd_card G x
  rw [hn] at hd
  apply hp.dvd_of_dvd_pow_of_ne_one hd
  intro h1
  exact hx (MulAction.mem_fixedPoints_of_card_orbit_eq_one h1)

open Classical in
@[to_additive IsAddPGroup.card_mod_eq_card_fixedPoints]
theorem IsPGroup.card_mod_eq_card_fixedPoints {p : ℕ} {G : Type u} {X : Type v} [Group G]
    [MulAction G X] [Fintype G] [Fintype X] (hp : Nat.Prime p) (hG : IsPGroup p G) :
    Fintype.card X % p = Fintype.card (MulAction.fixedPoints G X) % p :=
  MulAction.card_mod_eq_card_fixedPoints (fun _ hx => hG.dvd_card_orbit hp hx)

/-! @end -/

/-!
@problem dvd_card_center
@title The Centre of a Group of Order pⁿ, n > 0, Has a Multiple of p Elements
@concept class_equation

@preamble
`ConjAct G` acts on `G` by conjugation, with the centre as its fixed points, by the previous section. Being `G` under a second name, it has the elements of `G`; the instance `ConjAct.instFintype` below copies the finite type, as `ConjAct.instGroup` copied the group. Conjugation has no additive version, so neither have this theorem and those that use it.

An equation of sets proved by `Set.ext` rewrites inside the count of the set as a type. Core Lean has `Nat.pow_one`, and
```lean
theorem Nat.pow_dvd_pow (b : ℕ) (h : m ≤ n) :
    b ^ m ∣ b ^ n
```
in which `0 < n` serves as `1 ≤ n`, by definition. The context holds `IsPGroup.card_mod_eq_card_fixedPoints` of the previous problem, `ConjAct.mem_fixedPoints_iff` of the previous section and `ConjAct.card`, given below. It also holds Mathlib's `Set.ext` and core Lean's `Nat.mod_eq_zero_of_dvd` and `Nat.dvd_of_mod_eq_zero`, met in the section on homomorphisms.
@description
Show that for a prime `p`, the centre of a group of order `p ^ n` with `n > 0` has a multiple of `p` elements, under the name `IsPGroup.dvd_card_center`.
-/

/-- @given -/
instance ConjAct.instFintype {G : Type u} [Fintype G] : Fintype (ConjAct G) :=
  inferInstanceAs (Fintype G)

/-- @given -/
theorem ConjAct.card {G : Type u} [Fintype G] : Fintype.card (ConjAct G) = Fintype.card G :=
  rfl

open Classical in
theorem IsPGroup.dvd_card_center {p n : ℕ} {G : Type u} [Group G] [Fintype G] (hp : Nat.Prime p)
    (hG : Fintype.card G = p ^ n) (hn : 0 < n) : p ∣ Fintype.card (Subgroup.center G).carrier := by
  have hc : IsPGroup p (ConjAct G) := ⟨n, by rw [ConjAct.card, hG]⟩
  have e : Fintype.card G % p = Fintype.card (MulAction.fixedPoints (ConjAct G) G) % p :=
    hc.card_mod_eq_card_fixedPoints hp
  have hs : MulAction.fixedPoints (ConjAct G) G = (Subgroup.center G).carrier := by
    apply Set.ext
    intro x
    exact ConjAct.mem_fixedPoints_iff
  have hd : p ∣ p ^ n := by
    have h1 := Nat.pow_dvd_pow p hn
    rw [Nat.pow_one] at h1
    exact h1
  rw [hs, hG, Nat.mod_eq_zero_of_dvd hd] at e
  exact Nat.dvd_of_mod_eq_zero e.symm

/-! @end -/

/-!
@problem exists_ne_one_mem_center
@title A Group of Order pⁿ, n > 0, Has Central Elements Other Than One
@concept class_equation

@preamble
Mathlib has
```lean
Fintype.exists_ne_of_one_lt_card
    (h : 1 < Fintype.card α) (a : α) : ∃ b, b ≠ a
Fintype.card_pos_iff :
    0 < Fintype.card α ↔ Nonempty α
```
The context holds `IsPGroup.dvd_card_center` of the previous problem; `Nat.Prime.two_le` of the section on cyclic groups; core Lean's `Nat.le_of_dvd` and `Subtype.ext`; and `Subgroup.one_mem` of the section on subgroups.
@description
Show that for a prime `p`, the centre of a group of order `p ^ n` with `n > 0` holds an element other than `1`, under the name `IsPGroup.exists_ne_one_mem_center`.
-/

open Classical in
theorem IsPGroup.exists_ne_one_mem_center {p n : ℕ} {G : Type u} [Group G] [Fintype G]
    (hp : Nat.Prime p) (hG : Fintype.card G = p ^ n) (hn : 0 < n) :
    ∃ z ∈ Subgroup.center G, z ≠ 1 := by
  have hd := IsPGroup.dvd_card_center hp hG hn
  have hpos : 0 < Fintype.card (Subgroup.center G).carrier :=
    Fintype.card_pos_iff.mpr ⟨⟨1, (Subgroup.center G).one_mem⟩⟩
  have h1 : 1 < Fintype.card (Subgroup.center G).carrier := by
    have h2 := hp.two_le
    have h3 := Nat.le_of_dvd hpos hd
    omega
  obtain ⟨z, hz⟩ := Fintype.exists_ne_of_one_lt_card h1 ⟨1, (Subgroup.center G).one_mem⟩
  exact ⟨z, z.2, fun e => hz (Subtype.ext e)⟩

/-! @end -/

/-!
@concept prime_square
@title Groups of Order p²
@kind theorem
@goal

Every group of order p², for a prime p, is commutative. It is the goal of the subject, the first theorem about all groups of one order that counting with actions gives.
-/

/--
@problem exists_zpow_mem
@title A Class Among the Powers of a Class Has a Power as Representative
@concept prime_square

@preamble
The quotient map `QuotientGroup.mk' N` of the section on quotient groups has `QuotientGroup.mk` as its function, by definition.

The context holds
```lean
GroupHom.map_zpow (f : G →* H) (a : G) (k : ℤ) :
    f.toFun (a ^ k) = f.toFun a ^ k
```
of the section on homomorphisms, `QuotientGroup.eq` of the section on cosets, and, of the section on subgroups,
```lean
Subgroup.mem_zpowers_iff :
    x ∈ Subgroup.zpowers g ↔ ∃ k : ℤ, g ^ k = x
```
@description
Show that if the class of `a` lies in the subgroup generated by the class of `g`, then `(g ^ k)⁻¹ * a ∈ N` for some integer `k`, under the name `QuotientGroup.exists_zpow_mem`, keeping the `@[to_additive]` line.
-/
@[to_additive QuotientAddGroup.exists_zsmul_mem]
theorem QuotientGroup.exists_zpow_mem {G : Type u} [Group G] {N : Subgroup G} [N.Normal] {g a : G}
    (h : (QuotientGroup.mk a : G ⧸ N) ∈ Subgroup.zpowers (QuotientGroup.mk g)) :
    ∃ k : ℤ, (g ^ k)⁻¹ * a ∈ N := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  have e := GroupHom.map_zpow (QuotientGroup.mk' N) g k
  exact ⟨k, QuotientGroup.eq.mp (e.trans hk)⟩

/--
@problem mul_comm_of_mem_center
@title Central Factors Keep Commuting Elements Commuting
@concept prime_square

@preamble
The chain of expressions, up to regrouping, is
```lean
x * z * (y * w) = x * y * (z * w)
  = y * x * (w * z) = y * w * (x * z)
```
The context holds `mul_assoc` of the second section and, of the section on subgroups,
```lean
Subgroup.mem_center_iff :
    z ∈ Subgroup.center G ↔ ∀ g, g * z = z * g
```
@description
Show that when `x` and `y` commute and `z` and `w` lie in the centre, `x * z` and `y * w` commute, under the name `mul_comm_of_mem_center`, keeping the `@[to_additive]` line.
-/
@[to_additive add_comm_of_mem_center]
theorem mul_comm_of_mem_center {G : Type u} [Group G] {x y z w : G} (hxy : x * y = y * x)
    (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G) :
    x * z * (y * w) = y * w * (x * z) := by
  rw [Subgroup.mem_center_iff] at hz hw
  calc x * z * (y * w) = x * y * (z * w) := by
        rw [mul_assoc, ← mul_assoc z, ← hz y, mul_assoc y, ← mul_assoc]
    _ = y * x * (w * z) := by rw [hxy, ← hz w]
    _ = y * w * (x * z) := by rw [mul_assoc, ← mul_assoc x, hw x, mul_assoc w, ← mul_assoc]

/--
@problem mul_comm_of_is_cyclic_quotient_center
@title A Group Cyclic Modulo Its Centre Is Commutative
@concept prime_square

@preamble
A group is commutative when its centre is the whole group; a weaker test looks at the quotient by the centre. `G ⧸ center G` is a group since the centre is normal, by an instance of the section on quotient groups, and `IsCyclic` of the section on subgroups asks for an element `g` with every element in `Subgroup.zpowers g`.

The context holds the theorems of the previous two problems; `QuotientGroup.mk_surjective` of the section on cosets; `zpow_add` of the section on powers; `mul_inv_cancel_left` of the second section; and core Lean's `Int.add_comm : a + b = b + a`.
@description
Show that a group whose quotient by its centre is cyclic is commutative, under the name `mul_comm_of_isCyclic_quotient_center`, keeping the `@[to_additive]` line.
-/
@[to_additive add_comm_of_isAddCyclic_quotient_center]
theorem mul_comm_of_isCyclic_quotient_center {G : Type u} [Group G]
    (h : IsCyclic (G ⧸ Subgroup.center G)) (a b : G) : a * b = b * a := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective q
  rw [← hg] at hq
  obtain ⟨i, hi⟩ := QuotientGroup.exists_zpow_mem (hq (QuotientGroup.mk a))
  obtain ⟨j, hj⟩ := QuotientGroup.exists_zpow_mem (hq (QuotientGroup.mk b))
  have hc : g ^ i * g ^ j = g ^ j * g ^ i := by
    rw [← zpow_add, ← zpow_add, Int.add_comm]
  rw [← mul_inv_cancel_left (g ^ i) a, ← mul_inv_cancel_left (g ^ j) b]
  exact mul_comm_of_mem_center hc hi hj

/-!
@problem index_center_of_card_eq_prime_sq
@title The Centre of a Group of Order p² Has Index 1 or p
@concept prime_square

@preamble
Core Lean has
```lean
theorem Nat.pow_two (n : ℕ) : n ^ 2 = n * n
theorem Nat.mul_left_comm (n m k : ℕ) :
    n * (m * k) = m * (n * k)
```

The context holds `IsPGroup.dvd_card_center` of the previous concept; core Lean's `Nat.eq_of_mul_eq_mul_left`, shown in this section's first concept; `Subgroup.index_mul_card` of the section on cosets; and `Nat.Prime.two_le` and `Nat.Prime.eq_one_or_self_of_dvd` of the section on cyclic groups.
@description
Show that for a prime `p`, the centre of a group of order `p ^ 2` has index `1` or `p`, under the name `index_center_of_card_eq_prime_sq`.
-/

open Classical in
theorem index_center_of_card_eq_prime_sq {p : ℕ} {G : Type u} [Group G] [Fintype G]
    (hp : Nat.Prime p) (hG : Fintype.card G = p ^ 2) :
    (Subgroup.center G).index = 1 ∨ (Subgroup.center G).index = p := by
  obtain ⟨c, hc⟩ := IsPGroup.dvd_card_center hp hG (by decide)
  have hl := (Subgroup.center G).index_mul_card
  rw [hc, hG, Nat.pow_two, Nat.mul_left_comm] at hl
  have e := Nat.eq_of_mul_eq_mul_left (by have := hp.two_le; omega) hl
  exact hp.eq_one_or_self_of_dvd _ ⟨c, e.symm⟩

/-! @end -/

/-!
@problem mul_comm_of_card_eq_prime_sq
@title A Group of Order p² Is Commutative
@concept prime_square

@preamble
The index of the centre is the number of elements of `G ⧸ center G`, by definition.

The context holds the theorems of the previous two problems; `Subgroup.index_mul_card` of the section on cosets; `Subgroup.eq_top_of_card_eq` and `isCyclic_of_prime_card` of the section on cyclic groups; core Lean's `Nat.one_mul`; and, of the section on subgroups,
```lean
Subgroup.center_eq_top_iff : Subgroup.center G = ⊤
    ↔ ∀ a b : G, a * b = b * a
```
@description
Show that for a prime `p`, every group of order `p ^ 2` is commutative, under the name `IsPGroup.mul_comm_of_card_eq_prime_sq`.
-/

open Classical in
theorem IsPGroup.mul_comm_of_card_eq_prime_sq {p : ℕ} {G : Type u} [Group G] [Fintype G]
    (hp : Nat.Prime p) (hG : Fintype.card G = p ^ 2) (a b : G) : a * b = b * a := by
  cases index_center_of_card_eq_prime_sq hp hG with
  | inl h =>
    have e : Fintype.card (Subgroup.center G).carrier = Fintype.card G := by
      rw [← (Subgroup.center G).index_mul_card, h, Nat.one_mul]
    exact Subgroup.center_eq_top_iff.mp (Subgroup.eq_top_of_card_eq _ e) a b
  | inr h =>
    exact mul_comm_of_isCyclic_quotient_center (isCyclic_of_prime_card hp h) a b

/-! @end -/

/-!
@problem order_four_and_eight
@title Order Four Is Commutative, Order Eight Need Not Be
@concept prime_square

@preamble
Every group of order `4 = 2 ^ 2` is commutative, as the Klein four-group `DihedralGroup 2` is. For `p = 2` the next power already fails: `DihedralGroup 4` has order `2 ^ 3` and is not commutative. The theorem `Nat.prime_two` below says that `2` is prime, proved by the same bounded `decide` as `5` was in the section on cyclic groups.

The context holds `IsPGroup.mul_comm_of_card_eq_prime_sq` of the previous problem.
@description
Show that every group of order `4` is commutative, under the name `mul_comm_of_card_eq_four`, and that `DihedralGroup 4` is not, under the name `dihedral_four_not_comm`.
-/

/-- @given -/
theorem Nat.prime_two : Nat.Prime 2 := by
  constructor
  · decide
  · intro m hm
    have hle : m ≤ 2 := Nat.le_of_dvd (by decide) hm
    have key : ∀ d ≤ 2, d ∣ 2 → d = 1 ∨ d = 2 := by
      decide
    exact key m hle hm

theorem mul_comm_of_card_eq_four {G : Type u} [Group G] [Fintype G] (hG : Fintype.card G = 4)
    (a b : G) : a * b = b * a :=
  IsPGroup.mul_comm_of_card_eq_prime_sq Nat.prime_two hG a b

theorem dihedral_four_not_comm : ¬ ∀ a b : DihedralGroup 4, a * b = b * a := by
  decide

/-! @end -/

end GroupTheory
