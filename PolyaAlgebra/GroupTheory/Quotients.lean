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
import PolyaAlgebra.GroupTheory.Cyclic

/-! @section Normal Subgroups and Quotient Groups -/

universe u v

namespace GroupTheory

set_option linter.translateGenerateName false

/-!
@concept normal_subgroups
@title Normal Subgroups
@kind definition

A subgroup is normal when it contains the conjugate of each of its elements by every element of the group. Normality is what lets the cosets of a subgroup be multiplied, so that they form a group.
-/

/-!
@problem normal
@title Normal Subgroups
@concept normal_subgroups

@preamble
The *conjugate* of `n` by `g` is `g * n * g⁻¹`, and a subgroup `N` is *normal* when it contains the conjugates of its elements.

We make normality a class with one field, a law, and write `N.Normal` for `Subgroup.Normal N`. The class's type is `Prop`: an instance of it is a proof, and a theorem may take `[N.Normal]` as a hypothesis that Lean finds by itself, as it finds `[Group G]`.
@description
Define the class `Subgroup.Normal N`, of type `Prop`, with the field `conj_mem`, its elements explicit:
```lean
∀ n, n ∈ N → ∀ g : G, g * n * g⁻¹ ∈ N
```
-/

class Subgroup.Normal {G : Type u} [Group G] (N : Subgroup G) : Prop where
  conj_mem : ∀ n, n ∈ N → ∀ g : G, g * n * g⁻¹ ∈ N

/-- @spec -/
example {G : Type u} [Group G] (N : Subgroup G) [N.Normal] (n g : G) (hn : n ∈ N) :
    g * n * g⁻¹ ∈ N := by
  apply Subgroup.Normal.conj_mem
  exact hn

/-! @end -/

/-!
@problem add_normal
@title Normal Additive Subgroups
@concept normal_subgroups

@preamble
In an additive group the conjugate of `n` by `g` is `g + n + -g`, and an additive subgroup is normal when it contains the conjugates of its elements. The class is what lets a theorem about normal subgroups have its additive version.

A class cannot be given its additive version by a line `@[to_additive]`, so the additive class is written out, as `AddGroup` was, and Lean is told that the two correspond.
@description
Define the class `AddSubgroup.Normal N` for an additive subgroup `N` of `A`, of type `Prop`, with the field `conj_mem`, its elements explicit:
```lean
∀ n, n ∈ N → ∀ g : A, g + n + -g ∈ N
```
-/

class AddSubgroup.Normal {A : Type u} [AddGroup A] (N : AddSubgroup A) : Prop where
  conj_mem : ∀ n, n ∈ N → ∀ g : A, g + n + -g ∈ N

/-- @spec -/
example {A : Type u} [AddGroup A] (N : AddSubgroup A) [N.Normal] (n g : A) (hn : n ∈ N) :
    g + n + -g ∈ N := by
  apply AddSubgroup.Normal.conj_mem
  exact hn

/-! @end -/

attribute [to_additive existing AddSubgroup.Normal] Subgroup.Normal

/--
@problem conj_mem_inv
@title Conjugating by an Inverse
@concept normal_subgroups

@preamble
A normal subgroup contains the conjugates of its elements by inverses too, since an inverse is an element of the group like any other.

Under the hypothesis `[N.Normal]` the field of the class is a theorem, whose normality hypothesis Lean supplies:
```lean
theorem Subgroup.Normal.conj_mem [N.Normal]
    (n : G) (hn : n ∈ N) (g : G) : g * n * g⁻¹ ∈ N
```
The context holds `inv_inv` of the second section, which says that `a⁻¹⁻¹ = a`.
@description
Show that a normal subgroup `N` contains `g⁻¹ * n * g` for each of its elements `n` and every `g`, under the name `Subgroup.Normal.conj_mem'`.
-/
@[to_additive AddSubgroup.Normal.conj_mem']
theorem Subgroup.Normal.conj_mem' {G : Type u} [Group G] {N : Subgroup G} [N.Normal] (n : G)
    (hn : n ∈ N) (g : G) : g⁻¹ * n * g ∈ N := by
  have h := Subgroup.Normal.conj_mem n hn g⁻¹
  rw [inv_inv] at h
  exact h

/-!
@problem normal_iff_cosets
@title Normality by Cosets, and a Subgroup of D₃ That Is Not Normal
@concept normal_subgroups

@preamble
A subgroup `N` is normal exactly when each of its left cosets is the right coset by the same element: `gN = Ng` for every `g`. Membership in the two cosets has the tests of the section on cosets:
```lean
theorem mem_leftCoset_iff :
    x ∈ leftCoset g N ↔ g⁻¹ * x ∈ N
theorem mem_rightCoset_iff :
    x ∈ rightCoset N g ↔ x * g⁻¹ ∈ N
```
A hypothesis `hN : N.Normal` gives the law as `hN.conj_mem`. To prove `N.Normal`, `constructor` leaves its one field to prove, as for a structure.

From the section on cosets, `leftCoset_ne_rightCoset` says that the left and right cosets of the subgroup `d3FixZero` of D₃ by `r 1` differ. The context also holds `Subgroup.Normal.conj_mem'`, `Set.ext`, and the laws of the second section, `mul_assoc`, `inv_inv`, `mul_inv_cancel_left` (`a * (a⁻¹ * b) = b`) and `inv_mul_cancel_right` (`a * b⁻¹ * b = a`) among them.
@description
Show that `N` is normal exactly when its left coset by every `g` is its right coset by `g`, under the name `Subgroup.normal_iff_leftCoset_eq_rightCoset`, and that `d3FixZero` is not normal.
-/

@[to_additive AddSubgroup.normal_iff_leftAddCoset_eq_rightAddCoset]
theorem Subgroup.normal_iff_leftCoset_eq_rightCoset {G : Type u} [Group G] {N : Subgroup G} :
    N.Normal ↔ ∀ g : G, leftCoset g N = rightCoset N g := by
  constructor
  · intro hN g
    apply Set.ext
    intro x
    rw [mem_leftCoset_iff, mem_rightCoset_iff]
    constructor
    · intro h
      have e : x * g⁻¹ = g * (g⁻¹ * x) * g⁻¹ := by
        rw [mul_inv_cancel_left]
      rw [e]
      exact hN.conj_mem _ h g
    · intro h
      have e : g⁻¹ * x = g⁻¹ * (x * g⁻¹) * g := by
        rw [mul_assoc, inv_mul_cancel_right]
      rw [e]
      exact Subgroup.Normal.conj_mem' _ h g
  · intro h
    constructor
    intro n hn g
    have hx : g * n ∈ leftCoset g N := ⟨n, hn, rfl⟩
    rw [h g, mem_rightCoset_iff] at hx
    exact hx

open DihedralGroup in
theorem d3FixZero_not_normal : ¬ d3FixZero.Normal := by
  intro h
  exact leftCoset_ne_rightCoset (Subgroup.normal_iff_leftCoset_eq_rightCoset.mp h (r 1))

/-! @end -/

/-!
@problem normal_of_comm
@title Subgroups That Are Always Normal
@concept normal_subgroups

@preamble
In a commutative group the conjugate `g * n * g⁻¹` is `n`, so every subgroup is normal, in the integers and in each `ZMod m` among them. The centre of any group is normal too, since its elements commute with every `g`.

We make both facts instances, so that Lean finds them whenever a subgroup of a commutative group, or a centre, needs to be normal. An instance of a class whose type is `Prop` is written with `where` and its field, as the instances of `CommGroup` in the section on examples were. The context holds `mul_comm` of the section on examples, `mul_inv_cancel_right` of the second section, and `Subgroup.mem_center_iff` of the section on subgroups, which says that `z` is in the centre exactly when `g * z = z * g` for every `g`.
@description
Supply the instance `Subgroup.normal_of_comm`, which makes every subgroup of a commutative group normal, and the instance `Subgroup.center_normal`, which makes the centre of every group normal.
-/

@[to_additive AddSubgroup.normal_of_comm]
instance Subgroup.normal_of_comm {G : Type u} [CommGroup G] (N : Subgroup G) : N.Normal where
  conj_mem := by
    intro n hn g
    rw [mul_comm g n, mul_inv_cancel_right]
    exact hn

@[to_additive AddSubgroup.center_normal]
instance Subgroup.center_normal {G : Type u} [Group G] : (Subgroup.center G).Normal where
  conj_mem := by
    intro z hz g
    rw [Subgroup.mem_center_iff] at hz
    rw [hz g, mul_inv_cancel_right, Subgroup.mem_center_iff]
    exact hz

/-- @spec -/
example {G : Type u} [CommGroup G] (N : Subgroup G) : N.Normal := inferInstance

/-- @spec -/
example {G : Type u} [Group G] : (Subgroup.center G).Normal := inferInstance

/-! @end -/

/-!
@problem normal_ker
@title Kernels Are Normal
@concept normal_subgroups

@preamble
The kernel of every homomorphism is normal, since a homomorphism carries conjugates to conjugates. The rotations of Dₙ are normal for that reason, being a kernel.

An instance of a class whose type is `Prop` is a proof, so it may also be given by a tactic block, `:= by …`, which can use an instance already supplied. The context holds the laws of the second section and, from the section on homomorphisms, `GroupHom.mem_ker`, `GroupHom.map_mul`, `GroupHom.map_inv` and, outside the namespace `DihedralGroup`,
```lean
theorem ker_orientation (n : ℕ) [NeZero n] :
    (DihedralGroup.orientation n).ker =
      DihedralGroup.rotations n
```
@description
Supply the instance `GroupHom.normal_ker`, which makes the kernel of every homomorphism normal, and the instance `DihedralGroup.rotations_normal`, which makes the rotations of Dₙ normal.
-/

@[to_additive AddGroupHom.normal_ker]
instance GroupHom.normal_ker {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) :
    f.ker.Normal where
  conj_mem := by
    intro n hn g
    rw [GroupHom.mem_ker] at hn
    rw [GroupHom.mem_ker, f.map_mul, f.map_mul, hn, mul_one, f.map_inv, mul_inv_cancel]

instance DihedralGroup.rotations_normal (n : ℕ) [NeZero n] :
    (DihedralGroup.rotations n).Normal := by
  rw [← ker_orientation]
  exact GroupHom.normal_ker _

/-- @spec -/
example {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) : f.ker.Normal := inferInstance

/-- @spec -/
example (n : ℕ) [NeZero n] : (DihedralGroup.rotations n).Normal := inferInstance

/-! @end -/

/-!
@concept products_of_subgroups
@title Products of Subgroups
@kind theorem

Two subgroups generate a subgroup, the smallest one containing both. When the second is normal, the elements of that subgroup are exactly the products of an element of the first with an element of the second, so the subgroup is known element by element rather than only as the smallest subgroup containing both.
-/

/-!
@problem sup
@title The Subgroup Generated by Two Subgroups
@concept products_of_subgroups

@preamble
Two subgroups `H` and `K` generate a subgroup, the subgroup generated by the union of their carriers, which is the smallest subgroup containing both. We write it `H ⊔ K` (typed `\lub`), for `max H K`, through the class
```lean
class Max (α : Type u) where
  max : α → α → α
```
as `H ⊓ K` came from `Min`. It is the least subgroup above both `H` and `K`, which we prove as `Subgroup.le_sup_left`, `Subgroup.le_sup_right` and `Subgroup.sup_le`. A membership `x ∈ A ∪ B` in a union of sets is `x ∈ A ∨ x ∈ B` by definition. The context holds `Subgroup.closure`, `Subgroup.subset_closure` and `Subgroup.closure_le` of the section on subgroups.
@description
Supply the instance `Max (Subgroup G)`, with `H ⊔ K` the subgroup generated by `H.carrier ∪ K.carrier`. Show that `H ⊔ K` lies above `H` and above `K`, and below every subgroup that lies above both.
-/

@[to_additive AddSubgroup.instMax]
instance Subgroup.instMax {G : Type u} [Group G] : Max (Subgroup G) :=
  ⟨fun H K => Subgroup.closure (H.carrier ∪ K.carrier)⟩

/-- @spec -/
example {G : Type u} [Group G] (H K : Subgroup G) :
    H ⊔ K = Subgroup.closure (H.carrier ∪ K.carrier) :=
  rfl

@[to_additive AddSubgroup.le_sup_left]
theorem Subgroup.le_sup_left {G : Type u} [Group G] (H K : Subgroup G) : H ≤ H ⊔ K := by
  intro x hx
  exact Subgroup.subset_closure (Or.inl hx)

@[to_additive AddSubgroup.le_sup_right]
theorem Subgroup.le_sup_right {G : Type u} [Group G] (H K : Subgroup G) : K ≤ H ⊔ K := by
  intro x hx
  exact Subgroup.subset_closure (Or.inr hx)

@[to_additive AddSubgroup.sup_le]
theorem Subgroup.sup_le {G : Type u} [Group G] {H K L : Subgroup G} (hH : H ≤ L) (hK : K ≤ L) :
    H ⊔ K ≤ L := by
  apply Subgroup.closure_le.mpr
  intro x hx
  cases hx with
  | inl h => exact hH h
  | inr h => exact hK h

/-! @end -/

/-!
@problem mul_normal
@title The Products of a Subgroup and a Normal Subgroup
@concept products_of_subgroups

@preamble
The products `h * n` of elements of `H` and of `N` form a subgroup when `N` is normal: an element of `N` moves past one of `H` at the price of a conjugate, which `N` contains. For two products,
```lean
h * n * (h' * n')
  = h * (h' * h'⁻¹) * n * (h' * n')
  = h * h' * (h'⁻¹ * n * h' * n')
```
and an inverse `(h * n)⁻¹` is treated the same way. A member of `Subgroup.mulNormal H N` opens into `⟨h, hh, n, hn, e⟩` with `e : h * n = x`, as a member of a coset did. The context holds `Subgroup.Normal.conj_mem` and `Subgroup.Normal.conj_mem'` of this section, `Subgroup.one_mem`, `Subgroup.mul_mem` and `Subgroup.inv_mem` of the section on subgroups, and the laws of the second section, `mul_assoc`, `mul_inv_rev`, `mul_inv_cancel_left` (`a * (a⁻¹ * b) = b`) and `inv_mul_cancel_left` (`a⁻¹ * (a * b) = b`) among them.
@description
Define `Subgroup.mulNormal H N` for a normal subgroup `N`, the subgroup whose carrier is the set of products, proving its three closure conditions:
```lean
{x | ∃ h ∈ H, ∃ n ∈ N, h * n = x}
```
-/

@[to_additive AddSubgroup.addNormal]
def Subgroup.mulNormal {G : Type u} [Group G] (H N : Subgroup G) [N.Normal] : Subgroup G where
  carrier := {x | ∃ h ∈ H, ∃ n ∈ N, h * n = x}
  one_mem' := ⟨1, H.one_mem, 1, N.one_mem, mul_one 1⟩
  mul_mem' := by
    intro x y ⟨h, hh, n, hn, ex⟩ ⟨h', hh', n', hn', ey⟩
    have e : x * y = h * h' * (h'⁻¹ * n * h' * n') := by
      rw [← ex, ← ey, mul_assoc h h', mul_assoc (h'⁻¹ * n), mul_assoc h'⁻¹, mul_inv_cancel_left,
        mul_assoc h n]
    exact ⟨h * h', H.mul_mem hh hh', _, N.mul_mem (Subgroup.Normal.conj_mem' n hn h') hn', e.symm⟩
  inv_mem' := by
    intro x ⟨h, hh, n, hn, ex⟩
    have e : x⁻¹ = h⁻¹ * (h * n⁻¹ * h⁻¹) := by
      rw [← ex, mul_inv_rev, ← mul_assoc, inv_mul_cancel_left]
    exact ⟨h⁻¹, H.inv_mem hh, _, Subgroup.Normal.conj_mem _ (N.inv_mem hn) h, e.symm⟩

/-- @spec -/
example {G : Type u} [Group G] (H N : Subgroup G) [N.Normal] (x : G) :
    x ∈ H.mulNormal N ↔ ∃ h, h ∈ H ∧ ∃ n, n ∈ N ∧ h * n = x := by
  constructor
  · intro hx
    obtain ⟨h, hh, n, hn, e⟩ := hx
    exact ⟨h, hh, n, hn, by grind⟩
  · intro ⟨h, hh, n, hn, e⟩
    exact ⟨h, hh, n, hn, by grind⟩

/-! @end -/

/-!
@problem mem_sup_of_normal
@title The Subgroup Generated by a Subgroup and a Normal Subgroup
@concept products_of_subgroups

@preamble
The subgroup generated by `H` and a normal subgroup `N` is the subgroup of products of the previous problem: it contains `H` and `N`, so every product, and it lies inside every subgroup containing them.

The context holds `Subgroup.mulNormal` of the previous problem, the three theorems on `⊔` of the problem that defined it, and `Subgroup.one_mem` and `Subgroup.mul_mem` of the section on subgroups; `Subgroup.mul_mem` takes the subgroup first, as in `K.mul_mem`.
@description
Show that, for a normal subgroup `N`, an element lies in `H ⊔ N` exactly when it is a product `h * n` with `h ∈ H` and `n ∈ N`, under the name `Subgroup.mem_sup_of_normal`.
-/

@[to_additive AddSubgroup.mem_sup_of_normal]
theorem Subgroup.mem_sup_of_normal {G : Type u} [Group G] {H N : Subgroup G} [N.Normal] {x : G} :
    x ∈ H ⊔ N ↔ ∃ h ∈ H, ∃ n ∈ N, h * n = x := by
  constructor
  · intro hx
    have hle : H ⊔ N ≤ H.mulNormal N := by
      apply Subgroup.sup_le
      · intro h hh
        exact ⟨h, hh, 1, N.one_mem, mul_one h⟩
      · intro n hn
        exact ⟨1, H.one_mem, n, hn, one_mul n⟩
    exact hle hx
  · intro ⟨h, hh, n, hn, e⟩
    rw [← e]
    exact (H ⊔ N).mul_mem (Subgroup.le_sup_left H N hh) (Subgroup.le_sup_right H N hn)

/-! @end -/

/--
@problem two_sup_three
@title The Multiples of Two and Three Generate ℤ
@concept products_of_subgroups

@preamble
In the integers, written additively, the multiples of `2` and of `3` generate the whole group: `intMultiples 2` is `2ℤ` and `intMultiples 3` is `3ℤ`. Every subgroup of `ℤ` is normal, by the instance `AddSubgroup.normal_of_comm`, so the additive version of the previous problem, `AddSubgroup.mem_sup_of_normal`, says what the members of `2ℤ ⊔ 3ℤ` are.

The context also holds, of the section on subgroups, `AddSubgroup.ext`, `AddSubgroup.mem_top` and `mem_intMultiples`. `omega` decides divisibility by a numeral.
@description
Show that `2ℤ ⊔ 3ℤ` is the whole of `ℤ`.
-/
theorem intMultiples_two_sup_three : intMultiples 2 ⊔ intMultiples 3 = ⊤ := by
  apply AddSubgroup.ext
  intro x
  constructor
  · intro _
    exact AddSubgroup.mem_top x
  · intro _
    rw [AddSubgroup.mem_sup_of_normal]
    have h2 : -2 * x ∈ intMultiples 2 := by
      rw [mem_intMultiples]
      omega
    have h3 : 3 * x ∈ intMultiples 3 := by
      rw [mem_intMultiples]
      omega
    exact ⟨-2 * x, h2, 3 * x, h3, by omega⟩

/-!
@concept quotient_groups
@title Quotient Groups
@kind definition

The cosets of a normal subgroup form a group, the quotient group, in which the product of two cosets is the coset of the product. The map sending each element to its coset is a homomorphism whose kernel is the normal subgroup, so the normal subgroups are exactly the kernels.-/

/-!
@problem left_rel_mul
@title Products and Inverses Respect the Cosets
@concept quotient_groups

@preamble
We want to multiply the cosets of a normal subgroup `N` through representatives, the coset of `a` times the coset of `b` being the coset of `a * b`. For that to define anything, other representatives `a'` and `b'` of the same cosets must give the same coset for `a' * b'`. Two elements lie in the same coset when `a⁻¹ * a' ∈ N`, the coset relation of the section on cosets, so the condition is that `(a * b)⁻¹ * (a' * b')` lies in `N`. Inverses respect cosets too: the relation between `a⁻¹` and `a'⁻¹` is `a⁻¹⁻¹ * a'⁻¹ ∈ N`. In each case the element is regrouped so that `a⁻¹ * a'` appears inside a conjugate, which `N` contains because it is normal.

The context holds `Subgroup.Normal.conj_mem` and `Subgroup.Normal.conj_mem'` of this section, `Subgroup.mul_mem` and `Subgroup.inv_mem` of the section on subgroups, and the laws of the second section, `mul_assoc`, `mul_inv_rev`, `inv_inv`, `mul_inv_cancel`, `mul_inv_cancel_left` (`a * (a⁻¹ * b) = b`) and `mul_inv_cancel_right` (`a * b * b⁻¹ = a`) among them.
@description
Show that if `a⁻¹ * a'` and `b⁻¹ * b'` lie in a normal subgroup `N`, so does `(a * b)⁻¹ * (a' * b')`, under the name `QuotientGroup.leftRel_mul`. Then show that if `a⁻¹ * a'` lies in `N`, so does `a⁻¹⁻¹ * a'⁻¹`, under the name `QuotientGroup.leftRel_inv`.
-/

@[to_additive QuotientAddGroup.leftRel_add]
theorem QuotientGroup.leftRel_mul {G : Type u} [Group G] {N : Subgroup G} [N.Normal]
    {a a' b b' : G} (ha : a⁻¹ * a' ∈ N) (hb : b⁻¹ * b' ∈ N) : (a * b)⁻¹ * (a' * b') ∈ N := by
  have e : (a * b)⁻¹ * (a' * b') = b⁻¹ * (a⁻¹ * a') * b * (b⁻¹ * b') := by
    rw [mul_assoc _ b, mul_inv_cancel_left, mul_inv_rev, mul_assoc, mul_assoc, mul_assoc]
  rw [e]
  exact N.mul_mem (Subgroup.Normal.conj_mem' _ ha b) hb

@[to_additive QuotientAddGroup.leftRel_neg]
theorem QuotientGroup.leftRel_inv {G : Type u} [Group G] {N : Subgroup G} [N.Normal]
    {a a' : G} (ha : a⁻¹ * a' ∈ N) : a⁻¹⁻¹ * a'⁻¹ ∈ N := by
  have e : a⁻¹⁻¹ * a'⁻¹ = a * (a⁻¹ * a')⁻¹ * a⁻¹ := by
    rw [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_right]
  rw [e]
  exact Subgroup.Normal.conj_mem _ (N.inv_mem ha) a

/-! @end -/

/-!
@problem quotient_mul
@title Multiplying Cosets
@concept quotient_groups

@preamble
The first section defined a function on a quotient by `Quotient.lift`, from a function on representatives and a proof that related representatives give the same value. A function of two classes is defined the same way:
```lean
def Quotient.lift₂ (f : α → β → φ)
    (h : ∀ a₁ b₁ a₂ b₂, a₁ ≈ a₂ → b₁ ≈ b₂ →
      f a₁ b₁ = f a₂ b₂) :
    Quotient s₁ → Quotient s₂ → φ
```
where the relations `s₁` on `α` and `s₂` on `β` are implicit, as for `Quotient.lift`. The function here sends `a` and `b` to the class of `a * b`. Here `a₁ ≈ a₂` is `a₁⁻¹ * a₂ ∈ N` by definition, as `G ⧸ N` is the quotient by the coset relation, so `Quotient.lift₂` applies to it. The inverse of a coset is the coset of an inverse, through `Quotient.lift`. The context holds the two theorems of the previous problem and `QuotientGroup.eq` of the section on cosets.
@description
Define `QuotientGroup.mul`, the product of two cosets of a normal subgroup, and `QuotientGroup.inv`, the inverse of a coset. Show that on the classes of `a` and `b` they give the classes of `a * b` and of `a⁻¹`, under the names `QuotientGroup.mul_mk` and `QuotientGroup.inv_mk`.
-/

@[to_additive QuotientAddGroup.add]
def QuotientGroup.mul {G : Type u} [Group G] {N : Subgroup G} [N.Normal] :
    G ⧸ N → G ⧸ N → G ⧸ N :=
  Quotient.lift₂ (fun a b => QuotientGroup.mk (a * b))
    (fun _ _ _ _ ha hb => QuotientGroup.eq.mpr (QuotientGroup.leftRel_mul ha hb))

@[to_additive QuotientAddGroup.neg]
def QuotientGroup.inv {G : Type u} [Group G] {N : Subgroup G} [N.Normal] : G ⧸ N → G ⧸ N :=
  Quotient.lift (fun a => QuotientGroup.mk a⁻¹)
    (fun _ _ h => QuotientGroup.eq.mpr (QuotientGroup.leftRel_inv h))

/-- @spec -/
example {G : Type u} [Group G] (N : Subgroup G) [N.Normal] (a b : G) :
    QuotientGroup.mul (QuotientGroup.mk a : G ⧸ N) (QuotientGroup.mk b) = QuotientGroup.mk (a * b) ∧
    QuotientGroup.inv (QuotientGroup.mk a : G ⧸ N) = QuotientGroup.mk a⁻¹ :=
  ⟨rfl, rfl⟩

@[to_additive QuotientAddGroup.add_mk]
theorem QuotientGroup.mul_mk {G : Type u} [Group G] {N : Subgroup G} [N.Normal] (a b : G) :
    QuotientGroup.mul (QuotientGroup.mk a : G ⧸ N) (QuotientGroup.mk b) = QuotientGroup.mk (a * b) :=
  rfl

@[to_additive QuotientAddGroup.neg_mk]
theorem QuotientGroup.inv_mk {G : Type u} [Group G] {N : Subgroup G} [N.Normal] (a : G) :
    QuotientGroup.inv (QuotientGroup.mk a : G ⧸ N) = QuotientGroup.mk a⁻¹ :=
  rfl

/-! @end -/

/-!
@problem quotient_is_group
@title The Quotient Group
@concept quotient_groups

@preamble
With these operations the cosets of a normal subgroup form a group, the *quotient group* `G ⧸ N`. Its neutral element is the class of `1`, which is the coset `N` itself. Its fields are the operations and the five laws of the class `Group` of the second section. Each law is proved by taking a representative of every coset, by `QuotientGroup.mk_surjective` of the section on cosets, and computing with representatives. For `one_mul`, inside the instance, where the operations appear as `QuotientGroup.mul p q` and not `p * q`:
```lean
  one_mul := by
    intro p
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective p
    rw [← ha, QuotientGroup.mul_mk, one_mul]
```
The additive version of the instance gives `A ⧸ N` an addition. The context holds `QuotientGroup.mul_mk` and `QuotientGroup.inv_mk` of the previous problem and the laws of the second section.
@description
Supply the instance `QuotientGroup.Quotient.group N`, which makes `G ⧸ N` a group for a normal subgroup `N`, with the product and the inverse of the previous problem and the class of `1` as its neutral element.
-/

@[to_additive QuotientAddGroup.Quotient.addGroup]
instance QuotientGroup.Quotient.group {G : Type u} [Group G] (N : Subgroup G) [N.Normal] :
    Group (G ⧸ N) where
  mul := QuotientGroup.mul
  one := QuotientGroup.mk 1
  inv := QuotientGroup.inv
  mul_assoc := by
    intro p q r
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective p
    obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective q
    obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective r
    rw [← ha, ← hb, ← hc, QuotientGroup.mul_mk, QuotientGroup.mul_mk, QuotientGroup.mul_mk,
      QuotientGroup.mul_mk, mul_assoc]
  one_mul := by
    intro p
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective p
    rw [← ha, QuotientGroup.mul_mk, one_mul]
  mul_one := by
    intro p
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective p
    rw [← ha, QuotientGroup.mul_mk, mul_one]
  inv_mul_cancel := by
    intro p
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective p
    rw [← ha, QuotientGroup.inv_mk, QuotientGroup.mul_mk, inv_mul_cancel]
  mul_inv_cancel := by
    intro p
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective p
    rw [← ha, QuotientGroup.inv_mk, QuotientGroup.mul_mk, mul_inv_cancel]

/-- @spec -/
example {G : Type u} [Group G] (N : Subgroup G) [N.Normal] (a b : G) :
    (QuotientGroup.mk a : G ⧸ N) * QuotientGroup.mk b = QuotientGroup.mk (a * b) ∧
    (1 : G ⧸ N) = QuotientGroup.mk 1 ∧
    (QuotientGroup.mk a : G ⧸ N)⁻¹ = QuotientGroup.mk a⁻¹ :=
  ⟨rfl, rfl, rfl⟩

/-! @end -/

/-!
@problem mk_hom
@title The Quotient Map
@concept quotient_groups

@preamble
The map sending each element to its class, `a ↦ aN`, is a homomorphism `G →* G ⧸ N`, which we call `QuotientGroup.mk' N`. The class of a product is the product of the classes, `QuotientGroup.mk_mul`, and the class of `1` is the neutral element, `QuotientGroup.mk_one`; both hold by definition, and the starting code states them.

Its kernel is `N`. The function of `QuotientGroup.mk' N` is `QuotientGroup.mk` by definition. The context also holds `pow_zero` and `pow_succ` of the section on powers, `QuotientGroup.mk_eq_mk_one_iff` of the section on cosets, which says that the class of `a` is the class of `1` exactly when `a ∈ N`, `GroupHom.mem_ker` of the section on homomorphisms and `Subgroup.ext` of the section on subgroups.
@description
Define `QuotientGroup.mk' N`, the homomorphism sending `a` to its class. Show that the class of `a ^ n` is the `n`-th power of the class of `a`, under the name `QuotientGroup.mk_pow`, and that the kernel of `QuotientGroup.mk' N` is `N`, under the name `QuotientGroup.ker_mk'`.
-/

/-- @given -/
@[to_additive QuotientAddGroup.mk_add]
theorem QuotientGroup.mk_mul {G : Type u} [Group G] {N : Subgroup G} [N.Normal] (a b : G) :
    (QuotientGroup.mk a : G ⧸ N) * QuotientGroup.mk b = QuotientGroup.mk (a * b) :=
  rfl

/-- @given -/
@[to_additive QuotientAddGroup.mk_zero]
theorem QuotientGroup.mk_one {G : Type u} [Group G] {N : Subgroup G} [N.Normal] :
    (QuotientGroup.mk 1 : G ⧸ N) = 1 :=
  rfl

@[to_additive QuotientAddGroup.mk']
def QuotientGroup.mk' {G : Type u} [Group G] (N : Subgroup G) [N.Normal] : G →* G ⧸ N where
  toFun := QuotientGroup.mk
  map_mul' := by
    intro a b
    rw [QuotientGroup.mk_mul]

/-- @spec -/
example {G : Type u} [Group G] (N : Subgroup G) [N.Normal] (a : G) :
    (QuotientGroup.mk' N).toFun a = QuotientGroup.mk a :=
  rfl

@[to_additive QuotientAddGroup.mk_nsmul]
theorem QuotientGroup.mk_pow {G : Type u} [Group G] {N : Subgroup G} [N.Normal] (a : G) (n : ℕ) :
    (QuotientGroup.mk (a ^ n) : G ⧸ N) = QuotientGroup.mk a ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, QuotientGroup.mk_one]
  | succ k ih => rw [pow_succ, pow_succ, ← ih, QuotientGroup.mk_mul]

@[to_additive QuotientAddGroup.ker_mk']
theorem QuotientGroup.ker_mk' {G : Type u} [Group G] (N : Subgroup G) [N.Normal] :
    (QuotientGroup.mk' N).ker = N := by
  apply Subgroup.ext
  intro x
  rw [GroupHom.mem_ker, ← QuotientGroup.mk_one]
  exact QuotientGroup.mk_eq_mk_one_iff

/-! @end -/

/-!
@problem quotient_comm
@title A Quotient of a Commutative Group Is Commutative
@concept quotient_groups

@preamble
Every subgroup of a commutative group is normal, so every quotient of a commutative group is a group, and it is commutative. Lean finds the normality by itself through the instance `Subgroup.normal_of_comm`, or its additive version. So `ℤ ⧸ nℤ` and every quotient of `ZMod n` are commutative.

The instance extends the quotient group by the law alone, as the instances of `CommGroup` in the section on examples extended a group. The context holds `QuotientGroup.mk_mul` of the previous problem, `QuotientGroup.mk_surjective` of the section on cosets, and `mul_comm` of the section on examples.
@description
Supply the instance `QuotientGroup.Quotient.commGroup N`, which makes `G ⧸ N` commutative when `G` is.
-/

@[to_additive QuotientAddGroup.Quotient.addCommGroup]
instance QuotientGroup.Quotient.commGroup {G : Type u} [CommGroup G] (N : Subgroup G) :
    CommGroup (G ⧸ N) where
  mul_comm := by
    intro p q
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective p
    obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective q
    rw [← ha, ← hb, QuotientGroup.mk_mul, QuotientGroup.mk_mul, mul_comm]

/-- @spec -/
example {G : Type u} [CommGroup G] (N : Subgroup G) (a b : G) :
    (QuotientGroup.mk a : G ⧸ N) * QuotientGroup.mk b = QuotientGroup.mk (a * b) ∧
    (QuotientGroup.mk a : G ⧸ N) * QuotientGroup.mk b = QuotientGroup.mk b * QuotientGroup.mk a :=
  ⟨rfl, mul_comm _ _⟩

/-! @end -/

/-!
@problem pow_index_mem
@title A Power by the Index Lies in a Normal Subgroup
@concept quotient_groups

@preamble
In a finite group `g` raised to the order of the group is `1`. The same holds in the quotient by a normal subgroup `N`, which has `N.index` elements.

The context holds `QuotientGroup.mk_pow` and `QuotientGroup.mk_one` of this section; from the section on cosets, `QuotientGroup.mk_eq_mk_one_iff` and `Subgroup.index`, defined as `Fintype.card (G ⧸ H)`; and, from the previous section,
```lean
theorem pow_card_eq_one [Fintype G] (g : G) :
    g ^ Fintype.card G = 1
```
@description
Show that for a normal subgroup `N` of a finite group, `g ^ N.index` lies in `N` for every `g`, under the name `Subgroup.pow_index_mem`.
-/

open Classical in
@[to_additive AddSubgroup.index_nsmul_mem]
theorem Subgroup.pow_index_mem {G : Type u} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    (g : G) : g ^ N.index ∈ N := by
  rw [← QuotientGroup.mk_eq_mk_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_one]
  exact pow_card_eq_one (QuotientGroup.mk g)

/-! @end -/

/-!
@problem int_quotient
@title The Class of One in ℤ ⧸ nℤ Has Order n
@concept quotient_groups

@preamble
The quotient `ℤ ⧸ nℤ` is an additive group, by the additive version of the quotient group, since every subgroup of `ℤ` is normal. It behaves as `ZMod n` does: the class of `1` has order `n`. In Lean the subgroup is `intMultiples n` and the class of `a` is `QuotientAddGroup.mk a`. The section on powers proved
```lean
theorem addOrderOf_eq_iff (hn : 0 < n) :
    addOrderOf a = n ↔ n • a = 0 ∧
      ∀ m, m < n → 0 < m → m • a ≠ 0
```
The context also holds additive versions: `QuotientAddGroup.mk_nsmul` and `QuotientAddGroup.mk_zero` of this section, and `QuotientAddGroup.mk_eq_mk_zero_iff` of the section on cosets; `int_nsmul_one` of the section on powers; `mem_intMultiples` of the section on subgroups; and core Lean's `Int.dvd_refl`, `Int.natCast_dvd_natCast`, `Nat.le_of_dvd` and `Nat.pos_of_neZero`.
@description
Show that the class of `1` in `ℤ ⧸ nℤ` has order `n`, for `n ≠ 0`.
-/

theorem addOrderOf_mk_one_int (n : ℕ) [NeZero n] :
    addOrderOf (QuotientAddGroup.mk 1 : ℤ ⧸ intMultiples n) = n := by
  rw [addOrderOf_eq_iff (Nat.pos_of_neZero n)]
  constructor
  · rw [← QuotientAddGroup.mk_nsmul, int_nsmul_one, ← QuotientAddGroup.mk_zero,
      QuotientAddGroup.mk_eq_mk_zero_iff, mem_intMultiples]
    exact Int.dvd_refl _
  · intro m hm hm0 h
    rw [← QuotientAddGroup.mk_nsmul, int_nsmul_one, ← QuotientAddGroup.mk_zero,
      QuotientAddGroup.mk_eq_mk_zero_iff, mem_intMultiples, Int.natCast_dvd_natCast] at h
    have hle := Nat.le_of_dvd hm0 h
    omega

/-! @end -/

/-!
@concept universal_property
@title The Universal Property of the Quotient
@kind theorem

A homomorphism that sends a normal subgroup to the neutral element factors through the quotient: it defines a homomorphism on the cosets, and that is the only homomorphism agreeing with it on the coset of each element. This is how homomorphisms out of a quotient group are built.
-/

/--
@problem eq_of_mem_ker
@title A Homomorphism Is Constant on the Cosets of Its Kernel
@concept universal_property

@preamble
A homomorphism `f` takes the same value at `a` and at `b` when the two lie in the same coset of its kernel, that is, when `a⁻¹ * b` lies in the kernel. So `f` is constant on each coset of its kernel.

The context holds `GroupHom.mem_ker` of the section on homomorphisms, which says that `x ∈ f.ker` exactly when `f.toFun x = 1`, with `GroupHom.map_mul` and `GroupHom.map_inv` of the same section, and `inv_inv` and `inv_eq_of_mul_eq_one_right` of the second section; the second says that `a * b = 1` gives `a⁻¹ = b`.
@description
Show that a homomorphism `f` takes the same value at `a` and `b` when `a⁻¹ * b` lies in its kernel, under the name `GroupHom.eq_of_inv_mul_mem_ker`.
-/
@[to_additive AddGroupHom.eq_of_neg_add_mem_ker]
theorem GroupHom.eq_of_inv_mul_mem_ker {G : Type u} {H : Type v} [Group G] [Group H]
    {f : G →* H} {a b : G} (h : a⁻¹ * b ∈ f.ker) : f.toFun a = f.toFun b := by
  rw [GroupHom.mem_ker, f.map_mul, f.map_inv] at h
  have e := inv_eq_of_mul_eq_one_right h
  rw [inv_inv] at e
  exact e

/-!
@problem lift
@title Homomorphisms Out of a Quotient
@concept universal_property

@preamble
Let `f : G →* H` be a homomorphism whose kernel contains a normal subgroup `N`, written `hN : N ≤ f.ker`. Then `f` is constant on each coset of `N`, so it defines a function on `G ⧸ N` through `Quotient.lift` of the first section, and that function is a homomorphism. We write it `QuotientGroup.lift N f hN`. As in multiplying cosets, `a ≈ b` on `G` is `a⁻¹ * b ∈ N` by definition. The lift sends the class of `a` to `f.toFun a`, by definition: `QuotientGroup.lift_mk`.

The context holds `GroupHom.eq_of_inv_mul_mem_ker` of the previous problem, `QuotientGroup.mk_mul` of this section, `QuotientGroup.mk_surjective` of the section on cosets, and `GroupHom.map_mul` of the section on homomorphisms.
@description
Define `QuotientGroup.lift N f hN`, the homomorphism from `G ⧸ N` to `H` that sends the class of `a` to `f.toFun a`, and show that it does so, under the name `QuotientGroup.lift_mk`.
-/

@[to_additive QuotientAddGroup.lift]
def QuotientGroup.lift {G : Type u} {H : Type v} [Group G] [Group H] (N : Subgroup G) [N.Normal]
    (f : G →* H) (hN : N ≤ f.ker) : G ⧸ N →* H where
  toFun := Quotient.lift f.toFun (fun _ _ h => GroupHom.eq_of_inv_mul_mem_ker (hN h))
  map_mul' := by
    intro p q
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective p
    obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective q
    rw [← ha, ← hb, QuotientGroup.mk_mul]
    exact f.map_mul a b

/-- @spec -/
example {G : Type u} {H : Type v} [Group G] [Group H] (N : Subgroup G) [N.Normal]
    (f : G →* H) (hN : N ≤ f.ker) (a : G) :
    (QuotientGroup.lift N f hN).toFun (QuotientGroup.mk a) = f.toFun a :=
  rfl

@[to_additive QuotientAddGroup.lift_mk]
theorem QuotientGroup.lift_mk {G : Type u} {H : Type v} [Group G] [Group H] {N : Subgroup G}
    [N.Normal] {f : G →* H} {hN : N ≤ f.ker} (a : G) :
    (QuotientGroup.lift N f hN).toFun (QuotientGroup.mk a) = f.toFun a :=
  rfl

/-! @end -/

/--
@problem lift_int
@title Reduction Modulo n on ℤ ⧸ nℤ
@concept universal_property

@preamble
The reduction `intToZMod n` of the section on homomorphisms sends every multiple of `n` to `0`, so it factors through the quotient `ℤ ⧸ nℤ`. The additive version of the lift, `QuotientAddGroup.lift`, with `QuotientAddGroup.lift_mk`, does this for additive groups.

Its hypothesis is an inclusion of subgroups, and `H ≤ K` says that every element of `H` lies in `K`, as the order on subgroups was defined. The section on homomorphisms proved
```lean
theorem ker_intToZMod (n : ℕ) [NeZero n] :
    (intToZMod n).ker = intMultiples n
```
@description
Show that some homomorphism from `ℤ ⧸ nℤ` to `ZMod n` sends the class of every integer `a` to `(intToZMod n).toFun a`.
-/
theorem exists_hom_int_quotient (n : ℕ) [NeZero n] :
    ∃ g : ℤ ⧸ intMultiples n →+ ZMod n,
      ∀ a, g.toFun (QuotientAddGroup.mk a) = (intToZMod n).toFun a := by
  have hN : intMultiples n ≤ (intToZMod n).ker := by
    rw [ker_intToZMod]
    intro x hx
    exact hx
  exact ⟨QuotientAddGroup.lift (intMultiples n) (intToZMod n) hN, QuotientAddGroup.lift_mk⟩

/-!
@problem lift_unique
@title The Lift Is Unique
@concept universal_property

@preamble
The lift is the only homomorphism from `G ⧸ N` that agrees with `f` on the class of every element, since every element of `G ⧸ N` is the class of some `a`. With the lift's construction this is the *universal property* of the quotient.

The context holds `QuotientGroup.lift_mk` of the problem that defined the lift and `QuotientGroup.mk_surjective` of the section on cosets.
@description
Show that a homomorphism `g : G ⧸ N →* H` that sends the class of every `a` to `f.toFun a` agrees with the lift everywhere, under the name `QuotientGroup.lift_unique`.
-/

@[to_additive QuotientAddGroup.lift_unique]
theorem QuotientGroup.lift_unique {G : Type u} {H : Type v} [Group G] [Group H]
    {N : Subgroup G} [N.Normal] {f : G →* H} {hN : N ≤ f.ker} (g : G ⧸ N →* H)
    (hg : ∀ a, g.toFun (QuotientGroup.mk a) = f.toFun a) (q : G ⧸ N) :
    g.toFun q = (QuotientGroup.lift N f hN).toFun q := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective q
  rw [← ha, hg, QuotientGroup.lift_mk]

/-! @end -/

end GroupTheory
