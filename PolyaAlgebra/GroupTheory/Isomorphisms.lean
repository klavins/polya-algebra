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
import PolyaAlgebra.GroupTheory.Quotients

/-! @section The Isomorphism Theorems -/

universe u v

namespace GroupTheory

set_option linter.translateGenerateName false

/-!
@concept first_isomorphism_theorem
@title The First Isomorphism Theorem
@kind theorem

A homomorphism matches the cosets of its kernel with its values, one for one, and the matching is an isomorphism: the quotient by the kernel is the image under other names. This is how a quotient group is recognized as a group already known, as the integers modulo the multiples of `n` are the residues modulo `n`.
-/

/-!
@problem of_bijective
@title A Bijective Homomorphism Is an Isomorphism
@concept first_isomorphism_theorem

@preamble
An isomorphism carries an inverse function, and a homomorphism whose function is bijective has one. Mathlib packages a bijection with its inverse:
```lean
noncomputable def Equiv.ofBijective (f : α → β)
    (hf : Function.Bijective f) : α ≃ β
```
Its function is `f`, and its inverse function picks, for each `b`, the element that `f` sends to `b`. That is a choice, so the definition is `noncomputable`, and so is every definition that uses it. The law of a homomorphism `f` is its field `f.map_mul'`.
@description
Define `GroupIso.ofBijective f hf`, the isomorphism whose function is that of a homomorphism `f` with a bijective function. Keep the `@[to_additive]` line.
-/

@[to_additive AddGroupIso.ofBijective]
noncomputable def GroupIso.ofBijective {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H)
    (hf : Function.Bijective f.toFun) : G ≃* H where
  toEquiv := Equiv.ofBijective f.toFun hf
  map_mul' := f.map_mul'

/-- @spec -/
example {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H)
    (hf : Function.Bijective f.toFun) (a : G) : (GroupIso.ofBijective f hf).toFun a = f.toFun a :=
  rfl

/-! @end -/

/-!
@problem lift_injective
@title When the Lift Is Injective and Surjective
@concept first_isomorphism_theorem

@preamble
The lift `QuotientGroup.lift N f hN` of the previous section is injective when `N` is the whole kernel of `f`, and surjective when `f` is. That the kernel lies in `N` is written `f.ker ≤ N`, the order of the section on subgroups: every element of `f.ker` lies in `N`.

The context holds `QuotientGroup.lift_mk` of the previous section; `QuotientGroup.mk_surjective` and
```lean
theorem QuotientGroup.eq {a b : G} :
    (mk a : G ⧸ N) = mk b ↔ a⁻¹ * b ∈ N
```
of the section on cosets; `GroupHom.mem_ker`, `GroupHom.map_mul` and `GroupHom.map_inv` of the section on homomorphisms; and `inv_mul_cancel` of the second section.
@description
Show that the lift is injective when the kernel of `f` lies in `N`, under the name `QuotientGroup.lift_injective`, and that it is surjective when `f.toFun` is, under the name `QuotientGroup.lift_surjective`.
-/

@[to_additive QuotientAddGroup.lift_injective]
theorem QuotientGroup.lift_injective {G : Type u} {H : Type v} [Group G] [Group H]
    {N : Subgroup G} [N.Normal] {f : G →* H} {hN : N ≤ f.ker} (h : f.ker ≤ N) :
    Function.Injective (QuotientGroup.lift N f hN).toFun := by
  intro p q hpq
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective p
  obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective q
  rw [← ha, ← hb, QuotientGroup.lift_mk, QuotientGroup.lift_mk] at hpq
  rw [← ha, ← hb, QuotientGroup.eq]
  apply h
  rw [GroupHom.mem_ker, f.map_mul, f.map_inv, hpq, inv_mul_cancel]

@[to_additive QuotientAddGroup.lift_surjective]
theorem QuotientGroup.lift_surjective {G : Type u} {H : Type v} [Group G] [Group H]
    {N : Subgroup G} [N.Normal] {f : G →* H} {hN : N ≤ f.ker} (hf : Function.Surjective f.toFun) :
    Function.Surjective (QuotientGroup.lift N f hN).toFun := by
  intro y
  obtain ⟨a, ha⟩ := hf y
  exact ⟨QuotientGroup.mk a, ha⟩

/-! @end -/

/-!
@problem quotient_ker_equiv_of_surjective
@title The First Isomorphism Theorem for a Surjective Homomorphism
@concept first_isomorphism_theorem

@preamble
The kernel of a homomorphism `f : G →* H` is normal, by the instance `GroupHom.normal_ker` of the previous section, so `G ⧸ f.ker` is a group. When `f` is surjective, the lift of `f` to it is an isomorphism
```lean
G ⧸ f.ker ≃* H
```
This is the *first isomorphism theorem* for a surjective homomorphism: its target is isomorphic to the quotient of its source by its kernel.

The order on subgroups is the relation `≤` of the section on subgroups and nothing more, so Mathlib's laws of orders, `le_refl` among them, do not apply to it. The context holds `GroupIso.ofBijective`, `QuotientGroup.lift_injective` and `QuotientGroup.lift_surjective` of this section, and `QuotientGroup.lift` of the previous section.
@description
Define `QuotientGroup.quotientKerEquivOfSurjective f hf`, the isomorphism from `G ⧸ f.ker` to `H` sending the class of `a` to `f.toFun a`, for a homomorphism `f` whose function is surjective.
-/

@[to_additive QuotientAddGroup.quotientKerEquivOfSurjective]
noncomputable def QuotientGroup.quotientKerEquivOfSurjective {G : Type u} {H : Type v} [Group G]
    [Group H] (f : G →* H) (hf : Function.Surjective f.toFun) : G ⧸ f.ker ≃* H :=
  GroupIso.ofBijective (QuotientGroup.lift f.ker f (fun _ hx => hx))
    ⟨QuotientGroup.lift_injective (fun _ hx => hx), QuotientGroup.lift_surjective hf⟩

/-- @spec -/
example {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f.toFun) (a : G) :
    (QuotientGroup.quotientKerEquivOfSurjective f hf).toFun (QuotientGroup.mk a) = f.toFun a :=
  rfl

/-! @end -/

/-!
@problem range_restrict
@title A Homomorphism Onto Its Image
@concept first_isomorphism_theorem

@preamble
A homomorphism `f : G →* H` is surjective onto its image `f.range`, of the section on homomorphisms, a group as `f.range.carrier`. We write `f.rangeRestrict` for `f` taken as a homomorphism *onto its image*: it sends `a` to `f.toFun a`, as an element of `f.range.carrier`.

An element of `f.range.carrier` is a pair `⟨y, hy⟩` of an element of `H` and a proof that it lies in the image, which by definition is `∃ x, f.toFun x = y`. The product of two such pairs has as its element of `H` the product of theirs, by definition. The context holds core Lean's `Subtype.ext` and `GroupHom.map_mul` of the section on homomorphisms.
@description
Define `GroupHom.rangeRestrict f`, the homomorphism from `G` onto the image of `f` that sends `a` to `f.toFun a`, and show that its function is surjective, under the name `GroupHom.rangeRestrict_surjective`.
-/

@[to_additive AddGroupHom.rangeRestrict]
def GroupHom.rangeRestrict {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) :
    G →* f.range.carrier where
  toFun a := ⟨f.toFun a, a, rfl⟩
  map_mul' a b := Subtype.ext (f.map_mul a b)

/-- @spec -/
example {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) (a : G) :
    (f.rangeRestrict.toFun a : H) = f.toFun a :=
  rfl

@[to_additive AddGroupHom.rangeRestrict_surjective]
theorem GroupHom.rangeRestrict_surjective {G : Type u} {H : Type v} [Group G] [Group H]
    (f : G →* H) : Function.Surjective f.rangeRestrict.toFun := by
  intro ⟨y, a, ha⟩
  exact ⟨a, Subtype.ext ha⟩

/-! @end -/

/--
@problem ker_range_restrict
@title The Homomorphism Onto the Image Has the Same Kernel
@concept first_isomorphism_theorem

@preamble
The neutral element of `f.range.carrier` has `1` as its element of `H`, by definition, so the homomorphism onto the image sends `a` to `1` exactly when `f` does.

The context holds core Lean's `congrArg`, which turns an equation `x = y` into `g x = g y` for a function `g`, and core Lean's `Subtype.ext`; `GroupHom.mem_ker` of the section on homomorphisms; and `Subgroup.ext` of the section on subgroups.
@description
Show that `f.rangeRestrict` has the same kernel as `f`, under the name `GroupHom.ker_rangeRestrict`.
-/
@[to_additive AddGroupHom.ker_rangeRestrict]
theorem GroupHom.ker_rangeRestrict {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) :
    f.rangeRestrict.ker = f.ker := by
  apply Subgroup.ext
  intro x
  rw [GroupHom.mem_ker, GroupHom.mem_ker]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

/-!
@problem quotient_ker_equiv_range
@title The Quotient by the Kernel Is the Image
@concept first_isomorphism_theorem

@preamble
The homomorphism onto the image is surjective and has the same kernel as `f`. So the *first isomorphism theorem* holds for every homomorphism `f`:
```lean
G ⧸ f.ker ≃* f.range.carrier
```
The context holds, of this section, `GroupIso.ofBijective`, `QuotientGroup.lift_injective`, `QuotientGroup.lift_surjective`, `GroupHom.rangeRestrict`, `GroupHom.rangeRestrict_surjective` and `GroupHom.ker_rangeRestrict`; and `QuotientGroup.lift` of the previous section.
@description
Define `QuotientGroup.quotientKerEquivRange f`, the isomorphism from `G ⧸ f.ker` to the image of `f` sending the class of `a` to `f.toFun a`.
-/

@[to_additive QuotientAddGroup.quotientKerEquivRange]
noncomputable def QuotientGroup.quotientKerEquivRange {G : Type u} {H : Type v} [Group G]
    [Group H] (f : G →* H) : G ⧸ f.ker ≃* f.range.carrier :=
  GroupIso.ofBijective
    (QuotientGroup.lift f.ker f.rangeRestrict (by
      rw [f.ker_rangeRestrict]
      exact fun _ hx => hx))
    ⟨QuotientGroup.lift_injective (by
      rw [f.ker_rangeRestrict]
      exact fun _ hx => hx),
      QuotientGroup.lift_surjective f.rangeRestrict_surjective⟩

/-- @spec -/
example {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) (a : G) :
    ((QuotientGroup.quotientKerEquivRange f).toFun (QuotientGroup.mk a) : H) = f.toFun a :=
  rfl

/-! @end -/

/--
@problem int_to_zmod_surjective
@title Every Residue Is the Reduction of an Integer
@concept first_isomorphism_theorem

@preamble
The reduction `intToZMod n` of the section on homomorphisms sends an integer `k` to `k • 1`, by definition. It reaches every residue.

The context holds core Lean's `Fin.ext` and `Nat.mod_eq_of_lt`, `natCast_zsmul` of the section on powers, and `ZMod.val_nsmul_one` of the section on subgroups.
@description
Show that the reduction `intToZMod n` is surjective, for `n ≠ 0`.
-/
theorem intToZMod_surjective (n : ℕ) [NeZero n] : Function.Surjective (intToZMod n).toFun := by
  intro a
  refine ⟨(a.val : ℤ), ?_⟩
  change ((a.val : ℤ) • (1 : ZMod n)) = a
  rw [natCast_zsmul]
  apply Fin.ext
  rw [ZMod.val_nsmul_one]
  exact Nat.mod_eq_of_lt a.isLt

/-!
@problem int_quotient_equiv
@title The Integers Modulo nℤ Are the Residues Modulo n
@concept first_isomorphism_theorem

@preamble
The reduction `intToZMod n` is surjective, and its kernel is `nℤ`, by `ker_intToZMod` of the section on homomorphisms. So the quotient `ℤ ⧸ nℤ`, built from cosets, is `ZMod n`, built from remainders:
```lean
ℤ ⧸ intMultiples n ≃+ ZMod n
```
The class of `a` must go to its reduction by definition, not only by a proof.

The context holds, of this section, the additive versions `AddGroupIso.ofBijective`, `QuotientAddGroup.lift_injective` and `QuotientAddGroup.lift_surjective`, and `intToZMod_surjective`; and `QuotientAddGroup.lift` of the previous section.
@description
Define `intQuotientEquivZMod n`, the isomorphism from `ℤ ⧸ nℤ` to `ZMod n` sending the class of `a` to `(intToZMod n).toFun a`, for `n ≠ 0`.
-/

noncomputable def intQuotientEquivZMod (n : ℕ) [NeZero n] : ℤ ⧸ intMultiples n ≃+ ZMod n :=
  AddGroupIso.ofBijective
    (QuotientAddGroup.lift (intMultiples n) (intToZMod n) (by
      rw [ker_intToZMod]
      exact fun _ hx => hx))
    ⟨QuotientAddGroup.lift_injective (by
      rw [ker_intToZMod]
      exact fun _ hx => hx),
      QuotientAddGroup.lift_surjective (intToZMod_surjective n)⟩

/-- @spec -/
example (n : ℕ) [NeZero n] (a : ℤ) :
    (intQuotientEquivZMod n).toFun (QuotientAddGroup.mk a) = (intToZMod n).toFun a :=
  rfl

/-! @end -/

/--
@problem zmod_six_quotient
@title ZMod 6 Modulo the Even Residues Is ZMod 2
@concept first_isomorphism_theorem

@preamble
The reduction `zmodSixToTwo` of the section on homomorphisms has the even residues `zmodSixEvens` as its kernel and the whole of `ZMod 2` as its image. So the quotient of `ZMod 6` by its even residues is `ZMod 2`: its two classes are the even residues and the odd ones.

The function of an isomorphism built by `AddGroupIso.ofBijective` is that of its homomorphism, by definition. The context holds `ker_zmodSixToTwo` and `range_zmodSixToTwo` of the section on homomorphisms, with `AddGroupHom.range_eq_top`, that the image is the whole group exactly when the function is surjective; `AddGroupIso.ofBijective`, `QuotientAddGroup.lift_injective` and `QuotientAddGroup.lift_surjective` of this section; and `QuotientAddGroup.lift` of the previous section.
@description
Show that some isomorphism from `ZMod 6 ⧸ zmodSixEvens` to `ZMod 2` sends the class of every `a` to `zmodSixToTwo.toFun a`.
-/
theorem exists_addGroupIso_zmodSix_quotient :
    ∃ e : ZMod 6 ⧸ zmodSixEvens ≃+ ZMod 2,
      ∀ a, e.toFun (QuotientAddGroup.mk a) = zmodSixToTwo.toFun a := by
  have hle : zmodSixEvens ≤ zmodSixToTwo.ker := by
    rw [ker_zmodSixToTwo]
    exact fun _ hx => hx
  have hge : zmodSixToTwo.ker ≤ zmodSixEvens := by
    rw [ker_zmodSixToTwo]
    exact fun _ hx => hx
  have hs := (AddGroupHom.range_eq_top zmodSixToTwo).mp range_zmodSixToTwo
  exact ⟨AddGroupIso.ofBijective (QuotientAddGroup.lift zmodSixEvens zmodSixToTwo hle)
    ⟨QuotientAddGroup.lift_injective hge, QuotientAddGroup.lift_surjective hs⟩,
    fun _ => rfl⟩

/-!
@concept correspondence_theorem
@title The Correspondence Theorem
@kind theorem

A homomorphism carries subgroups forward, as images, and back, as preimages. For the map sending each element to its class modulo a normal subgroup, the two match the subgroups that contain the normal subgroup with the subgroups of the quotient, one for one. So the subgroups of a quotient are known from those of the group.
-/

/-!
@problem comap
@title The Preimage of a Subgroup
@concept correspondence_theorem

@preamble
A homomorphism `f : G →* H` carries each subgroup `K` of `H` back to a subgroup of `G`, its *preimage*, whose carrier is
```lean
{x | f.toFun x ∈ K}
```
We write it `K.comap f`.

A membership in a set written `{x | p x}` is `p x` by definition, and `change` writes it out. The context holds `GroupHom.map_one`, `GroupHom.map_mul` and `GroupHom.map_inv` of the section on homomorphisms, written `f.map_one`, and `Subgroup.one_mem`, `Subgroup.mul_mem` and `Subgroup.inv_mem` of the section on subgroups, written `K.one_mem`.
@description
Define `Subgroup.comap f K`, the subgroup of `G` with that carrier, and prove `Subgroup.mem_comap`, which holds by definition:
```lean
x ∈ K.comap f ↔ f.toFun x ∈ K
```
-/

@[to_additive AddSubgroup.comap]
def Subgroup.comap {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) (K : Subgroup H) :
    Subgroup G where
  carrier := {x | f.toFun x ∈ K}
  one_mem' := by
    change f.toFun 1 ∈ K
    rw [f.map_one]
    exact K.one_mem
  mul_mem' := by
    intro a b ha hb
    change f.toFun (a * b) ∈ K
    rw [f.map_mul]
    exact K.mul_mem ha hb
  inv_mem' := by
    intro a ha
    change f.toFun a⁻¹ ∈ K
    rw [f.map_inv]
    exact K.inv_mem ha

/-- @spec -/
example {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) (K : Subgroup H) (x : G) :
    x ∈ K.comap f ↔ f.toFun x ∈ K := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

@[to_additive AddSubgroup.mem_comap]
theorem Subgroup.mem_comap {G : Type u} {H : Type v} [Group G] [Group H] {f : G →* H}
    {K : Subgroup H} {x : G} : x ∈ K.comap f ↔ f.toFun x ∈ K :=
  Iff.rfl

/-! @end -/

/-!
@problem map
@title The Image of a Subgroup
@concept correspondence_theorem

@preamble
Forward, a homomorphism `f` carries each subgroup `K` of `G` to a subgroup of `H`, its *image*, the values of `f` on `K`:
```lean
{y | ∃ x ∈ K, f.toFun x = y}
```
We write it `K.map f`. A member of the image opens into `⟨x, hx, e⟩`, with `hx : x ∈ K` and `e : f.toFun x = y`, as a member of `f.range` opened into a pair.

The context holds the facts of the previous problem: `GroupHom.map_one`, `GroupHom.map_mul` and `GroupHom.map_inv` of the section on homomorphisms, and `Subgroup.one_mem`, `Subgroup.mul_mem` and `Subgroup.inv_mem` of the section on subgroups.
@description
Define `Subgroup.map f K`, the subgroup of `H` with that carrier, and prove `Subgroup.mem_map`, which holds by definition:
```lean
y ∈ K.map f ↔ ∃ x ∈ K, f.toFun x = y
```
-/

@[to_additive AddSubgroup.map]
def Subgroup.map {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) (K : Subgroup G) :
    Subgroup H where
  carrier := {y | ∃ x ∈ K, f.toFun x = y}
  one_mem' := ⟨1, K.one_mem, f.map_one⟩
  mul_mem' := by
    intro a b ⟨x, hx, ex⟩ ⟨y, hy, ey⟩
    exact ⟨x * y, K.mul_mem hx hy, by rw [f.map_mul, ex, ey]⟩
  inv_mem' := by
    intro a ⟨x, hx, ex⟩
    exact ⟨x⁻¹, K.inv_mem hx, by rw [f.map_inv, ex]⟩

/-- @spec -/
example {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) (K : Subgroup G) (y : H) :
    y ∈ K.map f ↔ ∃ x, x ∈ K ∧ f.toFun x = y := by
  constructor
  · intro ⟨x, hx, e⟩
    exact ⟨x, hx, by grind⟩
  · intro ⟨x, hx, e⟩
    exact ⟨x, hx, by grind⟩

@[to_additive AddSubgroup.mem_map]
theorem Subgroup.mem_map {G : Type u} {H : Type v} [Group G] [Group H] {f : G →* H}
    {K : Subgroup G} {y : H} : y ∈ K.map f ↔ ∃ x ∈ K, f.toFun x = y :=
  Iff.rfl

/-! @end -/

/-!
@problem map_comap_mk
@title Subgroups of a Quotient as Images
@concept correspondence_theorem

@preamble
Let `N` be a normal subgroup of `G`. The *quotient map* is the homomorphism `QuotientGroup.mk' N` from `G` to `G ⧸ N` of the previous section, whose function is `QuotientGroup.mk` by definition. Every subgroup of `G ⧸ N` is the image of a subgroup of `G` containing `N`.

The context holds `Subgroup.mem_comap` and `Subgroup.mem_map` of this section; `QuotientGroup.ker_mk'` of the previous section; `QuotientGroup.mk_surjective` of the section on cosets; `GroupHom.mem_ker` of the section on homomorphisms; and `Subgroup.ext` and `Subgroup.one_mem` of the section on subgroups.
@description
Show that `N` lies in the preimage of `L`, under the name `QuotientGroup.le_comap_mk'`, and that the image of the preimage of `L` is `L`, under the name `QuotientGroup.map_comap_mk'`.
-/

@[to_additive QuotientAddGroup.le_comap_mk']
theorem QuotientGroup.le_comap_mk' {G : Type u} [Group G] (N : Subgroup G) [N.Normal]
    (L : Subgroup (G ⧸ N)) : N ≤ L.comap (QuotientGroup.mk' N) := by
  intro x hx
  rw [Subgroup.mem_comap]
  have h : (QuotientGroup.mk' N).toFun x = 1 := by
    rw [← GroupHom.mem_ker, QuotientGroup.ker_mk']
    exact hx
  rw [h]
  exact L.one_mem

@[to_additive QuotientAddGroup.map_comap_mk']
theorem QuotientGroup.map_comap_mk' {G : Type u} [Group G] (N : Subgroup G) [N.Normal]
    (L : Subgroup (G ⧸ N)) : (L.comap (QuotientGroup.mk' N)).map (QuotientGroup.mk' N) = L := by
  apply Subgroup.ext
  intro q
  rw [Subgroup.mem_map]
  constructor
  · intro ⟨x, hx, e⟩
    rw [← e]
    exact hx
  · intro hq
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective q
    rw [← ha] at hq
    exact ⟨a, hq, ha⟩

/-! @end -/

/--
@problem comap_map_mk
@title Every Subgroup Above N Comes From the Quotient
@concept correspondence_theorem

@preamble
In the other direction, a subgroup `K` of `G` that contains `N` is the preimage of its image under the quotient map. With the previous problem this is the *correspondence theorem*.

The context holds `Subgroup.mem_comap` and `Subgroup.mem_map` of this section; `QuotientGroup.eq` of the section on cosets; `Subgroup.ext` and `Subgroup.mul_mem` of the section on subgroups; and `mul_inv_cancel_left` of the second section.
@description
Show that the preimage of the image of `K` is `K` when `N ≤ K`, under the name `QuotientGroup.comap_map_mk'`.
-/
@[to_additive QuotientAddGroup.comap_map_mk']
theorem QuotientGroup.comap_map_mk' {G : Type u} [Group G] {N K : Subgroup G} [N.Normal]
    (h : N ≤ K) : (K.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = K := by
  apply Subgroup.ext
  intro x
  rw [Subgroup.mem_comap, Subgroup.mem_map]
  constructor
  · intro ⟨y, hy, e⟩
    have hk : y⁻¹ * x ∈ N := QuotientGroup.eq.mp e
    have e' : x = y * (y⁻¹ * x) := by
      rw [mul_inv_cancel_left]
    rw [e']
    exact K.mul_mem hy (h hk)
  · intro hx
    exact ⟨x, hx, rfl⟩

/-!
@problem zmod_six_correspondence
@title The Even Residues and the Trivial Subgroup of ZMod 2
@concept correspondence_theorem

@preamble
The reduction `zmodSixToTwo` of the section on homomorphisms is surjective and plays the part of the quotient map by the even residues. The correspondence matches the subgroups of `ZMod 6` that contain the even residues with the subgroups of `ZMod 2`, and this problem checks its smallest pair.

The context holds `AddSubgroup.mem_comap` and `AddSubgroup.mem_map` of this section, and `AddSubgroup.ext`, `AddSubgroup.mem_bot` and `mem_zmodSixEvens` of the section on subgroups.
@description
Show that the preimage of `⊥` under `zmodSixToTwo` is `zmodSixEvens`, and that the image of `zmodSixEvens` under `zmodSixToTwo` is `⊥`.
-/

theorem comap_bot_zmodSixToTwo : (⊥ : AddSubgroup (ZMod 2)).comap zmodSixToTwo = zmodSixEvens := by
  apply AddSubgroup.ext
  simp only [AddSubgroup.mem_comap, AddSubgroup.mem_bot, mem_zmodSixEvens]
  decide

theorem map_zmodSixEvens_zmodSixToTwo : zmodSixEvens.map zmodSixToTwo = ⊥ := by
  apply AddSubgroup.ext
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_bot, mem_zmodSixEvens]
  decide

/-! @end -/

/-!
@concept second_isomorphism_theorem
@title The Second Isomorphism Theorem
@kind theorem

A subgroup and a normal subgroup give two groups: the quotient of the subgroup by its intersection with the normal subgroup, and the classes of the subgroup's elements in the quotient by the normal subgroup. The second isomorphism theorem says that they are isomorphic. It is how a quotient of a subgroup is found inside a quotient of the whole group.
-/

/-!
@problem subgroup_of
@title A Subgroup Seen Inside Another
@concept second_isomorphism_theorem

@preamble
To take a quotient of a subgroup `H`, we need subgroups of the group `H.carrier`. The *inclusion* `Subgroup.subtype H` is the homomorphism from `H.carrier` to `G` that sends each element `a` of `H` to itself, `a.1`; the product of `H.carrier` is that of `G`, by definition. The preimage of a subgroup `N` of `G` under the inclusion is `N.subgroupOf H`. Its elements are the elements of `H` that lie in `N`: it is the intersection `H ⊓ N`, seen inside `H`.

The context holds `Subgroup.comap` of this section.
@description
Define the homomorphism `Subgroup.subtype H`, sending `a` to `a.1`, and `Subgroup.subgroupOf N H`, the preimage of `N` under it, and prove `Subgroup.mem_subgroupOf`, which holds by definition:
```lean
h ∈ N.subgroupOf H ↔ (h : G) ∈ N
```
-/

@[to_additive AddSubgroup.subtype]
def Subgroup.subtype {G : Type u} [Group G] (H : Subgroup G) : H.carrier →* G where
  toFun a := a.1
  map_mul' _ _ := rfl

@[to_additive AddSubgroup.addSubgroupOf]
def Subgroup.subgroupOf {G : Type u} [Group G] (N H : Subgroup G) : Subgroup H.carrier :=
  N.comap H.subtype

/-- @spec -/
example {G : Type u} [Group G] (N H : Subgroup G) (a : H.carrier) :
    H.subtype.toFun a = a.1 ∧ (a ∈ N.subgroupOf H ↔ a.1 ∈ N) := by
  constructor
  · rfl
  · constructor
    · intro h
      exact h
    · intro h
      exact h

@[to_additive AddSubgroup.mem_addSubgroupOf]
theorem Subgroup.mem_subgroupOf {G : Type u} [Group G] {N H : Subgroup G} {h : H.carrier} :
    h ∈ N.subgroupOf H ↔ (h : G) ∈ N :=
  Iff.rfl

/-! @end -/

/-!
@problem normal_subgroup_of
@title A Normal Subgroup Seen Inside a Subgroup
@concept second_isomorphism_theorem

@preamble
When `N` is normal in `G`, the subgroup `N.subgroupOf H` is normal in `H.carrier`, since the product and the inverse of `H.carrier` are those of `G`, by definition. `Subgroup.Normal` has one field, the law `Subgroup.Normal.conj_mem` shown below, so the instance is written with `where` and that field.

The context holds `Subgroup.mem_subgroupOf` of the previous problem and, of the previous section,
```lean
theorem Subgroup.Normal.conj_mem [N.Normal]
    (n : G) (hn : n ∈ N) (g : G) : g * n * g⁻¹ ∈ N
```
@description
Supply the instance `Subgroup.normal_subgroupOf`, which makes `N.subgroupOf H` normal when `N` is.
-/

@[to_additive AddSubgroup.normal_addSubgroupOf]
instance Subgroup.normal_subgroupOf {G : Type u} [Group G] (N H : Subgroup G) [N.Normal] :
    (N.subgroupOf H).Normal where
  conj_mem := by
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.Normal.conj_mem (n : G) hn (g : G)

/-- @spec -/
example {G : Type u} [Group G] (N H : Subgroup G) [N.Normal] : (N.subgroupOf H).Normal :=
  inferInstance

/-! @end -/

/--
@problem ker_restrict
@title The Kernel of the Quotient Map on a Subgroup
@concept second_isomorphism_theorem

@preamble
*Restricting* the quotient map to a subgroup `H` gives the composite
```lean
(QuotientGroup.mk' N).comp H.subtype :
    H.carrier →* G ⧸ N
```
which sends each element of `H` to its class.

The function of a composite applies one homomorphism and then the other, by the definition of `GroupHom.comp` in the section on homomorphisms. The neutral element of `G ⧸ N` is the class of `1`, by definition. The context holds `Subgroup.mem_subgroupOf` of this section, `QuotientGroup.mk_eq_mk_one_iff` of the section on cosets, `GroupHom.mem_ker` of the section on homomorphisms, and `Subgroup.ext` of the section on subgroups.
@description
Show that the kernel of the restriction is `N.subgroupOf H`, under the name `QuotientGroup.ker_restrict`.
-/
@[to_additive QuotientAddGroup.ker_restrict]
theorem QuotientGroup.ker_restrict {G : Type u} [Group G] (H N : Subgroup G) [N.Normal] :
    ((QuotientGroup.mk' N).comp H.subtype).ker = N.subgroupOf H := by
  apply Subgroup.ext
  intro x
  rw [GroupHom.mem_ker, Subgroup.mem_subgroupOf]
  exact QuotientGroup.mk_eq_mk_one_iff

/-!
@problem second_isomorphism
@title The Second Isomorphism Theorem
@concept second_isomorphism_theorem

@preamble
The image of the restriction consists of the classes of the elements of `H`. Textbooks write it as the quotient of `H ⊔ N` by `N`, with `H ⊔ N` the subgroup of the previous section. The quotient of `H.carrier` by the kernel of the restriction, `N.subgroupOf H`, is isomorphic to this image: the *second isomorphism theorem*. The first isomorphism theorem itself is not in this problem's context; its argument is.

As for `ℤ ⧸ nℤ`, the isomorphism is to send the class of `h` to the class of `h` by definition. The context holds, of this section, `GroupIso.ofBijective`, `QuotientGroup.lift_injective`, `QuotientGroup.lift_surjective`, `GroupHom.rangeRestrict`, `GroupHom.rangeRestrict_surjective`, `GroupHom.ker_rangeRestrict` and `QuotientGroup.ker_restrict`; and `QuotientGroup.lift` of the previous section.
@description
Define `QuotientGroup.quotientSubgroupOfEquivRange H N`, an isomorphism from `H.carrier ⧸ N.subgroupOf H` to the image of the restriction, sending the class of `h` to the class of `h` in `G ⧸ N`.
-/

@[to_additive QuotientAddGroup.quotientAddSubgroupOfEquivRange]
noncomputable def QuotientGroup.quotientSubgroupOfEquivRange {G : Type u} [Group G]
    (H N : Subgroup G) [N.Normal] :
    H.carrier ⧸ N.subgroupOf H ≃* ((QuotientGroup.mk' N).comp H.subtype).range.carrier :=
  GroupIso.ofBijective
    (QuotientGroup.lift (N.subgroupOf H) ((QuotientGroup.mk' N).comp H.subtype).rangeRestrict (by
      rw [GroupHom.ker_rangeRestrict, QuotientGroup.ker_restrict]
      exact fun _ hx => hx))
    ⟨QuotientGroup.lift_injective (by
      rw [GroupHom.ker_rangeRestrict, QuotientGroup.ker_restrict]
      exact fun _ hx => hx),
      QuotientGroup.lift_surjective (GroupHom.rangeRestrict_surjective _)⟩

/-- @spec -/
example {G : Type u} [Group G] (H N : Subgroup G) [N.Normal] (h : H.carrier) :
    ((QuotientGroup.quotientSubgroupOfEquivRange H N).toFun (QuotientGroup.mk h) : G ⧸ N) =
      QuotientGroup.mk (h : G) :=
  rfl

/-! @end -/

/-!
@concept index_formula
@title The Index in Stages
@kind theorem

When one subgroup lies inside another, the cosets of the smaller one can be counted in stages: the cosets of the larger one in the group, then the cosets of the smaller one inside the larger. So the index of the smaller subgroup is the product of two indices, and an index can be found through any subgroup in between.
-/

/-!
@problem card_subgroup_of
@title A Subgroup Inside Another Keeps Its Size
@concept index_formula

@preamble
When `K ≤ H`, the elements of `K.subgroupOf H` are the elements of `K`, each seen inside `H`. An element `x` of `(K.subgroupOf H).carrier` has an element `x.1` of `H.carrier`, whose element of `G` is `x.1.1`, and a proof `x.2 : x.1 ∈ K.subgroupOf H`, which is `x.1.1 ∈ K` by definition.

Mathlib has
```lean
theorem Fintype.card_of_bijective {f : α → β}
    (hf : Function.Bijective f) : Fintype.card α = Fintype.card β
```
The context holds core Lean's `Subtype.ext` and `Subtype.mk.inj`, which takes an equation `⟨a, ha⟩ = ⟨b, hb⟩` to `a = b`, and takes the equation that injectivity gives as it stands.
@description
Show that `K.subgroupOf H` has as many elements as `K` when `K ≤ H`, under the name `Subgroup.card_subgroupOf`.
-/

open Classical in
@[to_additive AddSubgroup.card_addSubgroupOf]
theorem Subgroup.card_subgroupOf {G : Type u} [Group G] [Fintype G] {K H : Subgroup G}
    (h : K ≤ H) : Fintype.card (K.subgroupOf H).carrier = Fintype.card K.carrier := by
  have hf : Function.Bijective
      (fun x : (K.subgroupOf H).carrier => (⟨x.1.1, x.2⟩ : K.carrier)) := by
    constructor
    · intro x y hxy
      have e : x.1.1 = y.1.1 := Subtype.mk.inj hxy
      exact Subtype.ext (Subtype.ext e)
    · intro ⟨x, hx⟩
      exact ⟨⟨⟨x, h hx⟩, hx⟩, rfl⟩
  exact Fintype.card_of_bijective hf

/-! @end -/

/-!
@problem index_eq_mul_index
@title The Index Multiplies in Stages
@concept index_formula

@preamble
Lagrange's theorem, `Subgroup.index_mul_card` of the section on cosets, holds in every finite group. Mathlib has
```lean
theorem Fintype.card_pos_iff :
    0 < Fintype.card α ↔ Nonempty α
```
The context holds `Subgroup.card_subgroupOf` of the previous problem, `Subgroup.one_mem` of the section on subgroups, and core Lean's `Nat.eq_of_mul_eq_mul_right` and `Nat.mul_assoc`.
@description
Show that, when `K ≤ H`, the index of `K` is the index of `H` times the index of `K.subgroupOf H`, under the name `Subgroup.index_eq_mul_index`.
-/

open Classical in
@[to_additive AddSubgroup.index_eq_mul_index]
theorem Subgroup.index_eq_mul_index {G : Type u} [Group G] [Fintype G] {K H : Subgroup G}
    (h : K ≤ H) : K.index = H.index * (K.subgroupOf H).index := by
  have hK := K.index_mul_card
  have hH := H.index_mul_card
  have hKH := (K.subgroupOf H).index_mul_card
  rw [Subgroup.card_subgroupOf h] at hKH
  have hpos : 0 < Fintype.card K.carrier :=
    Fintype.card_pos_iff.mpr ⟨⟨1, K.one_mem⟩⟩
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [hK, Nat.mul_assoc, hKH, hH]

/-! @end -/

/-!
@concept direct_products
@title Internal Direct Products
@kind theorem
@goal

Two normal subgroups that meet only in the neutral element and together generate the group make it their product: each element is the product of one element of each, in exactly one way, and elements of the two commute. A group is then known from two smaller ones.
-/

/-!
@problem mul_comm_of_inf_eq_bot
@title Elements of Normal Subgroups Meeting Trivially Commute
@concept direct_products

@preamble
A direct product needs the elements of its two factors to commute. The *commutator* of `h` and `k` is `h * k * h⁻¹ * k⁻¹`.

The context holds, of the previous section,
```lean
theorem Subgroup.Normal.conj_mem [N.Normal]
    (n : G) (hn : n ∈ N) (g : G) : g * n * g⁻¹ ∈ N
```
`Subgroup.inv_mem`, `Subgroup.mem_bot`, `Subgroup.mem_inf` and `Subgroup.mul_mem` of the section on subgroups, written `H.mul_mem`; and `inv_eq_of_mul_eq_one_right`, `inv_injective`, `mul_assoc` and `mul_inv_rev` of the second section.
@description
Show that `h * k = k * h` when `h ∈ H` and `k ∈ K` for normal subgroups `H` and `K` with `H ⊓ K = ⊥`, under the name `Subgroup.mul_comm_of_inf_eq_bot`.
-/

@[to_additive AddSubgroup.add_comm_of_inf_eq_bot]
theorem Subgroup.mul_comm_of_inf_eq_bot {G : Type u} [Group G] {H K : Subgroup G} [H.Normal]
    [K.Normal] (hHK : H ⊓ K = ⊥) {h k : G} (hh : h ∈ H) (hk : k ∈ K) : h * k = k * h := by
  have hH : h * (k * h⁻¹ * k⁻¹) ∈ H :=
    H.mul_mem hh (Subgroup.Normal.conj_mem _ (H.inv_mem hh) k)
  have hK : h * k * h⁻¹ * k⁻¹ ∈ K :=
    K.mul_mem (Subgroup.Normal.conj_mem _ hk h) (K.inv_mem hk)
  have e : h * (k * h⁻¹ * k⁻¹) = h * k * h⁻¹ * k⁻¹ := by
    rw [mul_assoc k, mul_assoc (h * k), mul_assoc h]
  rw [e] at hH
  have h1 : h * k * h⁻¹ * k⁻¹ ∈ H ⊓ K := Subgroup.mem_inf.mpr ⟨hH, hK⟩
  rw [hHK, Subgroup.mem_bot] at h1
  have h2 : h * k * (k * h)⁻¹ = 1 := by
    rw [mul_inv_rev, ← mul_assoc]
    exact h1
  exact inv_injective (inv_eq_of_mul_eq_one_right h2)

/-! @end -/

/-!
@problem prod_mul
@title Multiplying the Components of a Pair
@concept direct_products

@preamble
For normal subgroups `H` and `K` with `H ⊓ K = ⊥`, multiplying the components of a pair is a homomorphism. It goes from the product group `H.carrier × K.carrier` of the section on examples to `G`, and sends `x` to `x.1.1 * x.2.1`, where `x.1.1` is the element of `G` in the first component. The product of pairs is componentwise and the product of `H.carrier` is that of `G`, both by definition.

The context holds `Subgroup.mul_comm_of_inf_eq_bot` of the previous problem and `mul_assoc` of the second section.
@description
Define `Subgroup.prodMul H K hHK`, the homomorphism from `H.carrier × K.carrier` to `G` sending `x` to `x.1.1 * x.2.1`.
-/

@[to_additive AddSubgroup.prodAdd]
def Subgroup.prodMul {G : Type u} [Group G] (H K : Subgroup G) [H.Normal] [K.Normal]
    (hHK : H ⊓ K = ⊥) : H.carrier × K.carrier →* G where
  toFun x := x.1.1 * x.2.1
  map_mul' x y := by
    change x.1.1 * y.1.1 * (x.2.1 * y.2.1) = x.1.1 * x.2.1 * (y.1.1 * y.2.1)
    rw [mul_assoc, ← mul_assoc y.1.1, Subgroup.mul_comm_of_inf_eq_bot hHK y.1.2 x.2.2,
      mul_assoc, mul_assoc]

/-- @spec -/
example {G : Type u} [Group G] (H K : Subgroup G) [H.Normal] [K.Normal] (hHK : H ⊓ K = ⊥)
    (x : H.carrier × K.carrier) : (Subgroup.prodMul H K hHK).toFun x = x.1.1 * x.2.1 :=
  rfl

/-! @end -/

/--
@problem prod_mul_injective
@title A Product of Elements in One Way Only
@concept direct_products

@preamble
When `H ⊓ K = ⊥`, an element of `G` is a product of an element of `H` and one of `K` in at most one way, so the homomorphism of the previous problem is injective.

The context holds core Lean's `Prod.ext` and `Subtype.ext`; `Subgroup.inv_mem`, `Subgroup.mem_bot`, `Subgroup.mem_inf` and `Subgroup.mul_mem` of the section on subgroups; and `inv_mul_cancel_left`, `mul_assoc`, `mul_inv_cancel_left`, `mul_inv_cancel_right`, `mul_left_cancel` and `mul_one` of the second section.
@description
Show that the function of `Subgroup.prodMul H K hHK` is injective, under the name `Subgroup.prodMul_injective`.
-/
@[to_additive AddSubgroup.prodAdd_injective]
theorem Subgroup.prodMul_injective {G : Type u} [Group G] {H K : Subgroup G} [H.Normal] [K.Normal]
    (hHK : H ⊓ K = ⊥) : Function.Injective (Subgroup.prodMul H K hHK).toFun := by
  intro x y hxy
  change x.1.1 * x.2.1 = y.1.1 * y.2.1 at hxy
  have e : y.1.1⁻¹ * x.1.1 = y.2.1 * x.2.1⁻¹ := by
    rw [← mul_inv_cancel_right (y.1.1⁻¹ * x.1.1) x.2.1, mul_assoc y.1.1⁻¹, hxy,
      inv_mul_cancel_left]
  have hm : y.1.1⁻¹ * x.1.1 ∈ H ⊓ K := by
    apply Subgroup.mem_inf.mpr
    constructor
    · exact H.mul_mem (H.inv_mem y.1.2) x.1.2
    · rw [e]
      exact K.mul_mem y.2.2 (K.inv_mem x.2.2)
  rw [hHK, Subgroup.mem_bot] at hm
  have h1 : x.1.1 = y.1.1 := by rw [← mul_inv_cancel_left y.1.1 x.1.1, hm, mul_one]
  rw [h1] at hxy
  exact Prod.ext (Subtype.ext h1) (Subtype.ext (mul_left_cancel hxy))

/-!
@problem prod_mul_equiv
@title A Group as the Product of Two Normal Subgroups
@concept direct_products

@preamble
If moreover `H ⊔ K = ⊤`, the homomorphism is also surjective, and so an isomorphism
```lean
H.carrier × K.carrier ≃* G
```
Then `G` is the *internal direct product* of `H` and `K`.

The context holds `GroupIso.ofBijective` of this section's first concept, `Subgroup.prodMul_injective` of the previous problem, `Subgroup.mem_top` of the section on subgroups, and, of the previous section,
```lean
theorem Subgroup.mem_sup_of_normal [N.Normal] :
    x ∈ H ⊔ N ↔ ∃ h ∈ H, ∃ n ∈ N, h * n = x
```
@description
Define `Subgroup.prodMulEquiv H K hHK hsup`, the isomorphism from `H.carrier × K.carrier` to `G` sending `x` to `x.1.1 * x.2.1`, for normal subgroups `H` and `K` with `H ⊓ K = ⊥` and `H ⊔ K = ⊤`.
-/

@[to_additive AddSubgroup.prodAddEquiv]
noncomputable def Subgroup.prodMulEquiv {G : Type u} [Group G] (H K : Subgroup G) [H.Normal]
    [K.Normal] (hHK : H ⊓ K = ⊥) (hsup : H ⊔ K = ⊤) : H.carrier × K.carrier ≃* G :=
  GroupIso.ofBijective (Subgroup.prodMul H K hHK) (by
    constructor
    · exact Subgroup.prodMul_injective hHK
    · intro g
      have hg : g ∈ H ⊔ K := by
        rw [hsup]
        exact Subgroup.mem_top g
      obtain ⟨h, hh, k, hk, e⟩ := Subgroup.mem_sup_of_normal.mp hg
      exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), e⟩)

/-- @spec -/
example {G : Type u} [Group G] (H K : Subgroup G) [H.Normal] [K.Normal] (hHK : H ⊓ K = ⊥)
    (hsup : H ⊔ K = ⊤) (x : H.carrier × K.carrier) :
    (Subgroup.prodMulEquiv H K hHK hsup).toFun x = x.1.1 * x.2.1 :=
  rfl

/-! @end -/

/-!
@problem zmod_six_product
@title The Residues Modulo Six as a Direct Product
@concept direct_products

@preamble
In `ZMod 6` take the even residues `zmodSixEvens`, `{0, 2, 4}`, and the subgroup `zmodSixThrees` of the residues `{0, 3}`, given below. Every subgroup of `ZMod 6` is normal, by the instance `AddSubgroup.normal_of_comm` of the previous section, so the previous problem applies to these two.

A membership in `⊔` is not decided as it stands, and `decide` refuses a goal about a variable that `intro` named. The context holds `AddSubgroup.mem_sup_of_normal` of the previous section; `AddSubgroup.prodAddEquiv`, the additive version of the previous problem; and `mem_zmodSixEvens`, `AddSubgroup.ext`, `AddSubgroup.mem_inf`, `AddSubgroup.mem_bot`, `AddSubgroup.le_top` and `AddSubgroup.le_antisymm` of the section on subgroups.
@description
Show that the two subgroups meet only in `0` and together give all of `ZMod 6`, and define `zmodSixProdEquiv`, the isomorphism from the product of the two subgroups to `ZMod 6` that adds the components.
-/

/-- @given -/
def zmodSixThrees : AddSubgroup (ZMod 6) where
  carrier := {x | x = 0 ∨ x = 3}
  zero_mem' := by decide
  add_mem' := by decide
  neg_mem' := by decide

/-- @given -/
theorem mem_zmodSixThrees (x : ZMod 6) : x ∈ zmodSixThrees ↔ x = 0 ∨ x = 3 := Iff.rfl

theorem zmodSixEvens_inf_threes : zmodSixEvens ⊓ zmodSixThrees = ⊥ := by
  apply AddSubgroup.ext
  simp only [AddSubgroup.mem_inf, mem_zmodSixEvens, mem_zmodSixThrees, AddSubgroup.mem_bot]
  decide

theorem zmodSixEvens_sup_threes : zmodSixEvens ⊔ zmodSixThrees = ⊤ := by
  have h : ∀ x : ZMod 6, x ∈ zmodSixEvens ⊔ zmodSixThrees := by
    simp only [AddSubgroup.mem_sup_of_normal, mem_zmodSixEvens, mem_zmodSixThrees]
    decide
  apply AddSubgroup.le_antisymm
  · exact AddSubgroup.le_top _
  · intro x _
    exact h x

noncomputable def zmodSixProdEquiv : zmodSixEvens.carrier × zmodSixThrees.carrier ≃+ ZMod 6 :=
  AddSubgroup.prodAddEquiv zmodSixEvens zmodSixThrees zmodSixEvens_inf_threes
    zmodSixEvens_sup_threes

/-- @spec -/
example (x : zmodSixEvens.carrier × zmodSixThrees.carrier) :
    zmodSixProdEquiv.toFun x = x.1.1 + x.2.1 :=
  rfl

/-! @end -/

end GroupTheory
