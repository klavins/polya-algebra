# What the student knows on arrival

A survey of the five subjects of `polya-basic` (GettingStarted, Logic, SetTheory, Programming,
Naturals), made on 2026-10-21 for the Prerequisites section of Group Theory, so that "is this
new to the student?" has an answer. Paths are under `polya-basic/PolyaBasic/`. Reviewers of a
section read this first; `BEST_PRACTICES.md` in `polya-publisher` calls it the baseline.

## What the student does NOT know

1. **Mathlib's `Set`.** Never imported or used. Set Theory builds its own
   `SetTheory.Set α := α → Prop`, and the prose says the course "does not use Mathlib's sets"
   (SetTheory/Definitions.lean:45). The names `Set.Subset`, `Set.union`, `Set.inter`,
   `Set.compl`, `Set.diff`, `Set.ins`, `Set.empty` and `Set.univ`, and the notations `''` and
   `⁻¹'`, are copies written to look like Mathlib's. `setOf`, `{x | p x}`, `Set.ext`,
   `Set.mem_setOf_eq` and the `ext` tactic were never met.
2. **`Equiv`/`≃`, surjective, bijective, inverses.** None appear. Injectivity appears only in
   prose (SetTheory/Functions.lean:414) and once as `Function.Injective succ`
   (Naturals/Peano.lean:117), with Lean's definition quoted and `⦃ ⦄` explained there.
3. **`Setoid`, `Quotient`, `≈`, `⟦a⟧`, `Equivalence`, `Reflexive`/`Symmetric`/`Transitive`.**
   None appear. "Reflexive", "transitive" and "antisymmetric" occur only as words in prose
   ("Divisibility is an order of its own: reflexive, transitive and antisymmetric",
   Naturals/Divisibility.lean:126). Equivalence relations were never defined; "equivalence"
   means `↔` (Logic/Equivalence).
4. **`Fin`, `Finset`, `Fintype`, `Fintype.card`.** Zero occurrences. The only counting is
   `List.length` in GettingStarted.
5. **`ℤ` and `%`.** `ℤ` is only data: `#check (71 : ℤ)`, `List ℤ` (GettingStarted/Types.lean),
   `Gaussian` with `ℤ` fields (Programming/Structures.lean:39). No proof about integers, no
   `omega` on `ℤ`, `Int` never written by name. `%` is used in a proof once, on `ℕ`
   (`is_even_mod_two`, Logic/HigherOrder.lean:137) and never explained; `17 % 5 = 2` by `rfl`
   (GettingStarted/Proofs.lean:74); `divmod (n d : ℕ) := (n / d, n % d)` in Programming.
   `Nat.gcd`, `Nat.Coprime`, primes and `Nat.find` never appear (`Nat.find` in prose only,
   Naturals/StrongInduction.lean:253). `∣` is defined on `MyNat` only, with `dvd_refl`,
   `dvd_trans`, `dvd_antisymm`, `dvd_add`, `dvd_sub`, `mul_dvd_mul`, `le_of_dvd`,
   `eq_one_of_dvd_one` (Naturals/Divisibility.lean).

## 1. Sets (SetTheory; imports `Mathlib.Logic.Basic`, `Mathlib.Order.Notation`, `Mathlib.Data.SProd`)

Everything is in `namespace SetTheory` with `universe u`.

- `def Set (α : Type u) : Type u := α → Prop`, a predicate (Definitions.lean:31, `define_set`).
  Example sets are functions: `def Evens : Set Nat := fun n => ∃ k, n = 2*k`.
- Membership: the student copies the `Membership` class, then
  `instance {α} : Membership α (Set α) := ⟨fun S x => S x⟩` (Definitions.lean:103-111).
- `Set.empty := fun _ => False` with `EmptyCollection`, `Set.univ := fun _ => True`
  (Definitions.lean:157-162); `open Set in` and a bare `univ` occur (Definitions.lean:490).
- Subset: `def Set.Subset A B : Prop := ∀ x, x ∈ A → x ∈ B`, `HasSubset`; `subset_refl`,
  `subset_trans`, `subset_antisym` (Definitions.lean:219-306).
- Extensionality: `theorem setext : (∀ x, x ∈ A ↔ x ∈ B) ↔ A = B`, by `funext x; apply propext`
  (Definitions.lean:286). Set equalities are usually proved with `apply subset_antisym`.
- Operations: `Set.union := fun x => x ∈ A ∨ x ∈ B` (`Union`), `Set.inter` (`Inter`),
  `Set.compl := fun x => x ∉ A` (`Compl`, `Aᶜ`), `Set.diff` (`SDiff`, `\`), `Set.ins`
  (`Insert`), `Set.singleton`, enumerated sets `({1, 2, 3} : Set Nat)`.
- Laws (Properties.lean): `empty_subset`, `subset_univ`, `union_comm`, `union_empty`,
  `union_subset`, `inter_comm`, `inter_univ`, `subset_inter`, `inter_union_distrib`,
  `union_inter_distrib`, `mem_compl`, `union_compl`, `inter_compl`, `compl_subset_compl`,
  `compl_union`, `compl_inter`, `mem_insert`, `insert_comm`, `diff_eq_inter_compl`.
- Families (Families.lean): `bigUnion (J : Set ι) (A : ι → Set α) := fun x => ∃ i, i ∈ J ∧ x ∈ A i`,
  `bigInter`; indexed by a set `J`; no `⋃`/`⋂`, no `Set.iUnion`.
- Products (Products.lean): `cross A B : Set (α × β) := fun p => p.1 ∈ A ∧ p.2 ∈ B`, `A ×ˢ B`;
  `bigCross J A : Set (ι → α)`.
- Image and preimage (Functions.lean): `def image f A := fun y => ∃ x, x ∈ A ∧ f x = y`
  (line 35), `infixl:80 " '' " => image` "as Mathlib writes it" (line 49); the witness order
  `∃ x, x ∈ A ∧ f x = y` differs from Mathlib's `∃ x ∈ A, f x = y` only cosmetically.
  `def preimage f B := fun x => f x ∈ B`, `⁻¹'`. Theorems: `image_subset`, `preimage_subset`,
  `image_empty`, `image_union` (line 207), `image_inter_subset`, `image_insert`,
  `preimage_empty`, `preimage_univ`, `preimage_union`, `preimage_inter`, `preimage_compl`,
  `image_preimage_subset`, `subset_preimage_image`, `image_subset_iff`.

## 2. Functions

- Injective: a prose definition during `preimage_image_double` ("sending distinct elements to
  distinct values, is called *injective*", SetTheory/Functions.lean:414); `half` shown not
  injective (Functions.lean:434).
- `Function.Injective` quoted from Lean with `⦃a₁ a₂⦄` explained (Naturals/Peano.lean:111-114);
  used once: `MyNat.succ_injective : Function.Injective succ` (Peano.lean:117).
- Surjective, bijective: never. "Onto" once in prose (Logic/HigherOrder.lean:154).
- Composition `∘`: `hqr ∘ hpq` (Logic/DeMorgan.lean:222), `invert_real ∘ invert_real = id`,
  `double ∘ half = id` (Programming/Advanced.lean:73,597). No `LeftInverse`, no inverse functions.

## 3. Relations

- "A predicate of two arguments is called a *relation*. On a type `α` it is a function
  `α → α → Prop`" (Logic/Predicates.lean:135, `define_next_to`, `NextTo` on `Person`, shown
  symmetric at line 179); `Between : ℕ → ℕ → ℕ → Prop` (line 201).
- Reflexive, symmetric, transitive: never defined as predicates; named theorems only
  (`iff_symmetric`, `iff_transitive`, `subset_refl`, `le_trans`, `dvd_trans`, `dvd_antisymm`).
- `class LE (α) where le : α → α → Prop` quoted (Programming/Lists.lean:213, Naturals/Order.lean:25);
  `DecidableRel` (Lists.lean:221); `Trans` instances for `calc` on `MyNat`
  (Naturals/Distributivity.lean:344-350).

## 4. Finiteness and counting

- `Fin`, `Finset`, `Fintype`, `Fintype.card`: zero occurrences. `List.length` in GettingStarted.
- `decide` first in Logic/Predicates.lean:194: "A comparison between two numerals is settled by
  computation: the tactic `decide` evaluates it and closes the goal when it is true." Then on
  `ℕ` arithmetic (Logic/Existence.lean:60, SetTheory/Definitions.lean:79,113); re-explained in
  Naturals with `instance : DecidableEq MyNat := MyNat.decEq` (Peano.lean:262-277), where
  `deriving DecidableEq` is prose only. `native_decide` in Programming specs.

## 5. Integers

- Data only (see above). No theorem about `ℤ`. `omega` only on `ℕ` (Logic/Predicates.lean:207,
  SetTheory throughout, Naturals after `toNat`: "A goal about Lean's own `Nat` may be closed by
  `omega`, as in Set Theory", Naturals/Addition.lean:369).

## 6. Nat arithmetic

- `%`: see above. `/`: `half n = n / 2` (SetTheory/Functions.lean:248), `17 / 5 = 3`.
- `∣` on `MyNat`: `def MyNat.dvd (a b) : Prop := ∃ c, b = a * c`, `instance : Dvd MyNat`
  (Naturals/Divisibility.lean:31-33); prose: "Lean's `ℕ` defines `∣` in this same form, and
  there `decide` settles both statements" (line 26).
- Never: `Nat.gcd`, `Nat.Coprime`, primes, `Nat.find` (prose only).

## 7. Classes and instances

- Programming/Structures.lean:194-255 (`instances`): quotes `class Add (α : Type u) where …`,
  "A class is a structure, here with one field"; `instance : Add Vec3 := ⟨fun v w => …⟩`,
  `Add Gaussian`, `Mul Gaussian`, `ToString Vec3`.
- Instances are always anonymous, `:= ⟨…⟩`; never `where`-bodied, never named. The student
  never declares a `class`; `Membership`, `Singleton`, `Add`, `LE` are quoted from Lean.
- Instance binders: `[LE A] [DecidableRel (α := A) (· ≤ ·)]` (Lists.lean:221), `[OfNat α 0] [Add α]`
  (Advanced.lean:503).
- Naturals instances: `Add`/`Mul`/`Sub MyNat`, `OfNat MyNat 0/1/(n+2)`, `Repr MyNat`,
  `LE`/`LT MyNat`, `Dvd MyNat`, `DecidableEq MyNat`, `Std.Associative`/`Std.Commutative`, `Trans`.
- Never: `extends`, `Inv`, `Pow` as a class, `SMul`/`•`, `deriving` in code, `notation`/`infixr`/
  `prefix` (only `infixl:80 " '' "` and `" ⁻¹' "`, SetTheory/Functions.lean:49,131).

## 8. Tactics, by first code use

| tactic | first use |
|---|---|
| `rfl` | term GettingStarted/Proofs.lean:21; tactic GettingStarted/Inductives.lean:164 |
| `simp` | SetTheory/Definitions.lean:72 (prose GettingStarted/Proofs.lean:95) |
| `simp only` | Naturals/Simp.lean:117 (once) |
| `simpa` | Naturals/Simp.lean:44 |
| `induction … with` | SetTheory/Definitions.lean:347; constant in Naturals |
| `cases … with` | GettingStarted/Inductives.lean:100 |
| `left` / `right` | GettingStarted/Structures.lean:58 |
| `intro`, `exact` | Logic/Propositions.lean:127-128 |
| `constructor`, `·` bullets, `trivial` | Logic/Negation.lean:71-73 |
| `exfalso`, `absurd`, `contradiction` | Logic/Negation.lean:90-95 |
| `.mp`/`.mpr` | Logic/Equivalence.lean:53 |
| `apply` | Logic/DeMorgan.lean:143 |
| `obtain ⟨_, _⟩ := …` | Logic/DeMorgan.lean:146 |
| `by_cases`, `Classical.em` | Logic/DeMorgan.lean:153-164 (extra credit) |
| `unfold`, `omega`, `decide` | Logic/Predicates.lean:206-211 |
| `<;>` | Logic/Predicates.lean:163 |
| `rw [h] at hp`, `rw [← h]` | Logic/Predicates.lean:231-236 |
| `Exists.intro` | Logic/Predicates.lean:36 |
| `have`; `congrFun`/`congrArg` as terms | Logic/HigherOrder.lean:159,150 |
| `intro x ⟨k, hk⟩` | SetTheory/Definitions.lean:132 |
| `funext`, `propext`, `rintro` | SetTheory/Definitions.lean:57 (`rintro` once, in a spec) |
| `grind` | SetTheory/Definitions.lean:133 (13 uses) |
| `calc` | SetTheory/Properties.lean (c. 530); heavily in Naturals |
| `subst`, `show` | SetTheory/Families.lean:60-62 |
| `generalize` | SetTheory/Families.lean:243 |
| `native_decide` | Programming/Types.lean:72 |
| `refine ⟨x, y, ?_, ?_⟩` | Programming/Advanced.lean:594-603 (once, extra credit) |
| `ring` | Programming/Advanced.lean:654 (extra credit, on `ℚ`) |

**Never appear:** `ext`, `rcases`, `use`, `exists` (tactic), `by_contra`, `push_neg`,
`contrapose`, `norm_num`, `linarith`, `nlinarith`, `positivity`, `aesop`, `tauto`, `specialize`,
`simp_all`, `congr` (tactic), `change` (tactic), `exact?`/`apply?`, `nomatch`, `symm` (tactic;
`h.symm` is used, Naturals/Simp.lean:162).

## 9. Syntax forms

- Present: `fun x => …`; `⟨_, _⟩` with nested patterns; `match` and equation-style
  definitions `| zero => …`; dot notation `h.mp`, `h.mpr`, `h.symm`, `p.1`/`p.2`, `n.pred`;
  implicit `{α : Type u}`; strict-implicit `⦃ ⦄` explained once (Peano.lean:114); instance
  binders `[…]` (Programming only); Prop-valued structures (`And`, `Iff`, `Conj` quoted);
  structure-instance `{ … }` notation; `namespace`, `open X`, `open X in`, `universe u`;
  `inductive … where`, `structure … where`, `abbrev` (quoted).
- Absent: `@` explicit application; `Subtype`/`{x // p x}`; `↑` coercion arrows (only
  `(3 : ℚ)` ascriptions); `where`-bodied definitions or instances; `variable` (once).

## 10. Visibility and goals

- No `@visibility private` in any current `@subject` block (NATS_PLAN.md:943 said Naturals was
  private; the source no longer says so). about.yaml orders the subjects
  `[gettingstarted, logic, settheory, programming, naturals]`.
- `@goal` markers: GettingStarted/Types.lean:580; Logic/Laws.lean:98; SetTheory/Functions.lean:446
  (`squares_and_parity`); Programming/Trees.lean:221; Naturals/Divisibility.lean:125 (`dvd_laws`).
- Naturals ends at divisibility: the last problem is `dvd_one`, `MyNat.eq_one_of_dvd_one`
  (Divisibility.lean:268-278). No gcd, division algorithm or primes, despite the blurb.

## 11. Voice

- `define_set` (SetTheory/Definitions.lean:22-25): "How does one specify a set? If the set has
  only a few elements one can list them, but the usual way is to take some property that
  elements may or may not possess and to form the set of all elements having that property. …
  In this course we make the property itself the set. A set of elements of a type `α` is a
  function that assigns to each element `x` of `α` a proposition, the proposition that `x`
  belongs to the set."
- `define_odds` (Definitions.lean:38-45): "With sets defined as properties, to write down a
  particular set is to write down a function from elements to propositions. … A number is odd
  when it is one more than an even number, that is, when `2*k+1 = n` for some `k`."
- Naturals, `define_dvd` (Divisibility.lean:22): "`3` divides `12` because `12` is `3 * 4`:
  some number of copies of `3` make `12`. We define divisibility from multiplication as we
  defined the order from addition, `a ∣ b` when `b = a * c` for some `c`, and supply the
  instance `Dvd MyNat` that gives the notation. The symbol is `\mid`, a vertical bar of its
  own, not the `|` on the keyboard."
- Naturals, `define_mynat` (Peano.lean:22-24): "Counting begins at a first number and goes on
  one step at a time. … We define our own copy, `MyNat`, rather than take Lean's, so that each
  law we use is one we have proved. Mathlib … proves thousands of theorems about `ℕ`, and the
  laws we prove here have the names they have there."
- Register: textbook prose, no second person; key terms in *italics*; Mathlib names pointed
  out ("as Mathlib writes it"); `@description` a short imperative.
