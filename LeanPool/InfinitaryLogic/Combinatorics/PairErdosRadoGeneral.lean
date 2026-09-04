/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Order.InitialSeg
import Mathlib.Data.Fin.VecNotation

/-!
# Pair Erdős–Rado, parameterized by the color bound `κ`

The color-parameterized pair Erdős–Rado theorem: for any infinite cardinal `κ` and any
color type `C` with `#C ≤ κ`, every pair coloring `cR : (Fin 2 ↪o Source κ) → C` of the
source order `Source κ = (Order.succ (2 ^ κ)).ord.ToType` (the initial well-order of the
successor of `2 ^ κ`) admits a `(Order.succ κ).ord`-indexed strict-mono suborder on which
`cR` is constant. In partition-calculus notation: `(2 ^ κ)⁺ → (κ⁺)²_κ`.

This is a fresh-namespace (`PairERGen`) port of the proven Bool/ℵ₀ theorem
`FirstOrder.Combinatorics.erdos_rado_pair_omega1` from `Combinatorics/ErdosRado.lean`,
with the renaming table `Bool → C`, `ℶ_1 → 2 ^ κ`, `ℵ_1 → Order.succ κ`,
`ω_1 → (Order.succ κ).ord`. The legacy theorem's shape is recovered as the `κ = ℵ₀`
specialization `erdos_rado_pair_omega1_from_general`. The consumers are the
end-homogenization engine (`EndHomogeneousErdosRado.lean`) and the finite-arity induction
(`FiniteArityErdosRadoInduction.lean`, culminating in the bounded
`finiteArityErdosRadoBounded`), which need the color bound at `κ = ℶ_1` (colors = functions
on continuum-indexed positions); the all-arity `FiniteArityErdosRadoOmega1` is false-shaped
(statement audit 2026-07-07 — see its docstring).

## Structure

- **`CardinalHelpers`**: all cardinal arithmetic isolated — source cardinality,
  the level-count bound `#(β.ToType → C) ≤ 2 ^ κ` for `β < (succ κ).ord`, the
  counting-core product `succ κ * 2 ^ κ = 2 ^ κ`, and the subset order-iso lemma.
- **EHMR canonical partition tree** (sections mirroring the source A–H): nodes are
  recorded-color sequences `β.ToType → C`, reps are chosen minima of successor sets,
  the coverage `y`-path shows every source element is some node's chosen rep, counting
  forces a live node of length `≥ (succ κ).ord`, and the resulting branch assembles
  into a `CoherentMajorityBranch` feeding the chain + pigeonhole endgame.
- **Headline**: `pairErdosRado_general`; regression: `erdos_rado_pair_omega1_from_general`;
  abstract-source wrapper: `pairErdosRado_general_of_large`.
-/

universe u

namespace FirstOrder.Combinatorics.PairERGen

/-! ### Generic toolbox (no `κ`): `pairEmbed`, pigeonhole, embeddings, order isos -/

section Toolbox

/-- Pair embedding: from an ordered pair `a < b` in a linearly-ordered
type, produce the canonical `Fin 2 ↪o α`. -/
noncomputable def pairEmbed {α : Type*} [LinearOrder α]
    {a b : α} (h : a < b) : Fin 2 ↪o α :=
  OrderEmbedding.ofStrictMono ![a, b] (by
    intro p q hpq
    match p, q, hpq with
    | ⟨0, _⟩, ⟨1, _⟩, _ => simpa using h
    | ⟨0, _⟩, ⟨0, _⟩, hp => exact absurd hp (lt_irrefl _)
    | ⟨1, _⟩, ⟨1, _⟩, hp => exact absurd hp (lt_irrefl _)
    | ⟨1, _⟩, ⟨0, _⟩, hp =>
      have hval : (1 : ℕ) < 0 := hp
      exact absurd hval (by omega))

/-- Path-counting pigeonhole. A function out of a set of cardinality `≥ succ μ` into a
codomain of cardinality `≤ μ` (with `μ ≥ ℵ_0`) has some fiber of cardinality `≥ succ μ`.

Routes through `Cardinal.infinite_pigeonhole_card` with parameter `θ := succ μ`. The
regularity of `succ μ` (successor cardinals are regular) supplies the cofinality
hypothesis. -/
theorem exists_large_fiber_of_small_codomain
    {α β : Type u} {μ : Cardinal.{u}}
    (hμ : Cardinal.aleph0 ≤ μ)
    (hα : Cardinal.mk α ≥ Order.succ μ)
    (hβ : Cardinal.mk β ≤ μ)
    (f : α → β) :
    ∃ b : β, Order.succ μ ≤ Cardinal.mk (f ⁻¹' {b}) := by
  have hReg : (Order.succ μ).IsRegular := Cardinal.isRegular_succ hμ
  have hθ_le_α : Order.succ μ ≤ Cardinal.mk α := hα
  have hθ_ge_aleph0 : Cardinal.aleph0 ≤ Order.succ μ :=
    hμ.trans (Order.le_succ μ)
  -- `#β ≤ μ < succ μ = (succ μ).ord.cof`.
  have hcof : Cardinal.mk β < (Order.succ μ).ord.cof := by
    rw [hReg.cof_ord]
    exact hβ.trans_lt (Order.lt_succ_of_le le_rfl)
  exact Cardinal.infinite_pigeonhole_card f (Order.succ μ)
    hθ_le_α hθ_ge_aleph0 hcof

/-- Project-local replacement for the deprecated `Ordinal.initialSegToType` (deprecated in
favor of `Ordinal.type_le_iff`, from which this is extracted): the initial segment
embedding of `α.ToType` into `β.ToType` from `α ≤ β`. -/
noncomputable def initialSegOfLe {α β : Ordinal.{u}} (h : α ≤ β) : α.ToType ≤i β.ToType := by
  apply Classical.choice (Ordinal.type_le_iff.mp _)
  rwa [Ordinal.type_toType, Ordinal.type_toType]

/-- A well-ordered source of cardinality at least `c` admits an order-embedding from the
initial-ordinal well-order of cardinality `c`. Used by the abstract-source wrapper
`pairErdosRado_general_of_large` to pull the coloring back to `Source κ`. -/
theorem exists_ordToType_embedding_of_card_ge
    {I : Type} [LinearOrder I] [WellFoundedLT I]
    {c : Cardinal} (hI : Cardinal.mk I ≥ c) :
    Nonempty (c.ord.ToType ↪o I) := by
  -- `β := type (<_I) : Ordinal`.  `β.card = #I ≥ c`, hence `c.ord ≤ β`.
  set β : Ordinal := Ordinal.type (· < · : I → I → Prop) with hβ
  have hβ_card : β.card = Cardinal.mk I := Ordinal.card_type (· < ·)
  have hord_le : c.ord ≤ β := by
    rw [Cardinal.ord_le, hβ_card]; exact hI
  -- Initial-segment embedding `c.ord.ToType ≤i β.ToType`.
  have seg : c.ord.ToType ≤i β.ToType := initialSegOfLe hord_le
  -- `β.ToType` ≃o `I` via `type_toType β = β = type (<_I)`.
  have htype : @Ordinal.type β.ToType (· < ·) _ =
      @Ordinal.type I (· < ·) _ := by
    rw [Ordinal.type_toType]
  have hiso : Nonempty
      ((· < · : β.ToType → β.ToType → Prop) ≃r (· < · : I → I → Prop)) :=
    Ordinal.type_eq.mp htype
  obtain ⟨r⟩ := hiso
  exact ⟨seg.toOrderEmbedding.trans (OrderIso.ofRelIsoLT r).toOrderEmbedding⟩

/-- Any subset of `c.ord.ToType` of cardinality at least `c` is order-isomorphic to
`c.ord.ToType` (the generalization of the legacy `ℵ_1`-subset-of-`ω_1` lemma).

Proof outline: the subset's order type `β` satisfies `β ≤ c.ord` (suborder) and
`β.card ≥ c`; since `c.ord` is the *least* ordinal of cardinality `c`, any `β < c.ord`
would force `β.card < c` (`Cardinal.lt_ord`), a contradiction. So `β = c.ord`, giving a
`RelIso` transported to an `OrderIso`. -/
theorem ordIso_ordToType_of_card_ge {c : Cardinal.{0}}
    {S : Set c.ord.ToType}
    (hS : Cardinal.mk S ≥ c) :
    Nonempty (S ≃o c.ord.ToType) := by
  have : IsWellOrder S (· < ·) := inferInstance
  set β : Ordinal.{0} := @Ordinal.type S (· < ·) _ with hβ
  -- The inclusion `S ↪o c.ord.ToType`.
  let incl : S ↪o c.ord.ToType := OrderEmbedding.subtype _
  -- `β ≤ c.ord`.
  have hβ_le : β ≤ c.ord := by
    have : @Ordinal.type c.ord.ToType (· < ·) _ = c.ord := Ordinal.type_toType _
    rw [← this]
    exact Ordinal.type_le_iff'.mpr ⟨incl.ltEmbedding⟩
  -- `β.card = #S ≥ c`.
  have hβ_card : β.card = Cardinal.mk S := Ordinal.card_type (· < ·)
  have hβ_card_ge : c ≤ β.card := hβ_card ▸ hS
  -- `β ≥ c.ord`: if `β < c.ord`, then `β.card < c`, contradicting the above.
  have hβ_ge : c.ord ≤ β := by
    by_contra hne
    push Not at hne
    have : β.card < c := Cardinal.lt_ord.mp hne
    exact absurd hβ_card_ge (not_le.mpr this)
  have hβ_eq : β = c.ord := le_antisymm hβ_le hβ_ge
  -- So `type (<_S) = type (<_{c.ord.ToType})`, giving a `RelIso`.
  have htype : @Ordinal.type S (· < ·) _ =
      @Ordinal.type c.ord.ToType (· < ·) _ := by
    show β = _; rw [hβ_eq, Ordinal.type_toType]
  obtain ⟨r⟩ := (Ordinal.type_eq.mp htype :
    Nonempty ((· < · : S → S → Prop) ≃r
      (· < · : c.ord.ToType → c.ord.ToType → Prop)))
  exact ⟨OrderIso.ofRelIsoLT r⟩

/-- Composition of `initialSegOfLe` via `InitialSeg.eq` uniqueness on well-orders.
Two initial segments from `α.ToType` to `γ.ToType` (both well-ordered) agree
pointwise.  (Shared with `EndHomogER`, which previously carried a private copy.) -/
lemma initialSegOfLe_compose
    {α β γ : Ordinal.{0}} (h_αβ : α ≤ β) (h_βγ : β ≤ γ) (x : α.ToType) :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder γ.ToType (· < ·) := isWellOrder_lt
    (initialSegOfLe h_βγ).toOrderEmbedding
        ((initialSegOfLe h_αβ).toOrderEmbedding x) =
      (initialSegOfLe (h_αβ.trans h_βγ)).toOrderEmbedding x := by
  have : IsWellOrder γ.ToType (· < ·) := isWellOrder_lt
  rw [InitialSeg.toOrderEmbedding_apply, InitialSeg.toOrderEmbedding_apply,
      InitialSeg.toOrderEmbedding_apply,
      ← InitialSeg.trans_apply (initialSegOfLe h_αβ)
        (initialSegOfLe h_βγ) x]
  exact ((initialSegOfLe h_αβ).trans
    (initialSegOfLe h_βγ)).eq
    (initialSegOfLe (h_αβ.trans h_βγ)) x

end Toolbox

/-! ### Cardinal helpers: all the `κ`-arithmetic the EHMR port consumes -/

section CardinalHelpers

/-- **Pair-ER source at color bound `κ`.** The initial ordinal of the regular successor
cardinal `succ (2 ^ κ)`, viewed as a linearly-ordered `Type`. All pair-Erdős–Rado
recursion happens inside `Source κ`; the specialization `κ = ℵ₀` recovers the legacy
`PairERSource` (since `2 ^ ℵ₀ = ℶ_1`). -/
abbrev Source (κ : Cardinal.{0}) : Type :=
  (Order.succ ((2 : Cardinal.{0}) ^ κ)).ord.ToType

/-- Cardinality of the source: `#(Source κ) = succ (2 ^ κ)`. -/
lemma mk_source (κ : Cardinal.{0}) :
    Cardinal.mk (Source κ) = Order.succ ((2 : Cardinal.{0}) ^ κ) :=
  Cardinal.mk_ord_toType _

instance (κ : Cardinal.{0}) : Nonempty (Source κ) :=
  Ordinal.nonempty_toType_iff.mpr fun h =>
    Cardinal.succ_ne_zero _ (Cardinal.ord_eq_zero.mp h)

/-- `2 ^ κ ≠ 0` (needed for `power_le_power_left` monotonicity). -/
lemma two_power_ne_zero (κ : Cardinal.{0}) : (2 : Cardinal.{0}) ^ κ ≠ 0 :=
  Cardinal.power_ne_zero κ two_ne_zero

/-- `succ κ ≤ 2 ^ κ` — Cantor plus successor minimality; holds for every `κ`. -/
lemma succ_le_two_power (κ : Cardinal.{0}) :
    Order.succ κ ≤ 2 ^ κ :=
  Order.succ_le_of_lt (Cardinal.cantor κ)

variable {κ : Cardinal.{0}}

/-- `ℵ_0 ≤ 2 ^ κ` for infinite `κ` (via Cantor). -/
lemma aleph0_le_two_power (hκ : Cardinal.aleph0 ≤ κ) :
    Cardinal.aleph0 ≤ (2 : Cardinal.{0}) ^ κ :=
  hκ.trans (Cardinal.cantor κ).le

/-- `ℵ_0 ≤ succ (2 ^ κ)` for infinite `κ`. -/
lemma aleph0_le_succ_two_power (hκ : Cardinal.aleph0 ≤ κ) :
    Cardinal.aleph0 ≤ Order.succ ((2 : Cardinal.{0}) ^ κ) :=
  (aleph0_le_two_power hκ).trans (Order.le_succ _)

/-- `ℵ_0 ≤ succ κ` for infinite `κ`. -/
lemma aleph0_le_succ_self (hκ : Cardinal.aleph0 ≤ κ) :
    Cardinal.aleph0 ≤ Order.succ κ :=
  hκ.trans (Order.le_succ κ)

/-- Ordinals below `(succ κ).ord` have `ToType` of cardinality `≤ κ` (the generalization
of "ordinals below `ω_1` are countable"). -/
theorem toType_card_le_of_lt_succ_ord {α : Ordinal.{0}}
    (hα : α < (Order.succ κ).ord) :
    Cardinal.mk α.ToType ≤ κ := by
  rw [Cardinal.mk_toType]
  exact Order.lt_succ_iff.mp (Cardinal.lt_ord.mp hα)

/-- `(succ κ).ord` is closed under ordinal successor for infinite `κ` (it is a limit
ordinal, being the initial ordinal of an uncountable-cofinality cardinal). -/
theorem succ_lt_ord_of_lt (hκ : Cardinal.aleph0 ≤ κ) {δ : Ordinal.{0}}
    (hδ : δ < (Order.succ κ).ord) :
    Order.succ δ < (Order.succ κ).ord :=
  (Cardinal.isSuccLimit_ord (aleph0_le_succ_self hκ)).succ_lt hδ

/-- **Node-count bound.** For `β < (succ κ).ord` and `#C ≤ κ`, the level of
recorded-color sequences has at most `2 ^ κ` nodes:
`#(β.ToType → C) = #C ^ #β.ToType ≤ (2 ^ κ) ^ κ = 2 ^ (κ * κ) = 2 ^ κ`. -/
theorem mk_node_le {C : Type} (hκ : Cardinal.aleph0 ≤ κ)
    (hC : Cardinal.mk C ≤ κ) {β : Ordinal.{0}}
    (hβ : β < (Order.succ κ).ord) :
    Cardinal.mk (β.ToType → C) ≤ 2 ^ κ :=
  calc Cardinal.mk (β.ToType → C)
      = Cardinal.mk C ^ Cardinal.mk β.ToType := (Cardinal.power_def C β.ToType).symm
    _ ≤ ((2 : Cardinal.{0}) ^ κ) ^ Cardinal.mk β.ToType :=
        Cardinal.power_le_power_right (hC.trans (Cardinal.cantor κ).le)
    _ ≤ ((2 : Cardinal.{0}) ^ κ) ^ κ :=
        Cardinal.power_le_power_left (two_power_ne_zero κ)
          (toType_card_le_of_lt_succ_ord hβ)
    _ = (2 : Cardinal.{0}) ^ (κ * κ) := Cardinal.power_mul.symm
    _ = (2 : Cardinal.{0}) ^ κ := by rw [Cardinal.mul_eq_self hκ]

/-- **Counting-core product.** `succ κ * 2 ^ κ = 2 ^ κ` for infinite `κ`
(the generalization of `ℵ_1 * ℶ_1 = ℶ_1`). -/
theorem succ_mul_two_power (hκ : Cardinal.aleph0 ≤ κ) :
    Order.succ κ * (2 : Cardinal.{0}) ^ κ = 2 ^ κ := by
  rw [Cardinal.mul_eq_max (aleph0_le_succ_self hκ) (aleph0_le_two_power hκ)]
  exact max_eq_right (succ_le_two_power κ)

/-- Any coloring on `Source κ` witnesses `Nonempty C`: the source is nontrivial
(`#(Source κ) = succ (2 ^ κ) ≥ 2`), so it contains a strict pair, whose color inhabits
`C`. Supplies the junk value the coverage `y`-path needs. -/
theorem nonempty_color {C : Type} (cR : (Fin 2 ↪o Source κ) → C) :
    Nonempty C := by
  have hnontriv : Nontrivial (Source κ) := by
    rw [← Cardinal.one_lt_iff_nontrivial, mk_source]
    exact Order.lt_succ_iff.mpr (Cardinal.one_le_iff_ne_zero.mpr (two_power_ne_zero κ))
  obtain ⟨a, b, hab⟩ := hnontriv
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨cR (pairEmbed h)⟩
  · exact ⟨cR (pairEmbed h)⟩

end CardinalHelpers

/-! ### Branch structures: `validFiber`, `CoherentMajorityBranch`, `EHMRBranch` -/

section BranchStructures

variable {κ : Cardinal.{0}} {C : Type}

/-- **Valid fiber (quantifier form).** The set of elements `y ∈ Source κ` strictly above
every `p β`, whose pair color with each `p β` matches `τ β`. Kept in quantifier form so
that successor rewriting and restriction lemmas do not have to commute big intersections
through the recursion. -/
def validFiber (cR : (Fin 2 ↪o Source κ) → C) {α : Ordinal.{0}}
    (p : α.ToType ↪o Source κ) (τ : α.ToType → C) : Set (Source κ) :=
  { y | ∀ β : α.ToType, ∃ h : p β < y, cR (pairEmbed h) = τ β }

/-- **`CoherentMajorityBranch cR`**: globally coherent prefix + branch data of length
`(succ κ).ord` — the object the pair Erdős–Rado endgame consumes. Produced from an
`EHMRBranch` by `exists_coherentMajorityBranch_of_ehmrBranch`. -/
structure CoherentMajorityBranch (cR : (Fin 2 ↪o Source κ) → C) where
  /-- Prefix at each level `α < (succ κ).ord`. -/
  prefixAt : ∀ α : Ordinal.{0},
    α < (Order.succ κ).ord → α.ToType ↪o Source κ
  /-- Type function at each level `α < (succ κ).ord`. -/
  branch : ∀ α : Ordinal.{0},
    α < (Order.succ κ).ord → α.ToType → C
  /-- Prefix coherence: prefix at α restricted to β-level via the
  initial-segment inclusion equals prefix at β. -/
  prefix_restrict : ∀ {β α : Ordinal.{0}} (hβα : β ≤ α)
    (hβ : β < (Order.succ κ).ord) (hα : α < (Order.succ κ).ord)
    (x : β.ToType),
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    prefixAt α hα ((initialSegOfLe hβα).toOrderEmbedding x) =
      prefixAt β hβ x
  /-- Branch coherence: branch at α restricted to β-level equals
  branch at β. -/
  branch_restrict : ∀ {β α : Ordinal.{0}} (hβα : β ≤ α)
    (hβ : β < (Order.succ κ).ord) (hα : α < (Order.succ κ).ord)
    (x : β.ToType),
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    branch α hα ((initialSegOfLe hβα).toOrderEmbedding x) =
      branch β hβ x
  /-- **Chain extension**: the value at the top of `(succ γ).ToType` is in the
  `validFiber` for the lower-level chain at γ. This is the within-chain pair-color
  consistency that pair-homogeneity needs. -/
  top_in_validFiber : ∀ (γ : Ordinal.{0}) (hγ : γ < (Order.succ κ).ord)
      (hsγ : Order.succ γ < (Order.succ κ).ord),
    haveI : IsWellOrder (Order.succ γ).ToType (· < ·) := isWellOrder_lt
    prefixAt (Order.succ γ) hsγ (⊤ : (Order.succ γ).ToType) ∈
      validFiber cR (prefixAt γ hγ) (branch γ hγ)

/-- **`EHMRBranch cR`**: a strictly increasing `(succ κ).ord`-indexed family of reps with
recorded colors — `cR({rep β, rep γ}) = bit β` for `β < γ` (EHMR fact (8) content).
Produced by the tree-counting theorem `ehmr_tree_has_branch`. -/
structure EHMRBranch (cR : (Fin 2 ↪o Source κ) → C) where
  /-- The rep at each position `β < (succ κ).ord`. -/
  rep : ∀ β : Ordinal.{0}, β < (Order.succ κ).ord → Source κ
  /-- The recorded color at each position `β < (succ κ).ord`. -/
  bit : ∀ β : Ordinal.{0}, β < (Order.succ κ).ord → C
  /-- The reps strictly increase. -/
  rep_strictMono : ∀ {β γ : Ordinal.{0}} (hβ : β < (Order.succ κ).ord)
    (hγ : γ < (Order.succ κ).ord), β < γ → rep β hβ < rep γ hγ
  /-- End-homogeneity: the pair color of `{rep β, rep γ}` is `bit β` for `β < γ`. -/
  coloring : ∀ {β γ : Ordinal.{0}} (hβ : β < (Order.succ κ).ord)
    (hγ : γ < (Order.succ κ).ord) (hβγ : β < γ),
    cR (pairEmbed (rep_strictMono hβ hγ hβγ)) = bit β hβ

end BranchStructures

/-! ### EHMR canonical-tree skeleton

Nodes are recorded-color sequences `β.ToType → C` (Type 0, so the counting stays in
`Cardinal.{0}`); reps `s(h↾γ) = min S(h↾γ)` are derived by well-founded recursion on
length; live = nonempty successor set. -/

section TreeSkeleton

/-- A node at level `β`: the recorded colors at the positions `β.ToType`. The eventual
branch is a cofinal chain through these of length `< (succ κ).ord`. -/
abbrev EHMRNodeAt (C : Type) (β : Ordinal.{0}) : Type := β.ToType → C

/-- Restrict a node to a shorter length `δ ≤ β`, via the initial-segment embedding. -/
noncomputable def EHMRNodeAt.restrict {C : Type} {β : Ordinal.{0}} (h : EHMRNodeAt C β)
    {δ : Ordinal.{0}} (hδβ : δ ≤ β) : EHMRNodeAt C δ :=
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder δ.ToType (· < ·) := isWellOrder_lt
  fun x => h ((initialSegOfLe hδβ).toOrderEmbedding x)

variable {κ : Cardinal.{0}} {C : Type}

/-- **[EHMR §14, Lemma 14.2 + |E| counting — coverage/counting engine]** If the
"used-up" sets `R i` cover `Source κ` and each is a subsingleton, then the node index
set has cardinality `≥ succ (2 ^ κ) = #(Source κ)`. This is the counting feeding the
branch-length theorem. -/
theorem ehmr_partitionTree_card_lower
    {ι : Type} (R : ι → Set (Source κ))
    (hcover : ∀ y : Source κ, ∃ i : ι, y ∈ R i)
    (hsub : ∀ i : ι, (R i).Subsingleton) :
    Order.succ ((2 : Cardinal.{0}) ^ κ) ≤ Cardinal.mk ι := by
  classical
  -- The choice function `y ↦ (some i with y ∈ R i)` is injective: subsingleton fibers.
  have hf : ∀ y : Source κ, y ∈ R (hcover y).choose := fun y => (hcover y).choose_spec
  have hinj : Function.Injective (fun y : Source κ => (hcover y).choose) := by
    intro y₁ y₂ h
    change (hcover y₁).choose = (hcover y₂).choose at h
    have h2 : y₂ ∈ R (hcover y₁).choose := by rw [h]; exact hf y₂
    exact hsub _ (hf y₁) h2
  calc Order.succ ((2 : Cardinal.{0}) ^ κ) = Cardinal.mk (Source κ) := (mk_source κ).symm
    _ ≤ Cardinal.mk ι := Cardinal.mk_le_of_injective hinj

/-- The successor set `S(h)`: points above all the reps respecting the recorded
colors. (`β.ToType`-indexed `validFiber` shape, with a plain-function `rep`.) -/
def ehmrFiber (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}}
    (rep : β.ToType → Source κ) (col : EHMRNodeAt C β) : Set (Source κ) :=
  { y | ∀ x : β.ToType, ∃ h : rep x < y, cR (pairEmbed h) = col x }

/-- **Chosen representative** `s(h) = min S(h)` — the `<`-least element of the successor
set (via `Source κ`'s well-order), by well-founded recursion on the node length: the rep
at position `x : β.ToType` is the chosen rep of the restriction to `typein x`. Junk
default on dead (empty-fiber) nodes. -/
noncomputable def ehmrChosen (cR : (Fin 2 ↪o Source κ) → C)
    (β : Ordinal.{0}) (h : EHMRNodeAt C β) : Source κ := by
  classical
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  exact
    if hne : (ehmrFiber cR
        (fun x => ehmrChosen cR (Ordinal.typein (· < ·) x)
          (h.restrict (le_of_lt (by
            have hh := Ordinal.typein_lt_type (· < · : β.ToType → β.ToType → Prop) x
            rwa [Ordinal.type_toType] at hh)))) h).Nonempty then
      (IsWellFounded.wf : WellFounded (· < · : Source κ → Source κ → Prop)).min _ hne
    else
      Classical.arbitrary (Source κ)
termination_by β
decreasing_by
  all_goals
    have : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    have hh := Ordinal.typein_lt_type (· < · : β.ToType → β.ToType → Prop) x
    rwa [Ordinal.type_toType] at hh

/-- The reps along a node: the chosen rep of the restriction to each position. -/
noncomputable def ehmrRep (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}}
    (h : EHMRNodeAt C β) : β.ToType → Source κ := by
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  exact fun x => ehmrChosen cR (Ordinal.typein (· < ·) x)
    (h.restrict (le_of_lt (by
      have hh := Ordinal.typein_lt_type (· < · : β.ToType → β.ToType → Prop) x
      rwa [Ordinal.type_toType] at hh)))

/-- `S(h)` as a set, via `ehmrRep`. -/
def ehmrS (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}} (h : EHMRNodeAt C β) :
    Set (Source κ) := ehmrFiber cR (ehmrRep cR h) h

/-- A node is **live** iff its successor set is nonempty. -/
def ehmrLive (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}}
    (h : EHMRNodeAt C β) : Prop := (ehmrS cR h).Nonempty

/-- The used/remainder set `R(h)`: `{s(h)}` on live nodes, else `∅`. -/
noncomputable def ehmrR (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}}
    (h : EHMRNodeAt C β) : Set (Source κ) := by
  classical
  exact if ehmrLive cR h then {ehmrChosen cR β h} else ∅

/-- `R(h)` is a subsingleton (it is `{s(h)}` or `∅`). -/
theorem ehmrR_subsingleton (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}}
    (h : EHMRNodeAt C β) : (ehmrR cR h).Subsingleton := by
  classical
  rw [ehmrR]
  split_ifs with hlive
  · exact Set.subsingleton_singleton
  · exact Set.subsingleton_empty

/-- On a live node, the chosen rep lies in the successor set. -/
theorem ehmrChosen_mem (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}}
    (h : EHMRNodeAt C β) (hlive : ehmrLive cR h) :
    ehmrChosen cR β h ∈ ehmrS cR h := by
  classical
  have hcond : (ehmrFiber cR
      (fun x => ehmrChosen cR (Ordinal.typein (· < ·) x)
        (h.restrict (le_of_lt (by
          have hh := Ordinal.typein_lt_type (· < · : β.ToType → β.ToType → Prop) x
          rwa [Ordinal.type_toType] at hh)))) h).Nonempty := hlive
  rw [ehmrChosen, dite_eq_left hcond]
  exact WellFounded.min_mem _ _ hcond

/-- On a live node, `ehmrChosen` is exactly the well-order minimum of the successor set
(the defining unfold). -/
theorem ehmrChosen_eq_min (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}}
    (h : EHMRNodeAt C β) (hlive : ehmrLive cR h) :
    ehmrChosen cR β h =
      (IsWellFounded.wf : WellFounded (· < · : Source κ → Source κ → Prop)).min
        (ehmrS cR h) hlive := by
  classical
  have hcond : (ehmrFiber cR
      (fun x => ehmrChosen cR (Ordinal.typein (· < ·) x)
        (h.restrict (le_of_lt (by
          have hh := Ordinal.typein_lt_type (· < · : β.ToType → β.ToType → Prop) x
          rwa [Ordinal.type_toType] at hh)))) h).Nonempty := hlive
  rw [ehmrChosen, dite_eq_left hcond]
  -- `rw`'s closing `rfl` is reducible-only; `ehmrS`/`ehmrRep` are regular defs, so the
  -- raw fiber and `ehmrS cR h` are defeq only at default transparency. Close it manually.
  rfl

/-- The chosen min is `≤` every successor (the `<`-least element of `S(h)` in the
linear well-order). -/
theorem ehmrChosen_le_of_mem (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}}
    (h : EHMRNodeAt C β) {y : Source κ} (hy : y ∈ ehmrS cR h) :
    ehmrChosen cR β h ≤ y := by
  have hlive : ehmrLive cR h := ⟨y, hy⟩
  rw [ehmrChosen_eq_min cR h hlive]
  exact not_lt.mp (WellFounded.not_lt_min _ _ hy)

/-- Level cardinality: for `β < (succ κ).ord` the level (all length-`β` nodes) has
cardinality `≤ 2 ^ κ` — `β.ToType` of size `≤ κ`, `C`-valued with `#C ≤ κ`. -/
theorem ehmr_level_card_le (hκ : Cardinal.aleph0 ≤ κ) (hC : Cardinal.mk C ≤ κ)
    {β : Ordinal.{0}} (hβ : β < (Order.succ κ).ord) :
    Cardinal.mk (EHMRNodeAt C β) ≤ (2 : Cardinal.{0}) ^ κ :=
  mk_node_le hκ hC hβ

/-- `ehmrChosen` transported along a level equality: equal levels plus
heterogeneously-equal nodes give equal chosen reps. -/
theorem ehmrChosen_congr (cR : (Fin 2 ↪o Source κ) → C) {δ₁ δ₂ : Ordinal.{0}}
    (hδ : δ₁ = δ₂) {n₁ : EHMRNodeAt C δ₁} {n₂ : EHMRNodeAt C δ₂} (hn : HEq n₁ n₂) :
    ehmrChosen cR δ₁ n₁ = ehmrChosen cR δ₂ n₂ := by
  subst hδ
  rw [eq_of_heq hn]

/-- Level smallness: for `β < (succ κ).ord` there are `≤ 2 ^ κ` live length-`β` nodes
(a fortiori `≤ 2 ^ κ` nodes, by `ehmr_level_card_le`). -/
theorem ehmr_live_level_small (hκ : Cardinal.aleph0 ≤ κ) (hC : Cardinal.mk C ≤ κ)
    (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}}
    (hβ : β < (Order.succ κ).ord) :
    Cardinal.mk {h : EHMRNodeAt C β // ehmrLive cR h} ≤ (2 : Cardinal.{0}) ^ κ :=
  (Cardinal.mk_subtype_le _).trans (ehmr_level_card_le hκ hC hβ)

end TreeSkeleton

/-! ### Coverage (EHMR Lemma 14.2) — the canonical `y`-path

Rather than build the `y`-path by transfinite recursion with an explicit limit step, we
define the whole path at once: `yNode cR y β` is the length-`β` node recording, at each
position `x`, the pair-color of `y` against the chosen rep of the path so far — or junk
(an arbitrary color) once that rep is no longer `< y`. Restriction-coherence then
becomes a lemma, and the stopping argument is pure well-foundedness. -/

section YPath

variable {κ : Cardinal.{0}} {C : Type} [Nonempty C]

/-- The chosen rep of the canonical `y`-path at level `γ`, defined by well-founded
recursion: it is the chosen min of the node whose recorded color at each position `x` is
`cR({yRep(typein x), y})` (or junk once that rep is `≥ y`). Because the recursion lands
in `Source κ` (non-dependent), restriction-coherence later needs only `congrArg`, not a
heterogeneous transport. -/
noncomputable def yRep (cR : (Fin 2 ↪o Source κ) → C) (y : Source κ)
    (γ : Ordinal.{0}) : Source κ := by
  classical
  haveI : IsWellOrder γ.ToType (· < ·) := isWellOrder_lt
  exact ehmrChosen cR γ (fun x =>
    if hlt : yRep cR y (Ordinal.typein (· < ·) x) < y then cR (pairEmbed hlt)
    else Classical.arbitrary C)
termination_by γ
decreasing_by
  all_goals
    have : IsWellOrder γ.ToType (· < ·) := isWellOrder_lt
    exact lt_of_lt_of_eq (Ordinal.typein_lt_type _ _) (Ordinal.type_toType γ)

/-- The canonical `y`-path node of length `β` (a *plain* def over `yRep`): at position
`x` it records the pair-color of `y` against `yRep (typein x)` (junk once that rep is
`≥ y`). -/
noncomputable def yNode (cR : (Fin 2 ↪o Source κ) → C) (y : Source κ)
    (β : Ordinal.{0}) : EHMRNodeAt C β := by
  classical
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  exact fun x =>
    if hlt : yRep cR y (Ordinal.typein (· < ·) x) < y then cR (pairEmbed hlt)
    else Classical.arbitrary C

/-- The defining fixpoint equation: `yRep` is the chosen min of `yNode`. -/
theorem yRep_eq (cR : (Fin 2 ↪o Source κ) → C) (y : Source κ) (γ : Ordinal.{0}) :
    yRep cR y γ = ehmrChosen cR γ (yNode cR y γ) := by
  classical
  conv_lhs => rw [yRep]
  rfl

/-- Restriction-coherence: every restriction of a `yNode` is again the `yNode` of that
length. (Each color depends only on `yRep (typein x)`, and `typein` is preserved by the
initial-segment embedding.) -/
theorem yNode_restrict (cR : (Fin 2 ↪o Source κ) → C) (y : Source κ)
    {β δ : Ordinal.{0}} (hδ : δ ≤ β) :
    (yNode cR y β).restrict hδ = yNode cR y δ := by
  classical
  have : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  have : IsWellOrder δ.ToType (· < ·) := isWellOrder_lt
  funext x'
  have htx : Ordinal.typein (· < ·) ((initialSegOfLe hδ).toOrderEmbedding x')
      = Ordinal.typein (· < ·) x' := Ordinal.typein_apply (initialSegOfLe hδ) x'
  show yNode cR y β ((initialSegOfLe hδ).toOrderEmbedding x') = yNode cR y δ x'
  simp only [yNode, htx]

/-- The reps of `yNode cR y β` are exactly `yRep cR y (typein x)`. (The `IsWellOrder`
binder lets `typein` appear in the signature; call sites discharge it with
`isWellOrder_lt`.) -/
theorem ehmrRep_yNode (cR : (Fin 2 ↪o Source κ) → C) (y : Source κ)
    {β : Ordinal.{0}} [IsWellOrder β.ToType (· < ·)] (x : β.ToType) :
    ehmrRep cR (yNode cR y β) x = yRep cR y (Ordinal.typein (· < ·) x) := by
  classical
  have hlt : Ordinal.typein (· < ·) x < β :=
    lt_of_lt_of_eq (Ordinal.typein_lt_type (· < ·) x) (Ordinal.type_toType β)
  show ehmrChosen cR (Ordinal.typein (· < ·) x) ((yNode cR y β).restrict (le_of_lt hlt))
     = yRep cR y (Ordinal.typein (· < ·) x)
  rw [yRep_eq, yNode_restrict]

/-- Liveness criterion: if every earlier rep stays `< y`, then `y` is a successor of
`yNode cR y β` (so the node is live and `y ∈ S`). -/
theorem yNode_mem_of (cR : (Fin 2 ↪o Source κ) → C) (y : Source κ)
    {β : Ordinal.{0}} (hbelow : ∀ δ : Ordinal.{0}, δ < β → yRep cR y δ < y) :
    y ∈ ehmrS cR (yNode cR y β) := by
  classical
  have : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  intro x
  have hrep : ehmrRep cR (yNode cR y β) x = yRep cR y (Ordinal.typein (· < ·) x) :=
    ehmrRep_yNode cR y x
  have htx_lt : Ordinal.typein (· < ·) x < β :=
    lt_of_lt_of_eq (Ordinal.typein_lt_type (· < ·) x) (Ordinal.type_toType β)
  have hlt : yRep cR y (Ordinal.typein (· < ·) x) < y := hbelow _ htx_lt
  rw [hrep]
  refine ⟨hlt, ?_⟩
  show cR (pairEmbed hlt) = yNode cR y β x
  simp only [yNode]
  rw [dite_eq_left hlt]

/-- As long as `yNode cR y γ₂` is live (every earlier rep stays `< y`), the canonical
reps strictly increase: `yRep γ₁ < yRep γ₂` for `γ₁ < γ₂`. (The rep at the position `γ₁`
of `yNode γ₂` is `yRep γ₁`, and it lies strictly below the chosen min `yRep γ₂`.) -/
theorem yRep_strictMono (cR : (Fin 2 ↪o Source κ) → C) (y : Source κ)
    {γ₁ γ₂ : Ordinal.{0}} (h12 : γ₁ < γ₂)
    (hlive : ∀ δ : Ordinal.{0}, δ < γ₂ → yRep cR y δ < y) :
    yRep cR y γ₁ < yRep cR y γ₂ := by
  classical
  have : IsWellOrder γ₂.ToType (· < ·) := isWellOrder_lt
  have hlive2 : ehmrLive cR (yNode cR y γ₂) := ⟨y, yNode_mem_of cR y hlive⟩
  have hγ₁ : γ₁ < Ordinal.type (· < · : γ₂.ToType → γ₂.ToType → Prop) := by
    rw [Ordinal.type_toType]; exact h12
  obtain ⟨hlt, _⟩ :=
    ehmrChosen_mem cR (yNode cR y γ₂) hlive2 (Ordinal.enum (· < ·) ⟨γ₁, hγ₁⟩)
  rw [ehmrRep_yNode cR y, Ordinal.typein_enum] at hlt
  rwa [← yRep_eq] at hlt

/-- **Stopping.** The canonical `y`-path stops: there is a *least* level `γ` where the
chosen rep reaches `y` (`y ≤ yRep γ`), with all earlier reps strictly below `y`.
Existence is pure well-foundedness — if every `yRep γ` stayed `< y` then `yRep` would be
a strictly increasing `Ordinal → Source κ`, and composing with `typein` gives a strictly
increasing `Ordinal → Ordinal` exceeding the order type of `Source κ`, impossible. -/
theorem exists_yRep_ge (cR : (Fin 2 ↪o Source κ) → C) (y : Source κ) :
    ∃ γ : Ordinal.{0}, y ≤ yRep cR y γ ∧ ∀ δ : Ordinal.{0}, δ < γ → yRep cR y δ < y := by
  classical
  have hexists : ∃ γ : Ordinal.{0}, y ≤ yRep cR y γ := by
    by_contra hcon
    push Not at hcon
    have : IsWellOrder (Source κ) (· < ·) := isWellOrder_lt
    have hmono : StrictMono (yRep cR y) := fun a b hab =>
      yRep_strictMono cR y hab (fun δ _ => hcon δ)
    have hmono_g : StrictMono (fun γ => Ordinal.typein (· < ·) (yRep cR y γ)) :=
      fun a b hab => (Ordinal.typein_lt_typein (· < ·)).mpr (hmono hab)
    have hself : ∀ a : Ordinal.{0}, a ≤ Ordinal.typein (· < ·) (yRep cR y a) := by
      intro a
      induction a using WellFoundedLT.induction with
      | _ a ih =>
        by_contra hlt
        push Not at hlt
        exact absurd ((ih _ hlt).trans_lt (hmono_g hlt)) (lt_irrefl _)
    have hΩ := hself (Ordinal.type (· < · : Source κ → Source κ → Prop))
    exact absurd (hΩ.trans_lt (Ordinal.typein_lt_type (· < ·) _)) (lt_irrefl _)
  obtain ⟨γ₀, hγ₀⟩ := hexists
  refine ⟨Ordinal.lt_wf.min {γ | y ≤ yRep cR y γ} ⟨γ₀, hγ₀⟩, ?_, ?_⟩
  · exact Ordinal.lt_wf.min_mem {γ | y ≤ yRep cR y γ} ⟨γ₀, hγ₀⟩
  · intro δ hδ
    exact not_le.mp (fun ha => Ordinal.lt_wf.not_lt_min {γ | y ≤ yRep cR y γ} ha hδ)

/-- **Coverage (EHMR Lemma 14.2).** Every source element is the chosen representative of
some node (`y ∈ R(h)`): take the least level `γ` where the canonical `y`-path reaches
`y` (`exists_yRep_ge`). There every earlier rep is `< y`, so the node is live
(`yNode_mem_of`) and its chosen min is `≤ y` (`ehmrChosen_le_of_mem`); combined with
`y ≤ yRep γ` this forces `y = s(yNode γ)`, i.e. `y ∈ R(yNode γ)`. -/
theorem exists_node_choosing_source (cR : (Fin 2 ↪o Source κ) → C)
    (y : Source κ) :
    ∃ (β : Ordinal.{0}) (h : EHMRNodeAt C β), y ∈ ehmrR cR h := by
  classical
  obtain ⟨γ, hge, hbelow⟩ := exists_yRep_ge cR y
  have hmem : y ∈ ehmrS cR (yNode cR y γ) := yNode_mem_of cR y hbelow
  have hle : yRep cR y γ ≤ y := by
    rw [yRep_eq]; exact ehmrChosen_le_of_mem cR (yNode cR y γ) hmem
  have heq : y = ehmrChosen cR γ (yNode cR y γ) := by
    rw [← yRep_eq]; exact le_antisymm hge hle
  have hlive : ehmrLive cR (yNode cR y γ) := ⟨y, hmem⟩
  refine ⟨γ, yNode cR y γ, ?_⟩
  rw [ehmrR, ite_eq_left hlive, Set.mem_singleton_iff]
  exact heq

end YPath

/-! ### End-homogeneity of live nodes (EHMR fact (8)) -/

section EndHomogeneity

variable {κ : Cardinal.{0}} {C : Type}

/-- Restriction is transitive (initial segments compose). -/
theorem EHMRNodeAt.restrict_trans {β : Ordinal.{0}} (h : EHMRNodeAt C β)
    {δ ε : Ordinal.{0}} (hδ : δ ≤ β) (hε : ε ≤ δ) :
    (h.restrict hδ).restrict hε = h.restrict (hε.trans hδ) := by
  classical
  have : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  have : IsWellOrder δ.ToType (· < ·) := isWellOrder_lt
  have : IsWellOrder ε.ToType (· < ·) := isWellOrder_lt
  funext z
  show h ((initialSegOfLe hδ).toOrderEmbedding
        ((initialSegOfLe hε).toOrderEmbedding z))
     = h ((initialSegOfLe (hε.trans hδ)).toOrderEmbedding z)
  rw [initialSegOfLe_compose]

/-- `EHMRNodeAt.restrict` at heterogeneously-equal lengths. -/
theorem EHMRNodeAt.restrict_heq {β : Ordinal.{0}} (h : EHMRNodeAt C β)
    {δ₁ δ₂ : Ordinal.{0}} (hδ : δ₁ = δ₂) (h1 : δ₁ ≤ β) (h2 : δ₂ ≤ β) :
    HEq (h.restrict h1) (h.restrict h2) := by
  subst hδ; exact heq_of_eq rfl

/-- The reps of a restriction agree with the parent's reps at the lifted positions. -/
theorem ehmrRep_restrict (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}}
    (h : EHMRNodeAt C β) {δ : Ordinal.{0}} (hδ : δ ≤ β) (x : δ.ToType) :
    ehmrRep cR (h.restrict hδ) x =
      ehmrRep cR h ((initialSegOfLe hδ).toOrderEmbedding x) := by
  classical
  have : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  have : IsWellOrder δ.ToType (· < ·) := isWellOrder_lt
  set lx := (initialSegOfLe hδ).toOrderEmbedding x with hlx_def
  have htx : Ordinal.typein (· < ·) lx = Ordinal.typein (· < ·) x := by
    rw [hlx_def]; exact Ordinal.typein_apply (initialSegOfLe hδ) x
  have hx_lt : Ordinal.typein (· < ·) x < δ :=
    lt_of_lt_of_eq (Ordinal.typein_lt_type (· < ·) x) (Ordinal.type_toType δ)
  have hlx_lt : Ordinal.typein (· < ·) lx < β :=
    lt_of_lt_of_eq (Ordinal.typein_lt_type (· < ·) lx) (Ordinal.type_toType β)
  show ehmrChosen cR (Ordinal.typein (· < ·) x) ((h.restrict hδ).restrict (le_of_lt hx_lt))
     = ehmrChosen cR (Ordinal.typein (· < ·) lx) (h.restrict (le_of_lt hlx_lt))
  refine ehmrChosen_congr cR htx.symm ?_
  rw [EHMRNodeAt.restrict_trans h hδ (le_of_lt hx_lt)]
  exact EHMRNodeAt.restrict_heq h htx.symm ((le_of_lt hx_lt).trans hδ) (le_of_lt hlx_lt)

/-- A restriction of a live node is live (the same witness `y` serves, since the reps
and recorded colors only shrink). -/
theorem ehmrLive_restrict (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}}
    {h : EHMRNodeAt C β} (hlive : ehmrLive cR h) {δ : Ordinal.{0}} (hδ : δ ≤ β) :
    ehmrLive cR (h.restrict hδ) := by
  classical
  have : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  have : IsWellOrder δ.ToType (· < ·) := isWellOrder_lt
  obtain ⟨y, hy⟩ := hlive
  refine ⟨y, ?_⟩
  intro x
  obtain ⟨hlt, hcol⟩ := hy ((initialSegOfLe hδ).toOrderEmbedding x)
  rw [ehmrRep_restrict cR h hδ x]
  exact ⟨hlt, hcol⟩

/-- `cR ∘ pairEmbed` depends only on the two endpoints, not on the `<`-proof: equal
endpoints give equal colors. -/
theorem cR_pairEmbed_congr (cR : (Fin 2 ↪o Source κ) → C)
    {a a' b b' : Source κ} (ha : a = a') (hb : b = b') (p : a < b) (q : a' < b') :
    cR (pairEmbed p) = cR (pairEmbed q) := by
  subst ha; subst hb; rfl

/-- **End-homogeneity, strict monotonicity.** On a live node the chosen reps strictly
increase: the rep at `x₁` is the rep of the restriction-to-`x₂` at the position of `x₁`,
hence strictly below that restriction's chosen min `= rep x₂`. -/
theorem ehmrRep_strictMono (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}}
    {h : EHMRNodeAt C β} (hlive : ehmrLive cR h) {x₁ x₂ : β.ToType} (hx : x₁ < x₂) :
    ehmrRep cR h x₁ < ehmrRep cR h x₂ := by
  classical
  have : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  have : IsWellOrder (Ordinal.typein (· < · : β.ToType → β.ToType → Prop) x₂).ToType (· < ·) :=
    isWellOrder_lt
  have hx₂lt : Ordinal.typein (· < ·) x₂ < β :=
    lt_of_lt_of_eq (Ordinal.typein_lt_type (· < ·) x₂) (Ordinal.type_toType β)
  have h₂live : ehmrLive cR (h.restrict (le_of_lt hx₂lt)) :=
    ehmrLive_restrict cR hlive (le_of_lt hx₂lt)
  have hx₁ty : Ordinal.typein (· < ·) x₁ <
      Ordinal.type (· < · : (Ordinal.typein (· < ·) x₂).ToType →
        (Ordinal.typein (· < ·) x₂).ToType → Prop) := by
    rw [Ordinal.type_toType]; exact (Ordinal.typein_lt_typein (· < ·)).mpr hx
  set z₁ := Ordinal.enum (· < ·) ⟨Ordinal.typein (· < ·) x₁, hx₁ty⟩ with hz₁_def
  have hlift : (initialSegOfLe (le_of_lt hx₂lt)).toOrderEmbedding z₁ = x₁ := by
    refine (Ordinal.typein_inj (· < ·)).mp ?_
    have e1 : Ordinal.typein (· < ·)
          ((initialSegOfLe (le_of_lt hx₂lt)).toOrderEmbedding z₁) =
        Ordinal.typein (· < ·) z₁ :=
      Ordinal.typein_apply (initialSegOfLe (le_of_lt hx₂lt)) z₁
    have e2 : Ordinal.typein (· < ·) z₁ = Ordinal.typein (· < ·) x₁ := by
      rw [hz₁_def]; exact Ordinal.typein_enum (· < ·) _
    rw [e1, e2]
  obtain ⟨hlt, _⟩ := ehmrChosen_mem cR (h.restrict (le_of_lt hx₂lt)) h₂live z₁
  rw [ehmrRep_restrict cR h (le_of_lt hx₂lt) z₁, hlift] at hlt
  exact hlt

/-- **End-homogeneity, EHMR fact (8).** On a live node, the recorded color at `x₁` is
the pair-color of the reps `{rep x₁, rep x₂}` for any `x₁ < x₂`. -/
theorem ehmr_fact8 (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}}
    {h : EHMRNodeAt C β} (hlive : ehmrLive cR h) {x₁ x₂ : β.ToType} (hx : x₁ < x₂) :
    cR (pairEmbed (ehmrRep_strictMono cR hlive hx)) = h x₁ := by
  classical
  have : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  have : IsWellOrder (Ordinal.typein (· < · : β.ToType → β.ToType → Prop) x₂).ToType (· < ·) :=
    isWellOrder_lt
  have hx₂lt : Ordinal.typein (· < ·) x₂ < β :=
    lt_of_lt_of_eq (Ordinal.typein_lt_type (· < ·) x₂) (Ordinal.type_toType β)
  have h₂live : ehmrLive cR (h.restrict (le_of_lt hx₂lt)) :=
    ehmrLive_restrict cR hlive (le_of_lt hx₂lt)
  have hx₁ty : Ordinal.typein (· < ·) x₁ <
      Ordinal.type (· < · : (Ordinal.typein (· < ·) x₂).ToType →
        (Ordinal.typein (· < ·) x₂).ToType → Prop) := by
    rw [Ordinal.type_toType]; exact (Ordinal.typein_lt_typein (· < ·)).mpr hx
  set z₁ := Ordinal.enum (· < ·) ⟨Ordinal.typein (· < ·) x₁, hx₁ty⟩ with hz₁_def
  have hlift : (initialSegOfLe (le_of_lt hx₂lt)).toOrderEmbedding z₁ = x₁ := by
    refine (Ordinal.typein_inj (· < ·)).mp ?_
    have e1 : Ordinal.typein (· < ·)
          ((initialSegOfLe (le_of_lt hx₂lt)).toOrderEmbedding z₁) =
        Ordinal.typein (· < ·) z₁ :=
      Ordinal.typein_apply (initialSegOfLe (le_of_lt hx₂lt)) z₁
    have e2 : Ordinal.typein (· < ·) z₁ = Ordinal.typein (· < ·) x₁ := by
      rw [hz₁_def]; exact Ordinal.typein_enum (· < ·) _
    rw [e1, e2]
  obtain ⟨hlt, hcol⟩ := ehmrChosen_mem cR (h.restrict (le_of_lt hx₂lt)) h₂live z₁
  have hrep_z : ehmrRep cR (h.restrict (le_of_lt hx₂lt)) z₁ = ehmrRep cR h x₁ := by
    rw [ehmrRep_restrict cR h (le_of_lt hx₂lt) z₁, hlift]
  have hcol_z : (h.restrict (le_of_lt hx₂lt)) z₁ = h x₁ := by
    show h ((initialSegOfLe (le_of_lt hx₂lt)).toOrderEmbedding z₁) = h x₁
    rw [hlift]
  rw [← hcol_z, ← hcol]
  exact cR_pairEmbed_congr cR hrep_z.symm rfl (ehmrRep_strictMono cR hlive hx) hlt

end EndHomogeneity

/-! ### Branch extraction from a high live node

EHMR Theorem 13.1 realized concretely: the `succ (2 ^ κ)`-many live nodes (coverage)
cannot all sit at levels `< (succ κ).ord` (each such level has `≤ 2 ^ κ` nodes, and
there are only `succ κ` of them), so some live node has length `≥ (succ κ).ord`;
reading it off at the first `(succ κ).ord` positions yields an `EHMRBranch`. -/

section BranchExtraction

variable {κ : Cardinal.{0}} {C : Type}

/-- The position `enum β'` of a length-`β` node, for `β' < (succ κ).ord ≤ β`. -/
noncomputable def ehmrBranchPos {β : Ordinal.{0}} (hβ : (Order.succ κ).ord ≤ β)
    (β' : Ordinal.{0}) (hβ' : β' < (Order.succ κ).ord) : β.ToType := by
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  exact Ordinal.enum (· < ·) ⟨β', by rw [Ordinal.type_toType]; exact hβ'.trans_le hβ⟩

/-- Positions are strictly monotone in the level. -/
theorem ehmrBranchPos_strictMono {β : Ordinal.{0}} (hβ : (Order.succ κ).ord ≤ β)
    {β' γ' : Ordinal.{0}} (hβ' : β' < (Order.succ κ).ord)
    (hγ' : γ' < (Order.succ κ).ord) (h' : β' < γ') :
    ehmrBranchPos hβ β' hβ' < ehmrBranchPos hβ γ' hγ' := by
  have : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  show Ordinal.enum (· < ·) ⟨β', _⟩ < Ordinal.enum (· < ·) ⟨γ', _⟩
  exact Ordinal.enum_lt_enum.mpr h'

/-- A live node of length `≥ (succ κ).ord` *is* an `EHMRBranch`: its reps (read off at
the positions `enum β'`) strictly increase (`ehmrRep_strictMono`) and satisfy fact (8)
(`ehmr_fact8`). -/
noncomputable def ehmrBranch_of_live {β : Ordinal.{0}}
    (cR : (Fin 2 ↪o Source κ) → C) (h : EHMRNodeAt C β)
    (hβ : (Order.succ κ).ord ≤ β) (hlive : ehmrLive cR h) : EHMRBranch cR where
  rep β' hβ' := ehmrRep cR h (ehmrBranchPos hβ β' hβ')
  bit β' hβ' := h (ehmrBranchPos hβ β' hβ')
  rep_strictMono hβ' hγ' h' :=
    ehmrRep_strictMono cR hlive (ehmrBranchPos_strictMono hβ hβ' hγ' h')
  coloring hβ' hγ' h' :=
    ehmr_fact8 cR hlive (ehmrBranchPos_strictMono hβ hβ' hγ' h')

/-- **[THE COUNTING CORE — EHMR Theorem 13.1]** Some live node has length
`≥ (succ κ).ord`.

Suppose not: every live node has length `< (succ κ).ord`. Then the coverage map
(`exists_node_choosing_source`) injects `Source κ` into the Type-0 index
`Σ b : (succ κ).ord.ToType, EHMRNodeAt C (typein b)` via
`ehmr_partitionTree_card_lower`. But that index has size at most
`succ κ * 2 ^ κ = 2 ^ κ` (`mk_node_le` per fibre, `succ_mul_two_power`), so
`succ (2 ^ κ) ≤ 2 ^ κ`, contradiction. -/
theorem exists_live_node_ge [Nonempty C] (hκ : Cardinal.aleph0 ≤ κ)
    (hC : Cardinal.mk C ≤ κ) (cR : (Fin 2 ↪o Source κ) → C) :
    ∃ (β : Ordinal.{0}) (h : EHMRNodeAt C β),
      (Order.succ κ).ord ≤ β ∧ ehmrLive cR h := by
  classical
  by_contra hcon
  push Not at hcon
  have : IsWellOrder (Order.succ κ).ord.ToType (· < ·) := isWellOrder_lt
  -- The Type-0 index of live nodes of length `< (succ κ).ord`.
  have hlower : Order.succ ((2 : Cardinal.{0}) ^ κ) ≤
      Cardinal.mk (Σ b : (Order.succ κ).ord.ToType,
        { h : EHMRNodeAt C (Ordinal.typein (· < ·) b) // ehmrLive cR h }) := by
    apply ehmr_partitionTree_card_lower (R := fun n => ehmrR cR n.2.1)
    · -- Coverage: every `y` is the chosen rep of a live node, which (by `hcon`) has
      -- length `< (succ κ).ord`.
      intro y
      obtain ⟨β_y, h_y, hy⟩ := exists_node_choosing_source cR y
      have hlive_y : ehmrLive cR h_y := by
        by_contra hnl
        rw [ehmrR, ite_eq_right hnl] at hy
        exact (Set.mem_empty_iff_false y).mp hy
      have hβ_lt : β_y < (Order.succ κ).ord := by
        by_contra hge
        exact hcon β_y h_y (not_lt.mp hge) hlive_y
      have hβ_ty : β_y < Ordinal.type (· < · : (Order.succ κ).ord.ToType →
          (Order.succ κ).ord.ToType → Prop) := by
        rw [Ordinal.type_toType]; exact hβ_lt
      set b_y := Ordinal.enum (· < ·) ⟨β_y, hβ_ty⟩ with hb_def
      have htb : Ordinal.typein (· < ·) b_y = β_y := by rw [hb_def, Ordinal.typein_enum]
      -- Move the node to length `typein b_y` by substituting the length equality.
      have key : ∃ (h' : EHMRNodeAt C (Ordinal.typein (· < ·) b_y))
          (_ : ehmrLive cR h'), y ∈ ehmrR cR h' := by
        rw [htb]; exact ⟨h_y, hlive_y, hy⟩
      obtain ⟨h', hl', hy'⟩ := key
      exact ⟨⟨b_y, h', hl'⟩, hy'⟩
    · -- Each used-up set is a subsingleton.
      intro n
      exact ehmrR_subsingleton cR n.2.1
  -- The index has size `≤ succ κ * 2 ^ κ = 2 ^ κ`, contradicting the lower bound.
  have hupper : Cardinal.mk (Σ b : (Order.succ κ).ord.ToType,
      { h : EHMRNodeAt C (Ordinal.typein (· < ·) b) // ehmrLive cR h }) ≤
      (2 : Cardinal.{0}) ^ κ := by
    rw [Cardinal.mk_sigma]
    calc Cardinal.sum (fun b => Cardinal.mk
            { h : EHMRNodeAt C (Ordinal.typein (· < ·) b) // ehmrLive cR h })
        ≤ Cardinal.sum (fun _ : (Order.succ κ).ord.ToType => (2 : Cardinal.{0}) ^ κ) :=
          Cardinal.sum_le_sum _ _ (fun b => ehmr_live_level_small hκ hC cR
            (lt_of_lt_of_eq (Ordinal.typein_lt_type (· < ·) b) (Ordinal.type_toType _)))
      _ = Cardinal.mk (Order.succ κ).ord.ToType * (2 : Cardinal.{0}) ^ κ :=
          Cardinal.sum_const' _ _
      _ = Order.succ κ * (2 : Cardinal.{0}) ^ κ := by rw [Cardinal.mk_ord_toType]
      _ = (2 : Cardinal.{0}) ^ κ := succ_mul_two_power hκ
  exact absurd (hlower.trans hupper)
    (not_le.mpr (Order.lt_succ ((2 : Cardinal.{0}) ^ κ)))

/-- **[EHMR §13 Theorem 13.1 / §14 Theorem 14.3 — branch-length]** The canonical
partition tree for `cR` has a branch of length `(succ κ).ord`: a live node of length
`≥ (succ κ).ord` (`exists_live_node_ge`) restricts to the sought `EHMRBranch`
(`ehmrBranch_of_live`). -/
theorem ehmr_tree_has_branch [Nonempty C] (hκ : Cardinal.aleph0 ≤ κ)
    (hC : Cardinal.mk C ≤ κ) (cR : (Fin 2 ↪o Source κ) → C) :
    Nonempty (EHMRBranch cR) := by
  obtain ⟨β, h, hβ, hlive⟩ := exists_live_node_ge hκ hC cR
  exact ⟨ehmrBranch_of_live cR h hβ hlive⟩

end BranchExtraction

/-! ### Assembly: EHMR branch → `CoherentMajorityBranch` -/

section Assembly

variable {κ : Cardinal.{0}} {C : Type}

/-- Assemble an `EHMRBranch` into a `CoherentMajorityBranch`. `prefixAt α` is the
embedding `α.ToType ↪o Source κ` sending position `β < α` to `rep β`; `branch α` reads
off `bit`; `prefix_restrict`/`branch_restrict` are immediate from the assembly;
`top_in_validFiber` is EHMR fact (8) (`coloring`). -/
theorem exists_coherentMajorityBranch_of_ehmrBranch
    {cR : (Fin 2 ↪o Source κ) → C} (b : EHMRBranch cR) :
    Nonempty (CoherentMajorityBranch cR) := by
  classical
  -- `typein x < (succ κ).ord` for `x : α.ToType` when `α < (succ κ).ord`.
  have htlt : ∀ {α : Ordinal.{0}} (_hα : α < (Order.succ κ).ord) (x : α.ToType),
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      Ordinal.typein (· < ·) x < (Order.succ κ).ord := by
    intro α hα x
    have : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    have h := Ordinal.typein_lt_type (· < · : α.ToType → α.ToType → Prop) x
    rw [Ordinal.type_toType] at h
    exact h.trans hα
  -- `rep`/`bit` depend on the ordinal only (proof-irrelevant in the `< (succ κ).ord` arg).
  have repc : ∀ {A B : Ordinal.{0}} (hA : A < (Order.succ κ).ord)
      (hB : B < (Order.succ κ).ord), A = B → b.rep A hA = b.rep B hB := by
    intro A B hA hB h; subst h; rfl
  have bitc : ∀ {A B : Ordinal.{0}} (hA : A < (Order.succ κ).ord)
      (hB : B < (Order.succ κ).ord), A = B → b.bit A hA = b.bit B hB := by
    intro A B hA hB h; subst h; rfl
  -- `typein ⊤ = γ` inside `(succ γ).ToType`.
  have htop : ∀ (γ : Ordinal.{0}),
      haveI : IsWellOrder (Order.succ γ).ToType (· < ·) := isWellOrder_lt
      Ordinal.typein (· < ·) (⊤ : (Order.succ γ).ToType) = γ := by
    intro γ
    have : IsWellOrder (Order.succ γ).ToType (· < ·) := isWellOrder_lt
    rw [show (⊤ : (Order.succ γ).ToType) = Ordinal.enum (α := (Order.succ γ).ToType) (· < ·)
          ⟨γ, by simp only [Set.mem_Iio, Ordinal.type_toType]; exact Order.lt_succ γ⟩ from
        Ordinal.enum_succ_eq_top.symm]
    exact Ordinal.typein_enum _ _
  -- The assembled prefix embedding at each level.
  let pre : ∀ α : Ordinal.{0}, α < (Order.succ κ).ord → α.ToType ↪o Source κ :=
    fun α hα =>
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      OrderEmbedding.ofStrictMono
        (fun x => b.rep (Ordinal.typein (· < ·) x) (htlt hα x))
        (fun _ _ hxy => b.rep_strictMono _ _ ((Ordinal.typein_lt_typein (· < ·)).mpr hxy))
  let br : ∀ α : Ordinal.{0}, α < (Order.succ κ).ord → α.ToType → C :=
    fun α hα x =>
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      b.bit (Ordinal.typein (· < ·) x) (htlt hα x)
  have pre_apply : ∀ (α : Ordinal.{0}) (hα : α < (Order.succ κ).ord) (x : α.ToType),
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      pre α hα x = b.rep (Ordinal.typein (· < ·) x) (htlt hα x) := by
    intro α hα x; have : IsWellOrder α.ToType (· < ·) := isWellOrder_lt; rfl
  have br_apply : ∀ (α : Ordinal.{0}) (hα : α < (Order.succ κ).ord) (x : α.ToType),
      haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
      br α hα x = b.bit (Ordinal.typein (· < ·) x) (htlt hα x) := by
    intro α hα x; rfl
  refine ⟨{
    prefixAt := pre
    branch := br
    prefix_restrict := ?_
    branch_restrict := ?_
    top_in_validFiber := ?_ }⟩
  · -- prefix_restrict
    intro β α hβα hβ hα x
    have : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    have : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    rw [pre_apply α hα, pre_apply β hβ]
    exact repc _ _ (Ordinal.typein_apply _ x)
  · -- branch_restrict
    intro β α hβα hβ hα x
    have : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    have : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    rw [br_apply α hα, br_apply β hβ]
    exact bitc _ _ (Ordinal.typein_apply _ x)
  · -- top_in_validFiber
    intro γ hγ hsγ
    have : IsWellOrder (Order.succ γ).ToType (· < ·) := isWellOrder_lt
    have : IsWellOrder γ.ToType (· < ·) := isWellOrder_lt
    intro x
    have hx_lt : Ordinal.typein (· < ·) x < γ := by
      have h := Ordinal.typein_lt_type (· < · : γ.ToType → γ.ToType → Prop) x
      rwa [Ordinal.type_toType] at h
    have hpx : pre γ hγ x = b.rep (Ordinal.typein (· < ·) x) (htlt hγ x) := pre_apply γ hγ x
    have hpt : pre (Order.succ γ) hsγ (⊤ : (Order.succ γ).ToType) = b.rep γ hγ := by
      rw [pre_apply (Order.succ γ) hsγ]; exact repc _ _ (htop γ)
    have h₀ : pre γ hγ x < pre (Order.succ γ) hsγ (⊤ : (Order.succ γ).ToType) := by
      rw [hpx, hpt]; exact b.rep_strictMono _ _ hx_lt
    refine ⟨h₀, ?_⟩
    have hpe : pairEmbed h₀ = pairEmbed (b.rep_strictMono (htlt hγ x) hγ hx_lt) := by
      apply RelEmbedding.ext
      intro i
      match i with
      | ⟨0, _⟩ => simp only [pairEmbed]; exact hpx
      | ⟨1, _⟩ => simp only [pairEmbed]; exact hpt
    rw [hpe, br_apply γ hγ]
    exact b.coloring (htlt hγ x) hγ hx_lt

/-- Existence of a `CoherentMajorityBranch` — a coherent branch (prefix/branch
restriction coherence + `top_in_validFiber`) of length `(succ κ).ord`, the object the
pair Erdős–Rado endgame consumes. Derived directly from the EHMR canonical partition
tree. -/
theorem exists_coherentMajorityBranch (hκ : Cardinal.aleph0 ≤ κ)
    (hC : Cardinal.mk C ≤ κ) (cR : (Fin 2 ↪o Source κ) → C) :
    Nonempty (CoherentMajorityBranch cR) := by
  have : Nonempty C := nonempty_color cR
  obtain ⟨b⟩ := ehmr_tree_has_branch hκ hC cR
  exact exists_coherentMajorityBranch_of_ehmrBranch b

end Assembly

/-! ### Chain + pigeonhole endgame -/

section Endgame

variable {κ : Cardinal.{0}} {C : Type}

/-- **`treeCommitOfBranch`**: canonical commit at position `δ` using B. Reads off
`B.prefixAt (succ δ) ⊤` (the top of the succ δ chain). -/
noncomputable def treeCommitOfBranch
    {cR : (Fin 2 ↪o Source κ) → C} (hκ : Cardinal.aleph0 ≤ κ)
    (B : CoherentMajorityBranch cR) (δ : Ordinal.{0})
    (hδ : δ < (Order.succ κ).ord) : Source κ :=
  haveI : IsWellOrder (Order.succ δ).ToType (· < ·) := isWellOrder_lt
  have hsδ : Order.succ δ < (Order.succ κ).ord := succ_lt_ord_of_lt hκ hδ
  B.prefixAt (Order.succ δ) hsδ (⊤ : (Order.succ δ).ToType)

/-- **`treeCommitColorOfBranch`**: canonical color at position `δ` using B. Reads off
`B.branch (succ δ) ⊤`. -/
noncomputable def treeCommitColorOfBranch
    {cR : (Fin 2 ↪o Source κ) → C} (hκ : Cardinal.aleph0 ≤ κ)
    (B : CoherentMajorityBranch cR) (δ : Ordinal.{0})
    (hδ : δ < (Order.succ κ).ord) : C :=
  haveI : IsWellOrder (Order.succ δ).ToType (· < ·) := isWellOrder_lt
  have hsδ : Order.succ δ < (Order.succ κ).ord := succ_lt_ord_of_lt hκ hδ
  B.branch (Order.succ δ) hsδ (⊤ : (Order.succ δ).ToType)

/-- **`treeCommitOfBranch_strictMono`**: strict monotonicity of the branch-driven chain
values, inherited from `B.prefixAt`'s order embedding structure + `prefix_restrict` to
identify levels. -/
lemma treeCommitOfBranch_strictMono
    {cR : (Fin 2 ↪o Source κ) → C} (hκ : Cardinal.aleph0 ≤ κ)
    (B : CoherentMajorityBranch cR) {δ₁ δ₂ : Ordinal.{0}}
    (hδ₁ : δ₁ < (Order.succ κ).ord) (hδ₂ : δ₂ < (Order.succ κ).ord)
    (h : δ₁ < δ₂) :
    treeCommitOfBranch hκ B δ₁ hδ₁ < treeCommitOfBranch hκ B δ₂ hδ₂ := by
  have : IsWellOrder (Order.succ δ₁).ToType (· < ·) := isWellOrder_lt
  have : IsWellOrder (Order.succ δ₂).ToType (· < ·) := isWellOrder_lt
  have hsδ₁ : Order.succ δ₁ < (Order.succ κ).ord := succ_lt_ord_of_lt hκ hδ₁
  have hsδ₂ : Order.succ δ₂ < (Order.succ κ).ord := succ_lt_ord_of_lt hκ hδ₂
  have hsδ₁_le_sδ₂ : Order.succ δ₁ ≤ Order.succ δ₂ :=
    Order.succ_le_succ (le_of_lt h)
  show B.prefixAt (Order.succ δ₁) hsδ₁ (⊤ : (Order.succ δ₁).ToType) <
    B.prefixAt (Order.succ δ₂) hsδ₂ (⊤ : (Order.succ δ₂).ToType)
  -- Use prefix_restrict to convert LHS to a (succ δ₂)-level expression.
  rw [← B.prefix_restrict hsδ₁_le_sδ₂ hsδ₁ hsδ₂
      (⊤ : (Order.succ δ₁).ToType)]
  -- Now both sides are B.prefixAt (succ δ₂) hsδ₂ applied at two
  -- elements of (succ δ₂).ToType; apply OrderEmbedding strict-mono.
  apply (B.prefixAt (Order.succ δ₂) hsδ₂).strictMono
  -- Compare typein values: initialSegOfLe ⊤_(succ δ₁) has typein δ₁;
  -- ⊤_(succ δ₂) has typein δ₂. Since δ₁ < δ₂, < holds.
  have h_typein_init :
      Ordinal.typein (α := (Order.succ δ₂).ToType) (· < ·)
        ((initialSegOfLe hsδ₁_le_sδ₂).toOrderEmbedding
          (⊤ : (Order.succ δ₁).ToType)) = δ₁ := by
    rw [show Ordinal.typein (α := (Order.succ δ₂).ToType) (· < ·)
          ((initialSegOfLe hsδ₁_le_sδ₂).toOrderEmbedding
            (⊤ : (Order.succ δ₁).ToType)) =
        Ordinal.typein (α := (Order.succ δ₁).ToType) (· < ·)
          (⊤ : (Order.succ δ₁).ToType) from
      Ordinal.typein_apply (initialSegOfLe hsδ₁_le_sδ₂) _]
    rw [show (⊤ : (Order.succ δ₁).ToType) =
        Ordinal.enum (α := (Order.succ δ₁).ToType) (· < ·)
          ⟨δ₁, (Ordinal.type_toType _).symm ▸ Order.lt_succ δ₁⟩ from
      Ordinal.enum_succ_eq_top.symm]
    exact Ordinal.typein_enum _ _
  have h_typein_top :
      Ordinal.typein (α := (Order.succ δ₂).ToType) (· < ·)
        (⊤ : (Order.succ δ₂).ToType) = δ₂ := by
    rw [show (⊤ : (Order.succ δ₂).ToType) =
        Ordinal.enum (α := (Order.succ δ₂).ToType) (· < ·)
          ⟨δ₂, (Ordinal.type_toType _).symm ▸ Order.lt_succ δ₂⟩ from
      Ordinal.enum_succ_eq_top.symm]
    exact Ordinal.typein_enum _ _
  -- typein-order corresponds to <.
  rw [← Ordinal.typein_lt_typein
    (· < · : (Order.succ δ₂).ToType → (Order.succ δ₂).ToType → Prop)]
  rw [h_typein_init, h_typein_top]
  exact h

/-- **`treeCommitColorFnOfBranch`**: indexed color function on `(succ κ).ord.ToType`
using B. -/
noncomputable def treeCommitColorFnOfBranch
    {cR : (Fin 2 ↪o Source κ) → C} (hκ : Cardinal.aleph0 ≤ κ)
    (B : CoherentMajorityBranch cR) :
    (Order.succ κ).ord.ToType → C := fun x =>
  haveI : IsWellOrder (Order.succ κ).ord.ToType (· < ·) := isWellOrder_lt
  treeCommitColorOfBranch hκ B (Ordinal.typein (· < ·) x) (by
    simpa [Ordinal.type_toType] using
      Ordinal.typein_lt_type
        (· < · : (Order.succ κ).ord.ToType →
          (Order.succ κ).ord.ToType → Prop) x)

/-- **`treeChainEmbeddingOfBranch`**: `(succ κ).ord.ToType ↪o Source κ` embedding
driven by B. -/
noncomputable def treeChainEmbeddingOfBranch
    {cR : (Fin 2 ↪o Source κ) → C} (hκ : Cardinal.aleph0 ≤ κ)
    (B : CoherentMajorityBranch cR) :
    (Order.succ κ).ord.ToType ↪o Source κ := by
  haveI : IsWellOrder (Order.succ κ).ord.ToType (· < ·) := isWellOrder_lt
  refine OrderEmbedding.ofStrictMono
    (fun x =>
      treeCommitOfBranch hκ B (Ordinal.typein (· < ·) x) (by
        simpa [Ordinal.type_toType] using
          Ordinal.typein_lt_type
            (· < · : (Order.succ κ).ord.ToType →
              (Order.succ κ).ord.ToType → Prop) x))
    ?_
  intro x y hxy
  have hx : Ordinal.typein (· < ·) x < (Order.succ κ).ord := by
    simpa [Ordinal.type_toType] using
      Ordinal.typein_lt_type
        (· < · : (Order.succ κ).ord.ToType →
          (Order.succ κ).ord.ToType → Prop) x
  have hy : Ordinal.typein (· < ·) y < (Order.succ κ).ord := by
    simpa [Ordinal.type_toType] using
      Ordinal.typein_lt_type
        (· < · : (Order.succ κ).ord.ToType →
          (Order.succ κ).ord.ToType → Prop) y
  exact treeCommitOfBranch_strictMono hκ B hx hy
    ((Ordinal.typein_lt_typein (· < ·)).mpr hxy)

/-- **`treeChain_pair_homogeneous_ofBranch`**: pair-homogeneity along the branch-driven
chain. For `δ < η < (succ κ).ord`,
`cR (pair (treeCommitOfBranch B δ) (treeCommitOfBranch B η)) = treeCommitColorOfBranch B δ`.

Proof: by `B.top_in_validFiber η`, `commit η = B.prefixAt (succ η) ⊤` is in
`validFiber cR (B.prefixAt η hη) (B.branch η hη)`. Apply at position `enum δ : η.ToType`;
use `B.prefix_restrict` / `B.branch_restrict` to identify the constraint values with
`commit δ` and `commit color δ`. -/
theorem treeChain_pair_homogeneous_ofBranch
    {cR : (Fin 2 ↪o Source κ) → C} (hκ : Cardinal.aleph0 ≤ κ)
    (B : CoherentMajorityBranch cR) {δ η : Ordinal.{0}}
    (hδη : δ < η) (hη : η < (Order.succ κ).ord) :
    cR (pairEmbed (treeCommitOfBranch_strictMono hκ B
        (hδη.trans hη) hη hδη)) =
      treeCommitColorOfBranch hκ B δ (hδη.trans hη) := by
  have : IsWellOrder η.ToType (· < ·) := isWellOrder_lt
  have : IsWellOrder (Order.succ δ).ToType (· < ·) := isWellOrder_lt
  have : IsWellOrder (Order.succ η).ToType (· < ·) := isWellOrder_lt
  have hδ : δ < (Order.succ κ).ord := hδη.trans hη
  have hsδ : Order.succ δ < (Order.succ κ).ord := succ_lt_ord_of_lt hκ hδ
  have hsη : Order.succ η < (Order.succ κ).ord := succ_lt_ord_of_lt hκ hη
  have hsδ_le_η : Order.succ δ ≤ η := Order.succ_le_of_lt hδη
  -- The top of (succ η)-chain is in the validFiber for level η.
  have h_top_in :=
    B.top_in_validFiber η hη hsη
  set x_η : η.ToType :=
    Ordinal.enum (α := η.ToType) (· < ·)
      ⟨δ, (Ordinal.type_toType η).symm ▸ hδη⟩
  obtain ⟨h_lt, h_col⟩ := h_top_in x_η
  -- Helper: x_η = initialSegOfLe (⊤ : (succ δ).ToType).
  have h_x_η_eq :
      (initialSegOfLe hsδ_le_η).toOrderEmbedding
          (⊤ : (Order.succ δ).ToType) = x_η := by
    have h_typein_init :
        Ordinal.typein (α := η.ToType) (· < ·)
          ((initialSegOfLe hsδ_le_η).toOrderEmbedding
            (⊤ : (Order.succ δ).ToType)) = δ := by
      rw [show Ordinal.typein (α := η.ToType) (· < ·)
            ((initialSegOfLe hsδ_le_η).toOrderEmbedding
              (⊤ : (Order.succ δ).ToType)) =
          Ordinal.typein (α := (Order.succ δ).ToType) (· < ·)
            (⊤ : (Order.succ δ).ToType) from
        Ordinal.typein_apply (initialSegOfLe hsδ_le_η) _]
      rw [show (⊤ : (Order.succ δ).ToType) =
          Ordinal.enum (α := (Order.succ δ).ToType) (· < ·)
            ⟨δ, (Ordinal.type_toType _).symm ▸ Order.lt_succ δ⟩ from
        Ordinal.enum_succ_eq_top.symm]
      exact Ordinal.typein_enum _ _
    rw [← Ordinal.enum_typein
        (· < · : η.ToType → η.ToType → Prop)
        ((initialSegOfLe hsδ_le_η).toOrderEmbedding
          (⊤ : (Order.succ δ).ToType))]
    congr 1
    apply Subtype.ext
    exact h_typein_init
  -- B.prefixAt η hη x_η = B.prefixAt (succ δ) hsδ ⊤ = commit δ.
  have h_prefix_η_x : B.prefixAt η hη x_η =
      B.prefixAt (Order.succ δ) hsδ (⊤ : (Order.succ δ).ToType) := by
    rw [← h_x_η_eq]
    exact B.prefix_restrict hsδ_le_η hsδ hη
      (⊤ : (Order.succ δ).ToType)
  -- Similar for branch.
  have h_branch_η_x : B.branch η hη x_η =
      B.branch (Order.succ δ) hsδ (⊤ : (Order.succ δ).ToType) := by
    rw [← h_x_η_eq]
    exact B.branch_restrict hsδ_le_η hsδ hη
      (⊤ : (Order.succ δ).ToType)
  -- Combine. Goal: cR(pair our_witness) = commit color δ.
  show cR _ = B.branch (Order.succ δ) hsδ (⊤ : (Order.succ δ).ToType)
  rw [← h_branch_η_x]
  -- pairEmbed of our_witness equals pairEmbed h_lt (same values).
  have h_pair_eq :
      (pairEmbed (treeCommitOfBranch_strictMono hκ B hδ hη hδη) :
        Fin 2 ↪o Source κ) = pairEmbed h_lt := by
    ext k
    match k with
    | ⟨0, _⟩ =>
      show treeCommitOfBranch hκ B δ hδ = B.prefixAt η hη x_η
      show B.prefixAt (Order.succ δ) hsδ (⊤ : (Order.succ δ).ToType) =
        B.prefixAt η hη x_η
      exact h_prefix_η_x.symm
    | ⟨1, _⟩ => rfl
  rw [h_pair_eq]
  exact h_col

/-- **[THE FINAL PIGEONHOLE]** Color pigeonhole on `treeCommitColorFnOfBranch B`: some
color has a `succ κ`-sized preimage (domain of size `succ κ`, codomain of size
`≤ κ`). -/
theorem exists_large_treeCommitColorFn_fiber_ofBranch
    {cR : (Fin 2 ↪o Source κ) → C} (hκ : Cardinal.aleph0 ≤ κ)
    (hC : Cardinal.mk C ≤ κ) (B : CoherentMajorityBranch cR) :
    ∃ b : C,
      Order.succ κ ≤
        Cardinal.mk ((treeCommitColorFnOfBranch hκ B) ⁻¹' {b}) := by
  have hα_card :
      Cardinal.mk (Order.succ κ).ord.ToType ≥ Order.succ κ := by
    rw [Cardinal.mk_ord_toType]
  exact exists_large_fiber_of_small_codomain hκ hα_card hC
    (treeCommitColorFnOfBranch hκ B)

/-- **[CONDITIONAL HEADLINE]** Parameterized pair Erdős–Rado, assuming a
`CoherentMajorityBranch`: there is a color `b` and a `(succ κ).ord`-indexed strict-mono
sequence into `Source κ` whose every pair has `cR`-color `b`.

Proof: color pigeonhole (`exists_large_treeCommitColorFn_fiber_ofBranch`) gives a
`succ κ`-sized preimage of some `b`; `ordIso_ordToType_of_card_ge` gives an order iso
preimage ≃ `(succ κ).ord.ToType`. Compose with `treeChainEmbeddingOfBranch B` to get the
embedding; pair-homogeneity comes from `treeChain_pair_homogeneous_ofBranch` + constancy
of `treeCommitColorFnOfBranch B` on the preimage. -/
theorem pairErdosRado_general_of_coherentMajorityBranch
    {cR : (Fin 2 ↪o Source κ) → C} (hκ : Cardinal.aleph0 ≤ κ)
    (hC : Cardinal.mk C ≤ κ) (B : CoherentMajorityBranch cR) :
    ∃ (f : (Order.succ κ).ord.ToType ↪o Source κ) (b : C),
      ∀ {x y : (Order.succ κ).ord.ToType} (hxy : x < y),
        cR (pairEmbed (f.strictMono hxy)) = b := by
  have : IsWellOrder (Order.succ κ).ord.ToType (· < ·) := isWellOrder_lt
  obtain ⟨b, hb⟩ := exists_large_treeCommitColorFn_fiber_ofBranch hκ hC B
  obtain ⟨iso⟩ := ordIso_ordToType_of_card_ge hb
  -- f : (succ κ).ord.ToType → Source κ via iso.symm + value extraction +
  -- treeChainEmbeddingOfBranch.
  have h_strict : StrictMono
      (fun z : (Order.succ κ).ord.ToType =>
        treeChainEmbeddingOfBranch hκ B (iso.symm z).val) := by
    intro a b hab
    apply (treeChainEmbeddingOfBranch hκ B).strictMono
    have h_iso_lt : iso.symm a < iso.symm b := iso.symm.lt_iff_lt.mpr hab
    exact h_iso_lt
  let f : (Order.succ κ).ord.ToType ↪o Source κ :=
    OrderEmbedding.ofStrictMono
      (fun z => treeChainEmbeddingOfBranch hκ B (iso.symm z).val) h_strict
  refine ⟨f, b, ?_⟩
  intro x y hxy
  -- f x = treeChainEmbeddingOfBranch B (iso.symm x).val.
  -- f y = treeChainEmbeddingOfBranch B (iso.symm y).val.
  -- By treeChain_pair_homogeneous_ofBranch + commitColorFn = b on preimage.
  have h_iso_x_in : (iso.symm x).val ∈
      (treeCommitColorFnOfBranch hκ B) ⁻¹' {b} := (iso.symm x).property
  have h_iso_x_eq : treeCommitColorFnOfBranch hκ B (iso.symm x).val = b :=
    h_iso_x_in
  have h_lt_typein :
      Ordinal.typein (· < ·) (iso.symm x).val <
        Ordinal.typein (· < ·) (iso.symm y).val := by
    have h_iso_lt : iso.symm x < iso.symm y := iso.symm.lt_iff_lt.mpr hxy
    exact (Ordinal.typein_lt_typein (· < ·)).mpr h_iso_lt
  have h_xval_lt : Ordinal.typein (· < ·) (iso.symm x).val <
      (Order.succ κ).ord := by
    simpa [Ordinal.type_toType] using
      Ordinal.typein_lt_type
        (· < · : (Order.succ κ).ord.ToType →
          (Order.succ κ).ord.ToType → Prop) _
  have h_yval_lt : Ordinal.typein (· < ·) (iso.symm y).val <
      (Order.succ κ).ord := by
    simpa [Ordinal.type_toType] using
      Ordinal.typein_lt_type
        (· < · : (Order.succ κ).ord.ToType →
          (Order.succ κ).ord.ToType → Prop) _
  have h_pair := treeChain_pair_homogeneous_ofBranch hκ B h_lt_typein h_yval_lt
  have h_color_eq : treeCommitColorOfBranch hκ B
      (Ordinal.typein (· < ·) (iso.symm x).val) h_xval_lt = b := by
    show treeCommitColorFnOfBranch hκ B _ = b
    exact h_iso_x_eq
  have h_pair_eq :
      (pairEmbed (f.strictMono hxy) : Fin 2 ↪o Source κ) =
      pairEmbed (treeCommitOfBranch_strictMono hκ B h_xval_lt h_yval_lt
        h_lt_typein) := by
    ext k
    match k with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  rw [h_pair_eq, h_pair]
  exact h_color_eq

end Endgame

/-! ### The headline, the regression specialization, and the abstract-source wrapper -/

/-- **[HEADLINE — parameterized pair Erdős–Rado]** For infinite `κ` and any color type
`C` with `#C ≤ κ`, every pair coloring of `Source κ = (succ (2 ^ κ)).ord.ToType` is
constant on a `(succ κ).ord`-indexed strict-mono suborder: `(2 ^ κ)⁺ → (κ⁺)²_κ`.
The `κ = ℵ₀`, `C = Bool` case is the legacy `erdos_rado_pair_omega1`. -/
theorem pairErdosRado_general (κ : Cardinal.{0}) (hκ : Cardinal.aleph0 ≤ κ)
    {C : Type} (hC : Cardinal.mk C ≤ κ) (cR : (Fin 2 ↪o Source κ) → C) :
    ∃ (f : (Order.succ κ).ord.ToType ↪o Source κ) (b : C),
      ∀ {x y : (Order.succ κ).ord.ToType} (hxy : x < y),
        cR (pairEmbed (f.strictMono hxy)) = b :=
  pairErdosRado_general_of_coherentMajorityBranch hκ hC
    (exists_coherentMajorityBranch hκ hC cR).some

/-- **[REGRESSION]** The legacy Bool/ℵ₀ shape, recovered from the general theorem at
`κ = ℵ₀` via `succ ℵ₀ = ℵ_1` and `(ℵ_1).ord = ω_1` (stated with this file's own
`Source`/`pairEmbed`; `Source ℵ₀ = (succ (2 ^ ℵ₀)).ord.ToType` matches the legacy
`PairERSource = (succ ℶ_1).ord.ToType` up to `2 ^ ℵ₀ = ℶ_1`). -/
theorem erdos_rado_pair_omega1_from_general
    (cR : (Fin 2 ↪o Source Cardinal.aleph0) → Bool) :
    ∃ (f : (Ordinal.omega.{0} 1).ToType ↪o Source Cardinal.aleph0) (b : Bool),
      ∀ {x y : (Ordinal.omega.{0} 1).ToType} (hxy : x < y),
        cR (pairEmbed (f.strictMono hxy)) = b := by
  have hord : (Order.succ Cardinal.aleph0).ord = Ordinal.omega.{0} 1 := by
    rw [Cardinal.succ_aleph0, Cardinal.ord_aleph]
  rw [← hord]
  exact pairErdosRado_general Cardinal.aleph0 le_rfl Cardinal.mk_le_aleph0 cR

/-- **[ABSTRACT SOURCE]** The parameterized pair Erdős–Rado over any well-ordered source
`I` of cardinality `≥ succ (2 ^ κ)`: embed `Source κ` into `I`
(`exists_ordToType_embedding_of_card_ge`), pull the coloring back, and transport the
homogeneous chain forward. -/
theorem pairErdosRado_general_of_large (κ : Cardinal.{0}) (hκ : Cardinal.aleph0 ≤ κ)
    {C : Type} (hC : Cardinal.mk C ≤ κ)
    {I : Type} [LinearOrder I] [WellFoundedLT I]
    (hI : Order.succ ((2 : Cardinal.{0}) ^ κ) ≤ Cardinal.mk I)
    (cR : (Fin 2 ↪o I) → C) :
    ∃ (f : (Order.succ κ).ord.ToType ↪o I) (b : C),
      ∀ {x y : (Order.succ κ).ord.ToType} (hxy : x < y),
        cR (pairEmbed (f.strictMono hxy)) = b := by
  obtain ⟨e⟩ : Nonempty (Source κ ↪o I) := exists_ordToType_embedding_of_card_ge hI
  obtain ⟨f, b, hf⟩ := pairErdosRado_general κ hκ hC (fun t => cR (t.trans e))
  refine ⟨f.trans e, b, ?_⟩
  intro x y hxy
  have key := hf hxy
  -- `key : cR ((pairEmbed (f.strictMono hxy)).trans e) = b`; the goal's pair embedding
  -- has the same two values `e (f x) < e (f y)`, so `cR` agrees.
  rw [← key]
  congr 1
  ext k
  match k with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

end FirstOrder.Combinatorics.PairERGen
