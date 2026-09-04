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
private lemma mk_source (κ : Cardinal.{0}) :
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
private lemma aleph0_le_two_power (hκ : Cardinal.aleph0 ≤ κ) :
    Cardinal.aleph0 ≤ (2 : Cardinal.{0}) ^ κ :=
  hκ.trans (Cardinal.cantor κ).le

/-- `ℵ_0 ≤ succ (2 ^ κ)` for infinite `κ`. -/
lemma aleph0_le_succ_two_power (hκ : Cardinal.aleph0 ≤ κ) :
    Cardinal.aleph0 ≤ Order.succ ((2 : Cardinal.{0}) ^ κ) :=
  (aleph0_le_two_power hκ).trans (Order.le_succ _)

/-- `ℵ_0 ≤ succ κ` for infinite `κ`. -/
private lemma aleph0_le_succ_self (hκ : Cardinal.aleph0 ≤ κ) :
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
private theorem mk_node_le {C : Type} (hκ : Cardinal.aleph0 ≤ κ)
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

end CardinalHelpers

/-! ### Branch structures: `validFiber`, `CoherentMajorityBranch`, `EHMRBranch` -/

section BranchStructures

variable {κ : Cardinal.{0}} {C : Type}

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
private def ehmrFiber (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}}
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
private noncomputable def ehmrRep (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}}
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
private theorem ehmrR_subsingleton (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}}
    (h : EHMRNodeAt C β) : (ehmrR cR h).Subsingleton := by
  classical
  rw [ehmrR]
  split_ifs with hlive
  · exact Set.subsingleton_singleton
  · exact Set.subsingleton_empty

/-- On a live node, the chosen rep lies in the successor set. -/
private theorem ehmrChosen_mem (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}}
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
private theorem ehmrChosen_eq_min (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}}
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
private theorem ehmrChosen_le_of_mem (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}}
    (h : EHMRNodeAt C β) {y : Source κ} (hy : y ∈ ehmrS cR h) :
    ehmrChosen cR β h ≤ y := by
  have hlive : ehmrLive cR h := ⟨y, hy⟩
  rw [ehmrChosen_eq_min cR h hlive]
  exact not_lt.mp (WellFounded.not_lt_min _ _ hy)

/-- Level cardinality: for `β < (succ κ).ord` the level (all length-`β` nodes) has
cardinality `≤ 2 ^ κ` — `β.ToType` of size `≤ κ`, `C`-valued with `#C ≤ κ`. -/
private theorem ehmr_level_card_le (hκ : Cardinal.aleph0 ≤ κ) (hC : Cardinal.mk C ≤ κ)
    {β : Ordinal.{0}} (hβ : β < (Order.succ κ).ord) :
    Cardinal.mk (EHMRNodeAt C β) ≤ (2 : Cardinal.{0}) ^ κ :=
  mk_node_le hκ hC hβ

/-- Level smallness: for `β < (succ κ).ord` there are `≤ 2 ^ κ` live length-`β` nodes
(a fortiori `≤ 2 ^ κ` nodes, by `ehmr_level_card_le`). -/
private theorem ehmr_live_level_small (hκ : Cardinal.aleph0 ≤ κ) (hC : Cardinal.mk C ≤ κ)
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
  change yNode cR y β ((initialSegOfLe hδ).toOrderEmbedding x') = yNode cR y δ x'
  simp only [yNode, htx]

/-- The reps of `yNode cR y β` are exactly `yRep cR y (typein x)`. (The `IsWellOrder`
binder lets `typein` appear in the signature; call sites discharge it with
`isWellOrder_lt`.) -/
private theorem ehmrRep_yNode (cR : (Fin 2 ↪o Source κ) → C) (y : Source κ)
    {β : Ordinal.{0}} [IsWellOrder β.ToType (· < ·)] (x : β.ToType) :
    ehmrRep cR (yNode cR y β) x = yRep cR y (Ordinal.typein (· < ·) x) := by
  classical
  have hlt : Ordinal.typein (· < ·) x < β :=
    lt_of_lt_of_eq (Ordinal.typein_lt_type (· < ·) x) (Ordinal.type_toType β)
  change ehmrChosen cR (Ordinal.typein (· < ·) x) ((yNode cR y β).restrict (le_of_lt hlt))
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
  change h ((initialSegOfLe hδ).toOrderEmbedding
        ((initialSegOfLe hε).toOrderEmbedding z))
     = h ((initialSegOfLe (hε.trans hδ)).toOrderEmbedding z)
  rw [initialSegOfLe_compose]

/-- `EHMRNodeAt.restrict` at heterogeneously-equal lengths. -/
theorem EHMRNodeAt.restrict_heq {β : Ordinal.{0}} (h : EHMRNodeAt C β)
    {δ₁ δ₂ : Ordinal.{0}} (hδ : δ₁ = δ₂) (h1 : δ₁ ≤ β) (h2 : δ₂ ≤ β) :
    HEq (h.restrict h1) (h.restrict h2) := by
  subst hδ; exact heq_of_eq rfl

end EndHomogeneity

/-! ### Branch extraction from a high live node

EHMR Theorem 13.1 realized concretely: the `succ (2 ^ κ)`-many live nodes (coverage)
cannot all sit at levels `< (succ κ).ord` (each such level has `≤ 2 ^ κ` nodes, and
there are only `succ κ` of them), so some live node has length `≥ (succ κ).ord`;
reading it off at the first `(succ κ).ord` positions yields an `EHMRBranch`. -/

section BranchExtraction

variable {κ : Cardinal.{0}} {C : Type}

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

end BranchExtraction

/-! ### Assembly: EHMR branch → `CoherentMajorityBranch` -/

section Assembly

variable {κ : Cardinal.{0}} {C : Type}

end Assembly

/-! ### Chain + pigeonhole endgame -/

section Endgame

variable {κ : Cardinal.{0}} {C : Type}

end Endgame

/-! ### The headline, the regression specialization, and the abstract-source wrapper -/

end FirstOrder.Combinatorics.PairERGen
