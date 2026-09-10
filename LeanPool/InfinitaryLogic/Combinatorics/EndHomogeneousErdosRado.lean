/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Combinatorics.PairErdosRadoGeneral
/-!
# End-homogeneous Erdős–Rado: the arity-general EHMR engine (ER hard chunk 2a)

The **end-homogenization Erdős–Rado theorem** at every finite arity: for an infinite
cardinal `lam`, a color type `C` with `#C ≤ lam`, and a coloring
`G : (Fin (n + 2) ↪o I) → C` of `(n+2)`-tuples in a well-ordered source `I` of size
`≥ succ (2 ^ lam)`, there is a `(succ lam).ord`-indexed suborder on which `G` is
**end-homogeneous**: the color of `s ⌢ x` depends only on the prefix `(n+1)`-tuple `s`,
not on the final point `x` above it (`exists_endHomogeneous_of_large`).

This is a port-with-modification of the proven pair engine
`Combinatorics/PairErdosRadoGeneral.lean` (namespace `PairERGen`, whose generic toolbox and
cardinal helpers are reused here, not re-proven). The single structural change: an EHMR
tree node at level `β` records the new point's color against every prefix **`(n+1)`-tuple**
(`NodeAt C n β = (Fin (n+1) ↪o β.ToType) → C`) instead of against every prefix **point**
(`EHMRNodeAt C β = β.ToType → C`). The endgame is *shorter* than the pair file's:
end-homogeneity is read directly off the branch (`Branch.coloring` = EHMR fact (8)); no
majority/pigeonhole layers are needed.

**Why pair colors cannot do this job.** One could try to prove the induction step by
pair-coloring `{x, y}` with "the induced tuple-color functions of `x` and `y` agree" — but
that comparison ranges over *all* lower `(n+1)`-tuples, a varying domain of size up to the
full source, so the color type explodes past every fixed bound. The EHMR tree never makes
that global comparison: a node only records colors against the `≤ lam`-sized branch prefix
below it, and that restriction *is* the proof — level counting stays at `2 ^ lam`, so the
`succ (2 ^ lam)`-sized source forces a branch of length `(succ lam).ord`.

The pair file is the `n = 0` shadow of this engine: the regression theorem
`pairER_from_endHomogeneous` re-derives the exact conclusion of
`PairERGen.pairErdosRado_general_of_large` from `exists_endHomogeneous_of_large` at `n = 0`
plus a point pigeonhole, protecting the statement against drift.

**Consumer** (ER hard chunk 2b, the finite-arity induction step): from an end-homogeneous
suborder, the induced arity-`(n+1)` coloring `c' s := G (s ⌢ any-point-above)` is
well-defined (end-homogeneity + the no-max lemma supply and identify the above-points), and
feeding `c'` to the arity-`(n+1)` inductive hypothesis homogenizes `G` outright.

## Structure

- **Tuple utilities**: `appendLastOE` (append a strict upper bound to an `(n+1)`-tuple),
  its evaluation/congruence/composition lemmas, and the arity-1 bridges to `pairEmbed`.
- **Cardinal helpers**: `mk_finTupleEmb_le` (`#(Fin m ↪o α) ≤ lam`) and `mk_tupleNode_le`
  (the tuple-node level bound `≤ 2 ^ lam`), plus `nonempty_color_tuple`.
- **EHMR tree with tuple-typed nodes**: `NodeAt`/`NodeAt.restrict` (restriction is tuple
  precomposition with the initial-segment embedding), the fiber/chosen-rep recursion, the
  coverage `y`-path, end-homogeneity of live nodes (`node_fact8`), and branch extraction
  (`exists_live_node_ge`, `tree_has_branch`).
- **Headline**: `exists_endHomogeneous` (concrete source), `exists_endHomogeneous_of_large`
  (abstract well-ordered source); **regression**: `pairER_from_endHomogeneous`.
-/

universe u

namespace FirstOrder.Combinatorics.EndHomogER

open FirstOrder.Combinatorics.PairERGen

/-! ### Tuple utilities: appending a strict upper bound to an `(n+1)`-tuple -/

section TupleUtils

variable {I : Type*} [LinearOrder I] {n : ℕ}

/-- Append a strict upper bound `x` to an `(n+1)`-tuple `s`, giving an `(n+2)`-tuple.
The underlying function is `Fin.snoc s x`; the `<`-proof `hx` enters only the
strict-monotonicity argument, so the embedding's data depends on `s` and `x` alone. -/
def appendLastOE (s : Fin (n + 1) ↪o I) (x : I) (hx : ∀ k, s k < x) :
    Fin (n + 2) ↪o I :=
  OrderEmbedding.ofStrictMono (Fin.snoc (⇑s) x) (by
    intro p q hpq
    induction p using Fin.lastCases with
    | last => exact absurd hpq (not_lt.mpr (Fin.le_last q))
    | cast p =>
      induction q using Fin.lastCases with
      | last =>
        rw [Fin.snoc_castSucc, Fin.snoc_last]
        exact hx p
      | cast q =>
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact s.strictMono (Fin.castSucc_lt_castSucc_iff.mp hpq))

/-- The underlying function of `appendLastOE` is `Fin.snoc s x`. -/
@[simp] theorem appendLastOE_coe (s : Fin (n + 1) ↪o I) (x : I) (hx : ∀ k, s k < x) :
    ⇑(appendLastOE s x hx) = Fin.snoc (⇑s) x := rfl

/-- `appendLastOE` at a prefix position gives the prefix value. -/
theorem appendLastOE_castSucc (s : Fin (n + 1) ↪o I) (x : I) (hx : ∀ k, s k < x)
    (k : Fin (n + 1)) : appendLastOE s x hx k.castSucc = s k := by
  simp [appendLastOE_coe]

/-- `appendLastOE` at the last position gives the appended point. -/
theorem appendLastOE_last (s : Fin (n + 1) ↪o I) (x : I) (hx : ∀ k, s k < x) :
    appendLastOE s x hx (Fin.last (n + 1)) = x := by
  simp [appendLastOE_coe]

/-- `appendLastOE` depends only on the underlying points (in particular it is
proof-irrelevant in the `<`-hypothesis). -/
theorem appendLastOE_congr {s s' : Fin (n + 1) ↪o I} {x x' : I}
    (hs : ∀ k, s k = s' k) (hxx : x = x')
    (hx : ∀ k, s k < x) (hx' : ∀ k, s' k < x') :
    appendLastOE s x hx = appendLastOE s' x' hx' := by
  have hcoe : (⇑s : Fin (n + 1) → I) = ⇑s' := funext hs
  refine DFunLike.ext _ _ fun i => ?_
  simp only [appendLastOE_coe]
  rw [hcoe, hxx]

/-- `appendLastOE` commutes with postcomposition by an order embedding
(`Fin.snoc` naturality). -/
private theorem appendLastOE_trans {J : Type*} [LinearOrder J]
    (s : Fin (n + 1) ↪o I) (x : I) (hx : ∀ k, s k < x) (e : I ↪o J) :
    (appendLastOE s x hx).trans e =
      appendLastOE (s.trans e) (e x) (fun k => e.strictMono (hx k)) := by
  refine DFunLike.ext _ _ fun i => ?_
  simp only [RelEmbedding.trans_apply, appendLastOE_coe]
  exact congrFun (Fin.comp_snoc (⇑e) (⇑s) x) i

end TupleUtils

/-! ### Cardinal helpers: the tuple-domain bounds the tree port consumes -/

section CardinalHelpers

variable {lam : Cardinal.{0}}

/-- Finite tuple-embedding count: `#(Fin m ↪o α) ≤ lam` for `#α ≤ lam` and infinite `lam`
(inject into `Fin m → α` and collapse the finite power). -/
private theorem mk_finTupleEmb_le (m : ℕ) {α : Type} [LinearOrder α]
    (hα : Cardinal.mk α ≤ lam) (hlam : Cardinal.aleph0 ≤ lam) :
    Cardinal.mk (Fin m ↪o α) ≤ lam := by
  have h1 : Cardinal.mk (Fin m ↪o α) ≤ Cardinal.mk (Fin m → α) :=
    Cardinal.mk_le_of_injective (f := fun t : Fin m ↪o α => ⇑t) DFunLike.coe_injective
  have h2 : Cardinal.mk (Fin m → α) = Cardinal.mk α ^ (m : Cardinal.{0}) := by
    rw [← Cardinal.power_def, Cardinal.mk_fin]
  calc Cardinal.mk (Fin m ↪o α) ≤ Cardinal.mk (Fin m → α) := h1
    _ = Cardinal.mk α ^ (m : Cardinal.{0}) := h2
    _ ≤ lam ^ (m : Cardinal.{0}) := Cardinal.power_le_power_right hα
    _ = lam ^ m := Cardinal.power_natCast lam m
    _ ≤ lam := Cardinal.power_nat_le hlam

/-- **Tuple-node count bound.** For `β < (succ lam).ord` and `#C ≤ lam`, the level of
recorded-color tuple nodes has at most `2 ^ lam` members:
`#((Fin (n+1) ↪o β.ToType) → C) ≤ (2 ^ lam) ^ lam = 2 ^ lam`. -/
private theorem mk_tupleNode_le {C : Type} (hC : Cardinal.mk C ≤ lam)
    (hlam : Cardinal.aleph0 ≤ lam) (n : ℕ) {β : Ordinal.{0}}
    (hβ : β < (Order.succ lam).ord) :
    Cardinal.mk ((Fin (n + 1) ↪o β.ToType) → C) ≤ (2 : Cardinal.{0}) ^ lam :=
  calc Cardinal.mk ((Fin (n + 1) ↪o β.ToType) → C)
      = Cardinal.mk C ^ Cardinal.mk (Fin (n + 1) ↪o β.ToType) :=
        (Cardinal.power_def _ _).symm
    _ ≤ ((2 : Cardinal.{0}) ^ lam) ^ Cardinal.mk (Fin (n + 1) ↪o β.ToType) :=
        Cardinal.power_le_power_right (hC.trans (Cardinal.cantor lam).le)
    _ ≤ ((2 : Cardinal.{0}) ^ lam) ^ lam :=
        Cardinal.power_le_power_left (two_power_ne_zero lam)
          (mk_finTupleEmb_le (n + 1) (toType_card_le_of_lt_succ_ord hβ) hlam)
    _ = (2 : Cardinal.{0}) ^ (lam * lam) := Cardinal.power_mul.symm
    _ = (2 : Cardinal.{0}) ^ lam := by rw [Cardinal.mul_eq_self hlam]

/-- Any `(n+2)`-tuple coloring on `Source lam` witnesses `Nonempty C`: the source's order
type is at least `ω`, so it contains an increasing `(n+2)`-tuple. -/
private theorem nonempty_color_tuple (hlam : Cardinal.aleph0 ≤ lam) {C : Type} {n : ℕ}
    (G : (Fin (n + 2) ↪o Source lam) → C) : Nonempty C := by
  have homega : Ordinal.omega0 ≤ (Order.succ ((2 : Cardinal.{0}) ^ lam)).ord := by
    rw [← Cardinal.ord_aleph0]
    exact Cardinal.ord_le_ord.mpr (aleph0_le_succ_two_power hlam)
  have hlt : ∀ k : Fin (n + 2),
      ((k : ℕ) : Ordinal.{0}) < (Order.succ ((2 : Cardinal.{0}) ^ lam)).ord :=
    fun k => lt_of_lt_of_le (Ordinal.natCast_lt_omega0 (k : ℕ)) homega
  exact ⟨G (OrderEmbedding.ofStrictMono
    (fun k => Ordinal.ToType.mk ⟨((k : ℕ) : Ordinal.{0}), hlt k⟩)
    (fun a b hab => Ordinal.ToType.mk.lt_iff_lt.mpr
      (Subtype.mk_lt_mk.mpr (by exact_mod_cast hab))))⟩

end CardinalHelpers

/-! ### The tuple-node EHMR tree skeleton

Nodes at level `β` are recorded-color assignments to prefix `(n+1)`-tuples
`(Fin (n+1) ↪o β.ToType) → C`; reps are chosen minima of successor sets by well-founded
recursion on the length, exactly as in `PairERGen` — only the node domain changes. -/

section TreeSkeleton

/-- A node at level `β`: the recorded colors at the prefix-position `(n+1)`-tuples of
`β.ToType`. -/
abbrev NodeAt (C : Type) (n : ℕ) (β : Ordinal.{0}) : Type :=
  (Fin (n + 1) ↪o β.ToType) → C

/-- Restrict a node to a shorter length `δ ≤ β`: precompose every position tuple with the
initial-segment embedding. -/
noncomputable def NodeAt.restrict {C : Type} {n : ℕ} {β : Ordinal.{0}} (h : NodeAt C n β)
    {δ : Ordinal.{0}} (hδβ : δ ≤ β) : NodeAt C n δ :=
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder δ.ToType (· < ·) := isWellOrder_lt
  fun τ => h (τ.trans (initialSegOfLe hδβ).toOrderEmbedding)

variable {lam : Cardinal.{0}} {C : Type} {n : ℕ}

/-- Restriction is transitive (initial segments compose). -/
theorem NodeAt.restrict_trans {β : Ordinal.{0}} (h : NodeAt C n β)
    {δ ε : Ordinal.{0}} (hδ : δ ≤ β) (hε : ε ≤ δ) :
    (h.restrict hδ).restrict hε = h.restrict (hε.trans hδ) := by
  have : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  have : IsWellOrder δ.ToType (· < ·) := isWellOrder_lt
  have : IsWellOrder ε.ToType (· < ·) := isWellOrder_lt
  funext τ
  change h ((τ.trans (initialSegOfLe hε).toOrderEmbedding).trans
        (initialSegOfLe hδ).toOrderEmbedding)
     = h (τ.trans (initialSegOfLe (hε.trans hδ)).toOrderEmbedding)
  refine congrArg h (DFunLike.ext _ _ fun k => ?_)
  exact initialSegOfLe_compose hε hδ (τ k)

/-- `NodeAt.restrict` at heterogeneously-equal lengths. -/
theorem NodeAt.restrict_heq {β : Ordinal.{0}} (h : NodeAt C n β)
    {δ₁ δ₂ : Ordinal.{0}} (hδ : δ₁ = δ₂) (h1 : δ₁ ≤ β) (h2 : δ₂ ≤ β) :
    HEq (h.restrict h1) (h.restrict h2) := by
  subst hδ; exact heq_of_eq rfl

/-- Level cardinality: for `β < (succ lam).ord` and `#C ≤ lam` the level (all length-`β`
tuple nodes) has cardinality `≤ 2 ^ lam`. -/
private theorem level_card_le (hlam : Cardinal.aleph0 ≤ lam) (hC : Cardinal.mk C ≤ lam)
    {β : Ordinal.{0}} (hβ : β < (Order.succ lam).ord) :
    Cardinal.mk (NodeAt C n β) ≤ (2 : Cardinal.{0}) ^ lam :=
  mk_tupleNode_le hC hlam n hβ

variable [Nonempty C]

/-- The color of the tuple `r ⌢ y` when `r` is strictly monotone and bounded by `y`
(junk otherwise). Factoring the tree's recorded colors through `colorAbove` makes every
"the color depends only on the underlying points" step a `congrArg`. -/
private noncomputable def colorAbove (G : (Fin (n + 2) ↪o Source lam) → C) (y : Source lam)
    (r : Fin (n + 1) → Source lam) : C := by
  classical
  exact if h : StrictMono r ∧ ∀ k, r k < y then
    G (appendLastOE (OrderEmbedding.ofStrictMono r h.1) y h.2)
  else Classical.arbitrary C

/-- On an actual bounded order embedding, `colorAbove` computes the appended color. -/
private theorem colorAbove_eq (G : (Fin (n + 2) ↪o Source lam) → C) {y : Source lam}
    (remb : Fin (n + 1) ↪o Source lam) (hlt : ∀ k, remb k < y) :
    colorAbove G y ⇑remb = G (appendLastOE remb y hlt) := by
  classical
  have hpos : StrictMono (⇑remb) ∧ ∀ k, remb k < y := ⟨remb.strictMono, hlt⟩
  rw [colorAbove, dite_eq_left hpos]
  exact congrArg G (appendLastOE_congr (fun k => rfl) rfl _ _)

/-- The successor set `S(h)` of a node with reps `rep`: points `y` strictly above every
rep whose appended tuple colors all match the recorded ones. -/
private def nodeFiber (G : (Fin (n + 2) ↪o Source lam) → C) {β : Ordinal.{0}}
    (rep : β.ToType → Source lam) (col : NodeAt C n β) : Set (Source lam) :=
  { y | (∀ x : β.ToType, rep x < y) ∧
        ∀ τ : Fin (n + 1) ↪o β.ToType, colorAbove G y (fun k => rep (τ k)) = col τ }

/-- **Chosen representative** `s(h) = min S(h)` — the `<`-least element of the successor
set, by well-founded recursion on the node length: the rep at position `x : β.ToType` is
the chosen rep of the restriction to `typein x`. Junk default on dead nodes. -/
noncomputable def nodeChosen (G : (Fin (n + 2) ↪o Source lam) → C)
    (β : Ordinal.{0}) (h : NodeAt C n β) : Source lam := by
  classical
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  exact
    if hne : (nodeFiber G
        (fun x => nodeChosen G (Ordinal.typein (· < ·) x)
          (h.restrict (le_of_lt (by
            have hh := Ordinal.typein_lt_type (· < · : β.ToType → β.ToType → Prop) x
            rwa [Ordinal.type_toType] at hh)))) h).Nonempty then
      (IsWellFounded.wf : WellFounded (· < · : Source lam → Source lam → Prop)).min _ hne
    else
      Classical.arbitrary (Source lam)
termination_by β
decreasing_by
  all_goals
    have : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    have hh := Ordinal.typein_lt_type (· < · : β.ToType → β.ToType → Prop) x
    rwa [Ordinal.type_toType] at hh

/-- The reps along a node: the chosen rep of the restriction to each position. -/
private noncomputable def nodeRep (G : (Fin (n + 2) ↪o Source lam) → C) {β : Ordinal.{0}}
    (h : NodeAt C n β) : β.ToType → Source lam := by
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  exact fun x => nodeChosen G (Ordinal.typein (· < ·) x)
    (h.restrict (le_of_lt (by
      have hh := Ordinal.typein_lt_type (· < · : β.ToType → β.ToType → Prop) x
      rwa [Ordinal.type_toType] at hh)))

/-- `S(h)` as a set, via `nodeRep`. -/
def nodeS (G : (Fin (n + 2) ↪o Source lam) → C) {β : Ordinal.{0}} (h : NodeAt C n β) :
    Set (Source lam) := nodeFiber G (nodeRep G h) h

/-- A node is **live** iff its successor set is nonempty. -/
def nodeLive (G : (Fin (n + 2) ↪o Source lam) → C) {β : Ordinal.{0}}
    (h : NodeAt C n β) : Prop := (nodeS G h).Nonempty

/-- The used/remainder set `R(h)`: `{s(h)}` on live nodes, else `∅`. -/
noncomputable def nodeR (G : (Fin (n + 2) ↪o Source lam) → C) {β : Ordinal.{0}}
    (h : NodeAt C n β) : Set (Source lam) := by
  classical
  exact if nodeLive G h then {nodeChosen G β h} else ∅

/-- `R(h)` is a subsingleton (it is `{s(h)}` or `∅`). -/
private theorem nodeR_subsingleton (G : (Fin (n + 2) ↪o Source lam) → C) {β : Ordinal.{0}}
    (h : NodeAt C n β) : (nodeR G h).Subsingleton := by
  classical
  rw [nodeR]
  split_ifs with hlive
  · exact Set.subsingleton_singleton
  · exact Set.subsingleton_empty

/-- On a live node, the chosen rep lies in the successor set. -/
private theorem nodeChosen_mem (G : (Fin (n + 2) ↪o Source lam) → C) {β : Ordinal.{0}}
    (h : NodeAt C n β) (hlive : nodeLive G h) :
    nodeChosen G β h ∈ nodeS G h := by
  classical
  have : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  have hcond : (nodeFiber G
      (fun x => nodeChosen G (Ordinal.typein (· < ·) x)
        (h.restrict (le_of_lt (by
          have hh := Ordinal.typein_lt_type (· < · : β.ToType → β.ToType → Prop) x
          rwa [Ordinal.type_toType] at hh)))) h).Nonempty := hlive
  rw [nodeChosen, dite_eq_left hcond]
  exact WellFounded.min_mem _ _ hcond

/-- On a live node, `nodeChosen` is exactly the well-order minimum of the successor set. -/
private theorem nodeChosen_eq_min (G : (Fin (n + 2) ↪o Source lam) → C) {β : Ordinal.{0}}
    (h : NodeAt C n β) (hlive : nodeLive G h) :
    nodeChosen G β h =
      (IsWellFounded.wf : WellFounded (· < · : Source lam → Source lam → Prop)).min
        (nodeS G h) hlive := by
  classical
  have : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  have hcond : (nodeFiber G
      (fun x => nodeChosen G (Ordinal.typein (· < ·) x)
        (h.restrict (le_of_lt (by
          have hh := Ordinal.typein_lt_type (· < · : β.ToType → β.ToType → Prop) x
          rwa [Ordinal.type_toType] at hh)))) h).Nonempty := hlive
  rw [nodeChosen, dite_eq_left hcond]
  rfl

/-- The chosen min is `≤` every successor. -/
private theorem nodeChosen_le_of_mem (G : (Fin (n + 2) ↪o Source lam) → C) {β : Ordinal.{0}}
    (h : NodeAt C n β) {y : Source lam} (hy : y ∈ nodeS G h) :
    nodeChosen G β h ≤ y := by
  have hlive : nodeLive G h := ⟨y, hy⟩
  rw [nodeChosen_eq_min G h hlive]
  exact not_lt.mp (WellFounded.not_lt_min _ _ hy)

/-- `nodeChosen` transported along a level equality. -/
private theorem nodeChosen_congr (G : (Fin (n + 2) ↪o Source lam) → C) {δ₁ δ₂ : Ordinal.{0}}
    (hδ : δ₁ = δ₂) {n₁ : NodeAt C n δ₁} {n₂ : NodeAt C n δ₂} (hn : HEq n₁ n₂) :
    nodeChosen G δ₁ n₁ = nodeChosen G δ₂ n₂ := by
  subst hδ
  rw [eq_of_heq hn]

/-- Level smallness: for `β < (succ lam).ord` there are `≤ 2 ^ lam` live length-`β`
tuple nodes. -/
private theorem live_level_small (hlam : Cardinal.aleph0 ≤ lam) (hC : Cardinal.mk C ≤ lam)
    (G : (Fin (n + 2) ↪o Source lam) → C) {β : Ordinal.{0}}
    (hβ : β < (Order.succ lam).ord) :
    Cardinal.mk {h : NodeAt C n β // nodeLive G h} ≤ (2 : Cardinal.{0}) ^ lam :=
  (Cardinal.mk_subtype_le _).trans (level_card_le hlam hC hβ)

end TreeSkeleton

/-! ### Coverage — the canonical `y`-path

As in `PairERGen`, the whole `y`-path is defined at once: `yNode G y β` is the length-`β`
node recording, at each prefix tuple `τ`, the color of `y` appended above the chosen reps
of the path so far (junk once a rep is no longer `< y`, or the reps fail monotonicity —
both absorbed by `colorAbove`). -/

section YPath

variable {lam : Cardinal.{0}} {C : Type} {n : ℕ} [Nonempty C]

/-- The chosen rep of the canonical `y`-path at level `γ`, by well-founded recursion:
the chosen min of the node recording `colorAbove` of `y` over the earlier path reps. -/
noncomputable def yRep (G : (Fin (n + 2) ↪o Source lam) → C) (y : Source lam)
    (γ : Ordinal.{0}) : Source lam := by
  classical
  haveI : IsWellOrder γ.ToType (· < ·) := isWellOrder_lt
  exact nodeChosen G γ (fun τ =>
    colorAbove G y (fun k => yRep G y (Ordinal.typein (· < ·) (τ k))))
termination_by γ
decreasing_by
  all_goals
    have : IsWellOrder γ.ToType (· < ·) := isWellOrder_lt
    exact lt_of_lt_of_eq (Ordinal.typein_lt_type _ _) (Ordinal.type_toType γ)

/-- The canonical `y`-path node of length `β` (a *plain* def over `yRep`). -/
noncomputable def yNode (G : (Fin (n + 2) ↪o Source lam) → C) (y : Source lam)
    (β : Ordinal.{0}) : NodeAt C n β := by
  classical
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  exact fun τ => colorAbove G y (fun k => yRep G y (Ordinal.typein (· < ·) (τ k)))

/-- The defining fixpoint equation: `yRep` is the chosen min of `yNode`. -/
theorem yRep_eq (G : (Fin (n + 2) ↪o Source lam) → C) (y : Source lam)
    (γ : Ordinal.{0}) :
    yRep G y γ = nodeChosen G γ (yNode G y γ) := by
  classical
  conv_lhs => rw [yRep]
  rfl

/-- Restriction-coherence: every restriction of a `yNode` is again the `yNode` of that
length (`typein` is preserved by the initial-segment embedding). -/
theorem yNode_restrict (G : (Fin (n + 2) ↪o Source lam) → C) (y : Source lam)
    {β δ : Ordinal.{0}} (hδ : δ ≤ β) :
    (yNode G y β).restrict hδ = yNode G y δ := by
  classical
  have : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  have : IsWellOrder δ.ToType (· < ·) := isWellOrder_lt
  funext τ
  change colorAbove G y (fun k => yRep G y (Ordinal.typein (· < ·)
        ((τ.trans (initialSegOfLe hδ).toOrderEmbedding) k)))
     = colorAbove G y (fun k => yRep G y (Ordinal.typein (· < ·) (τ k)))
  refine congrArg (colorAbove G y) (funext fun k => ?_)
  exact congrArg (yRep G y) (Ordinal.typein_apply (initialSegOfLe hδ) (τ k))

/-- The reps of `yNode G y β` are exactly `yRep G y (typein x)`. -/
private theorem nodeRep_yNode (G : (Fin (n + 2) ↪o Source lam) → C) (y : Source lam)
    {β : Ordinal.{0}} [IsWellOrder β.ToType (· < ·)] (x : β.ToType) :
    nodeRep G (yNode G y β) x = yRep G y (Ordinal.typein (· < ·) x) := by
  classical
  have hlt : Ordinal.typein (· < ·) x < β :=
    lt_of_lt_of_eq (Ordinal.typein_lt_type (· < ·) x) (Ordinal.type_toType β)
  change nodeChosen G (Ordinal.typein (· < ·) x) ((yNode G y β).restrict (le_of_lt hlt))
     = yRep G y (Ordinal.typein (· < ·) x)
  rw [yRep_eq, yNode_restrict]

/-- Liveness criterion: if every earlier rep stays `< y`, then `y` is a successor of
`yNode G y β` (so the node is live and `y ∈ S`). -/
theorem yNode_mem_of (G : (Fin (n + 2) ↪o Source lam) → C) (y : Source lam)
    {β : Ordinal.{0}} (hbelow : ∀ δ : Ordinal.{0}, δ < β → yRep G y δ < y) :
    y ∈ nodeS G (yNode G y β) := by
  classical
  have : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  constructor
  · intro x
    rw [nodeRep_yNode]
    exact hbelow _ (lt_of_lt_of_eq (Ordinal.typein_lt_type (· < ·) x)
      (Ordinal.type_toType β))
  · intro τ
    have hfun : (fun k => nodeRep G (yNode G y β) (τ k))
        = fun k => yRep G y (Ordinal.typein (· < ·) (τ k)) :=
      funext fun k => nodeRep_yNode G y (τ k)
    rw [hfun]
    rfl

/-- As long as every rep below `γ₂` stays `< y`, the canonical reps strictly increase. -/
theorem yRep_strictMono (G : (Fin (n + 2) ↪o Source lam) → C) (y : Source lam)
    {γ₁ γ₂ : Ordinal.{0}} (h12 : γ₁ < γ₂)
    (hlive : ∀ δ : Ordinal.{0}, δ < γ₂ → yRep G y δ < y) :
    yRep G y γ₁ < yRep G y γ₂ := by
  classical
  have : IsWellOrder γ₂.ToType (· < ·) := isWellOrder_lt
  have hlive2 : nodeLive G (yNode G y γ₂) := ⟨y, yNode_mem_of G y hlive⟩
  have hγ₁ : γ₁ < Ordinal.type (· < · : γ₂.ToType → γ₂.ToType → Prop) := by
    rw [Ordinal.type_toType]; exact h12
  have hlt := (nodeChosen_mem G (yNode G y γ₂) hlive2).1 (Ordinal.enum (· < ·) ⟨γ₁, hγ₁⟩)
  rw [nodeRep_yNode G y, Ordinal.typein_enum] at hlt
  rwa [← yRep_eq] at hlt

/-- **Stopping.** The canonical `y`-path stops: there is a *least* level `γ` where the
chosen rep reaches `y`, with all earlier reps strictly below `y` (pure
well-foundedness, as in `PairERGen`). -/
theorem exists_yRep_ge (G : (Fin (n + 2) ↪o Source lam) → C) (y : Source lam) :
    ∃ γ : Ordinal.{0}, y ≤ yRep G y γ ∧ ∀ δ : Ordinal.{0}, δ < γ → yRep G y δ < y := by
  classical
  have hexists : ∃ γ : Ordinal.{0}, y ≤ yRep G y γ := by
    by_contra hcon
    push Not at hcon
    have : IsWellOrder (Source lam) (· < ·) := isWellOrder_lt
    have hmono : StrictMono (yRep G y) := fun a b hab =>
      yRep_strictMono G y hab (fun δ _ => hcon δ)
    have hmono_g : StrictMono (fun γ => Ordinal.typein (· < ·) (yRep G y γ)) :=
      fun a b hab => (Ordinal.typein_lt_typein (· < ·)).mpr (hmono hab)
    have hself : ∀ a : Ordinal.{0}, a ≤ Ordinal.typein (· < ·) (yRep G y a) := by
      intro a
      induction a using WellFoundedLT.induction with
      | _ a ih =>
        by_contra hlt
        push Not at hlt
        exact absurd ((ih _ hlt).trans_lt (hmono_g hlt)) (lt_irrefl _)
    have hΩ := hself (Ordinal.type (· < · : Source lam → Source lam → Prop))
    exact absurd (hΩ.trans_lt (Ordinal.typein_lt_type (· < ·) _)) (lt_irrefl _)
  obtain ⟨γ₀, hγ₀⟩ := hexists
  refine ⟨Ordinal.lt_wf.min {γ | y ≤ yRep G y γ} ⟨γ₀, hγ₀⟩, ?_, ?_⟩
  · exact Ordinal.lt_wf.min_mem {γ | y ≤ yRep G y γ} ⟨γ₀, hγ₀⟩
  · intro δ hδ
    exact not_le.mp (fun ha => Ordinal.lt_wf.not_lt_min {γ | y ≤ yRep G y γ} ha hδ)

/-- **Coverage.** Every source element is the chosen representative of some node
(`y ∈ R(h)`), at the least level where the canonical `y`-path reaches `y`. -/
theorem exists_node_choosing_source (G : (Fin (n + 2) ↪o Source lam) → C)
    (y : Source lam) :
    ∃ (β : Ordinal.{0}) (h : NodeAt C n β), y ∈ nodeR G h := by
  classical
  obtain ⟨γ, hge, hbelow⟩ := exists_yRep_ge G y
  have hmem : y ∈ nodeS G (yNode G y γ) := yNode_mem_of G y hbelow
  have hle : yRep G y γ ≤ y := by
    rw [yRep_eq]; exact nodeChosen_le_of_mem G (yNode G y γ) hmem
  have heq : y = nodeChosen G γ (yNode G y γ) := by
    rw [← yRep_eq]; exact le_antisymm hge hle
  have hlive : nodeLive G (yNode G y γ) := ⟨y, hmem⟩
  refine ⟨γ, yNode G y γ, ?_⟩
  rw [nodeR, ite_eq_left hlive, Set.mem_singleton_iff]
  exact heq

end YPath

/-! ### End-homogeneity of live nodes (EHMR fact (8), tuple form) -/

section EndHomogeneity

variable {lam : Cardinal.{0}} {C : Type} {n : ℕ} [Nonempty C]

/-- The reps of a restriction agree with the parent's reps at the lifted positions. -/
private theorem nodeRep_restrict (G : (Fin (n + 2) ↪o Source lam) → C) {β : Ordinal.{0}}
    (h : NodeAt C n β) {δ : Ordinal.{0}} (hδ : δ ≤ β) (x : δ.ToType) :
    nodeRep G (h.restrict hδ) x =
      nodeRep G h ((initialSegOfLe hδ).toOrderEmbedding x) := by
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
  change nodeChosen G (Ordinal.typein (· < ·) x) ((h.restrict hδ).restrict (le_of_lt hx_lt))
     = nodeChosen G (Ordinal.typein (· < ·) lx) (h.restrict (le_of_lt hlx_lt))
  refine nodeChosen_congr G htx.symm ?_
  rw [NodeAt.restrict_trans h hδ (le_of_lt hx_lt)]
  exact NodeAt.restrict_heq h htx.symm ((le_of_lt hx_lt).trans hδ) (le_of_lt hlx_lt)

/-- A restriction of a live node is live (the same witness serves: the constraints of the
restriction are a subset of the parent's, transported along `nodeRep_restrict`). -/
private theorem nodeLive_restrict (G : (Fin (n + 2) ↪o Source lam) → C) {β : Ordinal.{0}}
    {h : NodeAt C n β} (hlive : nodeLive G h) {δ : Ordinal.{0}} (hδ : δ ≤ β) :
    nodeLive G (h.restrict hδ) := by
  classical
  have : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  have : IsWellOrder δ.ToType (· < ·) := isWellOrder_lt
  obtain ⟨y, hy1, hy2⟩ := hlive
  refine ⟨y, ?_, ?_⟩
  · intro x
    rw [nodeRep_restrict G h hδ x]
    exact hy1 _
  · intro τ
    have hfun : (fun k => nodeRep G (h.restrict hδ) (τ k))
        = fun k => nodeRep G h
            ((τ.trans (initialSegOfLe hδ).toOrderEmbedding) k) :=
      funext fun k => nodeRep_restrict G h hδ (τ k)
    rw [hfun]
    exact hy2 (τ.trans (initialSegOfLe hδ).toOrderEmbedding)

/-- Lift a point strictly below `x₂` into the initial segment of length `typein x₂`. -/
private lemma exists_seg_preimage {β : Ordinal.{0}} [IsWellOrder β.ToType (· < ·)]
    {x₁ x₂ : β.ToType} (hx : x₁ < x₂) (hx₂lt : Ordinal.typein (· < ·) x₂ < β) :
    ∃ z : (Ordinal.typein (· < ·) x₂).ToType,
      (initialSegOfLe (le_of_lt hx₂lt)).toOrderEmbedding z = x₁ := by
  have : IsWellOrder (Ordinal.typein (· < · : β.ToType → β.ToType → Prop) x₂).ToType
      (· < ·) := isWellOrder_lt
  have hx₁ty : Ordinal.typein (· < ·) x₁ <
      Ordinal.type (· < · : (Ordinal.typein (· < ·) x₂).ToType →
        (Ordinal.typein (· < ·) x₂).ToType → Prop) := by
    rw [Ordinal.type_toType]
    exact (Ordinal.typein_lt_typein (· < ·)).mpr hx
  set z := Ordinal.enum (· < ·) ⟨Ordinal.typein (· < ·) x₁, hx₁ty⟩ with hz_def
  refine ⟨z, (Ordinal.typein_inj (· < ·)).mp ?_⟩
  have e1 : Ordinal.typein (· < ·)
        ((initialSegOfLe (le_of_lt hx₂lt)).toOrderEmbedding z) =
      Ordinal.typein (· < ·) z :=
    Ordinal.typein_apply (initialSegOfLe (le_of_lt hx₂lt)) z
  have e2 : Ordinal.typein (· < ·) z = Ordinal.typein (· < ·) x₁ := by
    rw [hz_def]; exact Ordinal.typein_enum (· < ·) _
  rw [e1, e2]

/-- Lift a tuple strictly below `x₂` into the initial segment of length `typein x₂`. -/
private lemma exists_seg_tuple {β : Ordinal.{0}} [IsWellOrder β.ToType (· < ·)]
    (τ : Fin (n + 1) ↪o β.ToType) {x₂ : β.ToType} (hx : ∀ k, τ k < x₂)
    (hx₂lt : Ordinal.typein (· < ·) x₂ < β) :
    ∃ σ : Fin (n + 1) ↪o (Ordinal.typein (· < ·) x₂).ToType,
      ∀ k, (initialSegOfLe (le_of_lt hx₂lt)).toOrderEmbedding (σ k) = τ k := by
  choose z hz using fun k => exists_seg_preimage (hx k) hx₂lt
  have hmono : StrictMono z := by
    intro a b hab
    have hτ : τ a < τ b := τ.strictMono hab
    rw [← hz a, ← hz b] at hτ
    exact (initialSegOfLe (le_of_lt hx₂lt)).toOrderEmbedding.lt_iff_lt.mp hτ
  exact ⟨OrderEmbedding.ofStrictMono z hmono, hz⟩

/-- **End-homogeneity, strict monotonicity.** On a live node the chosen reps strictly
increase. -/
private theorem nodeRep_strictMono (G : (Fin (n + 2) ↪o Source lam) → C) {β : Ordinal.{0}}
    {h : NodeAt C n β} (hlive : nodeLive G h) {x₁ x₂ : β.ToType} (hx : x₁ < x₂) :
    nodeRep G h x₁ < nodeRep G h x₂ := by
  classical
  have : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  have hx₂lt : Ordinal.typein (· < ·) x₂ < β :=
    lt_of_lt_of_eq (Ordinal.typein_lt_type (· < ·) x₂) (Ordinal.type_toType β)
  have h₂live : nodeLive G (h.restrict (le_of_lt hx₂lt)) :=
    nodeLive_restrict G hlive (le_of_lt hx₂lt)
  obtain ⟨z, hz⟩ := exists_seg_preimage hx hx₂lt
  have hlt := (nodeChosen_mem G (h.restrict (le_of_lt hx₂lt)) h₂live).1 z
  rw [nodeRep_restrict G h (le_of_lt hx₂lt) z, hz] at hlt
  exact hlt

/-- **End-homogeneity, EHMR fact (8) in tuple form.** On a live node, the recorded color
at the prefix tuple `τ` is the actual appended color of `{rep ∘ τ, rep x₂}` for any
position `x₂` strictly above all of `τ`. -/
private theorem node_fact8 (G : (Fin (n + 2) ↪o Source lam) → C) {β : Ordinal.{0}}
    {h : NodeAt C n β} (hlive : nodeLive G h) {τ : Fin (n + 1) ↪o β.ToType}
    {x₂ : β.ToType} (hx : ∀ k, τ k < x₂) :
    colorAbove G (nodeRep G h x₂) (fun k => nodeRep G h (τ k)) = h τ := by
  classical
  have : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  have hx₂lt : Ordinal.typein (· < ·) x₂ < β :=
    lt_of_lt_of_eq (Ordinal.typein_lt_type (· < ·) x₂) (Ordinal.type_toType β)
  have h₂live : nodeLive G (h.restrict (le_of_lt hx₂lt)) :=
    nodeLive_restrict G hlive (le_of_lt hx₂lt)
  obtain ⟨σ, hσ⟩ := exists_seg_tuple τ hx hx₂lt
  have hcol := (nodeChosen_mem G (h.restrict (le_of_lt hx₂lt)) h₂live).2 σ
  have hreps : (fun k => nodeRep G (h.restrict (le_of_lt hx₂lt)) (σ k))
      = fun k => nodeRep G h (τ k) := by
    funext k
    rw [nodeRep_restrict G h (le_of_lt hx₂lt) (σ k), hσ k]
  have hcolval : (h.restrict (le_of_lt hx₂lt)) σ = h τ := by
    change h (σ.trans (initialSegOfLe (le_of_lt hx₂lt)).toOrderEmbedding) = h τ
    exact congrArg h (DFunLike.ext _ _ hσ)
  rw [hreps, hcolval] at hcol
  exact hcol

end EndHomogeneity

/-! ### Branch extraction from a high live node

The counting core: `succ (2 ^ lam)`-many live nodes (coverage) cannot all sit at levels
`< (succ lam).ord` (each such level has `≤ 2 ^ lam` tuple nodes and there are only
`succ lam` levels), so some live node has length `≥ (succ lam).ord`; reading it off along
the initial segment yields a `Branch`. -/

section BranchExtraction

variable {lam : Cardinal.{0}} {C : Type} {n : ℕ} [Nonempty C]

/-- **`Branch G`**: a strictly increasing `(succ lam).ord.ToType`-indexed family of reps
together with the recorded tuple colors — end-homogeneity holds along it: the appended
color of `{rep ∘ τ, rep q}` is `nodeFn τ` for every position tuple `τ` and every level `q`
strictly above all of `τ`. Produced by `tree_has_branch`. -/
structure Branch (G : (Fin (n + 2) ↪o Source lam) → C) where
  /-- The rep at each position of `(succ lam).ord.ToType`. -/
  rep : (Order.succ lam).ord.ToType → Source lam
  /-- The reps strictly increase. -/
  rep_strictMono : StrictMono rep
  /-- The recorded color at each prefix position tuple. -/
  nodeFn : (Fin (n + 1) ↪o (Order.succ lam).ord.ToType) → C
  /-- End-homogeneity along the branch (EHMR fact (8) read off the live node). -/
  coloring : ∀ (τ : Fin (n + 1) ↪o (Order.succ lam).ord.ToType)
      (q : (Order.succ lam).ord.ToType), (∀ k, τ k < q) →
    colorAbove G (rep q) (fun k => rep (τ k)) = nodeFn τ

/-- A live node of length `≥ (succ lam).ord` *is* a `Branch`: its reps (read off along
the initial-segment embedding) strictly increase (`nodeRep_strictMono`) and satisfy fact
(8) (`node_fact8`). -/
private noncomputable def branchOfLive (G : (Fin (n + 2) ↪o Source lam) → C) {β : Ordinal.{0}}
    (h : NodeAt C n β) (hβ : (Order.succ lam).ord ≤ β) (hlive : nodeLive G h) :
    Branch G :=
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder (Order.succ lam).ord.ToType (· < ·) := isWellOrder_lt
  { rep := fun z => nodeRep G h ((initialSegOfLe hβ).toOrderEmbedding z)
    rep_strictMono := fun _ _ hab => nodeRep_strictMono G hlive
      ((initialSegOfLe hβ).toOrderEmbedding.strictMono hab)
    nodeFn := fun τ => h (τ.trans (initialSegOfLe hβ).toOrderEmbedding)
    coloring := fun τ q hq =>
      node_fact8 G hlive
        (τ := τ.trans (initialSegOfLe hβ).toOrderEmbedding)
        (x₂ := (initialSegOfLe hβ).toOrderEmbedding q)
        (fun k => (initialSegOfLe hβ).toOrderEmbedding.strictMono (hq k)) }

/-- **[THE COUNTING CORE]** Some live node has length `≥ (succ lam).ord`. Otherwise the
coverage map injects `Source lam` (size `succ (2 ^ lam)`) into the index
`Σ b : (succ lam).ord.ToType, {live nodes of length typein b}` of size
`≤ succ lam * 2 ^ lam = 2 ^ lam`, contradiction. -/
theorem exists_live_node_ge (hlam : Cardinal.aleph0 ≤ lam)
    (hC : Cardinal.mk C ≤ lam) (G : (Fin (n + 2) ↪o Source lam) → C) :
    ∃ (β : Ordinal.{0}) (h : NodeAt C n β),
      (Order.succ lam).ord ≤ β ∧ nodeLive G h := by
  classical
  by_contra hcon
  push Not at hcon
  have : IsWellOrder (Order.succ lam).ord.ToType (· < ·) := isWellOrder_lt
  have hlower : Order.succ ((2 : Cardinal.{0}) ^ lam) ≤
      Cardinal.mk (Σ b : (Order.succ lam).ord.ToType,
        { h : NodeAt C n (Ordinal.typein (· < ·) b) // nodeLive G h }) := by
    apply ehmr_partitionTree_card_lower (R := fun nd => nodeR G nd.2.1)
    · intro y
      obtain ⟨β_y, h_y, hy⟩ := exists_node_choosing_source G y
      have hlive_y : nodeLive G h_y := by
        by_contra hnl
        rw [nodeR, ite_eq_right hnl] at hy
        exact (Set.mem_empty_iff_false y).mp hy
      have hβ_lt : β_y < (Order.succ lam).ord := by
        by_contra hge
        exact hcon β_y h_y (not_lt.mp hge) hlive_y
      have hβ_ty : β_y < Ordinal.type (· < · : (Order.succ lam).ord.ToType →
          (Order.succ lam).ord.ToType → Prop) := by
        rw [Ordinal.type_toType]; exact hβ_lt
      set b_y := Ordinal.enum (· < ·) ⟨β_y, hβ_ty⟩ with hb_def
      have htb : Ordinal.typein (· < ·) b_y = β_y := by rw [hb_def, Ordinal.typein_enum]
      have key : ∃ (h' : NodeAt C n (Ordinal.typein (· < ·) b_y))
          (_ : nodeLive G h'), y ∈ nodeR G h' := by
        rw [htb]; exact ⟨h_y, hlive_y, hy⟩
      obtain ⟨h', hl', hy'⟩ := key
      exact ⟨⟨b_y, h', hl'⟩, hy'⟩
    · intro nd
      exact nodeR_subsingleton G nd.2.1
  have hupper : Cardinal.mk (Σ b : (Order.succ lam).ord.ToType,
      { h : NodeAt C n (Ordinal.typein (· < ·) b) // nodeLive G h }) ≤
      (2 : Cardinal.{0}) ^ lam := by
    rw [Cardinal.mk_sigma]
    calc Cardinal.sum (fun b => Cardinal.mk
            { h : NodeAt C n (Ordinal.typein (· < ·) b) // nodeLive G h })
        ≤ Cardinal.sum (fun _ : (Order.succ lam).ord.ToType => (2 : Cardinal.{0}) ^ lam) :=
          Cardinal.sum_le_sum _ _ (fun b => live_level_small hlam hC G
            (lt_of_lt_of_eq (Ordinal.typein_lt_type (· < ·) b) (Ordinal.type_toType _)))
      _ = Cardinal.mk (Order.succ lam).ord.ToType * (2 : Cardinal.{0}) ^ lam :=
          Cardinal.sum_const' _ _
      _ = Order.succ lam * (2 : Cardinal.{0}) ^ lam := by rw [Cardinal.mk_ord_toType]
      _ = (2 : Cardinal.{0}) ^ lam := succ_mul_two_power hlam
  exact absurd (hlower.trans hupper)
    (not_le.mpr (Order.lt_succ ((2 : Cardinal.{0}) ^ lam)))

/-- **Branch-length.** The canonical tuple partition tree for `G` has a branch of length
`(succ lam).ord`. -/
private theorem tree_has_branch (hlam : Cardinal.aleph0 ≤ lam) (hC : Cardinal.mk C ≤ lam)
    (G : (Fin (n + 2) ↪o Source lam) → C) :
    Nonempty (Branch G) := by
  obtain ⟨β, h, hβ, hlive⟩ := exists_live_node_ge hlam hC G
  exact ⟨branchOfLive G h hβ hlive⟩

end BranchExtraction

/-! ### The endgame: end-homogeneity read directly off the branch -/

section Endgame

variable {lam : Cardinal.{0}} {C : Type} {n : ℕ}

/-- **[CONCRETE HEADLINE]** End-homogenization over `Source lam`: there is a
`(succ lam).ord`-indexed suborder on which the color of `s ⌢ x` depends only on the
prefix tuple `s` — both branch-coherence instances at the position tuple of `s` give the
recorded `nodeFn` value. -/
private theorem exists_endHomogeneous (lam : Cardinal.{0}) (hlam : Cardinal.aleph0 ≤ lam)
    {C : Type} (hC : Cardinal.mk C ≤ lam) (n : ℕ)
    (G : (Fin (n + 2) ↪o Source lam) → C) :
    ∃ f : (Order.succ lam).ord.ToType ↪o Source lam,
      ∀ (s : Fin (n + 1) ↪o Source lam) (x y : Source lam)
        (_ : ∀ k, s k ∈ Set.range f) (_ : x ∈ Set.range f) (_ : y ∈ Set.range f)
        (hx : ∀ k, s k < x) (hy : ∀ k, s k < y),
        G (appendLastOE s x hx) = G (appendLastOE s y hy) := by
  have : Nonempty C := nonempty_color_tuple hlam G
  obtain ⟨B⟩ := tree_has_branch hlam hC G
  refine ⟨OrderEmbedding.ofStrictMono B.rep B.rep_strictMono, ?_⟩
  intro s x y hs hx_mem hy_mem hx hy
  choose p hp using hs
  obtain ⟨q, hq⟩ := hx_mem
  obtain ⟨q', hq'⟩ := hy_mem
  have hq₀ : B.rep q = x := hq
  have hq'₀ : B.rep q' = y := hq'
  have hpmono : StrictMono p := by
    intro a b hab
    have : B.rep (p a) < B.rep (p b) := by
      rw [show B.rep (p a) = s a from hp a, show B.rep (p b) = s b from hp b]
      exact s.strictMono hab
    exact B.rep_strictMono.lt_iff_lt.mp this
  have hτq : ∀ k, (OrderEmbedding.ofStrictMono p hpmono) k < q := by
    intro k
    have : B.rep (p k) < B.rep q := by
      rw [show B.rep (p k) = s k from hp k, hq₀]
      exact hx k
    exact B.rep_strictMono.lt_iff_lt.mp this
  have hτq' : ∀ k, (OrderEmbedding.ofStrictMono p hpmono) k < q' := by
    intro k
    have : B.rep (p k) < B.rep q' := by
      rw [show B.rep (p k) = s k from hp k, hq'₀]
      exact hy k
    exact B.rep_strictMono.lt_iff_lt.mp this
  have h1 := B.coloring (OrderEmbedding.ofStrictMono p hpmono) q hτq
  have h2 := B.coloring (OrderEmbedding.ofStrictMono p hpmono) q' hτq'
  have hfun : (fun k => B.rep ((OrderEmbedding.ofStrictMono p hpmono) k)) = ⇑s :=
    funext fun k => hp k
  rw [hfun, hq₀] at h1
  rw [hfun, hq'₀] at h2
  calc G (appendLastOE s x hx) = colorAbove G x ⇑s := (colorAbove_eq G s hx).symm
    _ = B.nodeFn (OrderEmbedding.ofStrictMono p hpmono) := h1
    _ = colorAbove G y ⇑s := h2.symm
    _ = G (appendLastOE s y hy) := colorAbove_eq G s hy

/-- **[HEADLINE — end-homogeneous Erdős–Rado, abstract source]** For infinite `lam`, a
color type `C` with `#C ≤ lam`, and any well-ordered source `I` of cardinality
`≥ succ (2 ^ lam)`: every `(n+2)`-tuple coloring admits a `(succ lam).ord`-indexed
suborder on which the color of `s ⌢ x` is independent of the final point `x` above the
prefix tuple `s`. -/
theorem exists_endHomogeneous_of_large
    (lam : Cardinal.{0}) (hlam : Cardinal.aleph0 ≤ lam)
    {C : Type} (hC : Cardinal.mk C ≤ lam) (n : ℕ)
    {I : Type} [LinearOrder I] [WellFoundedLT I]
    (hI : Order.succ ((2 : Cardinal.{0}) ^ lam) ≤ Cardinal.mk I)
    (G : (Fin (n + 2) ↪o I) → C) :
    ∃ f : (Order.succ lam).ord.ToType ↪o I,
      ∀ (s : Fin (n + 1) ↪o I) (x y : I)
        (_ : ∀ k, s k ∈ Set.range f) (_ : x ∈ Set.range f) (_ : y ∈ Set.range f)
        (hx : ∀ k, s k < x) (hy : ∀ k, s k < y),
        G (appendLastOE s x hx) = G (appendLastOE s y hy) := by
  obtain ⟨e⟩ : Nonempty (Source lam ↪o I) := exists_ordToType_embedding_of_card_ge hI
  obtain ⟨f', hf'⟩ := exists_endHomogeneous lam hlam hC n (fun t => G (t.trans e))
  refine ⟨f'.trans e, ?_⟩
  intro s x y hs hx_mem hy_mem hx hy
  choose p hp using hs
  obtain ⟨q, hq⟩ := hx_mem
  obtain ⟨q', hq'⟩ := hy_mem
  have hpmono : StrictMono p := by
    intro a b hab
    have : (f'.trans e) (p a) < (f'.trans e) (p b) := by
      rw [hp a, hp b]; exact s.strictMono hab
    exact (OrderEmbedding.lt_iff_lt (f'.trans e)).mp this
  set s' : Fin (n + 1) ↪o Source lam := (OrderEmbedding.ofStrictMono p hpmono).trans f'
    with hs'_def
  have hs'e : ∀ k, e (s' k) = s k := fun k => hp k
  have hx' : ∀ k, s' k < f' q := by
    intro k
    have : e (s' k) < e (f' q) := by rw [hs'e k]; exact hq ▸ hx k
    exact e.lt_iff_lt.mp this
  have hy' : ∀ k, s' k < f' q' := by
    intro k
    have : e (s' k) < e (f' q') := by rw [hs'e k]; exact hq' ▸ hy k
    exact e.lt_iff_lt.mp this
  have key := hf' s' (f' q) (f' q') (fun k => ⟨p k, rfl⟩) ⟨q, rfl⟩ ⟨q', rfl⟩ hx' hy'
  have e1 : (fun t : Fin (n + 2) ↪o Source lam => G (t.trans e))
        (appendLastOE s' (f' q) hx') = G (appendLastOE s x hx) := by
    change G ((appendLastOE s' (f' q) hx').trans e) = G (appendLastOE s x hx)
    rw [appendLastOE_trans]
    exact congrArg G (appendLastOE_congr (fun k => hs'e k) hq _ _)
  have e2 : (fun t : Fin (n + 2) ↪o Source lam => G (t.trans e))
        (appendLastOE s' (f' q') hy') = G (appendLastOE s y hy) := by
    change G ((appendLastOE s' (f' q') hy').trans e) = G (appendLastOE s y hy)
    rw [appendLastOE_trans]
    exact congrArg G (appendLastOE_congr (fun k => hs'e k) hq' _ _)
  calc G (appendLastOE s x hx)
      = (fun t : Fin (n + 2) ↪o Source lam => G (t.trans e)) (appendLastOE s' (f' q) hx') :=
        e1.symm
    _ = (fun t : Fin (n + 2) ↪o Source lam => G (t.trans e)) (appendLastOE s' (f' q') hy') := key
    _ = G (appendLastOE s y hy) := e2

end Endgame

end FirstOrder.Combinatorics.EndHomogER
