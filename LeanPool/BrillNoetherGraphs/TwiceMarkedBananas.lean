/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.TwiceMarkedBananas.StatementVocabulary

/-!
# Easy-access reference: *Twice-Marked Banana Graphs*

This file is a single navigable index of every definition, lemma,
proposition, theorem, corollary, and mathematically-substantive remark in
*Twice-Marked Banana Graphs*, in the paper's own order, each paired with its
formalization in this library.

**How to read an entry.**

* Definitions, conjectures, purely qualitative remarks, and items with no
  Lean counterpart are recorded as plain comment blocks (`/- ... -/`): a
  quotation or close paraphrase of the paper's statement, its TeX `\label` and paper
  number, and (where one exists) the name of the Lean declaration that
  formalizes it. No new declaration is introduced for these — the existing
  name is the citable one.
* Every proved lemma/proposition/theorem/corollary gets a **statement
  theorem** here (named `Bananas.TwiceMarkedBananas.s<section>_...`). Its
  statement is written over the self-contained, Mathlib-only vocabulary of
  the namespace `TMB` in the imported vocabulary modules — the same vocabulary block, verbatim, as the
  statement-only audit copy `TwiceMarkedBananasStatements.lean` — and its
  proof crosses explicitly from that vocabulary to the repository's proved
  API through the bridge lemmas of the section *Bridges to the
  implementation library*. The docstring on each statement records the
  paper's statement, TeX label, and number. Where a checked statement uses
  a different or more explicit formulation, that is recorded explicitly —
  see `Bananas/FORMALIZATION_NOTES.md` for the corresponding formulation
  notes.
* When a result has genuinely no single assembled Lean statement (either
  because the mechanization deliberately avoids the paper's exact
  formulation, or because coverage is split across several files), the
  entry says so and points at the closest available pieces.
* Five further entries whose types intrinsically require implementation
  objects (concrete proof-carrying chain factors, the bridgeless class map,
  `AspPerm`) are kept at the end of the file as thin wrappers over the
  library vocabulary; they have no counterpart in the audit copy.

Source-text licensing is recorded in `THIRD_PARTY_NOTICES.md`. This file is a
reference index, not new mathematics: every statement below is a direct
restatement of an existing proof. Further paper-specific reference sources are
`Bananas/Sections/SectionFiveStatements.lean` and
`Bananas/FORMALIZATION_NOTES.md`.
-/

@[expose] public section

/-!
## Bridges to the implementation library

The imported `CoreVocabulary` and `StatementVocabulary` modules retain the
standalone statement vocabulary corresponding to `TwiceMarkedBananasStatements.lean`.  The declarations below are where
this file deliberately crosses into the implementation library: each
standalone notion is carried to its library counterpart by a conversion
function (`toLib`, `toLibBanana`, `toLibTM`, ...), and the vocabulary
predicates are shown to agree with the library predicates along those
conversions.  Almost every such agreement holds by unfolding definitions; the
one genuine difference is the standalone `rank`, which is defined by a
definite description and is identified with the library's rank through the
library's `rank_geq_iff`.
-/

namespace TMB

universe u v

/-! ### Graphs -/

/-- Cross a standalone graph into the library's graph type without changing
any data. -/
abbrev toLib (G : CFGraph.{u}) : _root_.CFGraph.{u} where
  V := G.V
  instDecidableEq := G.instDecidableEq
  instFintype := G.instFintype
  instNonempty := G.instNonempty
  edges := G.edges
  loopless := G.loopless

/-- Read a library graph as a standalone graph. -/
abbrev ofLib (G : _root_.CFGraph.{u}) : CFGraph.{u} where
  V := G.V
  instDecidableEq := G.instDecidableEq
  instFintype := G.instFintype
  instNonempty := G.instNonempty
  edges := G.edges
  loopless := G.loopless

/-! ### Rank -/

theorem rank_geq_toLib (G : CFGraph) (D : CFDiv G) (r : ℤ) :
    rankGeq G D r ↔ _root_.rankGeq (toLib G) D r := Iff.rfl

theorem rank_eq_toLib (G : CFGraph) (D : CFDiv G) (r : ℤ) :
    rankEq G D r ↔ _root_.rankEq (toLib G) D r := Iff.rfl

/-- The library rank satisfies the standalone exact-rank predicate. -/
theorem rank_eq_lib_rank (G : CFGraph) (D : CFDiv G) :
    rankEq G D (_root_.rank (toLib G) D) := by
  refine ⟨(_root_.rank_geq_iff (toLib G) D _).mpr (le_refl _), fun h => ?_⟩
  have := (_root_.rank_geq_iff (toLib G) D _).mp h
  omega

/-- The standalone rank is the library rank. -/
theorem rank_toLib (G : CFGraph) (D : CFDiv G) :
    rank G D = _root_.rank (toLib G) D := by
  have h : ∃ r, rankEq G D r := ⟨_root_.rank (toLib G) D, rank_eq_lib_rank G D⟩
  have hc : rankEq G D (Classical.choose h) := Classical.choose_spec h
  have h1 := (_root_.rank_geq_iff (toLib G) D (Classical.choose h)).mp hc.1
  have h2 : ¬ _root_.rank (toLib G) D ≥ Classical.choose h + 1 := fun hh =>
    hc.2 ((_root_.rank_geq_iff (toLib G) D (Classical.choose h + 1)).mpr hh)
  unfold rank
  rw [dif_pos h]
  omega

theorem bnExists_toLib (G : CFGraph) (r d : ℤ) :
    BNExists G r d ↔ Utilities.BNExists (toLib G) r d := by
  unfold BNExists Utilities.BNExists
  simp only [rank_toLib]
  all_goals exact Iff.rfl

theorem brillNoetherGeneral_toLib (G : CFGraph) :
    BrillNoetherGeneral G ↔ Bananas.BrillNoetherGeneral (toLib G) := by
  unfold BrillNoetherGeneral Bananas.BrillNoetherGeneral
  simp only [bnExists_toLib]
  all_goals exact Iff.rfl

theorem rankSupport_toLib (G : CFGraph) (D : CFDiv G) :
    rankSupport G D = Bananas.rankSupport (toLib G) D := by
  unfold rankSupport Bananas.rankSupport
  simp only [rank_toLib]
  all_goals rfl

/-! ### Twice-marked graphs -/

/-- Cross a standalone twice-marked graph into the library's bundle. -/
abbrev toLibTM (M : TwiceMarked) : Bananas.TwiceMarked where
  graph := toLib M.graph
  u := M.u
  v := M.v

theorem rankDelta_toLib (M : TwiceMarked) (D : CFDiv M.graph) :
    rankDelta M D = Bananas.rankDelta (toLibTM M) D := by
  unfold rankDelta Bananas.rankDelta
  simp only [rank_toLib]
  all_goals rfl

theorem submodular_toLib (M : TwiceMarked) (D : CFDiv M.graph) :
    Submodular M D ↔ Bananas.Submodular (toLibTM M) D := by
  unfold Submodular Bananas.Submodular
  simp only [rankDelta_toLib]
  all_goals exact Iff.rfl

theorem allSubmodular_toLib (M : TwiceMarked) :
    AllSubmodular M ↔ Bananas.AllSubmodular (toLibTM M) := by
  unfold AllSubmodular Bananas.AllSubmodular
  simp only [submodular_toLib]

theorem isTransmissionPermutation_toLib (M : TwiceMarked) (D : CFDiv M.graph)
    (τ : ℤ → ℤ) :
    IsTransmissionPermutation M D τ ↔
      Bananas.IsTransmissionPermutation (toLibTM M) D τ := by
  unfold IsTransmissionPermutation Bananas.IsTransmissionPermutation
  simp only [rankDelta_toLib]
  all_goals exact Iff.rfl

theorem kGeneralTransmission_toLib (M : TwiceMarked) (k : ℕ) :
    KGeneralTransmission M k ↔ Bananas.KGeneralTransmission (toLibTM M) k := by
  unfold KGeneralTransmission Bananas.KGeneralTransmission
  simp only [allSubmodular_toLib, isTransmissionPermutation_toLib]
  all_goals exact Iff.rfl

theorem nonRecurrent_toLib (M : TwiceMarked) (k : ℕ) :
    NonRecurrent M k ↔ Bananas.NonRecurrent (toLibTM M) k := by
  unfold NonRecurrent Bananas.NonRecurrent
  simp only [rank_toLib]
  all_goals exact Iff.rfl

theorem canonicalMarkedSupportsPairwiseDisjoint_toLib (M : TwiceMarked) (k : ℕ) :
    CanonicalMarkedSupportsPairwiseDisjoint M k ↔
      Bananas.CanonicalMarkedSupportsPairwiseDisjoint (toLibTM M) k := by
  unfold CanonicalMarkedSupportsPairwiseDisjoint
    Bananas.CanonicalMarkedSupportsPairwiseDisjoint
  simp only [rankSupport_toLib]
  all_goals exact Iff.rfl

theorem effectiveDegreeOneTwistResidues_toLib (M : TwiceMarked) (D : CFDiv M.graph)
    (k : ℕ) :
    effectiveDegreeOneTwistResidues M D k =
      Bananas.effectiveDegreeOneTwistResidues (toLibTM M) D k := by
  unfold effectiveDegreeOneTwistResidues Bananas.effectiveDegreeOneTwistResidues
  simp only [rank_toLib]
  all_goals rfl

theorem invTauCorrection_toLib (M : TwiceMarked) (D : CFDiv M.graph) :
    invTauCorrection M D = Bananas.invTauCorrection (toLibTM M) D := rfl

theorem sectionFiveRankDropSum_toLib (M : TwiceMarked) (D : CFDiv M.graph) (k : ℕ) :
    sectionFiveRankDropSum M D k = Bananas.sectionFiveRankDropSum (toLibTM M) D k := by
  unfold sectionFiveRankDropSum Bananas.sectionFiveRankDropSum
  simp only [rank_toLib]
  all_goals rfl

theorem hasInversionLowerBound_toLib (M : TwiceMarked) (k q : ℕ) :
    HasInversionLowerBound M k q ↔ Bananas.HasInversionLowerBound (toLibTM M) k q := by
  unfold HasInversionLowerBound Bananas.HasInversionLowerBound
  simp only [isTransmissionPermutation_toLib]
  all_goals exact Iff.rfl

/-! ### Graph isomorphisms -/

/-- Cross a standalone graph isomorphism into the library's. -/
abbrev toLibIso {G : CFGraph.{u}} {H : CFGraph.{v}} (φ : CFGraphIso G H) :
    Utilities.CFGraphIso (toLib G) (toLib H) where
  vertexEquiv := φ.vertexEquiv
  map_num_edges := φ.map_num_edges

/-- Read a library graph isomorphism as a standalone one. -/
abbrev ofLibIso {G : _root_.CFGraph.{u}} {H : _root_.CFGraph.{v}}
    (φ : Utilities.CFGraphIso G H) : CFGraphIso (ofLib G) (ofLib H) where
  vertexEquiv := φ.vertexEquiv
  map_num_edges := φ.map_num_edges

theorem mapDiv_toLib {G : CFGraph.{u}} {H : CFGraph.{v}} (φ : CFGraphIso G H)
    (D : CFDiv G) : (toLibIso φ).mapDiv D = φ.mapDiv D := rfl

theorem pointedGenusOneRigid_toLib (H : CFGraph) (y : H.V) :
    PointedGenusOneRigid H y ↔ Utilities.PointedGenusOneRigid (toLib H) y :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2, h.3, h.4⟩⟩

/-- Cross a mark-swapping automorphism into the library's bundle. -/
abbrev toLibSwap {M : TwiceMarked} (φ : MarkedPointSwap M) :
    Bananas.MarkedPointSwap (toLibTM M) where
  iso := toLibIso φ.iso
  preserves_marked_set := φ.preserves_marked_set
  map_u := φ.map_u
  map_v := φ.map_v

/-! ### Marked graphs and chains -/

/-- Cross a standalone marked graph into the library's bundle. -/
abbrev toLibMG (M : MarkedGraph) : Utilities.MarkedGraph.{0} where
  graph := toLib M.graph
  left := M.left
  right := M.right

theorem toLibMG_wedge (M N : MarkedGraph) :
    toLibMG (M.wedge N) = (toLibMG M).wedge (toLibMG N) := rfl

theorem toLibMG_chain (M : MarkedGraph) (L : List MarkedGraph) :
    toLibMG (M.chain L) = (toLibMG M).chain (L.map toLibMG) := by
  induction L generalizing M with
  | nil => rfl
  | cons N rest ih => exact ih (M.wedge N)

theorem toLib_chain_graph (M : MarkedGraph) (L : List MarkedGraph) :
    toLib (M.chain L).graph = ((toLibMG M).chain (L.map toLibMG)).graph :=
  congrArg Utilities.MarkedGraph.graph (toLibMG_chain M L)

/-! ### Chain factors -/

/-- Cross a chain factor, bridging its `k`-general transmission proof. -/
abbrev toLibFactor (F : KGeneralChainFactor) : Bananas.KGeneralChainFactor where
  marked := toLibMG F.marked
  period := F.period
  connected := F.connected
  kGeneral := (kGeneralTransmission_toLib _ _).mp F.kGeneral

theorem chainPrefixBudget_toLib (g : ℤ) (L : List KGeneralChainFactor) :
    ChainPrefixBudget g L ↔ Bananas.ChainPrefixBudget g (L.map toLibFactor) := by
  induction L generalizing g with
  | nil => exact Iff.rfl
  | cons F rest ih =>
      simp only [List.map_cons, ChainPrefixBudget, Bananas.ChainPrefixBudget]
      exact and_congr Iff.rfl (ih _)

theorem chainFactorGenus_toLib (L : List KGeneralChainFactor) :
    chainFactorGenus L = Bananas.chainFactorGenus (L.map toLibFactor) := by
  unfold chainFactorGenus Bananas.chainFactorGenus
  rw [List.map_map]
  rfl

theorem chainMinBudget_toLib (L : List KGeneralChainFactor) :
    ChainMinBudget L ↔ Bananas.ChainMinBudget (L.map toLibFactor) := by
  unfold ChainMinBudget Bananas.ChainMinBudget
  constructor
  · intro h i hi
    have hi' : i < L.length := by simpa using hi
    have := h i hi'
    rw [← List.map_take, ← List.map_drop, ← chainFactorGenus_toLib,
      ← chainFactorGenus_toLib]
    simp only [List.get_eq_getElem, List.getElem_map]
    exact this
  · intro h i hi
    have hi' : i < (L.map toLibFactor).length := by simpa using hi
    have := h i hi'
    rw [← List.map_take, ← List.map_drop, ← chainFactorGenus_toLib,
      ← chainFactorGenus_toLib] at this
    simp only [List.get_eq_getElem, List.getElem_map] at this
    exact this

/-! ### Weierstrass partitions and the once-marked census -/

theorem poleOrder_toLib (G : CFGraph) (v : G.V) (D : CFDiv G) (i : ℕ) :
    poleOrder G v D i = Bananas.poleOrder (toLib G) v D i := by
  unfold poleOrder Bananas.poleOrder poleOrderSet Bananas.poleOrderSet
  simp only [rank_toLib]
  all_goals rfl

theorem weierstrassPart_toLib (G : CFGraph) (v : G.V) (D : CFDiv G) (i : ℕ) :
    weierstrassPart G v D i = Bananas.weierstrassPart (toLib G) v D i := by
  unfold weierstrassPart Bananas.weierstrassPart weierstrassPartInt
    Bananas.weierstrassPartInt
  simp only [poleOrder_toLib]
  all_goals rfl

theorem graph_connected_toLib (G : CFGraph) :
    graphConnected G ↔ _root_.graphConnected (toLib G) := Iff.rfl

theorem weierstrassSize_toLib {G : CFGraph} (hconn : graphConnected G) (v : G.V)
    (D : CFDiv G) :
    weierstrassSize hconn v D =
      Bananas.weierstrassSize (G := toLib G) ((graph_connected_toLib G).mp hconn) v D := by
  refine Eq.trans ?_ (Bananas.weierstrassSize_eq_sum (G := toLib G)
    ((graph_connected_toLib G).mp hconn) v D).symm
  unfold weierstrassSize
  simp only [weierstrassPart_toLib]
  all_goals rfl

theorem onceMarkedCensusContains_toLib (G : CFGraph) (v : G.V) (lambda : YoungDiagram) :
    OnceMarkedCensusContains G v lambda ↔
      Utilities.OnceMarkedCensusContains (toLib G) v lambda := by
  unfold OnceMarkedCensusContains Utilities.OnceMarkedCensusContains
  simp only [rank_toLib]
  all_goals exact Iff.rfl

theorem onceMarkedBrillNoetherGeneral_toLib (G : CFGraph) (v : G.V) :
    OnceMarkedBrillNoetherGeneral G v ↔
      Bananas.OnceMarkedBrillNoetherGeneral (toLib G) v := by
  unfold OnceMarkedBrillNoetherGeneral Bananas.OnceMarkedBrillNoetherGeneral
  simp only [onceMarkedCensusContains_toLib]
  all_goals exact Iff.rfl

/-- Once-marked generality at the right mark of a chain, in library form. -/
theorem onceMarkedBrillNoetherGeneral_chain_toLib (M : MarkedGraph) (L : List MarkedGraph) :
    OnceMarkedBrillNoetherGeneral (M.chain L).graph (M.chain L).right ↔
      Bananas.OnceMarkedBrillNoetherGeneral
        ((toLibMG M).chain (L.map toLibMG)).graph
        ((toLibMG M).chain (L.map toLibMG)).right := by
  rw [← toLibMG_chain]
  exact onceMarkedBrillNoetherGeneral_toLib _ _

/-! ### Bananas -/

/-- Cross a standalone banana into the library's subdivision specification. -/
abbrev toLibBanana {g : ℕ} (B : Banana g) : Bananas.Banana g where
  core := { tail := B.tail, head := B.head }
  length := B.length
  core_nonempty := by decide
  core_loopless := B.core_loopless
  length_pos := B.length_pos

/-- Read a library banana as a standalone one. -/
abbrev ofLibBanana {g : ℕ} (B : Bananas.Banana g) : Banana g where
  tail := B.core.tail
  head := B.core.head
  length := B.length
  core_loopless := B.core_loopless
  length_pos := B.length_pos

theorem toLib_banana_graph {g : ℕ} (B : Banana g) :
    toLib B.graph = (toLibBanana B).graph := rfl

theorem strandVertex_toLib {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (i : B.PathPosition α) :
    strandVertex B α i = Bananas.strandVertex (toLibBanana B) α i := rfl

theorem semibreakDivisor_toLib {g : ℕ} (B : Banana g)
    (chips : ∀ α : Fin (g + 1), Option (Fin (B.length α - 1))) :
    semibreakDivisor B chips = Bananas.semibreakDivisor (toLibBanana B) chips := by
  funext x
  rcases x with _ | ⟨α, offset⟩ <;> rfl

theorem isSemibreak_toLib {g : ℕ} (B : Banana g) (E : CFDiv B.graph) :
    IsSemibreak B E ↔ Bananas.IsSemibreak (toLibBanana B) E := by
  unfold IsSemibreak Bananas.IsSemibreak
  simp only [semibreakDivisor_toLib]
  all_goals exact Iff.rfl

theorem thetaKGeneralCoordinates_toLib {k : ℕ} (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta) :
    ThetaKGeneralCoordinates (k := k) B alpha beta i j ↔
      Bananas.ThetaKGeneralCoordinates (k := k) (toLibBanana B) alpha beta i j := by
  unfold ThetaKGeneralCoordinates Bananas.ThetaKGeneralCoordinates
  simp only [nonRecurrent_toLib]
  all_goals exact Iff.rfl

theorem bridgelessGenusTwoKGeneralCharacterization_toLib (G : CFGraph.{0}) (u v : G.V)
    (k : ℕ) :
    BridgelessGenusTwoKGeneralCharacterization G u v k ↔
      Bananas.BridgelessGenusTwoKGeneralCharacterization (toLib G) u v k := by
  unfold BridgelessGenusTwoKGeneralCharacterization
    Bananas.BridgelessGenusTwoKGeneralCharacterization
  constructor
  · rintro (⟨B, φ, alpha, beta, i, j, hu, hv, hcoord⟩ |
      ⟨base, factor, attachment, root, φ, hbase, hfactor, hbc, hfc, hwc, hplace⟩)
    · exact Or.inl ⟨toLibBanana B, toLibIso φ, alpha, beta, i, j, hu, hv,
        (thetaKGeneralCoordinates_toLib B alpha beta i j).mp hcoord⟩
    · exact Or.inr ⟨toLib base, toLib factor, attachment, root, toLibIso φ,
        (pointedGenusOneRigid_toLib _ _).mp hbase,
        (pointedGenusOneRigid_toLib _ _).mp hfactor, hbc, hfc, hwc, hplace⟩
  · rintro (⟨B, φ, alpha, beta, i, j, hu, hv, hcoord⟩ |
      ⟨base, factor, attachment, root, φ, hbase, hfactor, hbc, hfc, hwc, hplace⟩)
    · exact Or.inl ⟨ofLibBanana B, ofLibIso φ, alpha, beta, i, j, hu, hv,
        (thetaKGeneralCoordinates_toLib (ofLibBanana B) alpha beta i j).mpr hcoord⟩
    · exact Or.inr ⟨ofLib base, ofLib factor, attachment, root, ofLibIso φ,
        (pointedGenusOneRigid_toLib _ _).mpr hbase,
        (pointedGenusOneRigid_toLib _ _).mpr hfactor, hbc, hfc, hwc, hplace⟩

end TMB

namespace TMB


/-!
## Section 1 — Introduction
-/

/- **Definition 1.1** (unlabeled) — divisor census of a graph.

> "For a graph or smooth algebraic curve, the divisor census is the set of
> all pairs (d,r) of integers for which there exists a divisor D with
> deg D = d and r(D) ≥ r."

Formalized (pointwise, as a membership predicate rather than a set) as
`Utilities.BNExists` (`Utilities/Foundations/Parameters.lean`). Argument order is
`(r, d)`, not the paper's `(d, r)`. -/

/- **Conjecture 1.2** (`conj:bn`) — Brill–Noether conjecture for graphs.
CONJECTURE, not a formalization target.

> "For every genus g ≥ 0: 1) Every genus g graph contains every pair (d,r)
> with ρ(g,r,d) ≥ 0 in its divisor census. 2) There exists a genus g graph
> such that every (d,r) in the divisor census satisfies ρ(g,r,d) ≥ 0 (proved
> in [CDPR12])."

Part 2) is `BrillNoetherGeneral` (Definition 1.3, below); its docstring
records explicitly that this is a one-directional reading of part 2), and
that part 1) has no standalone Lean counterpart. -/

/- **Definition 1.3** (unlabeled) — Brill–Noether general graph.

> "Graphs satisfying part 2) of Conjecture 1.2 are called Brill--Noether
> general."

Formalized exactly as `Bananas.BrillNoetherGeneral`
(`Bananas/Basics/Definitions.lean`). -/

/- **Definition 1.6** (unlabeled) — pole orders and the Weierstrass
partition.

> "Let (G,v) be a genus g graph with a marked vertex v. For any divisor D
> and integer i ≥ 0, let s_i(D,v) = min{ℓ ∈ ℤ : r(D+ℓv) ≥ i}. ... The
> Weierstrass partition of D with respect to v is the nonincreasing sequence
> of nonnegative integers λ(D,v) = (λ_0(D,v), λ_1(D,v), …) defined by
> λ_i(D,v) = i + g - deg D - s_i(D,v). The (finite) sum ∑_{i=0}^∞ λ_i(D,v) is
> denoted |λ(D,v)|."

Formalized in `Bananas/Classification/WeierstrassPartition.lean` as
`Bananas.poleOrder` (s_i(D,v)),
`Bananas.weierstrassPart` (λ_i(D,v)), and
`Bananas.weierstrassPartition` (λ(D,v), as a `YoungDiagram`;
`|λ(D,v)|` is then `YoungDiagram.card`). Connectivity is an added standing
hypothesis, needed for `sInf` to be a genuine minimum. -/

/- **Definition 1.7** (unlabeled) — divisor census of a once-marked graph.

> "For a once-marked graph (G,v), the divisor census is the set of all
> partitions λ for which there exists a divisor D with λ_i(D,v) ≥ λ_i for
> all i ≥ 0."

Formalized as `Utilities.OnceMarkedCensusContains`
(`Utilities/Grassmannian/OnceMarked.lean`), a pointwise membership predicate stated
without choosing minima. Equivalent (on connected graphs) to the normalized
`Utilities.OnceMarkedBNExists`. -/

/- **Conjecture 1.8** (`conj:bnOnceMarked`) — Brill–Noether existence
conjecture for once-marked graphs. CONJECTURE, not a formalization target.

> "For any once-marked graph (G,u) of genus g, every partition λ with
> |λ| ≤ g is in the divisor census."

Stated (but of course not proved) as `Utilities.OnceMarkedBNConjecture`,
built from `Utilities.OnceMarkedBNExistence`
(`Utilities/Grassmannian/OnceMarked.lean`). -/

/- **Definition 1.9** (unlabeled) — Brill–Noether general once-marked graph.

> "A once-marked graph (G,v) is called Brill--Noether general if
> |λ(D,v)| ≤ g for all divisors D on G. In other words, every partition in
> the divisor census has size at most the genus."

Formalized exactly as `Bananas.OnceMarkedBrillNoetherGeneral`
(`Bananas/Sections/SectionSixDefinitions.lean`). By the paper's shared per-section
counter this is Definition 1.9 (1.7 is the once-marked divisor census
above); the formal definition's docstring has been corrected to agree with
this entry. -/

/- **Definition 1.10** (unlabeled) — k-general transmission.

> "A genus g twice-marked graph (G,u,v) for which ku ∼ kv is said to have
> k-general transmission if all divisors D are submodular, and satisfy
> inv_k(τ_D) ≤ g."

Formalized as `Bananas.KGeneralTransmission`
(`Bananas/Basics/Definitions.lean`), stated directly in terms of transmission
permutations and their `k`-inversion counts, with an added explicit
finiteness conjunct (`Set.ncard` is `0` on an infinite set, so without it the
bound would be vacuous). Known gap (`Bananas/FORMALIZATION_NOTES.md`, "Distinctness of
the two marks"): `TwiceMarked` does not itself encode `u ≠ v`. -/

/-- **Example 1.11** (`eg:cycle`). Section 1.

> "If G is a cycle graph, with two marked points u,v joined by two paths of
> length a and b, then the torsion order of (G,u,v) is k = (a+b)/gcd(a,b) and
> (G,u,v) has k-general transmission [Pfl22, §2.1]."

Exact. A cycle graph marked at its two junction vertices is the genus-one
banana `B : Banana g` at `g = 1`, marked at `leftEndpoint B` /
`rightEndpoint B`, with `a = B.length 0`, `b = B.length 1`
(`Bananas/Transmission/CycleTorsionOrder.lean`). The paper defers its own proof to
[Pfl22, §2.1]; the argument here instead runs through the banana Jacobian
presentation of Proposition 2.14 (`Bananas/Jacobian/BananaJacobianProposition214.lean`):
the diagonal and strand-length relations identify `k(u - v)` with a multiple
of the shared coordinate step that is annihilated exactly at
`k = (a+b)/gcd(a,b)`, and a homomorphism to `ZMod (a+b)` that kills exactly
the displayed relation lattice rules out any smaller witness. -/
theorem _root_.Bananas.TwiceMarkedBananas.s1_eg1_11 (B : Banana 1) :
    IsTorsionOrder (mark B.graph (leftEndpoint B) (rightEndpoint B))
      ((B.length 0 + B.length 1) / Nat.gcd (B.length 0) (B.length 1)) ∧
    KGeneralTransmission (mark B.graph (leftEndpoint B) (rightEndpoint B))
      ((B.length 0 + B.length 1) / Nat.gcd (B.length 0) (B.length 1)) := by
  exact ⟨Bananas.cycle_isTorsionOrder (toLibBanana B),
    (kGeneralTransmission_toLib _ _).mpr (Bananas.cycle_kGeneralTransmission (toLibBanana B))⟩

/-- **Theorem 1.12** (`thm:thetaSimple`), part 1). Section 1.

> "Let (G,u,v) be a theta graph with two marked points. 1) If u and v are
> located on the interiors of distinct strands of G, then all divisors on G
> are submodular."

Exact. Also cross-labeled `cor-allSubmodSameStrand` (Corollary 3.6, case 1,
`⇐` direction). -/
theorem _root_.Bananas.TwiceMarkedBananas.s1_thm1_12a
    (B : Banana 2) (α β : Fin 3) (i : B.PathPosition α)
    (j : B.PathPosition β) (hαβ : α ≠ β)
    (hi : 0 < i.val ∧ i.val < B.length α)
    (hj : 0 < j.val ∧ j.val < B.length β) :
    AllSubmodular (mark B.graph (strandVertex B α i) (strandVertex B β j)) := by
  exact (allSubmodular_toLib _).mpr
    (Bananas.theta_allSubmodular_of_distinct_interior_strands (toLibBanana B) α β i j hαβ hi hj)

/-- **Theorem 1.12** (`thm:thetaSimple`), part 2). Section 1.

> "2) If (G,u,v) is evenly marked, meaning that u and v divide their strands
> into two segments with the same ratio a/b ∈ ℚ, then (G,u,v) has
> k-general transmission, where k is the torsion order of (G,u,v)."

Exact and unconditional. Also Corollary 4.17 (`cor:evenlyMarkedKGT`). The theorem discharges the auxiliary inversion-data hypothesis. -/
theorem _root_.Bananas.TwiceMarkedBananas.s1_thm1_12b
    (B : Banana 2) (α β : Fin 3) (i : B.PathPosition α)
    (j : B.PathPosition β)
    (hEven : EvenlyMarkedTheta B α β i j) :
    KGeneralTransmission
      (mark B.graph (strandVertex B α i) (strandVertex B β j))
      (B.length α / Nat.gcd (B.length α) i.val) := by
  exact (kGeneralTransmission_toLib _ _).mpr
    (Bananas.evenlyMarkedTheta_kGeneral (toLibBanana B) α β i j hEven)

/-- **Theorem 1.13** (`thm:bngChain`), part 1). Section 1. Body of the paper:
Corollary 6.16, part 1).

> "Let (G_i,u_i,v_i), i = 1,…,ℓ, be a sequence of twice-marked graphs, and
> (G,u,v) the iterated vertex gluing. Let g_i, k_i be the genus of G_i and
> torsion order of (G_i,u_i,v_i). Suppose each (G_i,u_i,v_i) has
> k_i-general transmission. 1) If k_i > g_1+…+g_i for all i, then (G,v) is a
> Brill--Noether general marked graph."

Exact, with the intended left-associated `MarkedGraph.chain` recursion
replacing the paper's self-referential display (`Bananas/FORMALIZATION_NOTES.md`, "Chain
theorem notation"). -/
theorem _root_.Bananas.TwiceMarkedBananas.s1_thm1_13a
    (head : KGeneralChainFactor) (tail : List KGeneralChainFactor)
    (hHeadBudget : genus head.marked.graph < (head.period : ℤ))
    (hTailBudget : ChainPrefixBudget (genus head.marked.graph) tail) :
    OnceMarkedBrillNoetherGeneral
      (head.marked.chain (tail.map KGeneralChainFactor.marked)).graph
      (head.marked.chain (tail.map KGeneralChainFactor.marked)).right := by
  have h := Bananas.onceMarkedBrillNoetherGeneral_mixedTorsionChain (toLibFactor head)
    (tail.map toLibFactor) hHeadBudget ((chainPrefixBudget_toLib _ _).mp hTailBudget)
  rw [List.map_map] at h
  refine (onceMarkedBrillNoetherGeneral_chain_toLib _ _).mpr ?_
  rw [List.map_map]
  exact h

/-- **Theorem 1.13** (`thm:bngChain`), part 2). Section 1. Body of the paper:
Corollary 6.16, part 2).

> "2) If k_i > min{g_1+…+g_i, g_i+g_{i+1}+…+g_ℓ} for all i, then G is a
> Brill--Noether general graph."

Exact, in the paper's full graph convention (connected genus-zero factors
allowed in arbitrary positions), via a recursive prefix/minimum-budget
encoding rather than the paper's indexed sums. -/
theorem _root_.Bananas.TwiceMarkedBananas.s1_thm1_13b
    (F : KGeneralChainFactor) (tail : List KGeneralChainFactor)
    (hMin : ChainMinBudget (F :: tail)) :
    BrillNoetherGeneral
      (F.marked.chain (tail.map KGeneralChainFactor.marked)).graph := by
  have h := Bananas.brillNoetherGeneral_mixedTorsionChain_of_minBudget (toLibFactor F)
    (tail.map toLibFactor) ((chainMinBudget_toLib _).mp hMin)
  rw [List.map_map] at h
  rw [brillNoetherGeneral_toLib, toLib_chain_graph, List.map_map]
  exact h


/-- **Theorem 1.16** (`thm:bananaSimple`). Section 1.

> "Let (G,u,v) be a banana graph of genus g ≥ 3, marked at two vertices u,v,
> at least one of which lies at least distance 2 from both multivalent
> vertices. Then there exist non-submodular divisors on (G,u,v)."

**Formalization note.** The checked statement includes the additional case in which the other mark is the midpoint of a distinct length-two strand. This is represented by `CorrectedBananaSimpleException`; see `Bananas/FORMALIZATION_NOTES.md`. -/
theorem _root_.Bananas.TwiceMarkedBananas.s1_thm1_16
    {g : ℕ} (hg : 3 ≤ g) (B : Banana g) (alpha beta : Fin (g + 1))
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (hFar : FarFromBananaEndpoints B alpha i ∨
      FarFromBananaEndpoints B beta j) :
    CorrectedBananaSimpleException B alpha beta i j ∨
      ∃ D : CFDiv B.graph,
        rankDelta
          (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)) D < 0 := by
  rcases Bananas.corrected_bananaSimple hg (toLibBanana B) alpha beta i j hFar with h | ⟨D, hD⟩
  · exact Or.inl h
  · exact Or.inr ⟨D, (rankDelta_toLib
      (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)) D).trans_lt hD⟩

/-- **Theorem 1.17** (`thm:bananas`). Section 1.

> "A twice-marked banana graph of genus g ≥ 3 does not have k-general
> transmission for any k ≥ 3."

**Corrected, now complete.** The published Proposition 4.19 exception family
it rests on was enlarged to `CorrectedMidpointException`
(`Bananas/FORMALIZATION_NOTES.md`); with that correction the theorem itself is exact and
unconditional. -/
theorem _root_.Bananas.TwiceMarkedBananas.s1_thm1_17
    {g k : ℕ} (hg : 3 ≤ g) (hk : 3 ≤ k) (B : Banana g)
    (α β : Fin (g + 1)) (i : B.PathPosition α) (j : B.PathPosition β) :
    ¬ KGeneralTransmission
      (mark B.graph (strandVertex B α i) (strandVertex B β j)) k := by
  intro hK
  exact Bananas.corrected_highGenus_banana_not_kGeneral hg hk (toLibBanana B) α β i j ((kGeneralTransmission_toLib _ _).mp hK)

/-- **Remark 1.18** (unlabeled), claim 1 — the endpoint pencil. Section 1.

> "Another important way in which banana graphs are special is that they are
> always hyperelliptic: they possess a degree 2 divisor of rank 1,
> consisting of the two non-bivalent vertices."

Exact. Same underlying fact as Lemma 2.20 (`lem:g12`). -/
theorem _root_.Bananas.TwiceMarkedBananas.s1_rem1_18a {g : ℕ} (B : Banana g) : BNExists B.graph 1 2 := by
  exact (bnExists_toLib _ _ _).mpr (toLibBanana B).bnExists_one_two_of_two_core_vertices

/-- **Remark 1.18** (unlabeled), claim 2 — hence not Brill–Noether general.
Section 1.

> "For g ≥ 3 this shows that they are not Brill--Noether general, since
> ρ(g,1,2) = 2-g."

Exact. (The moduli-theoretic dimension/codimension sentence preceding this
in the remark is not a graph-theoretic claim and is not formalized.) -/
theorem _root_.Bananas.TwiceMarkedBananas.s1_rem1_18b {g : ℕ} (hg : 3 ≤ g) (B : Banana g) :
    ¬ BrillNoetherGeneral B.graph := by
  intro h
  exact Bananas.banana_not_brillNoetherGeneral hg (toLibBanana B) ((brillNoetherGeneral_toLib _).mp h)

/-!
## Section 2 — Background
-/

/- **Definition 2.1** (`def-Graph`) — "Graph".

> "We assume the convention that a graph G is finite, connected, and
> loopless, possibly with parallel edges. ... The valence of a vertex,
> denoted val(v), is the number of edges incident to v. We refer to vertices
> v with val(v) ≥ 3 as multivalent vertices. We take the genus g of a graph
> to be #E(G) - #V(G) + 1."

Split across `CFGraph` (finite, loopless, parallel edges — but *not*
connectivity, which is the separate explicit hypothesis
`_root_.graphConnected`), `genus`, and `vertexDegree` (all in the
`chip-firing-with-lean` package, `ChipFiringWithLean/Basic.lean`). -/

/- **Definition 2.2** (unlabeled) — vertex gluing / iterated vertex gluing.

> "If (G_1,u_1,v_1),(G_2,u_2,v_2) are twice-marked graphs, we may obtain a
> new twice-marked graph (G,u_1,v_2) by taking the disjoint union of G_1 and
> G_2 and identifying v_1 and u_2. ... Given a sequence of ℓ twice-marked
> graphs, the iterated vertex gluing is the graph obtained by taking
> (G_1,u_1,v_1), then successively forming the vertex gluing with the rest."

Exact. `Utilities.vertexWedge` is the vertex gluing;
`Utilities.MarkedGraph.wedge`/`.chain` (`Utilities/Gluing/VertexWedge.lean`,
`Utilities/Gluing/ChainGluing.lean`) are the marked and iterated versions,
left-associated. -/

/-- **Lemma 2.3** (`lem-bridgelessFacts`), part 1). Section 2.

> "If G is a bridgeless graph then 1) If u,v ∈ V(G) then u = v if and only
> if u ∼ v."

Corrected: formalized with `TwoEdgeCutCondition` as the precise no-bridge
hypothesis. -/
theorem _root_.Bananas.TwiceMarkedBananas.s2_lem2_3a
    (G : CFGraph) (hConnected : graphConnected G)
    (hCut : TwoEdgeCutCondition G) (u v : G.V) :
    u = v ↔ linearEquiv G (oneChip u) (oneChip v) := by
  exact Bananas.vertex_eq_iff_one_chip_linear_equiv_of_twoEdgeCutCondition (toLib G)
    hConnected hCut u v


/- **Definition 2.4** (`def-BanGraph`) — "Banana-Graph".

> "For n_0,…,n_g ∈ ℕ we define the banana graph B_{n_0,…,n_g} to be the
> graph obtained by connecting two vertices with g+1 paths of length
> n_0,…,n_g. ... In the case g = 2 we refer to such graphs as theta graphs
> and denote them θ_{n_0,n_1,n_2}. ... We refer to the collection of
> vertices v_{α,0},…,v_{α,n_α} as the α-th strand of our graph."

Exact, split across several declarations: `Bananas.Banana`
(`Bananas/Basics/Definitions.lean`, `:= Spec 2 (g+1)`),
`bananaOfLengths` (the coordinate-first constructor from the strand-length
vector), `strandVertex` (the
coordinates v_{α,i}), `strandMirror` (the bar operation), `leftEndpoint` /
`rightEndpoint` (the two multivalent vertices), and the labeling-coincidence
theorems `strandVertex_zero` / `strandVertex_length` / `strandVertex_injective`
(`Bananas/Basics/BananaBasics.lean`). Theta graphs are `Banana 2`; the `x_i/y_i/z_i`
typographical shorthand has no separate Lean name.  For a completely expanded
three-length presentation aimed at readers rather than internal proofs, see
`Highlights.Theta`, `Highlights.TMTheta`, and `Highlights.evenlyMarkedK`. -/

/- **Definition 2.5** (`def-delt`) — indicator function δ. NOT FOUND: no
named declaration.

> "We define δ(P) for a proposition P to be the indicator function which is
> 1 when P holds and 0 when P does not."

Realized inline everywhere via `if P then (1 : ℤ) else 0` with Lean's
`Decidable` instances, rather than as a standalone definition. -/

/- **Definition 2.6** (`def-TwMkGraph`) — twice-marked graph, torsion order.

> "A twice-marked graph (G,u,v) is a graph with a choice of two
> distinguished vertices u,v. The torsion order of (G,u,v) is the order of
> [u-v] as an element of Jac(G), i.e. the minimum k ∈ ℕ such that ku ∼ kv."

Exact. `Bananas.TwiceMarked` / `.mark`, and
`TorsionWitness` / `IsTorsionOrder` (`Bananas/Basics/Definitions.lean`). Caution:
`TorsionWitness` alone is the weaker `ku ∼ kv` of Definition 1.10, not the
torsion order. -/

/- **Definition 2.7** (`def-Twist`) — twist.

> "A twist of a divisor D on a twice-marked graph (G,u,v) is a divisor of
> the form D+au+bv, a,b ∈ ℤ."

Exact: `Bananas.twist` (`Bananas/Basics/Definitions.lean`). -/

/- **Definition 2.8** (`def-Delt`) — the function Δ.

> "For a divisor D on (G,u,v) we define Δ(D) := r(D) - r(D-u) - r(D-v) +
> r(D-u-v)."

Exact: `Bananas.rankDelta` (`Bananas/Basics/Definitions.lean`); the
marks are carried in the `TwiceMarked` argument rather than suppressed. -/

/- **Definition 2.9** (`def-submod`, cited to [Pfl22]) — submodular divisor.

> "A divisor D on (G,u,v) is submodular with respect to u,v if Δ(D') ≥ 0 for
> all twists D' = D+au+bv."

Exact: `Bananas.Submodular` / `.AllSubmodular`
(`Bananas/Basics/Definitions.lean`). -/

/- **Definition 2.10** (`def-EA`) — extended affine symmetric group.

> "A permutation is a bijection τ:ℤ→ℤ. Given k ∈ ℕ, permutations satisfying
> τ(n+k) = τ(n)+k for all n ∈ ℤ form a group denoted Ẽa_k, referred to as
> the extended affine symmetric group."

Exact, modelled as a predicate rather than a bundled group:
`Bananas.IsKAffine` (`Bananas/Basics/Definitions.lean`). -/

/- **Definition 2.11** (`def-tauD`, cited to [Pfl22]) — transmission
permutation.

> "Given a twice-marked graph (G,u,v), let D be a divisor in Pic(G). If it
> exists, the transmission permutation of D, denoted τ_D, is the unique
> bijection τ_D : ℤ → ℤ which satisfies, for all a,b ∈ ℤ,
> δ(τ_D(b)=a) = Δ(D+au-bv)."

Exact, including the bijectivity requirement:
`Bananas.IsTransmissionPermutation`
(`Bananas/Basics/Definitions.lean`). The main library separately models the same
notion by `AspPerm` + `Utilities.SatisfiesTransmission`, bridged in
`Bananas/Transmission/TransmissionBridge.lean`. -/

/-- **Lemma 2.12** (`lem:tauChars`, cited to [Pfl22, Remark 1.5, Prop 2.3]),
existence half. Section 2.

> "A divisor D on (G,u,v) has a well-defined transmission permutation if and
> only if it is submodular. If (G,u,v) has torsion order k, or more
> generally if ku ∼ kv, then τ_D ∈ Ẽa_k."

Partial: only the "all divisors submodular + torsion witness ⇒ affine
transmission permutation exists" direction, and only for banana graphs; the
converse and uniqueness are not separately exposed. One of two paper results
(with Example 1.11) the paper itself defers to [Pfl22]. -/
theorem _root_.Bananas.TwiceMarkedBananas.s2_lem2_12a
    {g k : ℕ} (B : Banana g) (u v : B.graph.V)
    (hk : TorsionWitness (mark B.graph u v) k)
    (hsub : AllSubmodular (mark B.graph u v))
    (D : CFDiv B.graph) :
    ∃ τ : ℤ → ℤ, IsTransmissionPermutation (mark B.graph u v) D τ ∧
      IsKAffine k τ ∧ (kInversions k τ).Finite := by
  obtain ⟨τ, hτ, hAff, hFin⟩ := Bananas.exists_affine_transmission_of_allSubmodular
    (M := toLibTM (mark B.graph u v)) (Bananas.banana_graph_connected (toLibBanana B)) hk ((allSubmodular_toLib _).mp hsub) D
  exact ⟨τ, (isTransmissionPermutation_toLib _ _ _).mpr hτ, hAff, hFin⟩

/-- **Lemma 2.12** (`lem:tauChars`), southeast rank formula. Section 2.

> "The transmission permutation is also characterized by ...
> r(D+au-bv)+1 = #{ℓ ≥ b : τ_D(ℓ) ≤ a}." -/
theorem _root_.Bananas.TwiceMarkedBananas.s2_lem2_12b
    {g : ℕ} (B : Banana g) (u v : B.graph.V) (D : CFDiv B.graph)
    (τ : ℤ → ℤ) (hτ : IsTransmissionPermutation (mark B.graph u v) D τ)
    (a b : ℤ) :
    rank B.graph (D + a • oneChip u - b • oneChip v) + 1 =
      (southeastSet τ (a + 1) b).ncard := by
  rw [rank_toLib]
  exact Bananas.transmission_rank_eq_southeast_ncard (toLibTM (mark B.graph u v)) D
    (Bananas.banana_graph_connected (toLibBanana B)) τ ((isTransmissionPermutation_toLib _ _ _).mp hτ) a b

/-- **Lemma 2.12** (`lem:tauChars`), northwest rank formula. Section 2.

> "... r(K_G-D-au+bv)+1 = #{ℓ < b : τ_D(ℓ) > a}." -/
theorem _root_.Bananas.TwiceMarkedBananas.s2_lem2_12c
    {g : ℕ} (B : Banana g) (u v : B.graph.V) (D : CFDiv B.graph)
    (τ : ℤ → ℤ) (hτ : IsTransmissionPermutation (mark B.graph u v) D τ)
    (a b : ℤ) :
    rank B.graph (canonicalDivisor B.graph - D - a • oneChip u +
        b • oneChip v) + 1 =
      (northwestSet τ (a + 1) b).ncard := by
  rw [rank_toLib]
  exact Bananas.transmission_complement_rank_eq_northwest_ncard (toLibTM (mark B.graph u v)) D
    (Bananas.banana_graph_connected (toLibBanana B)) τ ((isTransmissionPermutation_toLib _ _ _).mp hτ) a b

/- **Definition 2.13** (`def-inv`, cited to [Pfl22]) — inversions and
k-inversions.

> "Given a permutation τ, an inversion is a pair (a,b) ∈ ℤ² such that a<b
> and τ(a)>τ(b). ... We write Inv_k(τ) for the set of k-equivalence classes
> of inversions of τ and inv_k(τ) for #Inv_k(τ)."

Exact up to the choice of representatives: `Bananas.kInversions`
/ `.kInversionCount` (`Bananas/Basics/Definitions.lean`), realized as the set of
representatives with `0 ≤ a < k` rather than a quotient type. -/

/- **Proposition 2.14** (`prop-JacBanana`) — Jacobian of a banana graph.

> "Given n_0,…,n_g ∈ ℕ_{≥1}, there is an isomorphism
> Jac(B_{n_0,…,n_g}) ≅ ℤ^{g+1}/⟨(1,…,1),(n_0,-n_1,0,…),…,(n_0,0,…,-n_g)⟩
> under which the coset [a_0,…,a_g] is identified with the divisor
> ∑_α [v_{α,a_α} - v_{0,0}]."

Exact/complete: `bananaDisplayedQuotientEquivClassRange` (the additive
equivalence), `bananaCoordinateRelations_eq_displayedRelations` (kernel =
displayed lattice), and `exists_bananaCoordinate_linearEquiv_of_degree_zero`
(surjectivity), all in `Bananas/Jacobian/BananaJacobian*.lean`. The Jacobian is
modelled as the degree-zero image inside `CFDiv ⧸ principalDivisors`
rather than as a separately-defined `Jac(G)`. -/

/- **Proposition 2.16** (unlabeled) — theta Jacobian in two coordinates.

> "For a theta graph θ_{a,b,c} we have Jac(θ_{a,b,c}) ≅
> ℤ²/⟨(a+c,c),(-a,b)⟩."

Exact: `Bananas.thetaLatticeQuotientEquivClassRange`
(`Bananas/Theta/ThetaJacobianPresentation.lean`). (the checked declaration is the reference used hererow calling this partial; the isomorphism is present.) -/

/- **Definition 2.17** (unlabeled) — "Abel-Jacobi Map".

> "For a graph G with a fixed base point v_0 we define the Abel-Jacobi map
> S_{v_0} : V(G) → Jac(G) by v ↦ [v-v_0]."

Partial: `Bananas.bridgelessDegreeOneClassMap`
(`Bananas/Classification/BridgelessDegreeOneClasses.lean`) is explicitly documented as "the
Abel--Jacobi vertex map", but its codomain is the *degree-one* rank-zero
classes `[v]`, not `Jac(G)` via `[v-v_0]`; no declaration named `abelJacobi`
exists. -/

/- **Definition 2.19** (unlabeled) — restricted rank and rank determining
set.

> "Given a set A ⊆ V(G) we define r_A(D) to be -1 if |D| = ∅ and r_A(D) ≥ r
> if |D-E| ≠ ∅ for every effective divisor of degree r supported on A. A set
> A is a rank determining set if r_A(D) = r(D) for all divisors D."

Corrected/faithful reformulation: `DivisorSupportedOn`, `restrictedRankGeq`,
`RankDetermining` (`Bananas/Transmission/RankDetermining.lean`), using the lower-bound
relation for restricted rank at every `k` rather than a second noncomputable
choice of integer rank. -/

/-- **Lemma 2.20** (`lem:g12`). Section 2.

> "For any banana graph G = B_{n_0,…,n_g}, the divisor v_{0,0}+v_{0,n_0}
> has rank 1."

Exact. Same underlying fact as Remark 1.18, claim 1. -/
theorem _root_.Bananas.TwiceMarkedBananas.s2_lem2_20 {g : ℕ} (B : Banana g) : BNExists B.graph 1 2 := by
  exact (bnExists_toLib _ _ _).mpr (toLibBanana B).bnExists_one_two_of_two_core_vertices

/-- **Lemma 2.21** (`lem-BananaRDS`). Section 2.

> "For any banana graph G = B_{n_0,…,n_g} the set {v_{0,0},v_{0,n_0}} is a
> rank determining set."

Exact/complete. -/
theorem _root_.Bananas.TwiceMarkedBananas.s2_lem2_21 {g : ℕ} (B : Banana g) :
    RankDetermining B.graph {leftEndpoint B, rightEndpoint B} := by
  exact Bananas.banana_endpoints_rankDetermining (toLibBanana B)

/-- **Lemma 2.23** (unlabeled), existence half. Section 2.

> "If D ∈ Pic(B_{n_0,…,n_g}) is v_{0,0}-reduced then D = av_{0,0}+bv_{0,n_0}+E
> where E is an effective divisor with at most one chip on each strand and
> no chips at either multivalent vertex, and 0 ≤ b ≤ g - deg E." -/
theorem _root_.Bananas.TwiceMarkedBananas.s2_lem2_23a {g : ℕ} (B : Banana g) (D : CFDiv B.graph) :
    ∃ (a b : ℤ) (E : CFDiv B.graph),
      IsSemibreak B E ∧ 0 ≤ b ∧ b + deg E ≤ (g : ℤ) ∧
      linearEquiv B.graph D (bananaNormalForm B a b E) := by
  obtain ⟨a, b, E, hE, hb, hdeg, hlin⟩ :=
    Bananas.exists_linearly_equiv_bananaNormalForm (toLibBanana B) D
  exact ⟨a, b, E, (isSemibreak_toLib _ _).mpr hE, hb, hdeg, hlin⟩

/-- **Lemma 2.23** (unlabeled), converse half. Section 2.

> "Conversely, every divisor of this form is v_{0,0}-reduced." -/
theorem _root_.Bananas.TwiceMarkedBananas.s2_lem2_23b {g : ℕ} (B : Banana g)
    (a b : ℤ) (E : CFDiv B.graph) (hE : IsSemibreak B E)
    (hb : 0 ≤ b) (hdeg : b + deg E ≤ (g : ℤ)) :
    qReduced B.graph (leftEndpoint B) (bananaNormalForm B a b E) := by
  exact Bananas.q_reduced_bananaNormalForm (toLibBanana B) a b E ((isSemibreak_toLib _ _).mp hE) hb hdeg

/-- **Lemma 2.23** (unlabeled), final clause. Section 2.

> "As with all reduced divisors, r(D) ≥ 0 if and only if a ≥ 0."

The Lean version proves strictly more than the paper: `Bananas/SameStrand/Semibreak.lean`'s
`bananaNormalForm_parameters_unique` also gives uniqueness of `(a,b,E)`,
which the paper only implies. -/
theorem _root_.Bananas.TwiceMarkedBananas.s2_lem2_23c {g : ℕ} (B : Banana g)
    (a b : ℤ) (E : CFDiv B.graph) (hE : IsSemibreak B E)
    (hb : 0 ≤ b) (hdeg : b + deg E ≤ (g : ℤ)) :
    0 ≤ rank B.graph (bananaNormalForm B a b E) ↔ 0 ≤ a := by
  rw [rank_toLib]
  exact Bananas.banana_normalForm_rank_nonneg_iff (toLibBanana B) a b E ((isSemibreak_toLib _ _).mp hE)
    hb hdeg

/-- **Corollary 2.24** (`cor-BanaRankComp`). Section 2.

> "If D = av_{0,0}+bv_{0,n_0}+E has the form described above, and a,b
> satisfy a,b ≥ -1 and either 0 ≤ a ≤ g-deg E or 0 ≤ b ≤ g - deg E, then
> r(D) = min{a,b}+max{0,max{a,b}-(g-deg E)} = max{min{a,b}, deg D - g}."

Exact, in the second displayed form. -/
theorem _root_.Bananas.TwiceMarkedBananas.s2_cor2_24 {g : ℕ} (B : Banana g)
    (a b : ℤ) (E : CFDiv B.graph) (hE : IsSemibreak B E)
    (ha : -1 ≤ a) (hb : 0 ≤ b) (hdeg : b + deg E ≤ (g : ℤ)) :
    rank B.graph (bananaNormalForm B a b E) =
      max (min a b) (a + b + deg E - (g : ℤ)) := by
  rw [rank_toLib]
  exact Bananas.rank_bananaNormalForm (toLibBanana B) a b E ((isSemibreak_toLib _ _).mp hE) ha hb hdeg

/-- **Corollary 2.25** (`cor-BananaDeltaComps`), part 1). Section 2.

> "Given a twice-marked banana graph (B_{n_0,…,n_g},u,v): 1) If
> (u,v)=(v_{0,0},v_{0,n_0}) and a ≥ 0 then Δ(a(v_{0,0}+v_{0,n_0})) =
> δ(a ≤ g)." -/
theorem _root_.Bananas.TwiceMarkedBananas.s2_cor2_25a {g : ℕ} (B : Banana g) (a : ℕ) :
    rankDelta (mark B.graph (leftEndpoint B) (rightEndpoint B))
        (a • endpointPencilDivisor B) =
      if a ≤ g then 1 else 0 := by
  rw [rankDelta_toLib]
  exact Bananas.rankDelta_endpointPencil_nsmul (toLibBanana B) a

/-- **Corollary 2.25** (`cor-BananaDeltaComps`), part 2) headline instance.
Section 2. One representative of the "one-off" family (there are four,
`Bananas/CrossOneOff/BananaOneOffDeltaFamilies.lean`); see that file for the others.

> "2) If (u,v)=(v_{0,0},v_{0,n_0-1}) with 0 ≤ b < a ≤ g … then
> Δ(av_{0,0}+bv_{0,n_0}+v) = δ(a=g)." -/
theorem _root_.Bananas.TwiceMarkedBananas.s2_cor2_25b
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (a b : ℕ) (hba : b < a) (hag : a ≤ g)
    (hLength : 1 < B.length alpha) :
    rankDelta
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
      ((a : ℤ) • oneChip (leftEndpoint B) +
        (b : ℤ) • oneChip (rightEndpoint B) +
        oneChip (strandVertex B alpha
          ⟨B.length alpha - 1, by omega⟩)) =
      if a = g then 1 else 0 := by
  rw [rankDelta_toLib]
  exact Bananas.rankDelta_oneOff_terminal_family (toLibBanana B) alpha a b hba hag hLength

/-- **Corollary 2.25** (`cor-BananaDeltaComps`), part 3) headline instance.
Section 2. This is the ledger's chosen representative of the "cross-off"
family (`Bananas/CrossOneOff/BananaCrossOneOffDeltaFamilies.lean` has the rest).

> "3) If (u,v)=(v_{0,1},v_{1,n_1-1}) … then
> Δ(a(v_{0,0}+v_{0,n_0})+v_{0,m}+v_{1,n}) = 1." -/
theorem _root_.Bananas.TwiceMarkedBananas.s2_cor2_25c
    {g : ℕ} (B : Banana g) (α β : Fin (g + 1))
    (p : B.PathPosition α) (q : B.PathPosition β) (c : ℕ)
    (hg : 2 ≤ g) (hαβ : α ≠ β)
    (hpLo : 2 ≤ p.val) (hpHi : p.val < B.length α)
    (hqLo : 1 ≤ q.val) (hqHi : q.val + 1 < B.length β)
    (hc : c ≤ g - 2) :
    rankDelta
      (mark B.graph
        (strandVertex B α ⟨1, by have := B.length_pos α; omega⟩)
        (strandVertex B β ⟨B.length β - 1, by omega⟩))
      ((c : ℤ) •
          (oneChip (leftEndpoint B) + oneChip (rightEndpoint B)) +
        oneChip (strandVertex B α p) + oneChip (strandVertex B β q)) = 1 := by
  rw [rankDelta_toLib]
  exact Bananas.rankDelta_crossOneOff_two_interior_eq_one (toLibBanana B) α β p q c hg hαβ hpLo hpHi
    hqLo hqHi hc

/-!
## Section 3 — Submodularity on Banana Graphs
-/

/- **Definition 3.1** (`def-Supp`) — the support complex.

> "For a divisor D, the support complex of D is the set of vertices to
> which D can transmit chips while remaining effective:
> Supp(D) = {v ∈ V(G) : r(D-v) ≥ 0}."

Exact: `Bananas.rankSupport` (`Bananas/Transmission/RankZeroSupport.lean`). -/

/-- **Lemma 3.2** (`lemm-rank0supp`), part 1). Section 3.

> "1) If (G,u,v) is a twice-marked graph of genus 2 and u ≁ v, then any
> divisor D with Δ(D) < 0 has degree 2 and rank 0." -/
theorem _root_.Bananas.TwiceMarkedBananas.s3_lem3_2a
    {g : ℕ} (B : Banana g) (u v : B.graph.V)
    (hGenus : genus B.graph = 2)
    (hDistinct : ¬ linearEquiv B.graph (oneChip u - oneChip v) 0)
    (D : CFDiv B.graph)
    (hNeg : rankDelta (mark B.graph u v) D < 0) :
    deg D = 2 ∧ rank B.graph D = 0 := by
  have h := Bananas.degree_and_rank_eq_of_rankDelta_neg_genus_two
    (toLibTM (mark B.graph u v)) D (Bananas.banana_graph_connected (toLibBanana B)) hGenus hDistinct
    (by rw [rankDelta_toLib] at hNeg; exact hNeg)
  rw [rank_toLib]
  exact h

/-- **Lemma 3.2** (`lemm-rank0supp`), part 2). Section 3.

> "2) If (G,u,v) is a twice-marked graph of any genus, and D is a divisor
> of rank 0, then Δ(D) < 0 if and only if v ∈ Supp(D)\Supp(D-u) and
> u ∈ Supp(D)\Supp(D-v)." -/
theorem _root_.Bananas.TwiceMarkedBananas.s3_lem3_2b
    {g : ℕ} (B : Banana g) (u v : B.graph.V) (D : CFDiv B.graph)
    (hD : rank B.graph D = 0) :
    rankDelta (mark B.graph u v) D < 0 ↔
      (v ∈ rankSupport B.graph D ∧
        v ∉ rankSupport B.graph (D - oneChip u)) ∧
      (u ∈ rankSupport B.graph D ∧
        u ∉ rankSupport B.graph (D - oneChip v)) := by
  simp only [rankDelta_toLib, rankSupport_toLib]
  exact Bananas.rankDelta_neg_iff_rankSupport_pattern (toLibTM (mark B.graph u v)) D
    (by rw [rank_toLib] at hD; exact hD)

/- **Remark 3.3** (`rem-closePoints`) — no formal claim, purely qualitative
gloss on Theorem 3.4 ("too close together" is not a defined predicate). -/

/-- **Theorem 3.4** (`thm-NonSubmodGenus2`), the full same-strand
equivalence 1) ⇔ 2), endpoint-inclusive. Section 3.

> "Let G = θ_{n_0,n_1,n_2}, (G,u,v) a twice-marked theta graph with u ≁ v.
> The following are equivalent. 1) There exist divisors D with Δ(D) < 0.
> 2) The marked points u,v are on the same strand … and the set N_{(G,u,v)}
> … is nonempty. In particular there is a bijection N_{(G,u,v)} →
> {[D] ∈ Pic(G) : Δ(D)<0}, v_{α,k} ↦ [v_{α,k}+v_{α,i}]."

The equivalence is proved (`theta_nonSubmodular_iff_same_strand`, below);
the paper's `u ≁ v` hypothesis is derived rather than assumed. The class
bijection of 2) is proved separately in three branches (interior,
initial-endpoint, terminal-endpoint — `Bananas/Theta/ThetaNegativeDivisorClasses*.lean`),
not as one re-exported statement. -/
theorem _root_.Bananas.TwiceMarkedBananas.s3_thm3_4
    (B : Banana 2) (alpha : Fin 3)
    (i j : B.PathPosition alpha) (hij : i.val < j.val) :
    (∃ D : CFDiv B.graph,
        rankDelta
          (mark B.graph (strandVertex B alpha i) (strandVertex B alpha j)) D < 0) ↔
      Set.Nonempty (thetaExceptionalPositions B alpha i j) := by
  refine Iff.trans ?_ (Bananas.theta_nonSubmodular_iff_same_strand (toLibBanana B) alpha i j hij)
  simp only [rankDelta_toLib]
  all_goals exact Iff.rfl

/-- **Lemma 3.5** (`lem-SameStrand`). Section 3.

> "On a banana graph B_{n_0,…,n_g} if r(v_{α,i}+v_{β,j}-v_{γ,k}) = 0, then
> one of: 1) v_{α,i}=v_{γ,k}; 2) v_{β,j}=v_{γ,k}; 3) the bar of v_{α,i}
> equals v_{β,j}; 4) v_{α,i},v_{β,j},v_{γ,k} all on the same strand."

**Corrected.** The paper's coordinate-pair parentheticals for 1), 2), 4)
(e.g. "i.e. (α,i)=(γ,k)") are false at the two shared endpoints, where
distinct strand labels name the same physical vertex
(`Bananas/FORMALIZATION_NOTES.md`). The Lean statement below uses physical vertex
equality and `VerticesOnCommonBananaStrand` instead. -/
theorem _root_.Bananas.TwiceMarkedBananas.s3_lem3_5
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g)
    (alpha beta gamma : Fin (g + 1))
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (k : B.PathPosition gamma)
    (hRank : rank B.graph
      (oneChip (strandVertex B alpha i) +
        oneChip (strandVertex B beta j) -
        oneChip (strandVertex B gamma k)) = 0) :
    strandVertex B alpha i = strandVertex B gamma k ∨
      strandVertex B beta j = strandVertex B gamma k ∨
      strandVertex B beta j =
        strandVertex B alpha (strandMirror B alpha i) ∨
      VerticesOnCommonBananaStrand B
        (strandVertex B alpha i) (strandVertex B beta j)
        (strandVertex B gamma k) := by
  exact Bananas.banana_rank_zero_three_vertices_same_strand_alternatives hg (toLibBanana B)
    alpha beta gamma i j k (by rw [rank_toLib] at hRank; exact hRank)

/-- **Corollary 3.6** (`cor-allSubmodSameStrand`), full endpoint-safe
classification. Section 3.

> "Given a theta graph (G,v_{α,i},v_{β,j}) every divisor is submodular if
> and only if either 1) α ≠ β, or 2) α = β and (i,j) ∈
> {(0,n_α-1),(0,n_α)} or (i,j) = (1,n_α) up to reordering."

Corrected then exact: clause 1) "α ≠ β" is not itself an invariant condition
(a multivalent vertex lies on every strand), so it is replaced by the
endpoint-safe `ThetaAllSubmodularCoordinates`
(`Bananas/Theta/ThetaBoundarySubmodularity.lean`). -/
theorem _root_.Bananas.TwiceMarkedBananas.s3_cor3_6
    (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta) :
    AllSubmodular
        (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)) ↔
      ThetaAllSubmodularCoordinates B alpha beta i j := by
  rw [allSubmodular_toLib]
  exact Bananas.theta_allSubmodular_iff_coordinates (toLibBanana B) alpha beta i j

/-- **Proposition 3.7** (labeled `rem-degenerateTheta` in the source, but a
`\begin{prop}`), distinct-loop clause. Section 3.

> "On a chain of two loops, every divisor is submodular if and only if the
> marked points are on distinct loops or if n_α = 2 and
> {u,v}={v_{α,0},v_{α,1}}."

This is the distinct-loop direction; the two same-loop iff's
(`chainTwoLoops_allSubmodular_same_left_arbitrary_iff` /
`..._same_right_arbitrary_iff`) are in `Bananas/Transmission/ChainTwoLoopsSameLeft.lean` /
`Bananas/Transmission/ChainTwoLoopsSameRight.lean`, not re-wrapped here. -/
theorem _root_.Bananas.TwiceMarkedBananas.s3_prop3_7
    (leftLength rightLength : Fin 2 → ℕ)
    (hLeftLength : ∀ edge, 0 < leftLength edge)
    (hRightLength : ∀ edge, 0 < rightLength edge)
    (leftGlue p : (TwoPathCycle.spec leftLength hLeftLength).graph.V)
    (rightGlue q : (TwoPathCycle.spec rightLength hRightLength).graph.V)
    (hp : p ≠ leftGlue) (hq : q ≠ rightGlue) :
    AllSubmodular
      (mark
        (vertexWedge
          (TwoPathCycle.spec leftLength hLeftLength).graph
          (TwoPathCycle.spec rightLength hRightLength).graph
          leftGlue rightGlue)
        (Sum.inl p)
        (wedgeRightVertex
          (TwoPathCycle.spec leftLength hLeftLength).graph
          (TwoPathCycle.spec rightLength hRightLength).graph
          leftGlue rightGlue q)) := by
  exact (allSubmodular_toLib _).mpr
    (Bananas.chainTwoLoops_allSubmodular_opposite leftLength rightLength hLeftLength
      hRightLength leftGlue p rightGlue q hp hq)

/-- **Corollary 3.8** (`cor:suppUV`), general genus. Section 3.

> "If u,v are vertices on B_{n_0,…,n_g} that do not lie on the same strand,
> then Supp(u+v) = {u,v}." -/
theorem _root_.Bananas.TwiceMarkedBananas.s3_cor3_8
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hi : B.IsInteriorPosition α i) (hj : B.IsInteriorPosition β j)
    (hαβ : α ≠ β) :
    rankSupport B.graph
        (oneChip (strandVertex B α i) + oneChip (strandVertex B β j)) =
      {strandVertex B α i, strandVertex B β j} := by
  rw [rankSupport_toLib]
  exact Bananas.suppUV hg (toLibBanana B) α β i j hi hj hαβ

/-- **Theorem 3.9** (`thm-NSMForBanana`), corrected and complete. Section 3.

> "Let (G,u,v) = (B_{n_0,…,n_g},v_{α,i},v_{β,j}) be a banana graph of genus
> g ≥ 3. Then either: 1a) α=β and, up to swapping u,v,
> (i,j) ∈ {(0,n_α),(1,n_α),(0,n_α-1)}; 1b) α≠β and, up to reversing each
> strand, (i,j)=(1,n_β-1); or 2) there exist divisors D with Δ(D) < 0."

**Formalization note.** The checked statement includes the additional length-two midpoint family as `NSMForBananaLengthTwoCrossException` and uses equality of represented vertices at shared endpoints rather than equality of strand labels; see `Bananas/FORMALIZATION_NOTES.md`. -/
theorem _root_.Bananas.TwiceMarkedBananas.s3_thm3_9
    {g : ℕ} (hg : 3 ≤ g) (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β) :
    NSMForBananaException B (strandVertex B α i) (strandVertex B β j) ∨
      ∃ D : CFDiv B.graph,
        rankDelta (mark B.graph (strandVertex B α i) (strandVertex B β j)) D < 0 := by
  rcases Bananas.nsmForBanana_classification hg (toLibBanana B) α β i j with h | ⟨D, hD⟩
  · exact Or.inl h
  · exact Or.inr ⟨D, (rankDelta_toLib
      (mark B.graph (strandVertex B α i) (strandVertex B β j)) D).trans_lt hD⟩

/- **Remark 3.10** (unlabeled) — no formal claim. Qualitative discussion of
a possible "forbidden-minor" characterization of non-submodularity, which
the paper explicitly declines to make precise. -/

/-!
## Section 4 — k-General Transmission in Banana Graphs
-/

/-- **Remark 4.1** (`rem-PermInvol`) — invariance under swapping the marked
points. Section 4.

> "A natural question ... is whether it depends [on] the order of the pair
> of marked vertices. ... Thus permuting the marked vertices merely permutes
> the set of transmission permutations, so k-general transmission is
> invariant under such a swap." -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_rem4_1
    {G : CFGraph} (u v : G.V) {k : ℕ}
    (hK : KGeneralTransmission (mark G u v) k) :
    KGeneralTransmission (mark G v u) k := by
  exact (kGeneralTransmission_toLib _ _).mpr
    (Bananas.KGeneralTransmission.swap_marks (G := toLib G) u v ((kGeneralTransmission_toLib _ _).mp hK))

/-- **Lemma 4.2** (`lem:kgtImpliesTorsionOrder`). Section 4.

> "If (G,u,v) is a twice-marked graph with k-general transmission, then k
> is the torsion order of (G,u,v)."

Exact, with three explicit hypotheses beyond the paper's statement that are
genuine gaps in a literal reading (connectivity, positive genus, and mark
distinctness — see the docstring of `KGeneralTransmission.isTorsionOrder`,
`Bananas/Transmission/TorsionOrderExact.lean`). -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_lem4_2
    {g k : ℕ} (B : Banana g) (u v : B.graph.V) (huv : u ≠ v)
    (hg : 0 < genus B.graph)
    (hK : KGeneralTransmission (mark B.graph u v) k) :
    IsTorsionOrder (mark B.graph u v) k := by
  exact Bananas.banana_kGeneral_isTorsionOrder (toLibBanana B) u v huv hg ((kGeneralTransmission_toLib _ _).mp hK)

/-- **Lemma 4.3** (`lem-TO2GenTrans`). Section 4.

> "If (G,u,v) has torsion order 2 and every divisor is submodular then G
> has 2-general transmission."

Exact; connectivity is the only requirement beyond the paper statement. -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_lem4_3
    {g : ℕ} (B : Banana g) (u v : B.graph.V)
    (hTO : IsTorsionOrder (mark B.graph u v) 2)
    (hSub : AllSubmodular (mark B.graph u v)) :
    KGeneralTransmission (mark B.graph u v) 2 := by
  exact (kGeneralTransmission_toLib _ _).mpr
    (Bananas.torsionOrder_two_allSubmodular_isKGeneral (M := toLibTM (mark B.graph u v))
      (Bananas.banana_graph_connected (toLibBanana B)) hTO ((allSubmodular_toLib _).mp hSub))

/- **Definition 4.4** (unlabeled) — "rigidly marked". NOT FOUND as a named
predicate.

> "A twice-marked graph (G,u,v) is rigidly marked if every divisor D ∈
> Pic(G) is submodular and r(u+v) = 0."

Unbundled everywhere it is used into `hSub : AllSubmodular (mark G u v)`
together with `hRigid : ¬ linearEquiv G (oneChip u + oneChip v)
(canonicalDivisor G)` (the genus-two equivalent of `r(u+v)=0`), e.g. in
`thetaRigid_kGeneral_iff_nonRecurrent_class`, below (Theorem 4.8). -/

/-- **Proposition 4.5** (`prop-thetaTransChar`), the complete five-case
table. Section 4.

> "Let (G,u,v) be a rigidly marked theta graph. Let D be any degree 2
> divisor. For t ∈ ℤ, define D'_t = D+t(u-v). Then τ_D(t) is t-2, t-1, t+1,
> t+2, or t according to five explicit linear-equivalence cases."

Exact, stated rowwise as implications; mutual exclusivity of the five cases
is not needed and so is not separately proved. -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_prop4_5
    (B : Banana 2) (u v : B.graph.V) (D : CFDiv B.graph)
    (tau : ℤ → ℤ) (t : ℤ)
    (hTau : IsTransmissionPermutation (mark B.graph u v) D tau)
    (hDegree : deg D = 2)
    (hRigid : ¬ linearEquiv B.graph
      (oneChip u + oneChip v) (canonicalDivisor B.graph)) :
    (ThetaTransmissionSubTwoCase B u
        (D + t • (oneChip u - oneChip v)) → tau t = t - 2) ∧
    (ThetaTransmissionSubOneCase B u v
        (D + t • (oneChip u - oneChip v)) → tau t = t - 1) ∧
    (ThetaTransmissionAddOneCase B u v
        (D + t • (oneChip u - oneChip v)) → tau t = t + 1) ∧
    (ThetaTransmissionAddTwoCase B u v
        (D + t • (oneChip u - oneChip v)) → tau t = t + 2) ∧
    (¬ ThetaTransmissionSubTwoCase B u
        (D + t • (oneChip u - oneChip v)) →
      ¬ ThetaTransmissionSubOneCase B u v
        (D + t • (oneChip u - oneChip v)) →
      ¬ ThetaTransmissionAddOneCase B u v
        (D + t • (oneChip u - oneChip v)) →
      ¬ ThetaTransmissionAddTwoCase B u v
        (D + t • (oneChip u - oneChip v)) → tau t = t) := by
  exact Bananas.theta_transmission_characteristic_rows (toLibBanana B) u v D tau t ((isTransmissionPermutation_toLib _ _ _).mp hTau)
    hDegree hRigid

/- **Definition 4.6** (unlabeled) — non-recurrence.

> "Let [D] ∈ Pic^0(G), with order k. Call [D] non-recurrent if for every
> v ∈ V(G), there is at most one integer n ∈ {1,…,k-1} such that
> |nD+v| ≠ ∅."

Exact, restated on concrete `Fin k` torsion residues rather than
Picard-quotient classes, specialized to `[D]=[u-v]` of a `TwiceMarked`:
`Bananas.NonRecurrent` (`Bananas/Theta/ThetaNonrecurrence.lean`). -/

/-- **Lemma 4.7** (`lem:nonrecDisjoint`). Section 4.

> "If G has genus 2 and [D] ∈ Pic^0(G), then [D] is non-recurrent if and
> only if the sets {Supp(K_G-nD) : n ∈ ℤ, nD ≁ 0} are pairwise disjoint." -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_lem4_7
    {M : TwiceMarked} {k : ℕ} (hconn : graphConnected M.graph)
    (hgenus : genus M.graph = 2) :
    NonRecurrent M k ↔ CanonicalMarkedSupportsPairwiseDisjoint M k := by
  rw [nonRecurrent_toLib, canonicalMarkedSupportsPairwiseDisjoint_toLib]
  exact Bananas.nonRecurrent_iff_canonicalMarkedSupportsPairwiseDisjoint (M := toLibTM M)
    hconn hgenus

/-- **Theorem 4.8** (`thm:kgtThetas`), theta case. Section 4.

> "Suppose (G,u,v) is a rigidly marked graph of genus 2 and torsion order
> k. Then (G,u,v) has k-general transmission if and only if [u-v] ∈
> Pic^0(G) is non-recurrent."

Exact. Also proved for every nontrivial bridgeless genus-two graph as
`bridgeless_genusTwo_rigid_kGeneral_iff_nonRecurrent`
(`Bananas/Classification/BridgelessGenusTwoCornerAlgebra.lean`). "Rigidly marked" is
unbundled, as in Definition 4.4. -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_thm4_8
    {k : ℕ} (B : Banana 2) (u v : B.graph.V)
    (hSub : AllSubmodular (mark B.graph u v))
    (hTO : IsTorsionOrder (mark B.graph u v) k)
    (hRigid : ¬ linearEquiv B.graph
      (oneChip u + oneChip v) (canonicalDivisor B.graph)) :
    KGeneralTransmission (mark B.graph u v) k ↔
      NonRecurrent (mark B.graph u v) k := by
  rw [kGeneralTransmission_toLib, nonRecurrent_toLib]
  exact Bananas.thetaRigid_kGeneral_iff_nonRecurrent_class (toLibBanana B) u v ((allSubmodular_toLib _).mp hSub) hTO hRigid

/- **Definition 4.9** (unlabeled) — degree-`d` twists T^d_D.

> "Let D be a divisor on a twice-marked graph (G,u,v). Denote by T^d_D the
> set of divisor classes T^d_D = {[D+au-bv] : a,b∈ℤ, deg D+a-b=d}. Note that
> #T^d_D = k, where k is the torsion order."

Exact, as a system of representatives rather than a set of classes:
`Bananas.degreeTwistInt` (`Bananas/Theta/ThetaNonrecurrence.lean`);
`effectiveDegreeOneTwistResidues` (`Bananas/Theta/ThetaInversionCount.lean`) is
the degree-one effective-residue model used throughout Lemma 4.10. -/

/-- **Lemma 4.10** (`lem:invtau`), theta form, in full. Section 4.

> "Suppose D is submodular on a twice-marked graph (G,u,v) of genus 2.
> Then inv_k(τ_D) = #{[D'] ∈ T^1_D : |D'| ≠ ∅} + δ(0 ∈ T^0_D and
> u+v ∼ K_G)."

Exact (including the correction term). Also proved for every nontrivial
bridgeless genus-two graph as `bridgeless_genusTwo_invTau_formula`
(`Bananas/Classification/BridgelessGenusTwoCornerAlgebra.lean`). The route differs from the
paper's infinite inclusion–exclusion: three genus-two corner-sum slices,
telescoped. -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_lem4_10
    (B : Banana 2) (u v : B.graph.V) (D : CFDiv B.graph)
    (k : ℕ) (τ : ℤ → ℤ)
    (hTO : IsTorsionOrder (mark B.graph u v) k)
    (hτ : IsTransmissionPermutation (mark B.graph u v) D τ)
    (hAffine : IsKAffine k τ) :
    (kInversionCount k τ : ℤ) =
      ((effectiveDegreeOneTwistResidues (mark B.graph u v) D k).ncard : ℤ) +
        invTauCorrection (mark B.graph u v) D := by
  rw [effectiveDegreeOneTwistResidues_toLib, invTauCorrection_toLib]
  exact Bananas.intCast_kInversionCount_eq_effectiveResidues_add_correction (toLibBanana B) u v D k τ
    hTO ((isTransmissionPermutation_toLib _ _ _).mp hτ) hAffine

/- **Definition 4.11** (unlabeled) — S^{d,e}_D(E). NOT FOUND, deliberately.

> "Let D,E be two divisors on (G,u,v) of any genus. For d+e=deg E, define
> S^{d,e}_D(E) = ∑_{[D']∈T^d_D} (r(D')+1)(r(E-D')+1). Denote also
> S_D(E) = ∑_d S^{d,deg E - d}(E)."

The mechanization deliberately avoids this infinite-sum aggregate; see
Lemma 4.12 below. -/

/-- **Lemma 4.12** (`lem:invtauGeneral`), equivalent finite-period form.
Section 4.

> "Let D,E be divisors on (G,u,v) of any genus with torsion order k, D
> submodular. Then inv_k(τ_D) = S_D(K_G) - S_D(K_G-u) - S_D(K_G-v) +
> S_D(K_G-u-v)."

Corrected/equivalent: valid in every genus as claimed, but expressed as a
finite sum of complementary ranks over one fundamental period rather than
the four-term `S_D` alternating sum (which recovers exactly by expanding
`rankDelta_eq_rankPlusOne_inclusionExclusion`). The extraneous variable `E`
in the paper's own statement is unused there too. -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_lem4_12
    {M : TwiceMarked} (D : CFDiv M.graph)
    (hconn : graphConnected M.graph)
    (k : ℕ) (τ : ℤ → ℤ) (hk : 0 < k)
    (hτ : IsTransmissionPermutation M D τ)
    (hAffine : IsKAffine k τ) :
    (kInversionCount k τ : ℤ) =
      ∑ b : Fin k,
        (rank M.graph
          (canonicalDivisor M.graph - D -
            (τ b) • oneChip M.u + (b : ℤ) • oneChip M.v) + 1) := by
  simp only [rank_toLib]
  exact Bananas.intCast_kInversionCount_eq_sum_complement_rank (toLibTM M) D hconn k τ hk
    ((isTransmissionPermutation_toLib _ _ _).mp hτ) hAffine

/- **Theorem 4.13** (`thm:g2general`) — classification of k-general
transmission on bridgeless genus-two graphs.

> "If (G,u,v) is a twice-marked bridgeless graph of genus 2 and torsion
> order k, then G has k-general transmission if and only if: 1) vertex
> gluing of two twice-marked cycles of equal torsion order k; 2) vertex
> gluing of two cycles, one of length 2, marked at its two vertices; or
> 3) a theta graph with [u-v] non-recurrent and one of three coordinate
> families."

Corrected and now bundled into a single biconditional,
`s4_thm4_13` below (`kGeneralTransmission_bridgelessGenusTwo_iff` in
`Bananas/Classification/BridgelessGenusTwoClassification.lean`), which transports both
branch classifiers across the certified isomorphism supplied by the
structural seam `marked_bridgelessGenusTwo_coreNormalForm`
(`Bananas/Classification/BridgelessGenusTwoPseudocore.lean`, reducing to either a theta
graph or a wedge of two `PointedGenusOneRigid` factors, with the two marks
carried along the isomorphism). The two branch classifiers are also kept
below as standalone wrappers. -/

/-- **Theorem 4.13** (`thm:g2general`), bundled single-theorem form.
Section 4.

The characterization predicate packages the theta branch (case 3, via a
certified isomorphism to a `Banana 2` presentation with the marks located
at explicit strand coordinates) and the wedge branch (cases 1 and 2, via a
certified isomorphism to a vertex wedge of two `PointedGenusOneRigid`
factors) as a disjunction; see `BridgelessGenusTwoKGeneralCharacterization`
in `Bananas/Classification/BridgelessGenusTwoClassification.lean`. -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_thm4_13
    (G : CFGraph) (u v : G.V) (k : ℕ)
    (hConnected : graphConnected G) (hCut : TwoEdgeCutCondition G)
    (huv : u ≠ v) (hGenus : genus G = 2)
    (hTO : IsTorsionOrder (mark G u v) k) :
    KGeneralTransmission (mark G u v) k ↔
      BridgelessGenusTwoKGeneralCharacterization G u v k := by
  rw [kGeneralTransmission_toLib, bridgelessGenusTwoKGeneralCharacterization_toLib]
  exact Bananas.kGeneralTransmission_bridgelessGenusTwo_iff (toLib G) u v k hConnected hCut
    huv hGenus hTO

/-- **Theorem 4.13** (`thm:g2general`), theta branch (case 3). Section 4. -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_thm4_13_theta
    {k : ℕ} (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (hTO : IsTorsionOrder
      (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)) k) :
    KGeneralTransmission
      (mark B.graph (strandVertex B alpha i) (strandVertex B beta j)) k ↔
      ThetaKGeneralCoordinates (k := k) B alpha beta i j := by
  rw [kGeneralTransmission_toLib, thetaKGeneralCoordinates_toLib]
  exact Bananas.theta_kGeneral_iff_coordinates_nonRecurrent (toLibBanana B) alpha beta i j hTO

/-- **Theorem 4.13** (`thm:g2general`), wedge branch (cases 1 and 2),
stated intrinsically on the vertex wedge of two `PointedGenusOneRigid`
factors rather than the paper's literal `TwoPathCycle` wording. Section 4. -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_thm4_13_wedge
    (G H : CFGraph) (x : G.V) (y : H.V)
    (u v : (vertexWedge G H x y).V) (k : ℕ)
    (hG : PointedGenusOneRigid G x) (hH : PointedGenusOneRigid H y)
    (hGCut : TwoEdgeCutCondition G) (hHCut : TwoEdgeCutCondition H)
    (hWCut : TwoEdgeCutCondition (vertexWedge G H x y))
    (huv : u ≠ v) :
    KGeneralTransmission (mark (vertexWedge G H x y) u v) k ↔
      WedgeKGeneralPlacement G H x y u v k := by
  rw [kGeneralTransmission_toLib]
  exact Bananas.kGeneral_iff_wedge_placement (toLib G) (toLib H) x y u v k
    ((pointedGenusOneRigid_toLib _ _).mp hG) ((pointedGenusOneRigid_toLib _ _).mp hH)
    hGCut hHCut hWCut huv

/- **Definition 4.14** (`defn:evenlyMarked`).

> "Let (θ_{n_0,n_1,n_2},v_{α,i},v_{β,j}) be a twice-marked theta graph. We
> say it is evenly marked if i/n_α = j/n_β, α ≠ β, and 0 < i < n_α."

Exact, with the ratio equality stated by cross-multiplication:
`Bananas.EvenlyMarkedTheta` (`Bananas/Basics/Definitions.lean`). -/

/-- **Lemma 4.15** (unlabeled, TeX line 1911), annihilation half. Section 4.

> "If (θ_{n_0,n_1,n_2},v_{α,i},v_{β,j}) is evenly marked, then the class
> [v_{α,i}-v_{β,j}] is non-recurrent, with order n_α/gcd(n_α,i) =
> n_β/gcd(n_β,j) in Jac(θ_{n_0,n_1,n_2})." -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_lem4_15a
    (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (hEven : EvenlyMarkedTheta B alpha beta i j) :
    TorsionWitness
      (mark B.graph (strandVertex B alpha i) (strandVertex B beta j))
      (B.length alpha / Nat.gcd (B.length alpha) i.val) := by
  exact Bananas.evenlyMarkedTheta_torsion (toLibBanana B) alpha beta i j hEven

/-- **Lemma 4.15** (unlabeled), exact-order half. Section 4. -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_lem4_15b
    (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (hEven : EvenlyMarkedTheta B alpha beta i j) :
    IsTorsionOrder
      (mark B.graph (strandVertex B alpha i) (strandVertex B beta j))
      (B.length alpha / Nat.gcd (B.length alpha) i.val) := by
  exact Bananas.evenlyMarkedTheta_isTorsionOrder (toLibBanana B) alpha beta i j hEven

/-- **Lemma 4.15** (unlabeled), period-equality half `n_α/gcd(n_α,i) =
n_β/gcd(n_β,j)`. Section 4. -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_lem4_15c
    (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta)
    (hEven : EvenlyMarkedTheta B alpha beta i j) :
    B.length alpha / Nat.gcd (B.length alpha) i.val =
      B.length beta / Nat.gcd (B.length beta) j.val := by
  exact Bananas.evenlyMarkedTheta_periods_agree (toLibBanana B) alpha beta i j hEven

/-- **Lemma 4.15** (unlabeled), non-recurrence half. Section 4. -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_lem4_15d
    (B : Banana 2) (α β : Fin 3) (i : B.PathPosition α)
    (j : B.PathPosition β) (hEven : EvenlyMarkedTheta B α β i j) :
    NonRecurrent (mark B.graph (strandVertex B α i) (strandVertex B β j))
      (B.length α / Nat.gcd (B.length α) i.val) := by
  exact (nonRecurrent_toLib _ _).mpr
    (Bananas.evenlyMarkedTheta_nonRecurrent_class (toLibBanana B) α β i j hEven)

/- **Remark 4.16** (unlabeled) — no formal claim beyond restating equation
`eq:multDiffMarkedPts`, already used inside Lemma 4.15's proof. -/

/-- **Corollary 4.17** (`cor:evenlyMarkedKGT`). Section 4. Same content as
Theorem 1.12, part 2).

> "An evenly marked theta graph (θ_{n_0,n_1,n_2},v_{α,i},v_{β,j}) has
> k-general transmission, where k = n_α/gcd(n_α,i) = n_β/gcd(n_β,j)."

Exact, unconditional. -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_cor4_17
    (B : Banana 2) (α β : Fin 3) (i : B.PathPosition α)
    (j : B.PathPosition β)
    (hEven : EvenlyMarkedTheta B α β i j) :
    KGeneralTransmission
      (mark B.graph (strandVertex B α i) (strandVertex B β j))
      (B.length α / Nat.gcd (B.length α) i.val) := by
  exact (kGeneralTransmission_toLib _ _).mpr
    (Bananas.evenlyMarkedTheta_kGeneral (toLibBanana B) α β i j hEven)

/- **Theorem 4.18** (`thm-quadInvGrowth`) — quadratic inversion growth.

> "If (G,u,v) is a twice-marked banana graph with genus ≥ 3 where every
> divisor is submodular and the marked strands are sufficiently long, then
> M is at least quadratic in g."

**Corrected/explicit.** "Sufficiently long" is not a defined predicate in
the paper and is replaced here by the sharp numeric predicate
`CrossOneOffLongEnough g n₀ n₁ := g+1+g/(n₁-1) ≤ n₀`
(`Bananas/CrossOneOff/CrossOneOffArithmetic.lean`); "at least quadratic in g" becomes
three *explicit* lower-bound regimes below, with no single aggregate
statement. -/

/-- **Theorem 4.18**, endpoint regime. Section 4. -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_thm4_18_endpoint
    {g k : ℕ} (B : Banana g)
    (hSub : AllSubmodular
      (mark B.graph (leftEndpoint B) (rightEndpoint B)))
    (hTO : IsTorsionOrder
      (mark B.graph (leftEndpoint B) (rightEndpoint B)) k) :
    HasInversionLowerBound
      (mark B.graph (leftEndpoint B) (rightEndpoint B)) k
      (Nat.choose (g + 1) 2) := by
  exact (hasInversionLowerBound_toLib _ _ _).mpr
    (Bananas.endpoint_has_quadratic_inversion_lower_bound (toLibBanana B) ((allSubmodular_toLib _).mp hSub) hTO)

/-- **Theorem 4.18**, same-strand one-off regime. Section 4. -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_thm4_18_oneOff
    {g k : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (hg : 2 ≤ g) (hLength : 1 < B.length alpha)
    (hSub : AllSubmodular (mark B.graph (leftEndpoint B)
      (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩)))
    (hTO : IsTorsionOrder (mark B.graph (leftEndpoint B)
      (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩)) k) :
    HasInversionLowerBound (mark B.graph (leftEndpoint B)
      (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩)) k
      (Nat.choose g 2 + g / (B.length alpha - 1)) := by
  exact (hasInversionLowerBound_toLib _ _ _).mpr
    (Bananas.oneOff_has_quadratic_inversion_lower_bound (toLibBanana B) alpha hg hLength
      ((allSubmodular_toLib _).mp hSub) hTO)

/-- **Theorem 4.18**, corrected cross-one-off regime. Section 4.

**Strengthened.** The paper's marking-independent "sufficiently long"
hypothesis on the *second* strand (`hBetaLong` in the earlier formal
statement) is no longer needed: `CrossOneOffLongEnough` already forces
`B.length alpha ≥ g + 1 ≥ 4 > 2`, and the closed-form period-separation
theorem `crossOneOff_cutoff_le_torsionOrder_of_not_both_two`
(`Bananas/CrossOneOff/CrossOneOffShortStrandPeriod.lean`) supplies the needed torsion
bound for *every* pair of marked strand lengths outside `n_alpha = n_beta =
2`, which this length threshold already excludes. Only the harmless
`hBeta : 1 < B.length beta` hypothesis (implied for free by the old
`hBetaLong`) is now stated explicitly. -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_thm4_18_crossOneOff
    {g k : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (hg : 3 ≤ g) (hab : alpha ≠ beta)
    (hAlpha : 1 < B.length alpha) (hBeta : 1 < B.length beta)
    (hLong : CrossOneOffLongEnough
      g (B.length alpha) (B.length beta))
    (hSub : AllSubmodular (mark B.graph
      (strandVertex B alpha ⟨1, by omega⟩)
      (strandVertex B beta ⟨B.length beta - 1, by omega⟩)))
    (hTO : IsTorsionOrder (mark B.graph
      (strandVertex B alpha ⟨1, by omega⟩)
      (strandVertex B beta ⟨B.length beta - 1, by omega⟩)) k) :
    HasInversionLowerBound (mark B.graph
      (strandVertex B alpha ⟨1, by omega⟩)
      (strandVertex B beta ⟨B.length beta - 1, by omega⟩)) k
      (correctedCrossOneOffForcedCount g (B.length beta)) := by
  exact (hasInversionLowerBound_toLib _ _ _).mpr
    (Bananas.crossOneOff_has_quadratic_inversion_lower_bound_of_not_both_two (toLibBanana B) alpha beta
      hg hab hAlpha hBeta hLong ((allSubmodular_toLib _).mp hSub) hTO)

/-- **Proposition 4.19** (`prop-bananTorsion`), full corrected dichotomy.
Section 4.

> "If (G,u,v) is a twice-marked banana graph of genus ≥ 3 and torsion
> order k where every divisor is submodular then either: 1) up to
> reordering, n_0=n_1=2 and (G,u,v)=(G,v_{0,1},v_{1,1}), so k=2; or 2) the
> torsion order is at least the genus, k ≥ g."

**Formalization note.** The checked exception family includes distinct-strand midpoints when at least one supporting strand has length two. This is expressed by `CorrectedMidpointException`. The length-two branch now follows from the stronger revised Lemma 4.33 (`lem-midpointTorsion`); see `Bananas/FORMALIZATION_NOTES.md`. -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_prop4_19
    {g k : ℕ} (hg : 3 ≤ g) (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (hTO : IsTorsionOrder
      (mark B.graph (strandVertex B α i) (strandVertex B β j)) k)
    (hSub : AllSubmodular
      (mark B.graph (strandVertex B α i) (strandVertex B β j))) :
    (CorrectedMidpointException B α β i j ∧ k = 2) ∨ g ≤ k := by
  exact Bananas.corrected_banana_torsion_dichotomy hg (toLibBanana B) α β i j hTO ((allSubmodular_toLib _).mp hSub)

/-- **Lemma 4.20** (`lem-TriangleInversionII`), period consequence. Section
4.

> "With (G,u,v)=(B,v_{0,0},v_{0,n_0}), D=gv_{0,n_0}, τ=τ_D, for
> 0 ≤ b ≤ g we have τ(b)=g-b. As a consequence this yields k ≥ g."

Exact, and **strictly stronger than printed**: Lean proves `g < k`. (The
transmission-block statement itself is
`exists_endpoint_transmission_block`, `Bananas/SameStrand/EndpointBlock.lean`.) -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_lem4_20
    {g k : ℕ} (B : Banana g)
    (hsub : AllSubmodular (mark B.graph (leftEndpoint B) (rightEndpoint B)))
    (hk : IsTorsionOrder
      (mark B.graph (leftEndpoint B) (rightEndpoint B)) k) :
    g < k := by
  exact Bananas.endpoint_marking_torsionOrder_gt_genus (toLibBanana B) ((allSubmodular_toLib _).mp hsub) hk

/-- **Proposition 4.21** (`prop-TriangleInversionNumber`). Section 4.

> "With (G,u,v) as above, we have M ≥ C(g+1,2)." -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_prop4_21
    {g k : ℕ} (B : Banana g)
    (hsub : AllSubmodular (mark B.graph (leftEndpoint B) (rightEndpoint B)))
    (hk : IsTorsionOrder (mark B.graph (leftEndpoint B) (rightEndpoint B)) k) :
    ∃ D τ, IsTransmissionPermutation
      (mark B.graph (leftEndpoint B) (rightEndpoint B)) D τ ∧
      IsKAffine k τ ∧ Nat.choose (g + 1) 2 ≤ kInversionCount k τ := by
  obtain ⟨D, τ, hτ, hAff, hCount⟩ :=
    Bananas.endpoint_marked_inversion_lower_bound (toLibBanana B) ((allSubmodular_toLib _).mp hsub) hk
  exact ⟨D, τ, (isTransmissionPermutation_toLib _ _ _).mpr hτ, hAff, hCount⟩

/-- **Remark 4.22** (unlabeled) — completing the genus-2 picture. Section 4.

> "As a consequence this entirely completes the picture for describing
> k-general transmission in genus 2 ... By the above proposition, M ≥ 3,
> ruling out k-general transmission in such cases as well."

Exact, and **stronger**: proved for every `g ≥ 2` and every `k`,
unconditionally. This is exactly what discharges the case deferred from
Theorem 4.13's theta branch. -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_rem4_22
    {g k : ℕ} (hg : 2 ≤ g) (B : Banana g) :
    ¬ KGeneralTransmission
      (mark B.graph (leftEndpoint B) (rightEndpoint B)) k := by
  intro hK
  exact Bananas.endpoint_marking_not_kGeneral hg (toLibBanana B) ((kGeneralTransmission_toLib _ _).mp hK)

/-- **Lemma 4.23** (`lem-BananOneOff`), the uniform three-row block.
Section 4.

> "Let (G,u,v)=(G,v_{0,0},v_{0,n_0-1}), D=gv_{0,n_0}, τ=τ_D. If
> 0 ≤ b ≤ (n_0/(n_0-1))g then τ(b) is one of three residue-determined
> formulas. As a consequence, k > (n_0/(n_0-1))g."

Exact, in exact integral form (`crossOneOffCutoff`) rather than the
paper's rational cutoff; `b=0` is handled separately
(`transmission_oneOff_zero`). The period consequence is
`oneOff_affine_period_gt_cutoff`, `Bananas/CrossOneOff/OneOffPeriodBound.lean`. -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_lem4_23
    {g : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (b : ℕ) (tau : ℤ → ℤ) (hg : 2 ≤ g)
    (hLength : 1 < B.length alpha)
    (_hbLo : 1 ≤ b) (hbHi : b ≤ crossOneOffCutoff g (B.length alpha))
    (hTau : IsTransmissionPermutation
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
      (g • oneChip (rightEndpoint B)) tau) :
    tau (b : ℤ) = (oneOffRow g (B.length alpha) b : ℕ) := by
  exact Bananas.transmission_oneOff_block (toLibBanana B) alpha b tau hg hLength _hbLo hbHi
    ((isTransmissionPermutation_toLib _ _ _).mp hTau)

/- **Proposition 4.24** (unlabeled) — a preliminary bound. NOT FOUND, but
harmlessly so.

> "With the same notation as above, M ≥ C((n_0-2)f(g), 2)."

The paper immediately supersedes this with Proposition 4.25, which *is*
formalized (`oneOff_refined_inversion_lower_bound`). -/

/-- **Proposition 4.25** (`prop-oneOffNotGeneral`), simplified equivalent
form. Section 4.

> "With h(g) = f(g)(n_0-2) + min{n_0-2, f(n_0 g) - n_0 f(g)}, M ≥
> C(f(g)+1,2) + f(g)h(g) + C(h(g),2)."

Exact, in an equivalent simplified form: writing f = ⌊g/(n_α-1)⌋, the
paper's four-family count is exactly `choose(g,2) + f`. Its KGT corollary
(`oneOff_not_kGeneral_of_four_le_genus`) rules out the marking for every
`g ≥ 4`. -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_prop4_25
    {g k : ℕ} (B : Banana g) (alpha : Fin (g + 1))
    (hg : 2 ≤ g) (hLength : 1 < B.length alpha)
    (hSub : AllSubmodular
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩)))
    (hTO : IsTorsionOrder
      (mark B.graph (leftEndpoint B)
        (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩)) k) :
    ∃ tau : ℤ → ℤ,
      IsTransmissionPermutation
        (mark B.graph (leftEndpoint B)
          (strandVertex B alpha ⟨B.length alpha - 1, by omega⟩))
        (g • oneChip (rightEndpoint B)) tau ∧
      IsKAffine k tau ∧
      Nat.choose g 2 + g / (B.length alpha - 1) ≤ kInversionCount k tau := by
  obtain ⟨tau, hTau, hAff, hCount⟩ :=
    Bananas.oneOff_refined_inversion_lower_bound_ledger (toLibBanana B) alpha hg hLength
      ((allSubmodular_toLib _).mp hSub) hTO
  exact ⟨tau, (isTransmissionPermutation_toLib _ _ _).mpr hTau, hAff, hCount⟩

/- **Example 4.26** (unlabeled) — NOT FOUND. Numerical illustration of
Proposition 4.25 on `B_{5,4,4,3,3,3,3,3,3,3}`; asserts nothing beyond an
already-formalized bound plus the unformalized claim that this particular
permutation has exactly 217 `k`-inversions. -/

/-- **Lemma 4.27** (`lem-bothOffTorOrder`), near-opposite interior family.
Section 4.

> "The torsion order k of (G,v_{0,1},v_{1,n_1-1}) is at least g unless
> n_0=n_1=2, in which case k=2."

**Corrected** (same correction as Proposition 4.19): the exceptional branch
is `CorrectedMidpointException ∧ k = 2` rather than the paper's literal
`n_0=n_1=2` — for this specific marking the two agree, since zero rise does
force both strands to length two (`zero_rise_cross_oneOff_forces_both_length_two`). -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_lem4_27
    {g k : ℕ} (hg : 1 ≤ g) (B : Banana g)
    (α β : Fin (g + 1)) (i : B.PathPosition α) (j : B.PathPosition β)
    (hαβ : α ≠ β) (hiInt : B.IsInteriorPosition α i)
    (hjInt : B.IsInteriorPosition β j)
    (hi : i.val = 1) (hj : j.val + 1 = B.length β)
    (hTO : IsTorsionOrder
      (mark B.graph (strandVertex B α i) (strandVertex B β j)) k) :
    (CorrectedMidpointException B α β i j ∧ k = 2) ∨ g ≤ k := by
  exact Bananas.cross_oneOff_torsion_dichotomy hg (toLibBanana B) α β i j hαβ hiInt hjInt hi hj hTO

/-- **Lemma 4.28** (`lem-topOffBottomOffSimple`), long-strand
specialization. Section 4.

> "For max{2,g+2-n_0} ≤ b ≤ min{g-1,n_1-2} and D=gv_{0,n_0} we have
> τ_D(b)=g-b+2."

Partial/restricted: proved for the long-strand specialization
`2 ≤ b ≤ g-1` under `CrossOneOffLongEnough` rather than the paper's general
two-sided range, which is subsumed by the corrected Lemma 4.30 block
below. -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_lem4_28
    {g : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (tau : ℤ → ℤ)
    (hg : 3 ≤ g) (hab : alpha ≠ beta)
    (hAlpha : 1 < B.length alpha)
    (hBetaLong : g + 1 ≤ B.length beta)
    (hLong : CrossOneOffLongEnough g (B.length alpha) (B.length beta))
    (hTau : IsTransmissionPermutation
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩))
      (g • oneChip (rightEndpoint B)) tau) :
    ∀ i : ℕ, i ≤ g - 3 → tau (2 + i : ℕ) = (g - i : ℕ) := by
  exact Bananas.transmission_crossOneOff_simple_block (toLibBanana B) alpha beta tau hg hab hAlpha
    hBetaLong hLong ((isTransmissionPermutation_toLib _ _ _).mp hTau)

/-- **Corollary 4.29** (`cor-bothOffMin`). Section 4.

> "If min{n_0,n_1} ≥ g+1, then M ≥ C(g-2,2)."

Exact count, with two hypotheses the paper does not state explicitly:
`hSeparate : g ≤ k` (the period-separation supplied in applications by
`crossOneOff_kGeneral_period_ge_genus`) and `CrossOneOffLongEnough`
replacing "min(n_0,n_1) ≥ g+1". -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_cor4_29
    {g k : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (tau : ℤ → ℤ)
    (hg : 3 ≤ g) (hab : alpha ≠ beta)
    (hAlpha : 1 < B.length alpha)
    (hBetaLong : g + 1 ≤ B.length beta)
    (hLong : CrossOneOffLongEnough g (B.length alpha) (B.length beta))
    (hTau : IsTransmissionPermutation
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩))
      (g • oneChip (rightEndpoint B)) tau)
    (hSeparate : g ≤ k)
    (hfinite : (kInversions k tau).Finite) :
    Nat.choose (g - 2) 2 ≤ kInversionCount k tau := by
  exact Bananas.crossOneOff_simple_inversion_lower_bound (toLibBanana B) alpha beta tau hg hab
    hAlpha hBetaLong hLong ((isTransmissionPermutation_toLib _ _ _).mp hTau) hSeparate hfinite

/-- **Lemma 4.30** (`lem-topOffBottomOff`), the corrected uniform block.
Section 4.

> "If D=gv_{0,n_0}, τ=τ_D then three residue-indexed cases give τ(b) as
> b/n_1+1, g+(b+1)/n_1, or g+2⌊b/n_1⌋-b+2 according to b mod n_1."

**Formalization note.** The checked block starts at `b = 2`, uses a single positive-remainder convention, and includes the `+2` term in the positive-residue row; see `Bananas/FORMALIZATION_NOTES.md`. -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_lem4_30
    {g : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (b : ℕ) (tau : ℤ → ℤ)
    (hg : 2 ≤ g) (hab : alpha ≠ beta)
    (hAlpha : 1 < B.length alpha) (hBeta : 1 < B.length beta)
    (hLong : CrossOneOffLongEnough g (B.length alpha) (B.length beta))
    (hbLo : 2 ≤ b) (hbHi : b ≤ crossOneOffCutoff g (B.length beta))
    (hTau : IsTransmissionPermutation
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩))
      (g • oneChip (rightEndpoint B)) tau) :
    tau (b : ℤ) = (crossOneOffRow g (B.length beta) b : ℕ) := by
  exact Bananas.transmission_crossOneOff_block (toLibBanana B) alpha beta b tau hg hab hAlpha hBeta
    hLong hbLo hbHi ((isTransmissionPermutation_toLib _ _ _).mp hTau)

/-- **Corollary 4.31** (`cor-bothOffMax`). Section 4.

> "When n_0 is sufficiently large relative to the genus, then we get a
> lower bound on M which is quadratic in g."

**Formalization note.** The checked target `correctedCrossOneOffForcedCount` separates the `n = 2` and `n ≥ 3` branches, and `CrossOneOffLongEnough` makes the length threshold explicit.
The generic affine-transmission-existence lemma
(`exists_affine_transmission_of_allSubmodular`,
`Bananas/Transmission/TransmissionAPI.lean`) supplies only that existence, not this
quadratic count, so the theorem below (from
`Bananas/CrossOneOff/CrossOneOffCorrectedInversion.lean`) is the one to cite.

The required period-separation inequality is derived from the torsion order, outside the midpoint family `n_alpha = n_beta = 2` already excluded by `CrossOneOffLongEnough`, using
`crossOneOff_corrected_inversion_lower_bound_of_not_both_two`
(`Bananas/CrossOneOff/CrossOneOffCorrectedInversion.lean`, via
`crossOneOff_cutoff_le_torsionOrder_of_not_both_two`,
`Bananas/CrossOneOff/CrossOneOffShortStrandPeriod.lean`), so it is supplied internally
from the torsion order `k` instead of being assumed. -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_cor4_31
    {g k : ℕ} (B : Banana g) (alpha beta : Fin (g + 1))
    (tau : ℤ → ℤ)
    (hg : 3 ≤ g) (hab : alpha ≠ beta)
    (hAlpha : 1 < B.length alpha) (hBeta : 1 < B.length beta)
    (hLong : CrossOneOffLongEnough
      g (B.length alpha) (B.length beta))
    (hTau : IsTransmissionPermutation
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩))
      (g • oneChip (rightEndpoint B)) tau)
    (hTO : IsTorsionOrder
      (mark B.graph
        (strandVertex B alpha ⟨1, by omega⟩)
        (strandVertex B beta ⟨B.length beta - 1, by omega⟩)) k)
    (hfinite : (kInversions k tau).Finite) :
    correctedCrossOneOffForcedCount g (B.length beta) ≤
      kInversionCount k tau := by
  exact Bananas.crossOneOff_corrected_inversion_lower_bound_of_not_both_two (toLibBanana B) alpha
    beta tau hg hab hAlpha hBeta hLong ((isTransmissionPermutation_toLib _ _ _).mp hTau) hTO hfinite

/- **Remark 4.32** (unlabeled) — no formal claim. Notes only that a
symmetric result to Corollary 4.31 "could be developed" via `gv_{0,0}`;
states no theorem. (`isTorsionOrder_swap_marks`,
`Bananas/Jacobian/BananaTorsionSlopes.lean`, supplies the mark-swap machinery such a
development would use.) -/

/-- **Lemma 4.33** (`lem-midpointTorsion`), even multiples, added in the
revised manuscript. If one mark is the midpoint of a length-two strand and
`1 ≤ j < n_beta / 2` on a distinct strand, no positive even `k ≤ 2g - 2`
annihilates the marked difference. No all-divisor submodularity or exactness
of the proposed period is assumed. -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_lem4_33a
    {g k : ℕ} (_hg : 2 ≤ g) (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (_hαβ : α ≠ β) (hαLen : B.length α = 2) (hi : i.val = 1)
    (hj : 1 ≤ j.val) (hjHalf : 2 * j.val < B.length β)
    (hk : 0 < k) (heven : Even k) (hbound : k ≤ 2 * g - 2) :
    ¬ linearEquiv B.graph
      ((k : ℤ) • oneChip (strandVertex B α i))
      ((k : ℤ) • oneChip (strandVertex B β j)) := by
  exact Bananas.midpoint_not_linearEquiv_even_multiple (toLibBanana B) α β i j
    (show 2 * i.val = B.length α by omega)
    (show B.IsInteriorPosition β j from ⟨by omega, by omega⟩)
    (show 2 * j.val ≠ B.length β by omega) hk heven hbound

/-- **Lemma 4.33** (`lem-midpointTorsion`), arbitrary small multiples.
Doubling a putative positive period `k < g` contradicts the even-multiple
assertion, so the torsion order is at least the genus. -/
theorem _root_.Bananas.TwiceMarkedBananas.s4_lem4_33b
    {g k : ℕ} (_hg : 2 ≤ g) (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (_hαβ : α ≠ β) (hαLen : B.length α = 2) (hi : i.val = 1)
    (hj : 1 ≤ j.val) (hjHalf : 2 * j.val < B.length β)
    (hk : 0 < k) (hbound : k < g) :
    ¬ linearEquiv B.graph
      ((k : ℤ) • oneChip (strandVertex B α i))
      ((k : ℤ) • oneChip (strandVertex B β j)) := by
  exact Bananas.midpoint_not_linearEquiv_small_multiple (toLibBanana B) α β i j
    (show 2 * i.val = B.length α by omega)
    (show B.IsInteriorPosition β j from ⟨by omega, by omega⟩)
    (show 2 * j.val ≠ B.length β by omega) hk hbound

/-!
## Section 5 — Symmetries and Quasi-Symmetries of Transmission Permutations
-/

/-- Displayed equation `eq-RRTauBounds`, lower bound. Section 5 preamble.

> "b - deg D ≤ τ_D(b) ≤ 2g + b - deg D." -/
theorem _root_.Bananas.TwiceMarkedBananas.s5_eqRRTauBounds_lower
    {M : TwiceMarked} {D : CFDiv M.graph} {τ : ℤ → ℤ}
    (hτ : IsTransmissionPermutation M D τ) (b : ℤ) :
    b - deg D ≤ τ b := by
  exact Bananas.transmissionPermutation_ge (M := toLibTM M) ((isTransmissionPermutation_toLib _ _ _).mp hτ) b

/-- Displayed equation `eq-RRTauBounds`, upper bound. Section 5 preamble.
Needs connectivity (Riemann's inequality); the lower bound does not. -/
theorem _root_.Bananas.TwiceMarkedBananas.s5_eqRRTauBounds_upper
    {M : TwiceMarked} {D : CFDiv M.graph} {τ : ℤ → ℤ}
    (hconn : graphConnected M.graph)
    (hτ : IsTransmissionPermutation M D τ) (b : ℤ) :
    τ b ≤ 2 * genus M.graph + b - deg D := by
  exact Bananas.transmissionPermutation_le (M := toLibTM M) hconn ((isTransmissionPermutation_toLib _ _ _).mp hτ) b

/- **Definition 5.1** (unlabeled) — marked point automorphism.

> "For a twice-marked graph (G,u,v) a marked point automorphism φ is a pair
> φ_V, φ_E of bijections respecting incidence. We further require that φ_V
> restricts to a bijection of the marked points."

Formalized as `Bananas.MarkedPointAutomorphism`
(`Bananas/Sections/SectionFiveDefinitions.lean`), using `CFGraphIso` (a vertex
`Equiv` plus edge-multiplicity preservation) rather than the paper's
explicit `(φ_V,φ_E)` pair; "restricts to a bijection of the marked points"
becomes a set-level iff permitting either fixing or swapping the marks.
`MarkedPointSwap` is the further specialization to mark-swapping
automorphisms used by Lemma 5.3. Note: the paper's induced action
`(φ(D))(w)=D(φ(w))` is a pull-back, while Lean's `CFGraphIso.mapDiv` is the
push-forward; since every hypothesis below quantifies over an arbitrary
automorphism and `MarkedPointSwap` is closed under inverse, no statement is
weakened by this choice. -/

/-- **Lemma 5.2** (`lem:mpIds`), part 2). Section 5. Value half only; the
substantive transport half is `IsTransmissionPermutation.swap_marks`
(`Bananas/Transmission/KGeneralSwap.lean`).

> "If φ is a marked point automorphism of (G,u,v) then: ... 2)
> τ_D^{v,u}(-a) = -b [is equivalent to 1) τ_D(b)=a]." -/
theorem _root_.Bananas.TwiceMarkedBananas.s5_lem5_2_2
    {M : TwiceMarked} {D : CFDiv M.graph} {tau : ℤ → ℤ}
    (hTau : IsTransmissionPermutation M D tau) (a b : ℤ) :
    tau b = a ↔ swapTransmissionPermutation tau (-a) = -b := by
  exact Bananas.sectionFive_swap_value_iff (M := toLibTM M) ((isTransmissionPermutation_toLib _ _ _).mp hTau) a b

/-- **Lemma 5.2** (`lem:mpIds`), part 3). Section 5.

> "3) τ_{ι(D)}^{v,u}(a)=b, where ι(D)=K_G-D+u+v."

Stronger than the paper's value form: identifies the *whole* transmission
permutation of `ι(D)` at the exchanged marks as `rawInverse tau`. -/
theorem _root_.Bananas.TwiceMarkedBananas.s5_lem5_2_3
    {G : CFGraph} (hconn : graphConnected G) (u v : G.V)
    {D : CFDiv G} {tau : ℤ → ℤ}
    (hTau : IsTransmissionPermutation (mark G u v) D tau) :
    IsTransmissionPermutation (mark G v u)
      (transmissionDualDivisor u v D) (rawInverse tau) := by
  exact (isTransmissionPermutation_toLib _ _ _).mpr
    (Bananas.sectionFive_dual_transmission (G := toLib G) hconn u v ((isTransmissionPermutation_toLib _ _ _).mp hTau))

/-- **Lemma 5.2** (`lem:mpIds`), part 4). Section 5.

> "4) τ_{φ(D)}^{φ(u),φ(v)}(b)=a."

Stronger than the paper's value form (the transported data has literally
the same raw permutation `tau`), and generalized to an arbitrary
`CFGraphIso G H` rather than an automorphism, without requiring `phi` to
preserve the marked set. -/
theorem _root_.Bananas.TwiceMarkedBananas.s5_lem5_2_4
    {G H : CFGraph} (phi : CFGraphIso G H) (u v : G.V)
    {D : CFDiv G} {tau : ℤ → ℤ}
    (hTau : IsTransmissionPermutation (mark G u v) D tau) :
    IsTransmissionPermutation
      (mark H (phi.vertexEquiv u) (phi.vertexEquiv v))
      (phi.mapDiv D) tau := by
  exact (isTransmissionPermutation_toLib _ _ _).mpr
    (Bananas.sectionFive_map_transmission (toLibIso phi) u v ((isTransmissionPermutation_toLib _ _ _).mp hTau))

/-- **Lemma 5.3** (`lem-tauSyms`), part 1). Section 5.

> "Let (G,u,v) be twice-marked, φ a marked point automorphism transposing
> u,v. 1) If φ(D)+D ∼ K_G+u+v then δ(τ_D(b)=a)=δ(τ_D(a)=b), i.e.
> (τ_D)² = id."

Faithful: the hypothesis is the equivalent solved form `φ(D) ∼
K_G-D+u+v`, and the conclusion is the iff form, equivalent to `τ²=id` given
bijectivity. -/
theorem _root_.Bananas.TwiceMarkedBananas.s5_lem5_3_1
    {M : TwiceMarked} (hconn : graphConnected M.graph)
    (phi : MarkedPointSwap M)
    {D : CFDiv M.graph} {tau : ℤ → ℤ}
    (hTau : IsTransmissionPermutation M D tau)
    (hDual : linearEquiv M.graph
      (phi.toMarkedPointAutomorphism.iso.mapDiv D)
      (transmissionDualDivisor M.u M.v D)) :
    ∀ a b : ℤ, tau b = a ↔ tau a = b := by
  exact Bananas.sectionFive_tau_involutive_of_dual_automorphism (M := toLibTM M) hconn
    (toLibSwap phi) ((isTransmissionPermutation_toLib _ _ _).mp hTau) hDual

/-- **Lemma 5.3** (`lem-tauSyms`), part 2). Section 5. Needs no
connectivity — its proof routes only through Lemma 5.2, parts 1,2,4.

> "2) If φ(D)-D ∼ n(u-v) for some n∈ℤ then δ(τ_D(b)=a)=δ(τ_D(n-a)=n-b)." -/
theorem _root_.Bananas.TwiceMarkedBananas.s5_lem5_3_2
    {M : TwiceMarked} (phi : MarkedPointSwap M)
    {D : CFDiv M.graph} {tau : ℤ → ℤ} (n : ℤ)
    (hTau : IsTransmissionPermutation M D tau)
    (hTwist : linearEquiv M.graph
      (phi.toMarkedPointAutomorphism.iso.mapDiv D - D)
      (n • (oneChip M.u - oneChip M.v))) :
    ∀ a b : ℤ, tau b = a ↔ tau (n - a) = n - b := by
  exact Bananas.sectionFive_tau_reflection_of_twisted_automorphism (M := toLibTM M)
    (toLibSwap phi) n ((isTransmissionPermutation_toLib _ _ _).mp hTau) hTwist

/- **Example 5.4** (unlabeled) — deliberately not formalized (illustration
only). Instantiates Lemma 5.3 on the `(g+1)`-valently-marked bananas of
§4.4.4 and the both-off markings of §4.4.3 with `n_0=n_1`. -/

/-- **Proposition 5.5** (unlabeled), the final unlabelled proposition of
Section 5. Section 5.

> "If φ is a marked point automorphism of (G,u,v) and D such that
> φ(D)+D ∼ K_G+u+v, then inv_k(τ_D) ≥ ∑_{M∈[k]} [r(D+(M-1)u-Mv) -
> r(D+(M-2)u-Mv)]."

The self-inverse hypothesis is deliberately refactored to a direct
hypothesis `hInvolutive` rather than the paper's `φ(D)+D∼K_G+u+v` — Lemma
5.3(1) supplies it from a marked-point automorphism, so the paper's literal
statement is the (unbundled) composite of that lemma with this one. Two
further hypotheses are made explicit: `0 < k` and `IsKAffine k tau`
(the paper's `τ_D ∈ Ẽa_k`). -/
theorem _root_.Bananas.TwiceMarkedBananas.s5_prop5_5
    {M : TwiceMarked} {D : CFDiv M.graph} {tau : ℤ → ℤ} {k : ℕ}
    (hk : 0 < k) (hconn : graphConnected M.graph)
    (hTau : IsTransmissionPermutation M D tau)
    (hAffine : IsKAffine k tau)
    (hInvolutive : ∀ a b : ℤ, tau b = a ↔ tau a = b) :
    sectionFiveRankDropSum M D k ≤ kInversionCount k tau := by
  rw [sectionFiveRankDropSum_toLib]
  exact Bananas.sectionFive_inversion_lower_bound_of_involutive_transmission (M := toLibTM M)
    hk hconn ((isTransmissionPermutation_toLib _ _ _).mp hTau) hAffine hInvolutive

/- **Remark 5.6** (unlabeled) — quasi-symmetry. No formal claim; the paper
itself states it has "no formal definition" and "no framework" for this
phenomenon (the near-periodicity of transmission permutations at a proper
divisor of the torsion order). -/

/-!
## Section 6 — Chains of mixed torsion orders

`OnceMarkedBrillNoetherGeneral` throughout is Definition 1.9, above.
-/

/-- **Proposition 6.1** (`prop:kgt-bngenl`). Section 6.

> "If (G,u,v) is a twice-marked graph of genus g with k-general
> transmission, and k ≥ g/2+1, then G is Brill--Noether general (as an
> unmarked graph)."

**Corrected (natural-number threshold).** The paper's real threshold
`k ≥ g/2+1` is formalized as `g+2 ≤ 2k`; the naive `g/2+1 ≤ k` is too weak
for odd `g` (`Bananas/FORMALIZATION_NOTES.md`). Rests on a
crossing-inversion pigeonhole argument, `Bananas/CrossOneOff/CrossingInversionCount.lean`. -/
theorem _root_.Bananas.TwiceMarkedBananas.s6_prop6_1
    {M : TwiceMarked} {g k : ℕ}
    (hconn : graphConnected M.graph)
    (hgenus : genus M.graph = g)
    (hK : KGeneralTransmission M k)
    (hthreshold : g + 2 ≤ 2 * k) :
    BrillNoetherGeneral M.graph := by
  exact (brillNoetherGeneral_toLib _).mpr
    (Bananas.kGeneralTransmission_brillNoetherGeneral (M := toLibTM M) hconn hgenus
      ((kGeneralTransmission_toLib _ _).mp hK) hthreshold)

/-- The equal-torsion chain corollary following Proposition 6.1 (unlabeled
in the source). Section 6.

> "Let (G_i,u_i,v_i), i=1,…,ℓ, ..., and (G,u,v) the iterated vertex gluing.
> If each (G_i,u_i,v_i) has k-general transmission for the *same* k, and
> k ≥ ½(g_1+…+g_ℓ)+1, then G is Brill--Noether general."

Corrected threshold, as in Proposition 6.1. The paper cites [Pfl22, Thm A]
for preservation of `k`-general transmission under chaining; Lean re-proves
it via the affine reduction developed for Proposition 6.13 instead of
importing it. -/
theorem _root_.Bananas.TwiceMarkedBananas.s6_cor6_3
    (M : MarkedGraph) (L : List MarkedGraph) (k : ℕ)
    (hMconn : graphConnected M.graph)
    (hMK : KGeneralTransmission (mark M.graph M.left M.right) k)
    (hLconn : ∀ N ∈ L, graphConnected N.graph)
    (hLK : ∀ N ∈ L, KGeneralTransmission (mark N.graph N.left N.right) k)
    (hthreshold : (genus (M.chain L).graph).toNat + 2 ≤ 2 * k) :
    BrillNoetherGeneral (M.chain L).graph := by
  have h := Bananas.brillNoetherGeneral_markedChain_of_commonPeriod (toLibMG M)
    (L.map toLibMG) k hMconn ((kGeneralTransmission_toLib _ _).mp hMK)
    (fun N hN => by
      obtain ⟨N₀, hN₀, rfl⟩ := List.mem_map.mp hN
      exact hLconn N₀ hN₀)
    (fun N hN => by
      obtain ⟨N₀, hN₀, rfl⟩ := List.mem_map.mp hN
      exact (kGeneralTransmission_toLib _ _).mp (hLK N₀ hN₀))
    (by rw [← toLibMG_chain]; exact hthreshold)
  rw [← toLibMG_chain] at h
  exact (brillNoetherGeneral_toLib _).mpr h

/-- **Corollary 6.4** (`cor:bananasWithKGT`). Section 6.

> "The only banana graphs of genus ≥ 3 which have k-general transmission
> are (B_{n_0,…,n_g},v_{α,1},v_{β,1}) with α≠β, n_α=n_β=2; these examples
> have 2-general transmission."

**Corrected**, same correction as Proposition 4.19: the exceptional family
only demands the two marks be distinct-strand *midpoints* with at least one
strand of length two, not literally `n_α=n_β=2`. -/
theorem _root_.Bananas.TwiceMarkedBananas.s6_cor6_4
    {g k : ℕ} (hg : 3 ≤ g) (B : Banana g) (α β : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β) :
    KGeneralTransmission
      (mark B.graph (strandVertex B α i) (strandVertex B β j)) k ↔
      CorrectedMidpointException B α β i j ∧ k = 2 := by
  rw [kGeneralTransmission_toLib]
  exact Bananas.corrected_banana_kGeneral_iff hg (toLibBanana B) α β i j

/-- **Theorem 6.6** (`thm:glueBNGtoKGT`). Section 6.

> "Let (G_1,u_1,v_1),(G_2,u_2,v_2) be twice-marked graphs of genera g_1,g_2
> on which all divisors are submodular, (G,u,v)=(G,u_1,v_2) their vertex
> gluing. Suppose (G_1,v_1) is Brill--Noether general as a marked graph, and
> (G_2,u_2,v_2) has k-general transmission with k > g_1+g_2. Then (G,v) is
> Brill--Noether general."

Exact modulo the added connectedness hypotheses. The paper's Remark 6.7
(that `u_1` and the submodularity of `(G_1,u_1,v_1)` are probably removable)
is **not** discharged: `hGsub` and `u` are still present. -/
theorem _root_.Bananas.TwiceMarkedBananas.s6_thm6_6
    (G H : CFGraph) (u x : G.V) (y v : H.V)
    (hGconn : graphConnected G)
    (hHconn : graphConnected H)
    (hGsub : AllSubmodular (mark G u x))
    (hGgeneral : OnceMarkedBrillNoetherGeneral G x)
    {k : ℕ} (hK : KGeneralTransmission (mark H y v) k)
    (hbudget : genus G + genus H < (k : ℤ)) :
    OnceMarkedBrillNoetherGeneral
      (vertexWedge G H x y) (wedgeRightVertex G H x y v) := by
  exact (onceMarkedBrillNoetherGeneral_toLib _ _).mpr
    (Bananas.onceMarkedBrillNoetherGeneral_vertexWedge_of_kGeneralTransmission (toLib G)
      (toLib H) u x y v hGconn hHconn ((allSubmodular_toLib _).mp hGsub)
      ((onceMarkedBrillNoetherGeneral_toLib _ _).mp hGgeneral) ((kGeneralTransmission_toLib _ _).mp hK) hbudget)

/-- The one-vertex specialization following Theorem 6.6 (unlabeled in the
source). Section 6.

> "If (G,u,v) is a twice-marked graph of genus g with k-general
> transmission, and k > g, then (G,v) is a Brill--Noether general
> once-marked graph."

Exact statement; the *proof* route differs from a literal specialization of
Theorem 6.6 (an identity Demazure factor rather than a genus-0 one-vertex
graph model). -/
theorem _root_.Bananas.TwiceMarkedBananas.s6_cor6_8
    {G : CFGraph} (u v : G.V)
    (hGconn : graphConnected G)
    {k : ℕ} (hK : KGeneralTransmission (mark G u v) k)
    (hbudget : genus G < (k : ℤ)) :
    OnceMarkedBrillNoetherGeneral G v := by
  exact (onceMarkedBrillNoetherGeneral_toLib _ _).mpr
    (Bananas.onceMarkedBrillNoetherGeneral_of_kGeneralTransmission (G := toLib G) u v hGconn
      ((kGeneralTransmission_toLib _ _).mp hK) hbudget)

/- **Definition 6.9** (unlabeled) — sign-changing inversions.

> "A sign-changing inversion of a permutation α is a pair (u,v)∈ℤ² with
> u<v and α(u)>0≥α(v). Denote the number of sign-changing inversions by
> sci(α)."

Exact: `Bananas.sci` / `.sciSet`
(`Bananas/CrossOneOff/SignChangingInversions.lean`); the `Set.ncard`-on-infinite-sets
convention applies, as with `kInversionCount`. -/

/-- **Proposition 6.10** (`prop:sciLambda`). Section 6.

> "If D is a submodular divisor on a twice-marked graph (G,u,v), then
> sci(τ_D) = |λ(D,v)|." -/
theorem _root_.Bananas.TwiceMarkedBananas.s6_prop6_10
    {G : CFGraph} (u v : G.V) (hG : graphConnected G)
    (D : CFDiv G) (tau : ℤ → ℤ)
    (hTau : IsTransmissionPermutation (mark G u v) D tau) :
    sci tau = weierstrassSize hG v D := by
  rw [weierstrassSize_toLib]
  exact Bananas.sci_eq_weierstrassSize (G := toLib G) u v ((graph_connected_toLib G).mp hG) D tau
    ((isTransmissionPermutation_toLib _ _ _).mp hTau)




/-- **Proposition 6.14** (`prop:glueMarked`). Section 6.

> "If (G_1,v_1),(G_2,v_2) are Brill--Noether general marked graphs of
> genera g_1,g_2, and G is the genus g_1+g_2 graph gluing v_1 to v_2, then
> G is Brill--Noether general."

Exact; the genus additivity is `genus_vertexWedge`, not a hypothesis. The
paper's appeal to [Pfl22, Prop. 3.15] is replaced by the library's exact
wedge rank formula
(`VertexWedgeRankFormula.vertexWedge_rank_ge_iff_profile_inequalities`).
Remark 6.15 (the max-formula for `r(D)`) is a remark with no separate
formal counterpart. -/
theorem _root_.Bananas.TwiceMarkedBananas.s6_prop6_14
    (G : CFGraph.{u}) (H : CFGraph.{v})
    (hG : graphConnected G) (hH : graphConnected H)
    (x : G.V) (y : H.V)
    (hGeneralG : OnceMarkedBrillNoetherGeneral G x)
    (hGeneralH : OnceMarkedBrillNoetherGeneral H y) :
    BrillNoetherGeneral (vertexWedge G H x y) := by
  exact (brillNoetherGeneral_toLib _).mpr
    (Bananas.onceMarkedBrillNoetherGeneral_vertexWedge (toLib G) (toLib H) hG hH x y
      ((onceMarkedBrillNoetherGeneral_toLib _ _).mp hGeneralG)
      ((onceMarkedBrillNoetherGeneral_toLib _ _).mp hGeneralH))

/-- **Corollary 6.16** (`\Cref{thm:bngChain}` — this is Theorem 1.13's body
proof, restated), part 1). Section 6.

Same statement and same Lean wrapper as `s1_thm1_13a`, above. The paper's
displayed definition of the iterated gluing "(G,u,v)=(G,u_1,v_ℓ)" is
self-referential (`Bananas/FORMALIZATION_NOTES.md`, "Chain theorem notation"; the same
pattern recurs in Corollary 6.3 and Theorem 6.6); Lean uses the intended
left-associated `MarkedGraph.chain`. -/
theorem _root_.Bananas.TwiceMarkedBananas.s6_cor6_16a
    (head : KGeneralChainFactor) (tail : List KGeneralChainFactor)
    (hHeadBudget : genus head.marked.graph < (head.period : ℤ))
    (hTailBudget : ChainPrefixBudget (genus head.marked.graph) tail) :
    OnceMarkedBrillNoetherGeneral
      (head.marked.chain (tail.map KGeneralChainFactor.marked)).graph
      (head.marked.chain (tail.map KGeneralChainFactor.marked)).right := by
  have h := Bananas.onceMarkedBrillNoetherGeneral_mixedTorsionChain (toLibFactor head)
    (tail.map toLibFactor) hHeadBudget ((chainPrefixBudget_toLib _ _).mp hTailBudget)
  rw [List.map_map] at h
  refine (onceMarkedBrillNoetherGeneral_chain_toLib _ _).mpr ?_
  rw [List.map_map]
  exact h

/-- **Corollary 6.16** (`\Cref{thm:bngChain}`), part 2). Section 6. Same
statement and same Lean wrapper as `s1_thm1_13b`, above, in the paper's full
graph convention (connected genus-zero factors allowed anywhere). -/
theorem _root_.Bananas.TwiceMarkedBananas.s6_cor6_16b
    (F : KGeneralChainFactor) (tail : List KGeneralChainFactor)
    (hMin : ChainMinBudget (F :: tail)) :
    BrillNoetherGeneral
      (F.marked.chain (tail.map KGeneralChainFactor.marked)).graph := by
  have h := Bananas.brillNoetherGeneral_mixedTorsionChain_of_minBudget (toLibFactor F)
    (tail.map toLibFactor) ((chainMinBudget_toLib _).mp hMin)
  rw [List.map_map] at h
  rw [brillNoetherGeneral_toLib, toLib_chain_graph, List.map_map]
  exact h

end TMB

/-!
## Library-vocabulary wrappers without a standalone counterpart

The five entries below are stated over the implementation library's own
vocabulary, because their types intrinsically involve implementation
objects: concrete proof-carrying chain factors (Example 1.15), the
bridgeless degree-one class map (Lemma 2.3, part 2), and the affine
symmetric-group permutations `AspPerm` (Equation 6.11, Lemma 6.12,
Proposition 6.13).  They have no counterpart in the statement-only audit
copy and are not part of the Comparator target list.
-/

namespace Bananas.TwiceMarkedBananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

universe u v

/-- **Example 1.15** (`eg:bng`). Section 1.

> "As an example, we exhibit an explicit genus-8 Brill–Noether general graph
> using the chain construction: glue the cycle B_{3,1}, the evenly marked
> theta graph θ_{4,1,4} marked at (x_1,z_1), the cycle B_{3,2}, the evenly
> marked theta graph θ_{5,2,10} marked at (x_2,z_4), and the evenly marked
> theta graph θ_{6,2,3} marked at (x_4,z_2)."

Exact, as a concrete five-factor instantiation
(`Bananas/Examples/ExampleBngChain.lean`). The two cycle factors use
`cycle_kGeneralTransmission` (Example 1.11); the three theta factors use
`evenlyMarkedTheta_kGeneral`; the chain conclusion is
`brillNoetherGeneral_mixedTorsionChain_of_minBudget`. Concrete `Banana g`
instances are built by `bananaOfLengths`, a two-vertex core with `g + 1`
parallel positive-length strands. The five per-factor torsion orders are
`4, 4, 5, 5, 3` (`Bananas/Examples/ExampleBngChain.lean`'s `bngF1`–`bngF5`), matching
the paper's own per-factor computations rather than its displayed
`4, 5, 5, 5, 3` (`Bananas/FORMALIZATION_NOTES.md`); the discrepancy is immaterial, since
`bngChainMinBudget` checks the minimum-budget hypothesis directly against
the correct values. -/
theorem s1_eg1_15 :
    BrillNoetherGeneral
      (bngF1.marked.chain
        ([bngF2, bngF3, bngF4, bngF5].map KGeneralChainFactor.marked)).graph :=
  exampleBng_brillNoetherGeneral

/-- **Lemma 2.3** (`lem-bridgelessFacts`), part 2). Section 2.

> "2) There is a bijection between rank 0 divisors in Pic^1(G) and vertices
> in V(G)."

**Corrected**: false as printed for the edgeless one-vertex graph (whose
unique degree-one class has rank one), so an explicit nontriviality
hypothesis `∃ p q, p ≠ q` is added. -/
theorem s2_lem2_3b
    (G : CFGraph) (hConnected : _root_.graphConnected G)
    (hCut : TwoEdgeCutCondition G)
    (hNontrivial : ∃ p q : G.V, p ≠ q) :
    Function.Bijective
      (bridgelessDegreeOneClassMap G hConnected hCut hNontrivial) :=
  bridgelessDegreeOneClassMap_bijective G hConnected hCut hNontrivial

/-- Equation 6.11 (`eq:tauGlued`, alongside `eq:starSigma`). Section 6.

> "If (G,u,v) is the vertex gluing of (G_1,u_1,v_1) and (G_2,u_2,v_2), D_1
> submodular on G_1, D_2 submodular on G_2, then D=D_1+D_2 is submodular on
> G and τ_D = τ_{D_1} ⋆ τ_{D_2}."

Proved in the inequality (`SatisfiesTransmission`) formulation rather than
as a literal equality of permutations; the equality form used by Theorem
6.6 is `exists_isTransmissionPermutation_wedgeAddDivisor_star`. Equation
`eq:starSigma` ([PflDemProd, Thm 8.7]) is imported from the `demazure`
dependency as `Demazure.Transpositions.starSigma`. -/
theorem s6_eq6_11
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (D : CFDiv G) (E : CFDiv H) (u : G.V) (v : H.V)
    (alpha beta : AspPerm)
    (hD : SatisfiesTransmission G u x alpha D)
    (hE : SatisfiesTransmission H y v beta E) :
    SatisfiesTransmission (vertexWedge G H x y) (Sum.inl u)
      (wedgeRightVertex G H x y v) (alpha ⋆ beta)
      (wedgeAddDivisor G H x y D E) :=
  satisfiesTransmission_wedgeAddDivisor_star G H x y D E u v alpha beta hD hE

/-- **Lemma 6.12** (`lem-SciSimpleRefl`). Section 6.

> "Let k ≥ 2, α ∈ Asp with sci(α) ≤ k-2. For any n, sci(α ⋆ σ^k_n) ≤
> sci(α)+1."

Slightly **more general** than the paper: instead of the specific affine
reflection `σ^k_n = σ_{n+kℤ}`, it takes any non-consecutive support set `S`
all of whose elements are congruent mod `k`. -/
theorem s6_lem6_12
    (k : ℤ) (α : AspPerm) (S : Set ℤ) (hS : Transpositions.NoConsecutive S)
    (hcong : ∀ l₁ ∈ S, ∀ l₂ ∈ S, k ∣ (l₂ - l₁))
    (hfin : (sciSet α.func).Finite)
    (hsci : (sci α.func : ℤ) ≤ k - 2) :
    (sci (α ⋆ Transpositions.sigma S hS).func : ℤ) ≤ (sci α.func : ℤ) + 1 :=
  sci_star_sigma_le k α S hS hcong hfin hsci

/-- **Proposition 6.13** (`prop:sciInvStar`). Section 6.

> "Suppose α ∈ Asp and β ∈ Ẽa_k satisfy k > sci(α) + inv_k(β). Then
> sci(α ⋆ β) ≤ sci(α) + inv_k(β)."

Literal match, with the affine Coxeter reduction discharged
unconditionally. -/
theorem s6_prop6_13
    (k : ℕ) (α β : AspPerm)
    (hβ : IsKAffine k β.func)
    (hbudget : (sci α.func : ℤ) + (kInversionCount k β.func : ℤ) < (k : ℤ)) :
    (sci (α ⋆ β).func : ℤ) ≤
      (sci α.func : ℤ) + (kInversionCount k β.func : ℤ) :=
  sci_star_le k α β hβ hbudget

end Bananas.TwiceMarkedBananas
