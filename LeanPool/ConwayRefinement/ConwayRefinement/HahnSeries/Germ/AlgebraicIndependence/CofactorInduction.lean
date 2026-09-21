/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.GlobalCofactors
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.LowerTruncationDegree
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.SeparatedPieceCantorBendixson
public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.CantorBendixsonConvexCover
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.ComponentsSpan
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.Components
import Mathlib.Algebra.MvPolynomial.CommRing
import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.GradedRing.HomogeneousSpan
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Boundary
import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.LeftNeighborhood

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Cofactors by well-founded induction

This file constructs global cofactors by well-founded induction at arbitrary cofinality. Helper
lemmas transfer translated truncations between a sum, its terms on disjoint ordered convex
carriers, and the local series translated to the piece centers, all modulo series bounded strictly
below zero.
-/

public noncomputable section

open Set Filter Topology MvPolynomial
open scoped NatOrdinal DirectSum

universe u v w x

namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [Field K] [CharZero K]

local notation "ν" => (cantorBendixsonDegreeValuation (G := G) (R := K))

/-- Reversing a difference preserves the property of having degree bottom. -/
theorem degree_reverse_sub_eq_bot {a b : Nonpositive G K} (h : ν (a - b) = ⊥) :
    ν (b - a) = ⊥ := by
  rw [← (ν).map_neg, neg_sub]
  exact h

/-- Reversing a difference preserves every strict degree bound. -/
theorem degree_reverse_sub_lt {a b : Nonpositive G K} {τ : WithBot NatOrdinal}
    (h : ν (a - b) < τ) : ν (b - a) < τ := by
  rw [← (ν).map_neg, neg_sub]
  exact h

/-- Three summands satisfying a common degree bound have a sum satisfying that bound. -/
theorem degree_add_add_le {a b c : Nonpositive G K} {τ : WithBot NatOrdinal}
    (ha : ν a ≤ τ) (hb : ν b ≤ τ) (hc : ν c ≤ τ) : ν (a + b + c) ≤ τ :=
  ((ν).map_add_le_max _ _).trans
    (max_le (((ν).map_add_le_max _ _).trans (max_le ha hb)) hc)

/-- Two terms and a finite family satisfying a common degree bound have a sum satisfying that
bound. -/
theorem degree_add_add_sum_le {J : Type w} [Fintype J]
    {a b : Nonpositive G K} {f : J → Nonpositive G K} {τ : WithBot NatOrdinal}
    (ha : ν a ≤ τ) (hb : ν b ≤ τ) (hf : ∀ j, ν (f j) ≤ τ) :
    ν (a + b + ∑ j, f j) ≤ τ :=
  ((ν).map_add_le_max _ _).trans (max_le
    (((ν).map_add_le_max _ _).trans (max_le ha hb))
      ((ν).map_sum_le_of_forall_le Finset.univ f τ fun j _ ↦ hf j))

/-- Degrees agree modulo series bounded strictly below zero. -/
theorem degree_eq_of_degree_sub_eq_bot {a b : Nonpositive G K}
    (h : ν (a - b) = ⊥) : ν a = ν b := by
  have h1 : ν a ≤ ν b := by
    have := (ν).map_add_le_max (a - b) b
    rw [sub_add_cancel, h, max_eq_right bot_le] at this
    exact this
  have h2 : ν b ≤ ν a := by
    have hba : ν (b - a) = ⊥ := degree_reverse_sub_eq_bot h
    have := (ν).map_add_le_max (b - a) a
    rw [sub_add_cancel, hba, max_eq_right bot_le] at this
    exact this
  exact le_antisymm h1 h2

/-- The strict tail of a nonpositive series above a cutoff. -/
def strictTail (c : G) (b : Nonpositive G K) : Nonpositive G K :=
  ⟨truncGT c (b : HahnSeries G K), fun _ hg ↦ b.property (support_truncGT_subset c _ hg)⟩

/-- Cutting away everything at or below a negative cutoff does not change the germ at zero. -/
theorem degree_sub_strictTail_eq_bot {c : G} (hc : c < 0) (b : Nonpositive G K) :
    ν (b - strictTail c b) = ⊥ := by
  apply (cantorBendixsonDegreeValuation_eq_bot_iff _).mpr
  refine ⟨c, hc, ?_⟩
  intro g hg
  have hg' : (b : HahnSeries G K).coeff g -
      (truncGT c (b : HahnSeries G K)).coeff g ≠ 0 := by
    simpa only [AddSubgroupClass.coe_sub, HahnSeries.coeff_sub, strictTail] using
      (mem_support _ _).mp hg
  rw [HahnSeries.coeff_truncGT] at hg'
  by_contra hcg
  rw [if_pos (not_le.mp hcg), sub_self] at hg'
  exact hg' rfl

/-- Above the cut, translated truncations of a series and its strict tail differ only by a series
bounded strictly below zero. -/
theorem degree_translatedTruncLE_sub_strictTail_eq_bot {c y : G} (hcy : c < y)
    (b : Nonpositive G K) :
    ν (translatedTruncLE y (b - strictTail c b)) = ⊥ := by
  apply (cantorBendixsonDegreeValuation_eq_bot_iff _).mpr
  refine ⟨c - y, sub_neg.mpr hcy, ?_⟩
  intro g hg
  have hg' : g + y ∈ ((b : HahnSeries G K) -
      (strictTail c b : HahnSeries G K)).support := by
    rw [coe_translatedTruncLE, mem_support, HahnSeries.coeff_translate,
      HahnSeries.coeff_truncLE] at hg
    split_ifs at hg with hle
    · exact (mem_support _ _).mpr (by simpa using hg)
    · exact absurd rfl hg
  have hcoeff : (b : HahnSeries G K).coeff (g + y) -
      (truncGT c (b : HahnSeries G K)).coeff (g + y) ≠ 0 := by
    simpa only [HahnSeries.coeff_sub, strictTail] using (mem_support _ _).mp hg'
  rw [HahnSeries.coeff_truncGT] at hcoeff
  have hle : g + y ≤ c := by
    by_contra hn
    rw [if_pos (not_le.mp hn), sub_self] at hcoeff
    exact hcoeff rfl
  simpa using sub_le_sub_right hle y

omit [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [CharZero K] in
/-- At or below the cut, every translated truncation of a strict tail vanishes. -/
theorem translatedTruncLE_strictTail_eq_zero {c y : G} (hyc : y ≤ c)
    (b : Nonpositive G K) : translatedTruncLE y (strictTail c b) = 0 := by
  apply Subtype.ext
  ext g
  rw [coe_translatedTruncLE, HahnSeries.coeff_translate, HahnSeries.coeff_truncLE,
    strictTail, HahnSeries.coeff_truncGT]
  split_ifs with h1 h2
  · exact absurd h2 (not_lt.mpr (le_trans (by simpa using h1) hyc))
  · rfl
  · rfl

/-- A strict tail above a negative cutoff represents the same homogeneous germ. -/
theorem represents_strictTail {c : G} (hc : c < 0) {b : Nonpositive G K}
    {m : NatOrdinal.{u}} {e : (ν).AssociatedGraded} (h : Represents b m e) :
    Represents (strictTail c b) m e := by
  have hbot := degree_sub_strictTail_eq_bot hc b
  have hdeg : ν b = ν (strictTail c b) := degree_eq_of_degree_sub_eq_bot hbot
  rw [represents_iff]
  refine ⟨hdeg ▸ h.degree_le, ?_⟩
  obtain ⟨hb, he⟩ := (represents_iff.mp h)
  calc
    (ν).homogeneousMk m ⟨strictTail c b, ((ν).mem_filtrationLE_iff m _).mpr (hdeg ▸ hb)⟩ =
        (ν).homogeneousMk m ⟨b, ((ν).mem_filtrationLE_iff m _).mpr hb⟩ := by
      rw [MaxAddDegree.homogeneousMk_apply, MaxAddDegree.homogeneousMk_apply]
      congr 1
      apply ((ν).componentMk_eq_componentMk_iff m _ _).mpr
      rw [show strictTail c b - b = -(b - strictTail c b) by ring, (ν).map_neg, hbot]
      exact WithBot.bot_lt_coe m
    _ = e := he

/-- Strict tails preserve the degree and proper-truncation bounds. -/
theorem hasLowerTruncationDegree_strictTail {c : G} (hc : c < 0) {b : Nonpositive G K}
    {m : NatOrdinal.{u}} (h : HasLowerTruncationDegree b m) :
    HasLowerTruncationDegree (strictTail c b) m := by
  have hbot := degree_sub_strictTail_eq_bot hc b
  have hdeg : ν b = ν (strictTail c b) := degree_eq_of_degree_sub_eq_bot hbot
  rw [hasLowerTruncationDegree_iff]
  refine ⟨hdeg ▸ h.degree_le, fun y hy ↦ ?_⟩
  by_cases hcy : c < y
  · have hdiff := degree_translatedTruncLE_sub_strictTail_eq_bot hcy b
    have heq := degree_eq_of_degree_sub_eq_bot
      (a := translatedTruncLE y b) (b := translatedTruncLE y (strictTail c b))
      (by rw [← map_sub]; exact hdiff)
    rw [← heq]
    exact h.degree_translatedTruncLE_lt hy
  · rw [translatedTruncLE_strictTail_eq_zero (not_lt.mp hcy), (ν).map_zero]
    exact WithBot.bot_lt_coe m

omit [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [CharZero K] in
/-- The translated truncation of a placed local series reads the local series at the shifted
cutoff. -/
theorem translatedTruncLE_placed (x y : G) (f : K⟦G⟧)
    (hshift : (translate (-x) f).support ⊆ Iic 0) :
    (translatedTruncLE (y - x) (⟨translate (-x) f, hshift⟩ : Nonpositive G K) :
      HahnSeries G K) = translate (-y) (truncLE y f) := by
  rw [coe_translatedTruncLE]
  change translate (-(y - x)) (truncLE (y - x) (translate (-x) f)) = _
  rw [truncLE_translate, show y - x - -x = y by abel, translate_add_apply]
  congr 1
  abel_nf

omit [AddCommGroup G] [IsOrderedAddMonoid G] [UniformSpace G] [IsUniformAddGroup G]
  [OrderTopology G] [Nontrivial G] [CompleteSpace G] [CharZero K] in
/-- A weak truncation of a series vanishes when the cutoff lies below the whole support. -/
theorem truncLE_eq_zero_of_forall_lt (f : K⟦G⟧) (y : G)
    (h : ∀ p ∈ f.support, y < p) : truncLE y f = 0 := by
  ext g
  rw [HahnSeries.coeff_truncLE]
  by_cases hgy : g ≤ y
  · rw [if_pos hgy]
    by_contra hne
    exact absurd hgy (not_le.mpr (h g ((mem_support _ _).mpr hne)))
  · rw [if_neg hgy, HahnSeries.coeff_zero]

omit [AddCommGroup G] [IsOrderedAddMonoid G] [UniformSpace G] [IsUniformAddGroup G]
  [OrderTopology G] [Nontrivial G] [CompleteSpace G] in
/-- Outside a convex piece containing a bound of the support, support points are below the whole
piece. -/
theorem lt_of_notMem_ordConnected {C : Set G} (hC : C.OrdConnected)
    {x : G} (hx : x ∈ C) {p : G} (hp : p ≤ x) (hpC : p ∉ C) :
    ∀ c ∈ C, p < c := by
  intro c hc
  by_contra hcp
  exact hpC (hC.out hc hx ⟨not_lt.mp hcp, hp⟩)

omit [AddCommGroup G] [IsOrderedAddMonoid G] [UniformSpace G] [IsUniformAddGroup G]
  [OrderTopology G] [Nontrivial G] [CompleteSpace G] in
/-- A point below a convex piece but outside it lies below each element of the piece. -/
theorem le_of_notMem_ordConnected {C : Set G} (hC : C.OrdConnected)
    {y c p : G} (hy : y ∈ C) (hc : c ∈ C) (hpy : p ≤ y) (hpC : p ∉ C) : p ≤ c :=
  (lt_of_notMem_ordConnected hC hy hpy hpC c hc).le

omit [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] [IsUniformAddGroup G]
  [OrderTopology G] [Nontrivial G] [CompleteSpace G] [Field K] [CharZero K] in
/-- A point outside a closed set lies outside the closure of the range of its subtype coercion. -/
theorem notMem_closure_range_subtype_coe {S : Set G} {y : G} (hS : closure S = S)
    (hy : y ∉ S) : y ∉ closure (Set.range (fun x : S ↦ (x : G))) := by
  rwa [Subtype.range_coe, hS]

omit [AddCommGroup G] [IsOrderedAddMonoid G] [IsUniformAddGroup G] [Nontrivial G]
  [CompleteSpace G] in
/-- In an open convex piece of a densely ordered group there is a piece element strictly below
any given piece element. -/
theorem exists_lt_mem_of_isOpen_ordConnected [DenselyOrdered G] [NoMinOrder G] [NoMaxOrder G]
    {C : Set G} (hCopen : IsOpen C) {y : G} (hy : y ∈ C) :
    ∃ c ∈ C, c < y := by
  obtain ⟨a, b, ⟨hay, hyb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hCopen.mem_nhds hy)
  obtain ⟨c, hac, hcy⟩ := exists_between hay
  exact ⟨c, hab ⟨hac, hcy.trans hyb⟩, hcy⟩

omit [AddCommGroup G] [IsOrderedAddMonoid G] [IsUniformAddGroup G] [Nontrivial G]
  [CompleteSpace G] [CharZero K] in
/-- Cantor–Bendixson ranks of closed supports are monotone under support inclusion. -/
theorem cantorBendixsonRank_le_of_support_subset {a b : K⟦G⟧} (h : a.support ⊆ b.support) (z : G) :
    a.cantorBendixsonRank z ≤ b.cantorBendixsonRank z := by
  have hle : a.closedSupport ≤ b.closedSupport := by
    have h1 : (a.closedSupport : Set G) ⊆ (b.closedSupport : Set G) := by
      rw [coe_closedSupport, coe_closedSupport]
      exact closure_mono h
    exact h1
  rw [cantorBendixsonRank_eq, cantorBendixsonRank_eq]
  apply TopologicalSpace.Closeds.cantorBendixsonRank_le_of_notMem _ _ z
  intro hmem
  exact b.closedSupport.notMem_cantorBendixson_rank_add_one b.closedSupport_isPWO z
    (TopologicalSpace.Closeds.cantorBendixson_mono hle _ hmem)

omit [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [CharZero K] in
/-- The translated truncation at a shifted cutoff reads the series placed at the shift. -/
theorem translatedTruncLE_shift (x y : G) (b : Nonpositive G K) :
    (translatedTruncLE (y - x) b : HahnSeries G K) =
      translate (-y) (truncLE y (translate x (b : HahnSeries G K))) := by
  rw [coe_translatedTruncLE, truncLE_translate, translate_add_apply]
  congr 1
  abel_nf

open Classical in
/-- Inside one piece, a separated sum of restricted translates has the same local germ as the
corresponding untranslated series. -/
theorem degree_translatedTruncLE_separatedHsum_sub_piece_eq_bot
    [DenselyOrdered G] [NoMinOrder G] [NoMaxOrder G]
    {X : Type w} [LinearOrder X] (hX : (Set.univ : Set X).IsPWO)
    (C : X → Set G) (hCopen : ∀ x, IsOpen (C x)) (hCconv : ∀ x, (C x).OrdConnected)
    (f : X → K⟦G⟧) (hfC : ∀ x, (f x).support ⊆ C x)
    (hord : ∀ x y : X, x < y → ∀ a ∈ C x, ∀ b ∈ C y, a < b)
    (hsep : ∀ i j, i < j → ∀ a ∈ (f i).support, ∀ b ∈ (f j).support, a < b)
    (x : X) (z : G) {y : G} (hy : y ∈ C x) (b : Nonpositive G K)
    (hpiece : f x = setRestrict (C x) (translate z (b : HahnSeries G K)))
    (c : Nonpositive G K) (hc : (c : HahnSeries G K) = separatedHsum hX f hsep) :
    ν (translatedTruncLE y c - translatedTruncLE (y - z) b) = ⊥ := by
  obtain ⟨cst, hcst, hcsty⟩ := exists_lt_mem_of_isOpen_ordConnected (hCopen x) hy
  apply (cantorBendixsonDegreeValuation_eq_bot_iff _).mpr
  refine ⟨cst - y, sub_neg.mpr hcsty, ?_⟩
  intro g hg
  rw [AddSubgroupClass.coe_sub, translatedTruncLE_shift z y b,
    coe_translatedTruncLE, hc] at hg
  have hb : ∀ p ∈ (translate z (b : HahnSeries G K)).support,
      p ∉ C x → p ≤ y → p ≤ cst :=
    fun _ _ hpC hpy ↦ le_of_notMem_ordConnected (hCconv x) hy hcst hpy hpC
  exact support_translate_truncLE_separatedHsum_sub_source_subset
    (G := G) (K := K) (X := X) hX C f hfC hord hsep x hy hcst
    (translate z (b : HahnSeries G K)) hpiece hb hg

open Classical in
/-- A separated sum has degree bottom at a cutoff outside every piece and outside the closure of
the piece centres. -/
theorem degree_translatedTruncLE_separatedHsum_eq_bot_of_notMem
    {X : Type w} [LinearOrder X] (hX : (Set.univ : Set X).IsPWO)
    (C : X → Set G) (z : X → G) (f : X → K⟦G⟧)
    (hfC : ∀ x, (f x).support ⊆ C x) (hfle : ∀ x, ∀ p ∈ (f x).support, p ≤ z x)
    (hzC : ∀ x, z x ∈ C x) (hCopen : ∀ x, IsOpen (C x))
    (hCconv : ∀ x, (C x).OrdConnected) (hCdisj : ∀ x y, x ≠ y → Disjoint (C x) (C y))
    (hCord : ∀ x y, x < y → ∀ a ∈ C x, ∀ b ∈ C y, a < b)
    (hsep : ∀ x y, x < y → ∀ a ∈ (f x).support, ∀ b ∈ (f y).support, a < b)
    (c : Nonpositive G K) (hc : (c : HahnSeries G K) = separatedHsum hX f hsep)
    {y : G} (hyC : ∀ x, y ∉ C x) (hyz : y ∉ closure (Set.range z)) :
    ν (translatedTruncLE y c) = ⊥ := by
  rw [degree_translatedTruncLE_eq, if_neg ?_]
  intro hy
  exact (by
    have hcl : ((c : HahnSeries G K).closedSupport : Set G) ⊆
        (⋃ x, C x) ∪ closure (Set.range z) := by
      rw [coe_closedSupport, hc, support_separatedHsum]
      exact closure_iUnion_subset_of_closure_piece_subset
        (fun x ↦ (f x).support) C z hfC hfle hzC hCopen hCdisj hCord
        (fun x ↦ closure_subset_of_isPWO_of_ordConnected (hCconv x)
          (f x).isPWO_support (hfC x) (hzC x) (hfle x))
    rcases hcl hy with hy | hy
    · obtain ⟨x, hyx⟩ := Set.mem_iUnion.mp hy
      exact hyC x hyx
    · exact hyz hy)

private structure SeparatedHsumFamily (J : Type x) (X : Type w) [LinearOrder X] where
  hX : (Set.univ : Set X).IsPWO
  piece : X → Set G
  center : X → G
  term : J → X → K⟦G⟧
  support_subset : ∀ j x, (term j x).support ⊆ piece x
  support_le_center : ∀ j x, ∀ p ∈ (term j x).support, p ≤ center x
  center_mem : ∀ x, center x ∈ piece x
  isOpen_piece : ∀ x, IsOpen (piece x)
  ordConnected_piece : ∀ x, (piece x).OrdConnected
  disjoint_piece : ∀ x y, x ≠ y → Disjoint (piece x) (piece y)
  piece_lt_piece : ∀ x y, x < y → ∀ a ∈ piece x, ∀ b ∈ piece y, a < b
  separated : ∀ j x y, x < y →
    ∀ a ∈ (term j x).support, ∀ b ∈ (term j y).support, a < b
  sum : J → Nonpositive G K
  coe_sum : ∀ j, (sum j : HahnSeries G K) = separatedHsum hX (term j) (separated j)

/-- Every member of a family of separated sums has degree bottom at a cutoff outside all pieces
and outside the closure of their common centres. -/
private theorem SeparatedHsumFamily.degree_translatedTruncLE_eq_bot_of_notMem
    {J : Type x} {X : Type w} [LinearOrder X] (F : SeparatedHsumFamily J X)
    {y : G} (hyC : ∀ x, y ∉ F.piece x) (hyz : y ∉ closure (Set.range F.center)) :
    ∀ j, ν (translatedTruncLE y (F.sum j)) = ⊥ := by
  intro j
  exact degree_translatedTruncLE_separatedHsum_eq_bot_of_notMem
    (G := G) (K := K) (X := X) (hX := F.hX) (C := F.piece) (z := F.center)
    (f := F.term j) (hfC := F.support_subset j) (hfle := F.support_le_center j)
    (hzC := F.center_mem) (hCopen := F.isOpen_piece)
    (hCconv := F.ordConnected_piece) (hCdisj := F.disjoint_piece)
    (hCord := F.piece_lt_piece) (hsep := F.separated j) (c := F.sum j)
    (hc := F.coe_sum j) (hyC := hyC) (hyz := hyz)

/-- A translated truncation at a strictly positive cutoff is bounded strictly below zero. -/
theorem degree_translatedTruncLE_of_pos {s : G} (hs : 0 < s) (b : Nonpositive G K) :
    ν (translatedTruncLE s b) = ⊥ := by
  apply (cantorBendixsonDegreeValuation_eq_bot_iff _).mpr
  refine ⟨-s, neg_neg_iff_pos.mpr hs, ?_⟩
  intro g hg
  rw [coe_translatedTruncLE, support_translate] at hg
  obtain ⟨p, hp, rfl⟩ := hg
  rw [support_truncLE] at hp
  have hp0 : p ≤ 0 := b.property hp.1
  have h := add_le_add_left hp0 (-s)
  rw [zero_add] at h
  have h' : -s + p ≤ -s := by
    rw [add_comm]
    exact h
  exact mem_Iic.mpr h'

/-- A translated truncation at a point outside the closed support has degree bottom. -/
theorem degree_translatedTruncLE_eq_bot_of_notMem_closedSupport
    {s : G} {b : Nonpositive G K} (hs : s ∉ (b : HahnSeries G K).closedSupport) :
    ν (translatedTruncLE s b) = ⊥ := by
  rw [degree_translatedTruncLE_eq, if_neg hs]

/-- A uniform degree bound at nonpositive cutoffs extends to every cutoff. -/
theorem degree_translatedTruncLE_le_of_nonpositive {b : Nonpositive G K}
    {τ : WithBot NatOrdinal} (hb : ∀ s : G, s ≤ 0 → ν (translatedTruncLE s b) ≤ τ)
    (s : G) : ν (translatedTruncLE s b) ≤ τ := by
  rcases le_or_gt s 0 with hs | hs
  · exact hb s hs
  · rw [degree_translatedTruncLE_of_pos hs]
    exact bot_le

/-- The boundary estimate at every cutoff: strictly negative cutoffs by the finite convolution
estimate, zero trivially, and strictly positive cutoffs because both terms are bounded strictly
below zero. -/
theorem degree_translatedTruncLE_mul_sub_mul_lt_forall
    (a b : Nonpositive G K) (ρ σ τ : NatOrdinal.{u})
    (ha : ν a ≤ ρ)
    (hat : ∀ x : G, x < 0 → ν (translatedTruncLE x a) ≤ ρ)
    (hbt : ∀ x : G, x < 0 → ν (translatedTruncLE x b) < σ)
    (hsep : ∀ θ, θ < σ → ρ + θ < τ) (γ : G) :
    ν (translatedTruncLE γ (a * b) - translatedTruncLE γ a * b) < τ := by
  rcases lt_trichotomy γ 0 with hγ | hγ | hγ
  · exact degree_translatedTruncLE_mul_sub_mul_lt_of_pointwise_bounds a b ρ σ τ ha hat hbt hsep hγ
  · subst hγ
    rw [translatedTruncLE_zero, translatedTruncLE_zero, sub_self, (ν).map_zero]
    exact WithBot.bot_lt_coe τ
  · have h1 : ν (translatedTruncLE γ (a * b)) = ⊥ := degree_translatedTruncLE_of_pos hγ _
    have h2 : ν (translatedTruncLE γ a * b) = ⊥ := by
      have := (ν).map_mul_le_add (translatedTruncLE γ a) b
      rw [degree_translatedTruncLE_of_pos hγ, WithBot.bot_add] at this
      exact le_bot_iff.mp this
    refine ((ν).map_sub_le_max _ _).trans_lt ?_
    rw [h1, h2, max_self]
    exact WithBot.bot_lt_coe τ

/-- The translated product error is small when the first factor either vanishes below the target
degree or satisfies the complementary degree bound. -/
theorem degree_translatedTruncLE_mul_sub_mul_lt_of_eq_zero_or_bounds
    (a b : Nonpositive G K) (ρ σ τ β : NatOrdinal.{u})
    (ha0 : β ≤ τ → a = 0)
    (ha : ν a ≤ ρ)
    (hat : ∀ x : G, x < 0 → ν (translatedTruncLE x a) ≤ ρ)
    (hbt : ∀ x : G, x < 0 → ν (translatedTruncLE x b) < σ)
    (hsep : τ < β → ∀ θ, θ < σ → ρ + θ < τ) (γ : G) :
    ν (translatedTruncLE γ (a * b) - translatedTruncLE γ a * b) < τ := by
  by_cases hβτ : β ≤ τ
  · rw [ha0 hβτ]
    simp only [zero_mul, map_zero, sub_zero, (ν).map_zero]
    exact WithBot.bot_lt_coe τ
  · exact degree_translatedTruncLE_mul_sub_mul_lt_forall a b ρ σ τ ha hat hbt
      (hsep (lt_of_not_ge hβτ)) γ

omit [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G]
  [CompleteSpace G] [CharZero K] in
/-- Decomposition of a summed residual into the local residual and three truncation errors. -/
theorem translatedTruncLE_sub_sum_eq_local_errors
    {J : Type w} [Fintype J] (y s : G) (R u : Nonpositive G K)
    (cp cP q : J → Nonpositive G K) :
    translatedTruncLE y R - ∑ j, translatedTruncLE y (cP j * q j) =
      (translatedTruncLE y R - translatedTruncLE s u) +
        translatedTruncLE s (u - ∑ j, cp j * q j) +
        ∑ j, ((translatedTruncLE s (cp j * q j) - translatedTruncLE s (cp j) * q j) +
          (translatedTruncLE s (cp j) - translatedTruncLE y (cP j)) * q j +
          (translatedTruncLE y (cP j) * q j - translatedTruncLE y (cP j * q j))) := by
  rw [map_sub, map_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_congr rfl fun j _ ↦ sub_mul (translatedTruncLE s (cp j))
      (translatedTruncLE y (cP j)) (q j),
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  abel

/-- If the source cutoff and all first-factor cutoffs have degree bottom, then bounds on the
truncation product errors bound the residual finite sum. -/
theorem degree_translatedTruncLE_sub_sum_le_of_eq_bot
    {J : Type w} [Fintype J] (R : Nonpositive G K) (c q : J → Nonpositive G K)
    {y : G} {τ : WithBot NatOrdinal}
    (hR : ν (translatedTruncLE y R) = ⊥)
    (herror : ∀ j, ν (translatedTruncLE y (c j * q j) -
      translatedTruncLE y (c j) * q j) < τ)
    (hc : ∀ j, ν (translatedTruncLE y (c j)) = ⊥) :
    ν (translatedTruncLE y R - ∑ j, translatedTruncLE y (c j * q j)) ≤ τ := by
  refine ((ν).map_sub_le_max _ _).trans ?_
  rw [hR]
  refine max_le bot_le ?_
  apply (ν).map_sum_le_of_forall_le
  intro j _
  have hsplit : translatedTruncLE y (c j * q j) =
      (translatedTruncLE y (c j * q j) - translatedTruncLE y (c j) * q j) +
        translatedTruncLE y (c j) * q j := by
    abel
  rw [hsplit]
  refine ((ν).map_add_le_max _ _).trans (max_le (herror j).le ?_)
  have hmul := (ν).map_mul_le_add (translatedTruncLE y (c j)) (q j)
  rw [hc j, WithBot.bot_add] at hmul
  exact hmul.trans bot_le


variable {κ : Type x} {ι : Type w} {κ' : Type w}

open Classical in
/-- **Cofactors by well-founded induction.** Fix representatives of homogeneous classes generating
the associated graded ring below `α`, each satisfying its assigned degree and proper-truncation
bounds, with graded evaluation injective below `α`, finitely many weighted homogeneous ideal
generators, and natural-sum separation data for their degrees.
If every translated truncation of `u` has degree at most `β ≤ μ` and, at every nonpositive
cutoff, the truncation agrees below every negative bound with an evaluated polynomial whose part
at or above `τ` lies in the polynomial ideal, then there are global cofactors, with the
prescribed pointwise degree bounds, whose combination with the evaluated generators corrects every
translated truncation of `u` to degree at most `τ`. The recursion covers each residual support by
disjoint convex pieces on a nested convex subgroup base and combines the local cofactors, so no
countability or cofinality hypothesis enters. -/
theorem exists_cofactors_degree_translatedTruncLE_le_of_locallyIdeal
    [DenselyOrdered G] [NoMinOrder G] [NoMaxOrder G]
    [LinearOrder κ] [WellFoundedLT κ] [Fintype κ']
    (U : κ → AddSubgroup G)
    (hUmono : ∀ {i j : κ}, i ≤ j → (U j : Set G) ⊆ (U i : Set G))
    (hUopen : ∀ i, IsOpen (U i : Set G))
    (hUconv : ∀ i, (U i : Set G).OrdConnected)
    (hUbase : ∀ ε : G, 0 < ε → ∃ i, (U i : Set G) ⊆ Ioo (-ε) ε)
    {wt : ι → NatOrdinal.{u}} {V : ι → Nonpositive G K}
    (xg : ι → (ν).AssociatedGraded)
    (hV : ∀ i, Represents (V i) (wt i) (xg i))
    (hVbounds : ∀ i, HasLowerTruncationDegree (V i) (wt i))
    (α : NatOrdinal.{u})
    (hgen : ∀ β : NatOrdinal.{u}, β < α → ∀ y ∈ DirectSum.rangeLof K (ν).Component β,
      ∃ F : MvPolynomial ι K, IsWeightedHomogeneous wt F β ∧ aeval xg F = y)
    (hinj : ∀ (β : NatOrdinal.{u}) (F : MvPolynomial ι K), β < α →
      IsWeightedHomogeneous wt F β → aeval xg F = 0 → F = 0)
    (Q : κ' → MvPolynomial ι K) (σQ : κ' → NatOrdinal.{u})
    (hQ : ∀ j, IsWeightedHomogeneous wt (Q j) (σQ j))
    (τ μ : NatOrdinal.{u}) (hτμ : τ < μ) (hμα : μ < α)
    (P : κ' → NatOrdinal.{u} → NatOrdinal.{u})
    (hP : ∀ j β, τ < β → β ≤ μ → P j β + σQ j = β)
    (hPsep : ∀ j θ, θ < σQ j → P j μ + θ < τ)
    (β : NatOrdinal.{u}) (hβμ : β ≤ μ)
    (u : Nonpositive G K)
    (hu : ∀ y : G, y ≤ 0 → ν (translatedTruncLE y u) ≤ β)
    (hp : ∀ y : G, y ≤ 0 → ∃ F : MvPolynomial ι K,
      (∀ d ∈ F.support, (Finsupp.weight wt) d < α) ∧
      ν (translatedTruncLE y u - aeval V F) = ⊥ ∧
      MvPolynomial.componentsGE wt τ F ∈ Ideal.span (Set.range Q)) :
    ∃ c : κ' → Nonpositive G K,
      (∀ j, ∀ y : G, y ≤ 0 → ν (translatedTruncLE y (c j)) ≤ P j β) ∧
      (β ≤ τ → ∀ j, c j = 0) ∧
      ∀ y : G, y ≤ 0 →
        ν (translatedTruncLE y (u - ∑ j, c j * aeval V (Q j))) ≤ τ := by
  classical
  let q : κ' → Nonpositive G K := fun j ↦ aeval V (Q j)
  change ∃ c : κ' → Nonpositive G K,
    (∀ j, ∀ y : G, y ≤ 0 → ν (translatedTruncLE y (c j)) ≤ P j β) ∧
    (β ≤ τ → ∀ j, c j = 0) ∧
    ∀ y : G, y ≤ 0 → ν (translatedTruncLE y (u - ∑ j, c j * q j)) ≤ τ
  -- Global data used at every stage of the induction.
  have hW : ∀ j, HasLowerTruncationDegree (q j) (σQ j) := fun j ↦
    hasLowerTruncationDegree_aeval hVbounds (hQ j)
  have hPle : ∀ j β', τ < β' → β' ≤ μ → P j β' ≤ μ := by
    intro j β' h1 h2
    have h0 : P j β' + 0 ≤ P j β' + σQ j := add_le_add le_rfl (zero_le (a := σQ j))
    rw [add_zero, hP j β' h1 h2] at h0
    exact h0.trans h2
  have hPmono : ∀ j β' β'', τ < β' → β' ≤ β'' → β'' ≤ μ → P j β' ≤ P j β'' := by
    intro j β' β'' h1 h2 h3
    have e1 := hP j β' h1 (h2.trans h3)
    have e2 := hP j β'' (h1.trans_le h2) h3
    have : P j β' + σQ j ≤ P j β'' + σQ j := by rw [e1, e2]; exact h2
    exact le_of_add_le_add_right this
  have hPlt : ∀ j β' β'', τ < β' → β' < β'' → β'' ≤ μ → P j β' < P j β'' := by
    intro j β' β'' h1 h2 h3
    have e1 := hP j β' h1 (h2.le.trans h3)
    have e2 := hP j β'' (h1.trans h2) h3
    have : P j β' + σQ j < P j β'' + σQ j := by rw [e1, e2]; exact h2
    exact lt_of_add_lt_add_right this
  have hPsep' : ∀ j β', τ < β' → β' ≤ μ → ∀ θ, θ < σQ j → P j β' + θ < τ := by
    intro j β' h1 h2 θ hθ
    exact (add_le_add (hPmono j β' μ h1 h2 le_rfl) le_rfl).trans_lt (hPsep j θ hθ)
  -- The induction over the stage.
  induction β using WellFoundedLT.induction generalizing u with
  | _ β ih =>
  by_cases hβτ : β ≤ τ
  · -- Base: the truncations are already at the floor.
    refine ⟨fun _ ↦ 0, ?_, fun _ j ↦ rfl, ?_⟩
    · intro j y hy
      rw [map_zero, (ν).map_zero]
      exact bot_le
    · intro y hy
      have hz : (∑ j, (0 : Nonpositive G K) * q j) = 0 := by
        simp
      rw [hz, sub_zero]
      exact (hu y hy).trans (WithBot.coe_le_coe.mpr hβτ)
  -- Main case: correct the top rank level, then partition and recurse.
  · have hτβ : τ < β := lt_of_not_ge hβτ
    have hβα : β < α := lt_of_le_of_lt hβμ hμα
    -- Step A: choose local cofactors at every exact rank-`β` cutoff.
    have hlocal : ∀ i : {x // x ∈ (u : HahnSeries G K).closedSupport ∧
        (u : HahnSeries G K).closedSupport.cantorBendixsonRank
          (u : HahnSeries G K).closedSupport_isPWO x = β.val},
        ∃ w : κ' → Nonpositive G K, (∀ j, ν (w j) ≤ P j β) ∧
          ν (translatedTruncLE (i : G) u - ∑ j, w j * q j) <
            (β : WithBot NatOrdinal) := by
      rintro ⟨z, hzs, hzr⟩
      have hz0 : z ≤ 0 := closure_minimal u.property isClosed_Iic
        ((mem_closedSupport _ _).mp hzs)
      obtain ⟨F, hFw, hFbot, hFGE⟩ := hp z hz0
      have hνT : ν (translatedTruncLE z u) = (β : WithBot NatOrdinal) := by
        rw [degree_translatedTruncLE_eq, if_pos hzs, cantorBendixsonRank_eq, hzr, NatOrdinal.of_val]
      have hνF : ν (aeval V F) = (β : WithBot NatOrdinal) := by
        rw [← degree_eq_of_degree_sub_eq_bot hFbot, hνT]
      have hwle : ∀ d ∈ F.support, (Finsupp.weight wt) d ≤ β := by
        intro d hd
        have := forall_weight_le_degree_aeval_of_injective xg hV hinj hFw d hd
        rw [hνF] at this
        exact WithBot.coe_le_coe.mp this
      set Fβ := weightedHomogeneousComponent wt β F with hFβ_def
      have hFβspan : Fβ ∈ Ideal.span (Set.range Q) :=
        weightedHomogeneousComponent_mem_span_of_componentsGE_mem wt hQ hFGE hτβ.le
      letI := weightedGradedAlgebra K wt
      obtain ⟨A, hA, -, hAsum⟩ := OrdinalGraded.exists_eq_sum_mul_of_mem_span
        (𝒜 := weightedHomogeneousSubmodule K wt)
        (fun j ↦ (mem_weightedHomogeneousSubmodule _ _ _ _).mpr (hQ j))
        ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr
          (weightedHomogeneousComponent_isWeightedHomogeneous (w := wt) (n := β) (φ := F)))
        hFβspan
      have hAhom : ∀ j, IsWeightedHomogeneous wt (A j) (P j β) := fun j ↦
        (mem_weightedHomogeneousSubmodule _ _ _ _).mp (hA j (P j β) (hP j β hτβ hβμ))
      refine ⟨fun j ↦ aeval V (A j), fun j ↦ (represents_aeval xg hV (hAhom j)).degree_le, ?_⟩
      have hsum : (∑ j, aeval V (A j) * q j) = aeval V Fβ := by
        rw [hFβ_def, hAsum, map_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [map_mul, mul_comm]
      rw [hsum]
      have hrest : ∀ d ∈ (F - Fβ).support, (Finsupp.weight wt) d < β := by
        intro d hd
        have hne := MvPolynomial.mem_support_iff.mp hd
        rw [MvPolynomial.coeff_sub, hFβ_def, coeff_weightedHomogeneousComponent] at hne
        by_cases hdw : (Finsupp.weight wt) d = β
        · rw [if_pos hdw, sub_self] at hne
          exact absurd rfl hne
        · rw [if_neg hdw, sub_zero] at hne
          exact lt_of_le_of_ne (hwle d (MvPolynomial.mem_support_iff.mpr hne)) hdw
      have hkey : translatedTruncLE z u - aeval V Fβ =
          (translatedTruncLE z u - aeval V F) + aeval V (F - Fβ) := by
        rw [map_sub]
        ring
      rw [hkey]
      refine ((ν).map_add_le_max _ _).trans_lt (max_lt ?_ ?_)
      · rw [hFbot]
        exact WithBot.bot_lt_coe β
      · exact degree_aeval_lt_of_forall_weight_lt xg hV hrest
    choose wA hwAb hwAcorr using hlocal
    obtain ⟨ctop, hctopb, hRdrop⟩ :=
      exists_forall_degree_translatedTruncLE_sub_sum_mul_lt β q
        (fun j ↦ P j β) σQ (fun j ↦ (hP j β hτβ hβμ).le) (fun j ↦ (hW j).degree_le)
        (fun j x hx ↦ (hW j).degree_translatedTruncLE_lt hx) u hu wA hwAb hwAcorr
    set R : Nonpositive G K := u - ∑ j, ctop j * q j with hR_def
    have hτα : τ < α := hτμ.trans hμα
    -- Step B: the local ideal condition passes to the corrected residual.
    have hpR : ∀ y : G, y ≤ 0 → ∃ F : MvPolynomial ι K,
        (∀ d ∈ F.support, (Finsupp.weight wt) d < α) ∧
        ν (translatedTruncLE y R - aeval V F) = ⊥ ∧
        MvPolynomial.componentsGE wt τ F ∈ Ideal.span (Set.range Q) := by
      intro y hy
      obtain ⟨F₀, hF₀w, hF₀bot, hF₀GE⟩ := hp y hy
      have hpolc : ∀ j, ∃ A' : MvPolynomial ι K,
          (∀ d ∈ A'.support,
            (((Finsupp.weight wt) d : NatOrdinal) : WithBot NatOrdinal) ≤
              ν (translatedTruncLE y (ctop j))) ∧
          (∀ d ∈ A'.support, (Finsupp.weight wt) d < α) ∧
          ν (translatedTruncLE y (ctop j) - aeval V A') = ⊥ := fun j ↦
        exists_forall_weight_lt_and_degree_sub_aeval_eq_bot xg hV α hgen _
          ((hctopb j y hy).trans_lt (WithBot.coe_lt_coe.mpr
            ((hPle j β hτβ hβμ).trans_lt hμα)))
      choose A' hA'd hA'w hA'bot using hpolc
      have hEbound : ∀ j, ν (translatedTruncLE y (ctop j * q j) -
          translatedTruncLE y (ctop j) * q j) < (τ : WithBot NatOrdinal) := by
        intro j
        exact degree_translatedTruncLE_mul_sub_mul_lt_forall (ctop j) (q j)
          (P j β) (σQ j) τ (by simpa only [translatedTruncLE_zero] using hctopb j 0 le_rfl)
          (fun x hx ↦ hctopb j x hx.le)
          (fun x hx ↦ (hW j).degree_translatedTruncLE_lt hx)
          (hPsep' j β hτβ hβμ) y
      have hpolE : ∀ j, ∃ FE : MvPolynomial ι K,
          (∀ d ∈ FE.support,
            (((Finsupp.weight wt) d : NatOrdinal) : WithBot NatOrdinal) ≤
              ν (translatedTruncLE y (ctop j * q j) -
                translatedTruncLE y (ctop j) * q j)) ∧
          (∀ d ∈ FE.support, (Finsupp.weight wt) d < α) ∧
          ν ((translatedTruncLE y (ctop j * q j) -
              translatedTruncLE y (ctop j) * q j) - aeval V FE) = ⊥ := fun j ↦
        exists_forall_weight_lt_and_degree_sub_aeval_eq_bot xg hV α hgen _
          ((hEbound j).trans (WithBot.coe_lt_coe.mpr hτα))
      choose FE hFEd hFEw hFEbot using hpolE
      have hFEGE : ∀ j, MvPolynomial.componentsGE wt τ (FE j) = 0 := by
        intro j
        apply componentsGE_eq_zero_of_forall_lt
        intro d hd
        have h1 := (hFEd j d hd).trans_lt (hEbound j)
        exact WithBot.coe_lt_coe.mp h1
      refine ⟨F₀ - ∑ j, A' j * Q j - ∑ j, FE j, ?_, ?_, ?_⟩
      · intro d hd
        rcases Finset.mem_union.mp (MvPolynomial.support_sub ι _ _ hd) with hd | hd
        · rcases Finset.mem_union.mp (MvPolynomial.support_sub ι _ _ hd) with hd | hd
          · exact hF₀w d hd
          · have hsum := MvPolynomial.support_sum hd
            rw [Finset.mem_biUnion] at hsum
            obtain ⟨j, -, hdj⟩ := hsum
            have hmul := MvPolynomial.support_mul _ _ hdj
            rw [Finset.mem_add] at hmul
            obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := hmul
            rw [map_add]
            have h1 : (Finsupp.weight wt) d₁ ≤ P j β := by
              have := (hA'd j d₁ hd₁).trans (hctopb j y hy)
              exact WithBot.coe_le_coe.mp this
            have h2 : (Finsupp.weight wt) d₂ = σQ j :=
              hQ j (MvPolynomial.mem_support_iff.mp hd₂)
            calc
              (Finsupp.weight wt) d₁ + (Finsupp.weight wt) d₂ ≤ P j β + σQ j := by
                rw [h2]
                exact add_le_add h1 le_rfl
              _ = β := hP j β hτβ hβμ
              _ < α := hβα
        · have hsum := MvPolynomial.support_sum hd
          rw [Finset.mem_biUnion] at hsum
          obtain ⟨j, -, hdj⟩ := hsum
          exact hFEw j d hdj
      · have hTsub : translatedTruncLE y R =
            translatedTruncLE y u - ∑ j, translatedTruncLE y (ctop j * q j) := by
          rw [hR_def, map_sub, map_sum]
        have hAQ : ∀ j, aeval V (A' j * Q j) = aeval V (A' j) * q j :=
          fun j ↦ map_mul _ _ _
        have hcalc : translatedTruncLE y R - aeval V (F₀ - ∑ j, A' j * Q j - ∑ j, FE j) =
            (translatedTruncLE y u - aeval V F₀) -
              ∑ j, (translatedTruncLE y (ctop j * q j) -
                aeval V (A' j) * q j - aeval V (FE j)) := by
          rw [hTsub, map_sub, map_sub, map_sum, map_sum,
            Finset.sum_congr rfl fun j _ ↦ hAQ j]
          conv_rhs => rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
          abel
        rw [hcalc]
        have hbot1 : ∀ j, ν (translatedTruncLE y (ctop j * q j) -
            aeval V (A' j) * q j - aeval V (FE j)) = ⊥ := by
          intro j
          have hshape : translatedTruncLE y (ctop j * q j) -
              aeval V (A' j) * q j - aeval V (FE j) =
              (translatedTruncLE y (ctop j) - aeval V (A' j)) * q j +
                ((translatedTruncLE y (ctop j * q j) -
                  translatedTruncLE y (ctop j) * q j) - aeval V (FE j)) := by
            ring
          rw [hshape]
          have h1 : ν ((translatedTruncLE y (ctop j) - aeval V (A' j)) * q j) = ⊥ := by
            have := (ν).map_mul_le_add (translatedTruncLE y (ctop j) - aeval V (A' j))
              (q j)
            rw [hA'bot j, WithBot.bot_add] at this
            exact le_bot_iff.mp this
          have h2 := hFEbot j
          refine le_bot_iff.mp (((ν).map_add_le_max _ _).trans ?_)
          rw [h1, h2, max_self]
        have hsumbot : ν (∑ j, (translatedTruncLE y (ctop j * q j) -
            aeval V (A' j) * q j - aeval V (FE j))) = ⊥ :=
          le_bot_iff.mp ((ν).map_sum_le_of_forall_le _ _ ⊥ fun j _ ↦ (hbot1 j).le)
        refine le_bot_iff.mp (((ν).map_sub_le_max _ _).trans ?_)
        rw [hF₀bot, hsumbot, max_self]
      · rw [componentsGE_sub, componentsGE_sub, componentsGE_sum, componentsGE_sum]
        have hAQGE : ∀ j ∈ Finset.univ, MvPolynomial.componentsGE wt τ (A' j * Q j) ∈
            Ideal.span (Set.range Q) := by
          intro j _
          exact componentsGE_mem_span wt hQ
            (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)) τ
        have hFEGE' : (∑ j, MvPolynomial.componentsGE wt τ (FE j)) = 0 := by
          rw [Finset.sum_congr rfl fun j _ ↦ hFEGE j, Finset.sum_const_zero]
        rw [hFEGE', sub_zero]
        exact Ideal.sub_mem _ hF₀GE (Ideal.sum_mem _ hAQGE)
    -- Step C: cover the residual support by disjoint convex pieces and recurse.
    obtain ⟨Xset, C, hXs, hCmem, hCopen, hCconv, hCdisj, hCord, hCcov, hCmax, hCrank, hXdisc⟩ :=
      TopologicalSpace.Closeds.exists_disjoint_convex_cover_with_rank_lt_center
        (R : HahnSeries G K).closedSupport (R : HahnSeries G K).closedSupport_isPWO
        U hUmono hUopen hUconv hUbase
    have hXpieces : Xset ⊆ ⋃ x : ↥Xset, C x := hXs.trans hCcov
    have hX0 : ∀ x : ↥Xset, (x : G) ≤ 0 := fun x ↦
      closure_minimal R.property isClosed_Iic ((mem_closedSupport _ _).mp (hXs x.2))
    have hXset_pwo : Xset.IsPWO := (R : HahnSeries G K).closedSupport_isPWO.mono hXs
    have hXpwo : (Set.univ : Set ↥Xset).IsPWO := by
      rw [Set.isPWO_iff_exists_monotone_subseq]
      intro f _
      obtain ⟨g, hg⟩ := hXset_pwo.exists_monotone_subseq fun n ↦ (f n).2
      exact ⟨g, fun a b hab ↦ Subtype.coe_le_coe.mp (hg hab)⟩
    let fx : ↥Xset → HahnSeries G K := fun x ↦ setRestrict (C x) (R : HahnSeries G K)
    have hfxC : ∀ x, (fx x).support ⊆ C x := by
      intro x
      rw [show fx x = setRestrict (C x) (R : HahnSeries G K) from rfl, support_setRestrict]
      exact inter_subset_right
    have hfxle : ∀ x : ↥Xset, ∀ p ∈ (fx x).support, p ≤ (x : G) := by
      intro x p hp
      have hp' : p ∈ (R : HahnSeries G K).support ∩ C x := by
        rwa [show fx x = setRestrict (C x) (R : HahnSeries G K) from rfl,
          support_setRestrict] at hp
      exact hCmax x p ⟨(mem_closedSupport _ _).mpr (subset_closure hp'.1), hp'.2⟩
    have hsepx : ∀ i j : ↥Xset, i < j →
        ∀ a ∈ (fx i).support, ∀ b ∈ (fx j).support, a < b :=
      fun i j hij a ha b hb ↦ hCord i j hij a (hfxC i ha) b (hfxC j hb)
    have hRsum : (R : HahnSeries G K) = separatedHsum hXpwo fx hsepx := by
      have hcov : (R : HahnSeries G K).support ⊆ ⋃ x : ↥Xset, C x := fun g hg ↦
        hCcov ((mem_closedSupport _ _).mpr (subset_closure hg))
      exact (separatedHsum_setRestrict_eq hXpwo C (R : HahnSeries G K) hcov
        (fun i j hij ↦ hCdisj i j hij)
        (fun i j hij a ha b hb ↦ hCord i j hij a ha b hb)).symm
    have hfx_shift : ∀ x : ↥Xset, (translate (-(x : G)) (fx x)).support ⊆ Iic 0 := by
      intro x
      rw [support_translate]
      rintro g ⟨p, hp, rfl⟩
      have hpx := hfxle x p hp
      have h3 : -(x : G) + p ≤ 0 := by
        have h2 : -(x : G) + p ≤ -(x : G) + (x : G) := add_le_add le_rfl hpx
        rwa [neg_add_cancel] at h2
      exact mem_Iic.mpr h3
    let ux : ↥Xset → Nonpositive G K := fun x ↦ ⟨translate (-(x : G)) (fx x), hfx_shift x⟩
    let bx : ↥Xset → NatOrdinal.{u} := fun x ↦
      NatOrdinal.of ((R : HahnSeries G K).cantorBendixsonRank (x : G))
    -- Locality of truncations inside a piece.
    have hloc : ∀ (x : ↥Xset) (y' : G), y' ∈ C x →
        ν (translatedTruncLE (y' - (x : G)) (ux x) - translatedTruncLE y' R) = ⊥ := by
      intro x y' hy'
      obtain ⟨cst, hcst, hcsty⟩ := exists_lt_mem_of_isOpen_ordConnected (hCopen x) hy'
      have hdiff := support_truncLE_separatedHsum_sub_piece_subset hXpwo C fx hfxC hCord
        hsepx x hy' hcst
      apply (cantorBendixsonDegreeValuation_eq_bot_iff _).mpr
      refine ⟨cst - y', sub_neg.mpr hcsty, ?_⟩
      intro g hg
      have hcoe1 : ((translatedTruncLE (y' - (x : G)) (ux x) : Nonpositive G K) :
          HahnSeries G K) = translate (-y') (truncLE y' (fx x)) :=
        translatedTruncLE_placed (x : G) y' (fx x) (hfx_shift x)
      rw [AddSubgroupClass.coe_sub, hcoe1, coe_translatedTruncLE] at hg
      have hcombine : translate (-y') (truncLE y' (fx x)) -
          translate (-y') (truncLE y' (R : HahnSeries G K)) =
          translate (-y') (truncLE y' (fx x) - truncLE y' (R : HahnSeries G K)) :=
        (map_sub (translate (-y')) _ _).symm
      rw [hcombine, support_translate] at hg
      obtain ⟨q, hq, rfl⟩ := hg
      have hq' : q ∈ (truncLE y' (separatedHsum hXpwo fx hsepx) -
          truncLE y' (fx x)).support := by
        rw [← support_neg, neg_sub, ← hRsum]
        exact hq
      have hqc : q ≤ cst := hdiff hq'
      have h3 : -y' + q ≤ cst - y' := by
        have h2 : -y' + q ≤ -y' + cst := add_le_add le_rfl hqc
        calc -y' + q ≤ -y' + cst := h2
          _ = cst - y' := by abel
      exact mem_Iic.mpr h3
    have hplaced_eq : ∀ (x : ↥Xset) (s : G),
        (translatedTruncLE s (ux x) : HahnSeries G K) =
          translate (-((x : G) + s)) (truncLE ((x : G) + s) (fx x)) := by
      intro x s
      have h2 : ((x : G) + s) - (x : G) = s := by abel
      have := translatedTruncLE_placed (x : G) ((x : G) + s) (fx x) (hfx_shift x)
      rw [h2] at this
      exact this
    -- The translated degree profile of each piece.
    have hux_prof : ∀ x : ↥Xset, ∀ s : G, s ≤ 0 →
        ν (translatedTruncLE s (ux x)) ≤ (bx x : WithBot NatOrdinal) := by
      intro x s hs
      have hy'x : (x : G) + s ≤ (x : G) := by
        calc (x : G) + s ≤ (x : G) + 0 := add_le_add le_rfl hs
          _ = (x : G) := add_zero _
      by_cases hy'C : (x : G) + s ∈ C x
      · have h1 := hloc x ((x : G) + s) hy'C
        have h2 : ((x : G) + s) - (x : G) = s := by abel
        rw [h2] at h1
        rw [degree_eq_of_degree_sub_eq_bot h1]
        rw [degree_translatedTruncLE_eq]
        by_cases hm : (x : G) + s ∈ (R : HahnSeries G K).closedSupport
        · rw [if_pos hm]
          rcases eq_or_ne ((x : G) + s) (x : G) with heq | hne
          · rw [heq]
          · have hlt := hCrank x ((x : G) + s) ⟨hm, hy'C⟩ hne
            have hlt' : (R : HahnSeries G K).cantorBendixsonRank ((x : G) + s) <
                (R : HahnSeries G K).cantorBendixsonRank (x : G) := by
              rw [cantorBendixsonRank_eq, cantorBendixsonRank_eq]
              exact hlt
            exact (WithBot.coe_le_coe.mpr (NatOrdinal.of.monotone hlt'.le))
        · rw [if_neg hm]
          exact bot_le
      · have hbelow := lt_of_notMem_ordConnected (hCconv x) (hCmem x) hy'x hy'C
        have hzero : truncLE ((x : G) + s) (fx x) = 0 :=
          truncLE_eq_zero_of_forall_lt _ _ (fun p hp ↦ hbelow p (hfxC x hp))
        have hzero' : translatedTruncLE s (ux x) = 0 := by
          apply Subtype.ext
          rw [hplaced_eq x s, hzero, map_zero]
          rfl
        rw [hzero', (ν).map_zero]
        exact bot_le
    have hbx_lt : ∀ x : ↥Xset, bx x < β := by
      intro x
      have h1 := hRdrop (x : G) (hX0 x)
      have hm : (x : G) ∈ (R : HahnSeries G K).closedSupport := hXs x.2
      rw [degree_translatedTruncLE_eq, if_pos hm] at h1
      exact WithBot.coe_lt_coe.mp h1
    -- The local ideal condition for each piece.
    have hpux : ∀ x : ↥Xset, ∀ s : G, s ≤ 0 → ∃ F : MvPolynomial ι K,
        (∀ d ∈ F.support, (Finsupp.weight wt) d < α) ∧
        ν (translatedTruncLE s (ux x) - aeval V F) = ⊥ ∧
        MvPolynomial.componentsGE wt τ F ∈ Ideal.span (Set.range Q) := by
      intro x s hs
      have hy'0 : (x : G) + s ≤ 0 := by
        calc (x : G) + s ≤ 0 + 0 := add_le_add (hX0 x) hs
          _ = 0 := add_zero _
      by_cases hy'C : (x : G) + s ∈ C x
      · obtain ⟨F, hFw, hFbot, hFGE⟩ := hpR ((x : G) + s) hy'0
        refine ⟨F, hFw, ?_, hFGE⟩
        have h1 := hloc x ((x : G) + s) hy'C
        have h2 : ((x : G) + s) - (x : G) = s := by abel
        rw [h2] at h1
        have hsplit : translatedTruncLE s (ux x) - aeval V F =
            (translatedTruncLE s (ux x) - translatedTruncLE ((x : G) + s) R) +
              (translatedTruncLE ((x : G) + s) R - aeval V F) := by
          abel
        rw [hsplit]
        refine le_bot_iff.mp (((ν).map_add_le_max _ _).trans ?_)
        rw [h1, hFbot, max_self]
      · have hy'x : (x : G) + s ≤ (x : G) := by
          calc (x : G) + s ≤ (x : G) + 0 := add_le_add le_rfl hs
            _ = (x : G) := add_zero _
        have hbelow := lt_of_notMem_ordConnected (hCconv x) (hCmem x) hy'x hy'C
        have hzero : truncLE ((x : G) + s) (fx x) = 0 :=
          truncLE_eq_zero_of_forall_lt _ _ (fun p hp ↦ hbelow p (hfxC x hp))
        have hzero' : translatedTruncLE s (ux x) = 0 := by
          apply Subtype.ext
          rw [hplaced_eq x s, hzero, map_zero]
          rfl
        refine ⟨0, by simp, ?_, ?_⟩
        · rw [hzero', map_zero, sub_zero, (ν).map_zero]
        · rw [componentsGE_zero]
          exact Ideal.zero_mem _
    -- Recurse on every piece.
    have hpiece : ∀ x : ↥Xset, ∃ cp : κ' → Nonpositive G K,
        (∀ j, ∀ s : G, s ≤ 0 → ν (translatedTruncLE s (cp j)) ≤ P j (bx x)) ∧
        (bx x ≤ τ → ∀ j, cp j = 0) ∧
        ∀ s : G, s ≤ 0 →
          ν (translatedTruncLE s (ux x - ∑ j, cp j * q j)) ≤ τ :=
      fun x ↦ ih (bx x) (hbx_lt x) ((hbx_lt x).le.trans hβμ) (ux x) (hux_prof x) (hpux x)
    choose cp hcpb hcp0 hcpres using hpiece
    -- Step D: translate the piece cofactors back and sum them.
    obtain ⟨placed, hplaced⟩ : ∃ placed : κ' → ↥Xset → K⟦G⟧, ∀ j x,
        placed j x = setRestrict (C x)
          (translate (x : G) ((cp x j : Nonpositive G K) : HahnSeries G K)) :=
      ⟨fun j x ↦ setRestrict (C x)
        (translate (x : G) ((cp x j : Nonpositive G K) : HahnSeries G K)), fun _ _ ↦ rfl⟩
    have hplC : ∀ j x, (placed j x).support ⊆ C x := by
      intro j x
      rw [hplaced j x, support_setRestrict]
      exact inter_subset_right
    have hplle : ∀ j (x : ↥Xset), ∀ p ∈ (placed j x).support, p ≤ (x : G) := by
      intro j x p hp
      rw [hplaced j x, support_setRestrict] at hp
      obtain ⟨hp1, -⟩ := hp
      rw [support_translate] at hp1
      obtain ⟨q, hq, rfl⟩ := hp1
      have hq0 : q ≤ 0 := (cp x j).property hq
      calc (x : G) + q ≤ (x : G) + 0 := add_le_add le_rfl hq0
        _ = (x : G) := add_zero _
    have hsepP : ∀ j, ∀ a b : ↥Xset, a < b →
        ∀ p ∈ (placed j a).support, ∀ q ∈ (placed j b).support, p < q :=
      fun j a b hab p hp q hq ↦ hCord a b hab p (hplC j a hp) q (hplC j b hq)
    have hcPnonpos : ∀ j, (separatedHsum hXpwo (placed j) (hsepP j)).support ⊆ Iic 0 := by
      intro j g hg
      rw [support_separatedHsum, Set.mem_iUnion] at hg
      obtain ⟨x, hgx⟩ := hg
      exact (hplle j x g hgx).trans (hX0 x)
    obtain ⟨cP, hcP_coe⟩ : ∃ cP : κ' → Nonpositive G K, ∀ j,
        ((cP j : Nonpositive G K) : HahnSeries G K) =
          separatedHsum hXpwo (placed j) (hsepP j) :=
      ⟨fun j ↦ ⟨separatedHsum hXpwo (placed j) (hsepP j), hcPnonpos j⟩, fun _ ↦ rfl⟩
    let pieceFamily : SeparatedHsumFamily κ' ↥Xset :=
      { hX := hXpwo
        piece := C
        center := fun x ↦ (x : G)
        term := placed
        support_subset := hplC
        support_le_center := hplle
        center_mem := hCmem
        isOpen_piece := hCopen
        ordConnected_piece := hCconv
        disjoint_piece := hCdisj
        piece_lt_piece := hCord
        separated := hsepP
        sum := cP
        coe_sum := hcP_coe }
    have hdiscP : ∀ z : G, ¬ AccPt z (𝓟 (Set.range (fun x : ↥Xset ↦ (x : G)))) := by
      intro z
      rw [Subtype.range_coe]
      exact hXdisc z
    have hplzero : ∀ j (x : ↥Xset), bx x ≤ τ → placed j x = 0 := by
      intro j x hbxτ
      rw [hplaced j x, hcp0 x hbxτ j]
      rw [show ((0 : Nonpositive G K) : HahnSeries G K) = 0 from rfl, map_zero]
      ext g
      rw [coeff_setRestrict]
      split_ifs <;> rfl
    have hstageP : ∀ j (x : ↥Xset),
        (((placed j x).closedSupport).cantorBendixson (P j β).val : Set G) ⊆ {(x : G)} := by
      intro j x
      by_cases hbxτ : bx x ≤ τ
      · rw [hplzero j x hbxτ]
        intro z hz
        exfalso
        have hzs := TopologicalSpace.Closeds.cantorBendixson_le _ _ hz
        rw [mem_closedSupport, HahnSeries.support_zero, closure_empty] at hzs
        exact hzs
      · intro z hz
        exfalso
        obtain ⟨hzs, hzr⟩ := ((placed j x).mem_support_derivative_iff z (P j β).val).mp hz
        have h1 : (placed j x).cantorBendixsonRank z ≤
            (translate (x : G)
              ((cp x j : Nonpositive G K) : HahnSeries G K)).cantorBendixsonRank z :=
          cantorBendixsonRank_le_of_support_subset (by
            rw [hplaced j x, support_setRestrict]
            exact inter_subset_left) z
        have h2 : (translate (x : G) ((cp x j : Nonpositive G K) :
            HahnSeries G K)).cantorBendixsonRank z =
            ((cp x j : Nonpositive G K) : HahnSeries G K).cantorBendixsonRank (z - (x : G)) := by
          have := cantorBendixsonRank_translate ((cp x j : Nonpositive G K) : HahnSeries G K)
            (x : G) (z - (x : G))
          rw [show (x : G) + (z - (x : G)) = z by abel] at this
          exact this
        have h3 : ((cp x j : Nonpositive G K) : HahnSeries G K).cantorBendixsonRank (z - (x : G)) ≤
            (P j (bx x)).val := by
          by_cases hm : z - (x : G) ∈
              ((cp x j : Nonpositive G K) : HahnSeries G K).closedSupport
          · have hz0 : z - (x : G) ≤ 0 := closure_minimal (cp x j).property isClosed_Iic
              ((mem_closedSupport _ _).mp hm)
            have hprof := hcpb x j (z - (x : G)) hz0
            rw [degree_translatedTruncLE_eq, if_pos hm, WithBot.coe_le_coe] at hprof
            have hval := NatOrdinal.of.symm.monotone hprof
            change NatOrdinal.val (NatOrdinal.of _) ≤ NatOrdinal.val _ at hval
            rwa [NatOrdinal.val_of] at hval
          · rw [cantorBendixsonRank_eq,
            TopologicalSpace.Closeds.cantorBendixsonRank_of_notMem _ _ hm]
            exact zero_le (a := (P j (bx x)).val)
        have h4 : (P j (bx x)).val < (P j β).val := by
          have hlt := hPlt j (bx x) β (lt_of_not_ge hbxτ) (hbx_lt x) hβμ
          have h := NatOrdinal.of.symm.strictMono hlt
          change NatOrdinal.val _ < NatOrdinal.val _ at h
          exact h
        exact absurd hzr (not_le_of_gt (((h1.trans_eq h2).trans h3).trans_lt h4))
    have hcPb : ∀ j, ∀ y : G, y ≤ 0 → ν (translatedTruncLE y (cP j)) ≤ P j β := by
      intro j y hy
      have hbounds := cantorBendixsonRank_separatedHsum_bounds hXpwo C (fun x ↦ (x : G)) (placed j)
        (hplC j) (hplle j) hCmem hCopen hCdisj hCord (hsepP j) hdiscP (P j β).val (hstageP j)
      rw [degree_translatedTruncLE_eq]
      by_cases hm : y ∈ ((cP j : Nonpositive G K) : HahnSeries G K).closedSupport
      · rw [if_pos hm]
        have hrank : ((cP j : Nonpositive G K) : HahnSeries G K).cantorBendixsonRank y ≤
            (P j β).val := by
          have hr := hbounds.1 y
          have hreq : ((cP j : Nonpositive G K) : HahnSeries G K).cantorBendixsonRank y =
              (separatedHsum hXpwo (placed j) (hsepP j)).cantorBendixsonRank y := by
            rw [hcP_coe j]
          rw [hreq]
          exact hr
        calc ((NatOrdinal.of (((cP j : Nonpositive G K) : HahnSeries G K).cantorBendixsonRank y)) :
            WithBot NatOrdinal) ≤ (NatOrdinal.of ((P j β).val) : WithBot NatOrdinal) :=
              WithBot.coe_le_coe.mpr (NatOrdinal.of.monotone hrank)
          _ = (P j β : WithBot NatOrdinal) := by rw [NatOrdinal.of_val]
      · rw [if_neg hm]
        exact bot_le
    -- Step E: the final cofactors correct every truncation to the floor.
    refine ⟨fun j ↦ ctop j + cP j, ?_, ?_, ?_⟩
    · intro j y hy
      rw [map_add]
      exact ((ν).map_add_le_max _ _).trans (max_le (hctopb j y hy) (hcPb j y hy))
    · intro habs
      exact (hβτ habs).elim
    · intro y hy
      have hres_eq : u - ∑ j, (ctop j + cP j) * q j =
          R - ∑ j, cP j * q j := by
        rw [hR_def, Finset.sum_congr rfl fun j _ ↦ add_mul (ctop j) (cP j) (q j),
          Finset.sum_add_distrib]
        ring
      rw [hres_eq, map_sub, map_sum]
      have hEc : ∀ j, ν (translatedTruncLE y (cP j * q j) -
          translatedTruncLE y (cP j) * q j) < (τ : WithBot NatOrdinal) := fun j ↦
        degree_translatedTruncLE_mul_sub_mul_lt_forall (cP j) (q j)
          (P j β) (σQ j) τ (by simpa only [translatedTruncLE_zero] using hcPb j 0 le_rfl)
          (fun z hz ↦ hcPb j z hz.le) (fun z hz ↦ (hW j).degree_translatedTruncLE_lt hz)
          (hPsep' j β hτβ hβμ) y
      by_cases hyC : ∃ x : ↥Xset, y ∈ C x
      · obtain ⟨x, hyx⟩ := hyC
        have hRloc := hloc x y hyx
        have hcPloc : ∀ j, ν (translatedTruncLE y (cP j) -
            translatedTruncLE (y - (x : G)) (cp x j)) = ⊥ := fun j ↦
          degree_translatedTruncLE_separatedHsum_sub_piece_eq_bot hXpwo C hCopen hCconv
            (placed j) (hplC j) hCord (hsepP j) x (x : G) hyx (cp x j) (hplaced j x)
            (cP j) (hcP_coe j)
        have hEin (j : κ') :=
          degree_translatedTruncLE_mul_sub_mul_lt_of_eq_zero_or_bounds
            (cp x j) (q j) (P j (bx x)) (σQ j) τ (bx x)
            (fun h ↦ hcp0 x h j)
            (by simpa only [translatedTruncLE_zero] using hcpb x j 0 le_rfl)
            (fun z hz ↦ hcpb x j z hz.le)
            (fun z hz ↦ (hW j).degree_translatedTruncLE_lt hz)
            (fun h ↦ hPsep' j (bx x) h ((hbx_lt x).le.trans hβμ)) (y - (x : G))
        have hkey := translatedTruncLE_sub_sum_eq_local_errors y (y - (x : G)) R (ux x)
          (cp x) cP q
        rw [hkey]
        apply degree_add_add_sum_le
        · rw [degree_reverse_sub_eq_bot hRloc]
          exact bot_le
        · exact degree_translatedTruncLE_le_of_nonpositive (hcpres x) (y - (x : G))
        · intro j
          apply degree_add_add_le (hEin j).le
          · rw [degree_mul_eq_bot_of_left
                (b := q j) (degree_reverse_sub_eq_bot (hcPloc j))]
            exact bot_le
          · exact (degree_reverse_sub_lt (hEc j)).le
      · have hyR := degree_translatedTruncLE_eq_bot_of_notMem_closedSupport (b := R) (by
          intro hm
          exact hyC (Set.mem_iUnion.mp (hCcov hm)))
        have hXclosed : closure Xset = Xset :=
          (isClosed_iff_accPt.mpr fun z hz ↦ (hXdisc z hz).elim).closure_eq
        have hyPieces : ∀ x : ↥Xset, y ∉ C x := fun x hyx ↦ hyC ⟨x, hyx⟩
        have hyX : y ∉ Xset := fun h ↦ hyC (Set.mem_iUnion.mp (hXpieces h))
        have hyCenters : y ∉ closure (Set.range (fun x : ↥Xset ↦ (x : G))) :=
          notMem_closure_range_subtype_coe hXclosed hyX
        have hycP :=
          pieceFamily.degree_translatedTruncLE_eq_bot_of_notMem hyPieces hyCenters
        apply degree_translatedTruncLE_sub_sum_le_of_eq_bot
          (G := G) (K := K) (J := κ') (R := R) (c := cP)
          (q := q) (y := y) (τ := τ) hyR hEc
        simpa only [pieceFamily] using hycP


open Classical in
/-- **The graded conclusion of the cofactor construction.** Under the hypotheses at the top degree
`μ`, the homogeneous class of `u` in degree `μ` lies in the ideal of the associated graded ring
generated by the classes of the evaluated generators. The cofactors exhibit this membership, and
the resulting residual has degree at most `τ < μ`, hence represents zero in degree `μ`. -/
theorem homogeneousClass_mem_span_of_locallyIdeal
    [DenselyOrdered G] [NoMinOrder G] [NoMaxOrder G]
    [LinearOrder κ] [WellFoundedLT κ] [Finite κ']
    (U : κ → AddSubgroup G)
    (hUmono : ∀ {i j : κ}, i ≤ j → (U j : Set G) ⊆ (U i : Set G))
    (hUopen : ∀ i, IsOpen (U i : Set G))
    (hUconv : ∀ i, (U i : Set G).OrdConnected)
    (hUbase : ∀ ε : G, 0 < ε → ∃ i, (U i : Set G) ⊆ Ioo (-ε) ε)
    {wt : ι → NatOrdinal.{u}} {V : ι → Nonpositive G K}
    (xg : ι → (ν).AssociatedGraded)
    (hV : ∀ i, Represents (V i) (wt i) (xg i))
    (hVbounds : ∀ i, HasLowerTruncationDegree (V i) (wt i))
    (α : NatOrdinal.{u})
    (hgen : ∀ β : NatOrdinal.{u}, β < α → ∀ y ∈ DirectSum.rangeLof K (ν).Component β,
      ∃ F : MvPolynomial ι K, IsWeightedHomogeneous wt F β ∧ aeval xg F = y)
    (hinj : ∀ (β : NatOrdinal.{u}) (F : MvPolynomial ι K), β < α →
      IsWeightedHomogeneous wt F β → aeval xg F = 0 → F = 0)
    (Q : κ' → MvPolynomial ι K) (σQ : κ' → NatOrdinal.{u})
    (hQ : ∀ j, IsWeightedHomogeneous wt (Q j) (σQ j))
    (τ μ : NatOrdinal.{u}) (hτμ : τ < μ) (hμα : μ < α)
    (P : κ' → NatOrdinal.{u} → NatOrdinal.{u})
    (hP : ∀ j β, τ < β → β ≤ μ → P j β + σQ j = β)
    (hPsep : ∀ j θ, θ < σQ j → P j μ + θ < τ)
    (u : Nonpositive G K) (eu : (ν).AssociatedGraded) (heu : Represents u μ eu)
    (hu : ∀ y : G, y ≤ 0 → ν (translatedTruncLE y u) ≤ μ)
    (hp : ∀ y : G, y ≤ 0 → ∃ F : MvPolynomial ι K,
      (∀ d ∈ F.support, (Finsupp.weight wt) d < α) ∧
      ν (translatedTruncLE y u - aeval V F) = ⊥ ∧
      MvPolynomial.componentsGE wt τ F ∈ Ideal.span (Set.range Q)) :
    eu ∈ Ideal.span (Set.range fun j ↦ aeval xg (Q j)) := by
  classical
  letI := Fintype.ofFinite κ'
  obtain ⟨c, hcb, -, hres⟩ := exists_cofactors_degree_translatedTruncLE_le_of_locallyIdeal
    U hUmono hUopen hUconv hUbase xg hV hVbounds α hgen hinj Q σQ hQ τ μ hτμ hμα P hP hPsep
    μ le_rfl u hu hp
  have hcrep : ∀ j, Represents (c j) (P j μ)
      ((ν).homogeneousMk (P j μ) ⟨c j, ((ν).mem_filtrationLE_iff (P j μ) (c j)).mpr
        (by simpa only [translatedTruncLE_zero] using hcb j 0 le_rfl)⟩) :=
    fun j ↦ represents_iff.mpr
      ⟨by simpa only [translatedTruncLE_zero] using hcb j 0 le_rfl, rfl⟩
  have hQrep : ∀ j, Represents (aeval V (Q j)) (σQ j) (aeval xg (Q j)) :=
    fun j ↦ represents_aeval xg hV (hQ j)
  have hterm : ∀ j, Represents (c j * aeval V (Q j)) μ
      ((ν).homogeneousMk (P j μ) ⟨c j, ((ν).mem_filtrationLE_iff (P j μ) (c j)).mpr
        (by simpa only [translatedTruncLE_zero] using hcb j 0 le_rfl)⟩ * aeval xg (Q j)) :=
    fun j ↦ (hcrep j).mul (hP j μ (lt_of_lt_of_le hτμ le_rfl) le_rfl).symm (hQrep j)
  have hsumrep := represents_sum (s := (Finset.univ : Finset κ')) (m := μ)
    fun j _ ↦ hterm j
  have hzero : Represents (u - ∑ j, c j * aeval V (Q j)) μ 0 := by
    apply represents_of_degree_lt
    have hle := hres 0 le_rfl
    rw [translatedTruncLE_zero] at hle
    exact hle.trans_lt (WithBot.coe_lt_coe.mpr hτμ)
  have hsplit : u = (u - ∑ j, c j * aeval V (Q j)) + ∑ j, c j * aeval V (Q j) := by abel
  have hurep : Represents u μ (0 + ∑ j, (ν).homogeneousMk (P j μ)
      ⟨c j, ((ν).mem_filtrationLE_iff (P j μ) (c j)).mpr
        (by simpa only [translatedTruncLE_zero] using hcb j 0 le_rfl)⟩ * aeval xg (Q j)) := by
    rw [hsplit]
    exact hzero.add hsumrep
  rw [heu.unique hurep, zero_add]
  exact Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

open Classical in
/-- **Ideal membership from proper translated truncations.** Suppose `ν u ≤ μ` and every
translated truncation at a strictly negative cutoff has degree below `μ`. If those truncations are
locally congruent to
evaluated polynomials with ideal high part, there are cofactors of the prescribed degrees whose
combination with the evaluated generators corrects the series to degree at most `τ + 1`. The
hypothesis is never used at the cutoff zero, where it would assert the conclusion: the closed
support is partitioned inside the strictly negative region, every piece is treated by the
well-founded cofactor construction at its own strictly smaller rank, and the translated local
cofactors combine with strict local stages, so the resulting cofactors keep their degrees at zero.
-/
@[blueprint "lem:well-founded-cofactor-construction"
  (phase := "Algebraic independence in graded rings")
  (title := "Cofactors from local data by well-founded induction")
  (statement := /--
    Let $K$ be a field of characteristic zero and let $G$ be a complete
    densely ordered abelian group with a decreasing well-founded neighbourhood
    basis $(U_i)$ of open convex additive subgroups. Let $b_i$ represent
    homogeneous classes $x_i$ of degrees $w_i$ in the Cantor--Bendixson
    associated graded ring, with
    \[
      \nu(b_i)\le w_i,
      \qquad \nu(b_i^{\vert y})<w_i\quad(y<0).
    \]
    Assume homogeneous evaluation at $(x_i)$ is generating and injective below
    $\alpha$.

    Let $Q_j$ be finitely many weighted-homogeneous polynomials of degrees
    $\sigma_j$.  Fix $\tau<\mu<\alpha$ and ordinals $P_j(\beta)$ satisfying
    \[
      P_j(\beta)\oplus\sigma_j=\beta
      \quad(\tau<\beta\le\mu),
      \qquad
      P_j(\mu)\oplus\theta<\tau\quad(\theta<\sigma_j).
    \]
    Suppose
    \[
      \nu(u)\le\mu,
      \qquad \nu(u^{\vert y})<\mu\quad(y<0),
    \]
    and, at every negative cutoff, $u^{\vert y}$ is congruent modulo series
    bounded away from zero to an evaluated polynomial all of whose monomials
    have weight below $\alpha$ and whose terms of degree at least $\tau$ lie
    in the ideal generated by the $Q_j$. Then there are series $c_j$ such that
    \[
      \nu(c_j)\le P_j(\mu),\qquad
      \nu\!\left(u-\sum_jc_jQ_j(b)\right)\le\tau\oplus1.
    \]
  -/)
  (proof := /--
    By \ref{thm:cantor-bendixson-value-multiplicative}, the
    Cantor--Bendixson degree defines the associated graded ring used below.
    Partition the closed support of $u$ inside the negative half-line into
    ordered disjoint convex pieces whose ranks are strictly smaller than the
    rank of the piece centre.  On each piece
    \ref{lem:homogeneous-element-of-generated-ideal} first decomposes the
    homogeneous ideal relation into cofactors of complementary degrees; the
    well-founded induction then produces local series cofactors with the
    prescribed degree bounds.  Translate them back to their piece centres.  Separation of
    the convex carriers makes the translated families summable, so their Hahn
    sums $c_j$ preserve the bounds $P_j(\mu)$. The local residual bounds combine
    on the same carriers, giving degree at most $\tau\oplus1$ for the global
    residual.
  -/)]
theorem exists_cofactors_degree_le_add_one_of_properly_locallyIdeal
    [DenselyOrdered G] [NoMinOrder G] [NoMaxOrder G]
    [LinearOrder κ] [WellFoundedLT κ] [Fintype κ']
    (U : κ → AddSubgroup G)
    (hUmono : ∀ {i j : κ}, i ≤ j → (U j : Set G) ⊆ (U i : Set G))
    (hUopen : ∀ i, IsOpen (U i : Set G))
    (hUconv : ∀ i, (U i : Set G).OrdConnected)
    (hUbase : ∀ ε : G, 0 < ε → ∃ i, (U i : Set G) ⊆ Ioo (-ε) ε)
    {wt : ι → NatOrdinal.{u}} {V : ι → Nonpositive G K}
    (xg : ι → (ν).AssociatedGraded)
    (hV : ∀ i, Represents (V i) (wt i) (xg i))
    (hVbounds : ∀ i, HasLowerTruncationDegree (V i) (wt i))
    (α : NatOrdinal.{u})
    (hgen : ∀ β : NatOrdinal.{u}, β < α → ∀ y ∈ DirectSum.rangeLof K (ν).Component β,
      ∃ F : MvPolynomial ι K, IsWeightedHomogeneous wt F β ∧ aeval xg F = y)
    (hinj : ∀ (β : NatOrdinal.{u}) (F : MvPolynomial ι K), β < α →
      IsWeightedHomogeneous wt F β → aeval xg F = 0 → F = 0)
    (Q : κ' → MvPolynomial ι K) (σQ : κ' → NatOrdinal.{u})
    (hQ : ∀ j, IsWeightedHomogeneous wt (Q j) (σQ j))
    (τ μ : NatOrdinal.{u}) (hτμ : τ < μ) (hμα : μ < α)
    (P : κ' → NatOrdinal.{u} → NatOrdinal.{u})
    (hP : ∀ j β, τ < β → β ≤ μ → P j β + σQ j = β)
    (hPsep : ∀ j θ, θ < σQ j → P j μ + θ < τ)
    (u : Nonpositive G K) (htruncationBounds : HasLowerTruncationDegree u μ)
    (hp : ∀ y : G, y < 0 → ∃ F : MvPolynomial ι K,
      (∀ d ∈ F.support, (Finsupp.weight wt) d < α) ∧
      ν (translatedTruncLE y u - aeval V F) = ⊥ ∧
      MvPolynomial.componentsGE wt τ F ∈ Ideal.span (Set.range Q)) :
    ∃ c : κ' → Nonpositive G K,
      (∀ j, ν (c j) ≤ P j μ) ∧
      ν (u - ∑ j, c j * aeval V (Q j)) ≤ ((τ + 1 : NatOrdinal) : WithBot NatOrdinal) := by
  classical
  have hW : ∀ j, HasLowerTruncationDegree (aeval V (Q j)) (σQ j) := fun j ↦
    hasLowerTruncationDegree_aeval hVbounds (hQ j)
  have hPmono : ∀ j β' β'', τ < β' → β' ≤ β'' → β'' ≤ μ → P j β' ≤ P j β'' := by
    intro j β' β'' h1 h2 h3
    have e1 := hP j β' h1 (h2.trans h3)
    have e2 := hP j β'' (h1.trans_le h2) h3
    have : P j β' + σQ j ≤ P j β'' + σQ j := by rw [e1, e2]; exact h2
    exact le_of_add_le_add_right this
  have hPlt : ∀ j β' β'', τ < β' → β' < β'' → β'' ≤ μ → P j β' < P j β'' := by
    intro j β' β'' h1 h2 h3
    have e1 := hP j β' h1 (h2.le.trans h3)
    have e2 := hP j β'' (h1.trans h2) h3
    have : P j β' + σQ j < P j β'' + σQ j := by rw [e1, e2]; exact h2
    exact lt_of_add_lt_add_right this
  have hPsep' : ∀ j β', τ < β' → β' ≤ μ → ∀ θ, θ < σQ j → P j β' + θ < τ := by
    intro j β' h1 h2 θ hθ
    exact (add_le_add (hPmono j β' μ h1 h2 le_rfl) le_rfl).trans_lt (hPsep j θ hθ)
  -- Partition the closed support inside the strictly negative region.
  obtain ⟨Xset, C, hXs, hCmem, hCopen, hCconv, hCW, hCdisj, hCord, hCcov, hCmax, hCrank,
      hXdisc⟩ :=
    TopologicalSpace.Closeds.exists_disjoint_convex_cover_with_rank_lt_center_within
      (u : HahnSeries G K).closedSupport (u : HahnSeries G K).closedSupport_isPWO
      (Iio 0) isOpen_Iio U hUmono hUopen hUconv hUbase
  have hXneg : ∀ x : ↥Xset, (x : G) < 0 := fun x ↦ (hXs x.2).2
  have hXset_pwo : Xset.IsPWO :=
    (u : HahnSeries G K).closedSupport_isPWO.mono fun p hp ↦ (hXs hp).1
  have hXpwo : (Set.univ : Set ↥Xset).IsPWO := by
    rw [Set.isPWO_iff_exists_monotone_subseq]
    intro f _
    obtain ⟨g, hg⟩ := hXset_pwo.exists_monotone_subseq fun n ↦ (f n).2
    exact ⟨g, fun a b hab ↦ Subtype.coe_le_coe.mp (hg hab)⟩
  -- Pieces of the source and their local data.
  obtain ⟨fx, hfx⟩ : ∃ fx : ↥Xset → K⟦G⟧, ∀ x,
      fx x = setRestrict (C x) ((u : Nonpositive G K) : HahnSeries G K) :=
    ⟨fun x ↦ setRestrict (C x) ((u : Nonpositive G K) : HahnSeries G K), fun _ ↦ rfl⟩
  have hfxC : ∀ x, (fx x).support ⊆ C x := by
    intro x
    rw [hfx x, support_setRestrict]
    exact inter_subset_right
  have hfxle : ∀ x : ↥Xset, ∀ p ∈ (fx x).support, p ≤ (x : G) := by
    intro x p hp
    rw [hfx x, support_setRestrict] at hp
    exact hCmax x p ⟨(mem_closedSupport _ _).mpr (subset_closure hp.1), hp.2⟩
  have hsepx : ∀ i j : ↥Xset, i < j →
      ∀ a ∈ (fx i).support, ∀ b ∈ (fx j).support, a < b :=
    fun i j hij a ha b hb ↦ hCord i j hij a (hfxC i ha) b (hfxC j hb)
  have hfx_shift : ∀ x : ↥Xset, (translate (-(x : G)) (fx x)).support ⊆ Iic 0 := by
    intro x
    rw [support_translate]
    rintro g ⟨p, hp, rfl⟩
    have hpx := hfxle x p hp
    have h3 : -(x : G) + p ≤ 0 := by
      have h2 : -(x : G) + p ≤ -(x : G) + (x : G) := add_le_add le_rfl hpx
      rwa [neg_add_cancel] at h2
    exact mem_Iic.mpr h3
  obtain ⟨ux, hux⟩ : ∃ ux : ↥Xset → Nonpositive G K, ∀ x,
      ((ux x : Nonpositive G K) : HahnSeries G K) = translate (-(x : G)) (fx x) :=
    ⟨fun x ↦ ⟨translate (-(x : G)) (fx x), hfx_shift x⟩, fun _ ↦ rfl⟩
  obtain ⟨bx, hbx⟩ : ∃ bx : ↥Xset → NatOrdinal.{u}, ∀ x,
      bx x = NatOrdinal.of (((u : Nonpositive G K) : HahnSeries G K).cantorBendixsonRank (x : G)) :=
    ⟨fun x ↦ NatOrdinal.of (((u : Nonpositive G K) : HahnSeries G K).cantorBendixsonRank (x : G)),
      fun _ ↦ rfl⟩
  have hbx_lt : ∀ x : ↥Xset, bx x < μ := by
    intro x
    have h1 := htruncationBounds.degree_translatedTruncLE_lt (hXneg x)
    have hm : (x : G) ∈ ((u : Nonpositive G K) : HahnSeries G K).closedSupport := (hXs x.2).1
    rw [degree_translatedTruncLE_eq, if_pos hm] at h1
    rw [hbx x]
    exact WithBot.coe_lt_coe.mp h1
  have hRsum : ((u : Nonpositive G K) : HahnSeries G K) = 0 ∨ True := Or.inr trivial
  -- Locality of truncations inside a piece.
  have hplaced_eq : ∀ (x : ↥Xset) (s : G),
      ((translatedTruncLE s (ux x) : Nonpositive G K) : HahnSeries G K) =
        translate (-((x : G) + s)) (truncLE ((x : G) + s) (fx x)) := by
    intro x s
    have h2 : ((x : G) + s) - (x : G) = s := by abel
    have hshift : ((translatedTruncLE (((x : G) + s) - (x : G)) (ux x) : Nonpositive G K) :
        HahnSeries G K) = translate (-((x : G) + s)) (truncLE ((x : G) + s)
          (translate (x : G) ((ux x : Nonpositive G K) : HahnSeries G K))) :=
      translatedTruncLE_shift (x : G) ((x : G) + s) (ux x)
    rw [h2] at hshift
    have hcancel : translate (x : G) (translate (-(x : G)) (fx x)) = fx x := by
      rw [translate_add_apply, add_neg_cancel, translate_zero_apply]
    rw [hshift, hux x, hcancel]
  have hloc : ∀ (x : ↥Xset) (y' : G), y' ∈ C x →
      ν (translatedTruncLE (y' - (x : G)) (ux x) - translatedTruncLE y' u) = ⊥ := by
    intro x y' hy'
    obtain ⟨cst, hcst, hcsty⟩ := exists_lt_mem_of_isOpen_ordConnected (hCopen x) hy'
    apply (cantorBendixsonDegreeValuation_eq_bot_iff _).mpr
    refine ⟨cst - y', sub_neg.mpr hcsty, ?_⟩
    intro g hg
    have hcoe1 : ((translatedTruncLE (y' - (x : G)) (ux x) : Nonpositive G K) :
        HahnSeries G K) = translate (-y') (truncLE y' (fx x)) := by
      have h2 : (x : G) + (y' - (x : G)) = y' := by abel
      have := hplaced_eq x (y' - (x : G))
      rw [h2] at this
      exact this
    rw [AddSubgroupClass.coe_sub, hcoe1, coe_translatedTruncLE] at hg
    have hcombine : translate (-y') (truncLE y' (fx x)) -
        translate (-y') (truncLE y' ((u : Nonpositive G K) : HahnSeries G K)) =
        translate (-y') (truncLE y' (fx x) -
          truncLE y' ((u : Nonpositive G K) : HahnSeries G K)) :=
      (map_sub (translate (-y')) _ _).symm
    rw [hcombine, support_translate] at hg
    obtain ⟨q, hq, rfl⟩ := hg
    have hb2 : ∀ p ∈ ((u : Nonpositive G K) : HahnSeries G K).support, p ∉ C x →
        p ≤ y' → p ≤ cst := by
      intro p _ hpC hpy
      by_contra hgt
      exact hpC ((hCconv x).out hcst hy' ⟨(not_le.mp hgt).le, hpy⟩)
    have hq2 := support_truncLE_sub_truncLE_setRestrict_subset (C x)
      ((u : Nonpositive G K) : HahnSeries G K) y' hb2
    have hqrev : q ∈ (truncLE y' ((u : Nonpositive G K) : HahnSeries G K) -
        truncLE y' (setRestrict (C x) ((u : Nonpositive G K) : HahnSeries G K))).support := by
      rw [← support_neg, neg_sub, ← hfx x]
      exact hq
    have hqc : q ≤ cst := hq2 hqrev
    have h3 : -y' + q ≤ cst - y' := by
      have h2 : -y' + q ≤ -y' + cst := add_le_add le_rfl hqc
      calc -y' + q ≤ -y' + cst := h2
        _ = cst - y' := by abel
    exact mem_Iic.mpr h3
  -- Degree profile and local ideal condition of each piece.
  have hux_prof : ∀ x : ↥Xset, ∀ s : G, s ≤ 0 →
      ν (translatedTruncLE s (ux x)) ≤ (bx x : WithBot NatOrdinal) := by
    intro x s hs
    have hy'x : (x : G) + s ≤ (x : G) := by
      calc (x : G) + s ≤ (x : G) + 0 := add_le_add le_rfl hs
        _ = (x : G) := add_zero _
    by_cases hy'C : (x : G) + s ∈ C x
    · have h1 := hloc x ((x : G) + s) hy'C
      have h2 : ((x : G) + s) - (x : G) = s := by abel
      rw [h2] at h1
      rw [degree_eq_of_degree_sub_eq_bot h1, degree_translatedTruncLE_eq]
      by_cases hm : (x : G) + s ∈ ((u : Nonpositive G K) : HahnSeries G K).closedSupport
      · rw [if_pos hm]
        rcases eq_or_ne ((x : G) + s) (x : G) with heq | hne
        · rw [heq, hbx x]
        · have hlt := hCrank x ((x : G) + s) ⟨hm, hy'C⟩ hne
          have hlt' : ((u : Nonpositive G K) : HahnSeries G K).cantorBendixsonRank ((x : G) + s) <
              ((u : Nonpositive G K) : HahnSeries G K).cantorBendixsonRank (x : G) := by
            rw [cantorBendixsonRank_eq, cantorBendixsonRank_eq]
            exact hlt
          rw [hbx x]
          exact WithBot.coe_le_coe.mpr (NatOrdinal.of.monotone hlt'.le)
      · rw [if_neg hm]
        exact bot_le
    · have hbelow := lt_of_notMem_ordConnected (hCconv x) (hCmem x) hy'x hy'C
      have hzero : truncLE ((x : G) + s) (fx x) = 0 :=
        truncLE_eq_zero_of_forall_lt _ _ (fun p hp ↦ hbelow p (hfxC x hp))
      have hzero' : translatedTruncLE s (ux x) = 0 := by
        apply Subtype.ext
        rw [hplaced_eq x s, hzero, map_zero]
        rfl
      rw [hzero', (ν).map_zero]
      exact bot_le
  have hpux : ∀ x : ↥Xset, ∀ s : G, s ≤ 0 → ∃ F : MvPolynomial ι K,
      (∀ d ∈ F.support, (Finsupp.weight wt) d < α) ∧
      ν (translatedTruncLE s (ux x) - aeval V F) = ⊥ ∧
      MvPolynomial.componentsGE wt τ F ∈ Ideal.span (Set.range Q) := by
    intro x s hs
    have hy'neg : (x : G) + s < 0 := by
      calc (x : G) + s ≤ (x : G) + 0 := add_le_add le_rfl hs
        _ = (x : G) := add_zero _
        _ < 0 := hXneg x
    by_cases hy'C : (x : G) + s ∈ C x
    · obtain ⟨F, hFw, hFbot, hFGE⟩ := hp ((x : G) + s) hy'neg
      refine ⟨F, hFw, ?_, hFGE⟩
      have h1 := hloc x ((x : G) + s) hy'C
      have h2 : ((x : G) + s) - (x : G) = s := by abel
      rw [h2] at h1
      have hsplit : translatedTruncLE s (ux x) - aeval V F =
          (translatedTruncLE s (ux x) - translatedTruncLE ((x : G) + s) u) +
            (translatedTruncLE ((x : G) + s) u - aeval V F) := by
        abel
      rw [hsplit]
      refine le_bot_iff.mp (((ν).map_add_le_max _ _).trans ?_)
      rw [h1, hFbot, max_self]
    · have hy'x : (x : G) + s ≤ (x : G) := by
        calc (x : G) + s ≤ (x : G) + 0 := add_le_add le_rfl hs
          _ = (x : G) := add_zero _
      have hbelow := lt_of_notMem_ordConnected (hCconv x) (hCmem x) hy'x hy'C
      have hzero : truncLE ((x : G) + s) (fx x) = 0 :=
        truncLE_eq_zero_of_forall_lt _ _ (fun p hp ↦ hbelow p (hfxC x hp))
      have hzero' : translatedTruncLE s (ux x) = 0 := by
        apply Subtype.ext
        rw [hplaced_eq x s, hzero, map_zero]
        rfl
      refine ⟨0, by simp, ?_, ?_⟩
      · rw [hzero', map_zero, sub_zero, (ν).map_zero]
      · rw [componentsGE_zero]
        exact Ideal.zero_mem _
  -- Construct cofactors on every piece by well-founded induction at its smaller rank.
  have hpiece : ∀ x : ↥Xset, ∃ cp : κ' → Nonpositive G K,
      (∀ j, ∀ s : G, s ≤ 0 → ν (translatedTruncLE s (cp j)) ≤ P j (bx x)) ∧
      (bx x ≤ τ → ∀ j, cp j = 0) ∧
      ∀ s : G, s ≤ 0 →
        ν (translatedTruncLE s (ux x - ∑ j, cp j * aeval V (Q j))) ≤ τ :=
    fun x ↦ exists_cofactors_degree_translatedTruncLE_le_of_locallyIdeal
      U hUmono hUopen hUconv hUbase xg hV hVbounds α hgen hinj Q σQ hQ τ μ hτμ hμα P hP hPsep
      (bx x) (hbx_lt x).le (ux x) (hux_prof x) (hpux x)
  choose cp hcpb hcp0 hcpres using hpiece
  -- Translate the piece cofactors and sum them.
  obtain ⟨placed, hplaced⟩ : ∃ placed : κ' → ↥Xset → K⟦G⟧, ∀ j x,
      placed j x = setRestrict (C x)
        (translate (x : G) ((cp x j : Nonpositive G K) : HahnSeries G K)) :=
    ⟨fun j x ↦ setRestrict (C x)
      (translate (x : G) ((cp x j : Nonpositive G K) : HahnSeries G K)), fun _ _ ↦ rfl⟩
  have hplC : ∀ j x, (placed j x).support ⊆ C x := by
    intro j x
    rw [hplaced j x, support_setRestrict]
    exact inter_subset_right
  have hplle : ∀ j (x : ↥Xset), ∀ p ∈ (placed j x).support, p ≤ (x : G) := by
    intro j x p hp
    rw [hplaced j x, support_setRestrict] at hp
    obtain ⟨hp1, -⟩ := hp
    rw [support_translate] at hp1
    obtain ⟨q, hq, rfl⟩ := hp1
    have hq0 : q ≤ 0 := (cp x j).property hq
    calc (x : G) + q ≤ (x : G) + 0 := add_le_add le_rfl hq0
      _ = (x : G) := add_zero _
  have hsepP : ∀ j, ∀ a b : ↥Xset, a < b →
      ∀ p ∈ (placed j a).support, ∀ q ∈ (placed j b).support, p < q :=
    fun j a b hab p hp q hq ↦ hCord a b hab p (hplC j a hp) q (hplC j b hq)
  have hcPnonpos : ∀ j, (separatedHsum hXpwo (placed j) (hsepP j)).support ⊆ Iic 0 := by
    intro j g hg
    rw [support_separatedHsum, Set.mem_iUnion] at hg
    obtain ⟨x, hgx⟩ := hg
    exact (hplle j x g hgx).trans (hXneg x).le
  obtain ⟨cP, hcP_coe⟩ : ∃ cP : κ' → Nonpositive G K, ∀ j,
      ((cP j : Nonpositive G K) : HahnSeries G K) =
        separatedHsum hXpwo (placed j) (hsepP j) :=
    ⟨fun j ↦ ⟨separatedHsum hXpwo (placed j) (hsepP j), hcPnonpos j⟩, fun _ ↦ rfl⟩
  let pieceFamily : SeparatedHsumFamily κ' ↥Xset :=
    { hX := hXpwo
      piece := C
      center := fun x ↦ (x : G)
      term := placed
      support_subset := hplC
      support_le_center := hplle
      center_mem := hCmem
      isOpen_piece := hCopen
      ordConnected_piece := hCconv
      disjoint_piece := hCdisj
      piece_lt_piece := hCord
      separated := hsepP
      sum := cP
      coe_sum := hcP_coe }
  -- The translated pieces have an empty stage at the target degree, so summing costs no successor.
  have hstageP : ∀ j (x : ↥Xset),
      (((placed j x).closedSupport).cantorBendixson (P j μ).val : Set G) = ∅ := by
    intro j x
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    by_cases hbxτ : bx x ≤ τ
    · have hzero : placed j x = 0 := by
        rw [hplaced j x, hcp0 x hbxτ j]
        rw [show ((0 : Nonpositive G K) : HahnSeries G K) = 0 from rfl, map_zero]
        ext g
        rw [coeff_setRestrict]
        split_ifs <;> rfl
      rw [hzero] at hz
      have hzs := TopologicalSpace.Closeds.cantorBendixson_le _ _ hz
      rw [mem_closedSupport, HahnSeries.support_zero, closure_empty] at hzs
      exact hzs
    · obtain ⟨hzs, hzr⟩ := ((placed j x).mem_support_derivative_iff z (P j μ).val).mp hz
      have h1 : (placed j x).cantorBendixsonRank z ≤
          (translate (x : G) ((cp x j : Nonpositive G K) : HahnSeries G K)).cantorBendixsonRank z :=
        cantorBendixsonRank_le_of_support_subset (by
          rw [hplaced j x, support_setRestrict]
          exact inter_subset_left) z
      have h2 : (translate (x : G) ((cp x j : Nonpositive G K) :
          HahnSeries G K)).cantorBendixsonRank z =
          ((cp x j : Nonpositive G K) : HahnSeries G K).cantorBendixsonRank (z - (x : G)) := by
        have := cantorBendixsonRank_translate ((cp x j : Nonpositive G K) : HahnSeries G K)
          (x : G) (z - (x : G))
        rw [show (x : G) + (z - (x : G)) = z by abel] at this
        exact this
      have h3 : ((cp x j : Nonpositive G K) : HahnSeries G K).cantorBendixsonRank (z - (x : G)) ≤
          (P j (bx x)).val := by
        by_cases hm : z - (x : G) ∈
            ((cp x j : Nonpositive G K) : HahnSeries G K).closedSupport
        · have hz0 : z - (x : G) ≤ 0 := closure_minimal (cp x j).property isClosed_Iic
            ((mem_closedSupport _ _).mp hm)
          have hprof := hcpb x j (z - (x : G)) hz0
          rw [degree_translatedTruncLE_eq, if_pos hm, WithBot.coe_le_coe] at hprof
          have hval := NatOrdinal.of.symm.monotone hprof
          change NatOrdinal.val (NatOrdinal.of _) ≤ NatOrdinal.val _ at hval
          rwa [NatOrdinal.val_of] at hval
        · rw [cantorBendixsonRank_eq, TopologicalSpace.Closeds.cantorBendixsonRank_of_notMem _ _ hm]
          exact zero_le (a := (P j (bx x)).val)
      have h4 : (P j (bx x)).val < (P j μ).val := by
        have hlt := hPlt j (bx x) μ (lt_of_not_ge hbxτ) (hbx_lt x) le_rfl
        have h := NatOrdinal.of.symm.strictMono hlt
        change NatOrdinal.val _ < NatOrdinal.val _ at h
        exact h
      exact absurd hzr (not_le_of_gt (((h1.trans_eq h2).trans h3).trans_lt h4))
  have hclcen : closure (Set.range (fun x : ↥Xset ↦ (x : G))) ⊆
      Set.range (fun x : ↥Xset ↦ (x : G)) ∪ {0} := by
    intro z hz
    have hz0 : z ≤ 0 := by
      apply closure_minimal _ isClosed_Iic hz
      rintro p ⟨x, rfl⟩
      exact (hXneg x).le
    rcases eq_or_lt_of_le hz0 with hz0' | hzneg
    · exact Or.inr (Set.mem_singleton_iff.mpr hz0')
    · refine Or.inl ?_
      rw [closure_eq_self_union_derivedSet] at hz
      rcases hz with h | h
      · exact h
      · exfalso
        have hrange : Set.range (fun x : ↥Xset ↦ (x : G)) = Xset := Subtype.range_coe
        rw [hrange] at h
        exact hXdisc z hzneg (mem_derivedSet.mp h)
  have hcPbt : ∀ j, ∀ z : G, ν (translatedTruncLE z (cP j)) ≤ (P j μ : WithBot NatOrdinal) := by
    intro j z
    have hbounds := cantorBendixsonRank_separatedHsum_le_of_stage_empty hXpwo C
      (fun x ↦ (x : G)) (placed j) (hplC j) (hplle j) hCmem hCopen hCdisj hCord (hsepP j)
      (P j μ).val (hstageP j) 0 hclcen
    rw [degree_translatedTruncLE_eq]
    by_cases hm : z ∈ ((cP j : Nonpositive G K) : HahnSeries G K).closedSupport
    · rw [if_pos hm]
      have hrank : ((cP j : Nonpositive G K) : HahnSeries G K).cantorBendixsonRank z ≤
          (P j μ).val := by
        have hr := hbounds z
        have hreq : ((cP j : Nonpositive G K) : HahnSeries G K).cantorBendixsonRank z =
            (separatedHsum hXpwo (placed j) (hsepP j)).cantorBendixsonRank z := by
          rw [hcP_coe j]
        rw [hreq]
        exact hr
      calc ((NatOrdinal.of (((cP j : Nonpositive G K) : HahnSeries G K).cantorBendixsonRank z)) :
          WithBot NatOrdinal) ≤ (NatOrdinal.of ((P j μ).val) : WithBot NatOrdinal) :=
            WithBot.coe_le_coe.mpr (NatOrdinal.of.monotone hrank)
        _ = (P j μ : WithBot NatOrdinal) := by rw [NatOrdinal.of_val]
    · rw [if_neg hm]
      exact bot_le
  have hcPb : ∀ j, ν (cP j) ≤ P j μ := fun j ↦ by
    simpa only [translatedTruncLE_zero] using hcPbt j 0
  -- The residual is at most the floor at every proper cutoff.
  have hres : ∀ y : G, y < 0 →
      ν (translatedTruncLE y (u - ∑ j, cP j * aeval V (Q j))) ≤ (τ : WithBot NatOrdinal) := by
    intro y hy
    rw [map_sub, map_sum]
    have hEc : ∀ j, ν (translatedTruncLE y (cP j * aeval V (Q j)) -
        translatedTruncLE y (cP j) * aeval V (Q j)) < (τ : WithBot NatOrdinal) := fun j ↦
      degree_translatedTruncLE_mul_sub_mul_lt_forall (cP j) (aeval V (Q j))
        (P j μ) (σQ j) τ (hcPb j)
        (fun z _ ↦ hcPbt j z)
        (fun z hz ↦ (hW j).degree_translatedTruncLE_lt hz)
        (hPsep' j μ hτμ le_rfl) y
    by_cases hyC : ∃ x : ↥Xset, y ∈ C x
    · obtain ⟨x, hyx⟩ := hyC
      have hRloc := hloc x y hyx
      have hcPloc : ∀ j, ν (translatedTruncLE y (cP j) -
          translatedTruncLE (y - (x : G)) (cp x j)) = ⊥ := fun j ↦
        degree_translatedTruncLE_separatedHsum_sub_piece_eq_bot hXpwo C hCopen hCconv
          (placed j) (hplC j) hCord (hsepP j) x (x : G) hyx (cp x j) (hplaced j x)
          (cP j) (hcP_coe j)
      have hEin (j : κ') :=
        degree_translatedTruncLE_mul_sub_mul_lt_of_eq_zero_or_bounds
          (cp x j) (aeval V (Q j)) (P j (bx x)) (σQ j) τ (bx x)
          (fun h ↦ hcp0 x h j)
          (by simpa only [translatedTruncLE_zero] using hcpb x j 0 le_rfl)
          (fun z hz ↦ hcpb x j z hz.le)
          (fun z hz ↦ (hW j).degree_translatedTruncLE_lt hz)
          (fun h ↦ hPsep' j (bx x) h (hbx_lt x).le) (y - (x : G))
      have hkey := translatedTruncLE_sub_sum_eq_local_errors y (y - (x : G)) u (ux x)
        (cp x) cP (fun j ↦ aeval V (Q j))
      rw [hkey]
      apply degree_add_add_sum_le
      · rw [degree_reverse_sub_eq_bot hRloc]
        exact bot_le
      · exact degree_translatedTruncLE_le_of_nonpositive (hcpres x) (y - (x : G))
      · intro j
        apply degree_add_add_le (hEin j).le
        · rw [degree_mul_eq_bot_of_left
              (b := aeval V (Q j)) (degree_reverse_sub_eq_bot (hcPloc j))]
          exact bot_le
        · exact (degree_reverse_sub_lt (hEc j)).le
    · have hyu := degree_translatedTruncLE_eq_bot_of_notMem_closedSupport (b := u) (by
        intro hm
        exact hyC (Set.mem_iUnion.mp (hCcov ⟨hm, hy⟩)))
      have hyPieces : ∀ x : ↥Xset, y ∉ C x := fun x hyx ↦ hyC ⟨x, hyx⟩
      have hyCenters : y ∉ closure (Set.range (fun x : ↥Xset ↦ (x : G))) := by
        intro h
        rcases hclcen h with h' | h'
        · exact hyC (Set.mem_iUnion.mp (hCcov ⟨(hXs (by
            rw [← Subtype.range_coe (s := Xset)]; exact h')).1, hy⟩))
        · exact absurd (Set.mem_singleton_iff.mp h') (ne_of_lt hy)
      have hycP :=
        pieceFamily.degree_translatedTruncLE_eq_bot_of_notMem hyPieces hyCenters
      apply degree_translatedTruncLE_sub_sum_le_of_eq_bot
        (G := G) (K := K) (J := κ') (R := u) (c := cP)
        (q := fun j ↦ aeval V (Q j)) (y := y) (τ := τ) hyu hEc
      simpa only [pieceFamily] using hycP
  exact ⟨cP, hcPb, degree_le_add_one_of_forall_neg_le _ τ hres⟩

open Classical in
/-- **The proper-cutoff graded ideal membership.** Suppose `ν u ≤ μ` and every translated
truncation at a strictly negative cutoff has degree below `μ`. If those truncations are locally
congruent to evaluated polynomials with ideal high part, the homogeneous class represented by `u`
in degree `μ` lies in the ideal generated by the classes of the evaluated generators. The
hypothesis is never used at the cutoff zero, where it would assert the conclusion.

This is the ideal-lifting conclusion used when the degree is a limit ordinal: the construction
produces cofactors whose classes exhibit the membership, and the corrected residual, of degree at
most one above the floor, represents zero in degree `μ`. -/
@[blueprint "lem:local-ideal-membership-associated-graded"
  (phase := "Algebraic independence in graded rings")
  (title := "Local ideal membership in the associated graded ring")
  (statement := /--
    Under all the hypotheses of
    \ref{lem:well-founded-cofactor-construction}, suppose in addition that
    $\tau\oplus1<\mu$.  If $u$ represents a homogeneous class $\bar u$ of
    degree $\mu$, then
    \[
      \bar u\in\bigl(Q_j(x):j\bigr)
    \]
    in the Cantor--Bendixson associated graded ring.
  -/)
  (proof := /--
    By \ref{lem:well-founded-cofactor-construction}, choose cofactors $c_j$ of
    degree at most $P_j(\mu)$ whose residual has degree at most
    $\tau\oplus1<\mu$.  The degree-$\mu$ class of the residual is therefore
    zero.  Multiplication of represented homogeneous classes and
    $P_j(\mu)\oplus\sigma_j=\mu$ identify the remaining degree-$\mu$ class with
    $\sum_j[c_j]Q_j(x)$.
  -/)]
theorem homogeneousClass_mem_span_of_properly_locallyIdeal
    [DenselyOrdered G] [NoMinOrder G] [NoMaxOrder G]
    [LinearOrder κ] [WellFoundedLT κ] [Finite κ']
    (U : κ → AddSubgroup G)
    (hUmono : ∀ {i j : κ}, i ≤ j → (U j : Set G) ⊆ (U i : Set G))
    (hUopen : ∀ i, IsOpen (U i : Set G))
    (hUconv : ∀ i, (U i : Set G).OrdConnected)
    (hUbase : ∀ ε : G, 0 < ε → ∃ i, (U i : Set G) ⊆ Ioo (-ε) ε)
    {wt : ι → NatOrdinal.{u}} {V : ι → Nonpositive G K}
    (xg : ι → (ν).AssociatedGraded)
    (hV : ∀ i, Represents (V i) (wt i) (xg i))
    (hVbounds : ∀ i, HasLowerTruncationDegree (V i) (wt i))
    (α : NatOrdinal.{u})
    (hgen : ∀ β : NatOrdinal.{u}, β < α → ∀ y ∈ DirectSum.rangeLof K (ν).Component β,
      ∃ F : MvPolynomial ι K, IsWeightedHomogeneous wt F β ∧ aeval xg F = y)
    (hinj : ∀ (β : NatOrdinal.{u}) (F : MvPolynomial ι K), β < α →
      IsWeightedHomogeneous wt F β → aeval xg F = 0 → F = 0)
    (Q : κ' → MvPolynomial ι K) (σQ : κ' → NatOrdinal.{u})
    (hQ : ∀ j, IsWeightedHomogeneous wt (Q j) (σQ j))
    (τ μ : NatOrdinal.{u}) (hτμ : (τ + 1 : NatOrdinal) < μ) (hμα : μ < α)
    (P : κ' → NatOrdinal.{u} → NatOrdinal.{u})
    (hP : ∀ j β, τ < β → β ≤ μ → P j β + σQ j = β)
    (hPsep : ∀ j θ, θ < σQ j → P j μ + θ < τ)
    (u : Nonpositive G K) (htruncationBounds : HasLowerTruncationDegree u μ)
    (eu : (ν).AssociatedGraded) (heu : Represents u μ eu)
    (hp : ∀ y : G, y < 0 → ∃ F : MvPolynomial ι K,
      (∀ d ∈ F.support, (Finsupp.weight wt) d < α) ∧
      ν (translatedTruncLE y u - aeval V F) = ⊥ ∧
      MvPolynomial.componentsGE wt τ F ∈ Ideal.span (Set.range Q)) :
    eu ∈ Ideal.span (Set.range fun j ↦ aeval xg (Q j)) := by
  classical
  letI := Fintype.ofFinite κ'
  have hτlt : τ < μ := lt_of_le_of_lt (le_of_lt (lt_add_one τ)) hτμ
  obtain ⟨c, hcb, hres⟩ := exists_cofactors_degree_le_add_one_of_properly_locallyIdeal
    U hUmono hUopen hUconv hUbase xg hV hVbounds α hgen hinj Q σQ hQ τ μ hτlt hμα P hP hPsep
    u htruncationBounds hp
  have hcrep : ∀ j, Represents (c j) (P j μ)
      ((ν).homogeneousMk (P j μ) ⟨c j, ((ν).mem_filtrationLE_iff (P j μ) (c j)).mpr (hcb j)⟩) :=
    fun j ↦ represents_iff.mpr ⟨hcb j, rfl⟩
  have hQrep : ∀ j, Represents (aeval V (Q j)) (σQ j) (aeval xg (Q j)) :=
    fun j ↦ represents_aeval xg hV (hQ j)
  have hterm : ∀ j, Represents (c j * aeval V (Q j)) μ
      ((ν).homogeneousMk (P j μ) ⟨c j, ((ν).mem_filtrationLE_iff (P j μ) (c j)).mpr (hcb j)⟩ *
        aeval xg (Q j)) :=
    fun j ↦ (hcrep j).mul (hP j μ hτlt le_rfl).symm (hQrep j)
  have hsumrep := represents_sum (s := (Finset.univ : Finset κ')) (m := μ) fun j _ ↦ hterm j
  have hzero : Represents (u - ∑ j, c j * aeval V (Q j)) μ 0 :=
    represents_of_degree_lt (hres.trans_lt (WithBot.coe_lt_coe.mpr hτμ))
  have hsplit : u = (u - ∑ j, c j * aeval V (Q j)) + ∑ j, c j * aeval V (Q j) := by abel
  have hurep : Represents u μ (0 + ∑ j, (ν).homogeneousMk (P j μ)
      ⟨c j, ((ν).mem_filtrationLE_iff (P j μ) (c j)).mpr (hcb j)⟩ * aeval xg (Q j)) := by
    rw [hsplit]
    exact hzero.add hsumrep
  rw [heu.unique hurep, zero_add]
  exact Ideal.sum_mem _ fun j _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

open Classical in
/-- **The polynomial syzygy.** If the class of a weighted homogeneous polynomial lies in the ideal
generated by the classes of finitely many weighted homogeneous generators, then the polynomial is
itself that combination of the generators, with cofactors weighted homogeneous of the
complementary degrees. Homogeneous ideal decomposition splits the class into graded cofactors,
generation names each cofactor by a polynomial, and injectivity below the degree returns the
identity to the polynomial ring. -/
@[blueprint "lem:homogeneous-ideal-membership-polynomial-syzygy"
  (phase := "Algebraic independence in graded rings")
  (title := "Polynomial syzygies from homogeneous ideal membership")
  (statement := /--
    Let $x_i$ be homogeneous elements of a graded $K$-algebra.  Assume
    homogeneous polynomial evaluation at $(x_i)$ is generating and injective
    below $\alpha$.  Let $A$ and the finitely many $Q_j$ be
    weighted-homogeneous of degrees $m<\alpha$ and $\sigma_j$.  If
    \[
      A(x)\in\bigl(Q_j(x):j\bigr),
    \]
    then there are polynomials $C_j$ such that
    \[
      A=\sum_jC_jQ_j,
    \]
    and $C_j$ is weighted-homogeneous of degree $\beta$ whenever
    $\beta\oplus\sigma_j=m$.
  -/)
  (proof := /--
    By \ref{thm:cantor-bendixson-value-multiplicative}, the
    Cantor--Bendixson degree defines the associated graded ring in which the
    ideal is formed.  By \ref{lem:homogeneous-element-of-generated-ideal},
    homogeneous ideal
    membership writes $A(x)$ as a sum of the $Q_j(x)$ with homogeneous
    cofactors of complementary degrees.  Homogeneous
    generation below $\alpha$ represents each cofactor by a polynomial of the
    same degree.  The resulting polynomial combination and $A$ have the same
    evaluation and are homogeneous of degree $m$; injectivity in that degree
    makes them equal.
  -/)]
theorem exists_eq_sum_mul_of_class_mem_span
    {ι : Type w} {κ' : Type w} [Fintype κ'] {wt : ι → NatOrdinal.{u}}
    (xg : ι → (ν).AssociatedGraded)
    (hxg : ∀ i, xg i ∈ DirectSum.rangeLof K (ν).Component (wt i))
    {α : NatOrdinal.{u}}
    (hgen : ∀ β : NatOrdinal.{u}, β < α → ∀ y ∈ DirectSum.rangeLof K (ν).Component β,
      ∃ F : MvPolynomial ι K, IsWeightedHomogeneous wt F β ∧ aeval xg F = y)
    (hinj : ∀ (β : NatOrdinal.{u}) (F : MvPolynomial ι K), β < α →
      IsWeightedHomogeneous wt F β → aeval xg F = 0 → F = 0)
    (Q : κ' → MvPolynomial ι K) (σQ : κ' → NatOrdinal.{u})
    (hQ : ∀ j, IsWeightedHomogeneous wt (Q j) (σQ j))
    {A : MvPolynomial ι K} {m : NatOrdinal.{u}} (hm : m < α)
    (hA : IsWeightedHomogeneous wt A m)
    (hmem : aeval xg A ∈ Ideal.span (Set.range fun j ↦ aeval xg (Q j))) :
    ∃ c : κ' → MvPolynomial ι K,
      (∀ j β, β + σQ j = m → IsWeightedHomogeneous wt (c j) β) ∧
      A = ∑ j, c j * Q j := by
  classical
  have hQmem : ∀ j, aeval xg (Q j) ∈ DirectSum.rangeLof K (ν).Component (σQ j) := fun j ↦
    OrdinalGraded.aeval_mem_of_forall_mem hxg (hQ j)
  have hAmem : aeval xg A ∈ DirectSum.rangeLof K (ν).Component m :=
    OrdinalGraded.aeval_mem_of_forall_mem hxg hA
  obtain ⟨u, hu, hu0, husum⟩ := OrdinalGraded.exists_eq_sum_mul_of_mem_span
    (𝒜 := DirectSum.rangeLof K (ν).Component) hQmem hAmem hmem
  -- Name each graded cofactor by a homogeneous polynomial.
  have hname : ∀ j : κ', ∃ p : MvPolynomial ι K,
      (∀ β, β + σQ j = m → IsWeightedHomogeneous wt p β) ∧ aeval xg p = u j ∧
        ((¬ ∃ β, β + σQ j = m) → p = 0) := by
    intro j
    by_cases hβ : ∃ β, β + σQ j = m
    · obtain ⟨β, hβm⟩ := hβ
      have hβlt : β < α := by
        refine lt_of_le_of_lt ?_ hm
        rw [← hβm]
        have h0 : β + 0 ≤ β + σQ j := add_le_add le_rfl (zero_le (a := σQ j))
        rwa [add_zero] at h0
      obtain ⟨p, hphom, hpval⟩ := hgen β hβlt (u j) (hu j β hβm)
      refine ⟨p, fun β' hβ' ↦ ?_, hpval, fun hno ↦ absurd ⟨β, hβm⟩ hno⟩
      have hββ : β' = β := add_right_cancel (hβ'.trans hβm.symm)
      rw [hββ]
      exact hphom
    · exact ⟨0, fun β hβm ↦ absurd ⟨β, hβm⟩ hβ,
        by rw [map_zero, hu0 j hβ], fun _ ↦ rfl⟩
  choose c hchom hcval hczero using hname
  refine ⟨c, hchom, ?_⟩
  -- The two sides have the same class, and injectivity identifies them.
  have hsumhom : IsWeightedHomogeneous wt (∑ j, c j * Q j) m := by
    rw [← MvPolynomial.mem_weightedHomogeneousSubmodule]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    by_cases hβ : ∃ β, β + σQ j = m
    · obtain ⟨β, hβm⟩ := hβ
      have h := (hchom j β hβm).mul (hQ j)
      rw [hβm] at h
      rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
      exact h
    · rw [hczero j hβ, zero_mul]
      exact Submodule.zero_mem _
  have hclass : aeval xg A = aeval xg (∑ j, c j * Q j) := by
    rw [map_sum, husum]
    exact Finset.sum_congr rfl fun j _ ↦ by
      rw [map_mul, hcval j, mul_comm]
  have hdiff : IsWeightedHomogeneous wt (A - ∑ j, c j * Q j) m := by
    rw [← MvPolynomial.mem_weightedHomogeneousSubmodule] at hA hsumhom ⊢
    exact Submodule.sub_mem _ hA hsumhom
  have := hinj m (A - ∑ j, c j * Q j) hm hdiff (by rw [map_sub, hclass, sub_self])
  exact sub_eq_zero.mp this

/-- **From the local ideal condition to a polynomial identity.** If at every proper cutoff the
truncation of an evaluated homogeneous polynomial is represented by a polynomial whose part in
degrees at or above `τ` lies in the ideal of the generators, then the polynomial itself is a
combination of the generators, with each cofactor homogeneous of the complementary degree.

This composes the lift-back, which turns the local condition into membership of the graded class,
with the polynomial syzygy, which returns that membership to an identity in the polynomial ring. It
is the step from the analysis to an actual relation among the partial derivatives. -/
theorem exists_eq_sum_mul_of_forall_componentsGE_mem
    [DenselyOrdered G] [NoMinOrder G] [NoMaxOrder G]
    {κ : Type x} [LinearOrder κ] [WellFoundedLT κ] {ι : Type w} {κ' : Type w} [Fintype κ']
    (U : κ → AddSubgroup G)
    (hUmono : ∀ {i j : κ}, i ≤ j → (U j : Set G) ⊆ (U i : Set G))
    (hUopen : ∀ i, IsOpen (U i : Set G))
    (hUconv : ∀ i, (U i : Set G).OrdConnected)
    (hUbase : ∀ ε : G, 0 < ε → ∃ i, (U i : Set G) ⊆ Set.Ioo (-ε) ε)
    {wt : ι → NatOrdinal.{u}} {V : ι → Nonpositive G K}
    (xg : ι → (ν).AssociatedGraded)
    (hV : ∀ i, Represents (V i) (wt i) (xg i))
    (hVbounds : ∀ i, HasLowerTruncationDegree (V i) (wt i))
    (α : NatOrdinal.{u})
    (hgen : ∀ β : NatOrdinal.{u}, β < α → ∀ y ∈ DirectSum.rangeLof K (ν).Component β,
      ∃ F : MvPolynomial ι K, IsWeightedHomogeneous wt F β ∧ aeval xg F = y)
    (hinj : ∀ (β : NatOrdinal.{u}) (F : MvPolynomial ι K), β < α →
      IsWeightedHomogeneous wt F β → aeval xg F = 0 → F = 0)
    (Q : κ' → MvPolynomial ι K) (σQ : κ' → NatOrdinal.{u})
    (hQ : ∀ j, IsWeightedHomogeneous wt (Q j) (σQ j))
    (τ μ : NatOrdinal.{u}) (hτμ : (τ + 1 : NatOrdinal) < μ) (hμα : μ < α)
    (P : κ' → NatOrdinal.{u} → NatOrdinal.{u})
    (hP : ∀ j β, τ < β → β ≤ μ → P j β + σQ j = β)
    (hPsep : ∀ j θ, θ < σQ j → P j μ + θ < τ)
    {Θ : MvPolynomial ι K} (hΘ : IsWeightedHomogeneous wt Θ μ)
    (htruncationBounds : HasLowerTruncationDegree (aeval V Θ) μ)
    (hp : ∀ y : G, y < 0 → ∃ F : MvPolynomial ι K,
      (∀ d ∈ F.support, (Finsupp.weight wt) d < α) ∧
      ν (translatedTruncLE y (aeval V Θ) - aeval V F) = ⊥ ∧
      MvPolynomial.componentsGE wt τ F ∈ Ideal.span (Set.range Q)) :
    ∃ c : κ' → MvPolynomial ι K,
      (∀ j β, β + σQ j = μ → IsWeightedHomogeneous wt (c j) β) ∧
      Θ = ∑ j, c j * Q j := by
  have hmem := homogeneousClass_mem_span_of_properly_locallyIdeal U hUmono hUopen hUconv hUbase
    xg hV hVbounds α hgen hinj Q σQ hQ τ μ hτμ hμα P hP hPsep (aeval V Θ) htruncationBounds
    (aeval xg Θ) (represents_aeval xg hV hΘ) hp
  exact exists_eq_sum_mul_of_class_mem_span xg (fun i ↦ (hV i).mem_rangeLof) hgen hinj Q σQ hQ
    hμα hΘ hmem

/-- **From the local ideal condition to a polynomial identity, from window data.** The same
conclusion as above, with the cofactor degrees produced from window bounds at the generator degrees
rather than supplied.

Each generator degree must precede the polynomial's degree in the algebraic order, and its window
bound must hold at the exponent of its last Cantor term. Those are conditions on natural ordinals
alone, and they are what the classification of the generators establishes. -/
theorem exists_eq_sum_mul_of_forall_componentsGE_mem_of_windows
    [DenselyOrdered G] [NoMinOrder G] [NoMaxOrder G]
    {κ : Type x} [LinearOrder κ] [WellFoundedLT κ] {ι : Type w} {κ' : Type w} [Fintype κ']
    (U : κ → AddSubgroup G)
    (hUmono : ∀ {i j : κ}, i ≤ j → (U j : Set G) ⊆ (U i : Set G))
    (hUopen : ∀ i, IsOpen (U i : Set G))
    (hUconv : ∀ i, (U i : Set G).OrdConnected)
    (hUbase : ∀ ε : G, 0 < ε → ∃ i, (U i : Set G) ⊆ Set.Ioo (-ε) ε)
    {wt : ι → NatOrdinal.{u}} {V : ι → Nonpositive G K}
    (xg : ι → (ν).AssociatedGraded)
    (hV : ∀ i, Represents (V i) (wt i) (xg i))
    (hVbounds : ∀ i, HasLowerTruncationDegree (V i) (wt i))
    (α : NatOrdinal.{u})
    (hgen : ∀ β : NatOrdinal.{u}, β < α → ∀ y ∈ DirectSum.rangeLof K (ν).Component β,
      ∃ F : MvPolynomial ι K, IsWeightedHomogeneous wt F β ∧ aeval xg F = y)
    (hinj : ∀ (β : NatOrdinal.{u}) (F : MvPolynomial ι K), β < α →
      IsWeightedHomogeneous wt F β → aeval xg F = 0 → F = 0)
    (Q : κ' → MvPolynomial ι K) (σQ ρQ : κ' → NatOrdinal.{u})
    (hQ : ∀ j, IsWeightedHomogeneous wt (Q j) (σQ j))
    (τ μ : NatOrdinal.{u}) (hτμ : (τ + 1 : NatOrdinal) < μ) (hμα : μ < α)
    (hσ : ∀ j, σQ j ≠ 0) (hgrade : ∀ j, ρQ j + σQ j = μ)
    (hwin : ∀ j, ∀ ε : NatOrdinal.{u}, NatOrdinal.leastTerm (σQ j) = ω^ ε →
      NatOrdinal.partGE ε μ ≤ τ)
    {Θ : MvPolynomial ι K} (hΘ : IsWeightedHomogeneous wt Θ μ)
    (htruncationBounds : HasLowerTruncationDegree (aeval V Θ) μ)
    (hp : ∀ y : G, y < 0 → ∃ F : MvPolynomial ι K,
      (∀ d ∈ F.support, (Finsupp.weight wt) d < α) ∧
      ν (translatedTruncLE y (aeval V Θ) - aeval V F) = ⊥ ∧
      MvPolynomial.componentsGE wt τ F ∈ Ideal.span (Set.range Q)) :
    ∃ c : κ' → MvPolynomial ι K,
      (∀ j β, β + σQ j = μ → IsWeightedHomogeneous wt (c j) β) ∧
      Θ = ∑ j, c j * Q j := by
  obtain ⟨P, hP, hPsep⟩ :=
    NatOrdinal.exists_cofactorDegree_of_forall_partGE_le σQ ρQ τ μ hσ hgrade hwin
  exact exists_eq_sum_mul_of_forall_componentsGE_mem U hUmono hUopen hUconv hUbase xg hV hVbounds
    α hgen hinj Q σQ hQ τ μ hτμ hμα P hP hPsep hΘ htruncationBounds hp

/-- **From an eventual local ideal condition to a polynomial identity.** It is enough that the
local ideal representatives exist at every negative cutoff sufficiently close to zero. Cutting the
evaluated homogeneous polynomial to its strict tail above the neighbourhood bound preserves its
represented class, its degree upper bound, and the strict degree drop at negative cutoffs; below
the cut every translated truncation is zero, so the proper-cutoff cofactor construction applies to
that tail. -/
@[blueprint "lem:eventual-local-ideal-membership-gives-syzygy"
  (phase := "Algebraic independence in graded rings")
  (title := "Local-to-global principle for homogeneous ideal membership")
  (statement := /--
    Let $K$ be a field of characteristic zero and let $G$ be a complete
    densely ordered abelian group with a decreasing well-founded neighbourhood
    basis $(U_i)$ of open convex additive subgroups. Let $b_i$ represent
    homogeneous classes $x_i$ of degrees $w_i$ in the Cantor--Bendixson
    associated graded ring, with
    \[
      \nu(b_i)\le w_i,
      \qquad \nu(b_i^{\vert y})<w_i\quad(y<0).
    \]
    Assume homogeneous evaluation at $(x_i)$ is generating and injective below
    $\alpha$.

    Let $\Theta$ and finitely many $Q_j$ be weighted homogeneous polynomials
    of degrees $\mu$ and $\sigma_j\ne0$, where $\mu<\alpha$. Suppose
    $\rho_j\oplus\sigma_j=\mu$, $\tau\oplus1<\mu$, and the upper Cantor terms
    of $\mu$ at and above the exponent of the last Cantor term of $\sigma_j$
    have sum at most $\tau$. Assume
    \[
      \nu(\Theta(b))\le\mu,
      \qquad \nu(\Theta(b)^{\vert\gamma})<\mu\quad(\gamma<0).
    \]
    If, for every negative cutoff sufficiently close to zero, there is a
    polynomial all of whose monomials have weight below $\alpha$, congruent
    to $\Theta(b)^{\vert\gamma}$ modulo series bounded away from zero, and
    whose terms of degree at least $\tau$ lie in the ideal generated by the
    $Q_j$, then
    \[
      \Theta=\sum_j C_jQ_j,
    \]
    where $C_j$ is weighted homogeneous of every degree $\beta$ satisfying
    $\beta\oplus\sigma_j=\mu$; in particular it has degree $\rho_j$.
  -/)
  (proof := /--
    Choose a cutoff after which the local ideal condition holds and replace
    $\Theta(b)$ by its strict tail there. This preserves the represented
    degree-$\mu$ class, the bound $\nu(\Theta(b))\le\mu$, and the strict
    translated-truncation bounds, while translated truncations below the
    cutoff vanish. Thus the local condition holds at every negative cutoff.
    \ref{lem:separation} turns each window bound into the separation inequality
    below the last Cantor term, and
    \ref{lem:intermediate-ordinal-hessenberg-decomposition} identifies the possible
    complementary degrees $\rho_j$.
    \ref{lem:local-ideal-membership-associated-graded} combines the local
    representatives and places the resulting homogeneous class in the ideal
    generated by the $Q_j$.  Then
    \ref{lem:homogeneous-ideal-membership-polynomial-syzygy} lifts that graded
    ideal membership to the stated polynomial identity.
  -/)]
theorem exists_eq_sum_mul_of_eventually_componentsGE_mem_of_windows
    [DenselyOrdered G] [NoMinOrder G] [NoMaxOrder G]
    {κ : Type x} [LinearOrder κ] [WellFoundedLT κ] {ι : Type w} {κ' : Type w} [Fintype κ']
    (U : κ → AddSubgroup G)
    (hUmono : ∀ {i j : κ}, i ≤ j → (U j : Set G) ⊆ (U i : Set G))
    (hUopen : ∀ i, IsOpen (U i : Set G))
    (hUconv : ∀ i, (U i : Set G).OrdConnected)
    (hUbase : ∀ ε : G, 0 < ε → ∃ i, (U i : Set G) ⊆ Set.Ioo (-ε) ε)
    {wt : ι → NatOrdinal.{u}} {V : ι → Nonpositive G K}
    (xg : ι → (ν).AssociatedGraded)
    (hV : ∀ i, Represents (V i) (wt i) (xg i))
    (hVbounds : ∀ i, HasLowerTruncationDegree (V i) (wt i))
    (α : NatOrdinal.{u})
    (hgen : ∀ β : NatOrdinal.{u}, β < α → ∀ z ∈ DirectSum.rangeLof K (ν).Component β,
      ∃ F : MvPolynomial ι K, IsWeightedHomogeneous wt F β ∧ aeval xg F = z)
    (hinj : ∀ (β : NatOrdinal.{u}) (F : MvPolynomial ι K), β < α →
      IsWeightedHomogeneous wt F β → aeval xg F = 0 → F = 0)
    (Q : κ' → MvPolynomial ι K) (σQ ρQ : κ' → NatOrdinal.{u})
    (hQ : ∀ j, IsWeightedHomogeneous wt (Q j) (σQ j))
    (τ μ : NatOrdinal.{u}) (hτμ : (τ + 1 : NatOrdinal) < μ) (hμα : μ < α)
    (hσ : ∀ j, σQ j ≠ 0) (hgrade : ∀ j, ρQ j + σQ j = μ)
    (hwin : ∀ j, ∀ ε : NatOrdinal.{u}, NatOrdinal.leastTerm (σQ j) = ω^ ε →
      NatOrdinal.partGE ε μ ≤ τ)
    {Θ : MvPolynomial ι K} (hΘ : IsWeightedHomogeneous wt Θ μ)
    (htruncationBounds : HasLowerTruncationDegree (aeval V Θ) μ)
    (hp : ∀ᶠ y in 𝓝[<] (0 : G), ∃ F : MvPolynomial ι K,
      (∀ d ∈ F.support, (Finsupp.weight wt) d < α) ∧
      ν (translatedTruncLE y (aeval V Θ) - aeval V F) = ⊥ ∧
      MvPolynomial.componentsGE wt τ F ∈ Ideal.span (Set.range Q)) :
    ∃ c : κ' → MvPolynomial ι K,
      (∀ j β, β + σQ j = μ → IsWeightedHomogeneous wt (c j) β) ∧
      Θ = ∑ j, c j * Q j := by
  obtain ⟨l, hl, hp'⟩ := eventually_nhdsLT_iff_exists.mp hp
  set b := strictTail l (aeval V Θ) with hbdef
  have hbrep : Represents b μ (aeval xg Θ) := by
    rw [hbdef]
    exact represents_strictTail hl (represents_aeval xg hV hΘ)
  have hbBounds : HasLowerTruncationDegree b μ := by
    rw [hbdef]
    exact hasLowerTruncationDegree_strictTail hl htruncationBounds
  have hlocal : ∀ y : G, y < 0 → ∃ F : MvPolynomial ι K,
      (∀ d ∈ F.support, (Finsupp.weight wt) d < α) ∧
      ν (translatedTruncLE y b - aeval V F) = ⊥ ∧
      MvPolynomial.componentsGE wt τ F ∈ Ideal.span (Set.range Q) := by
    intro y hy
    by_cases hly : l < y
    · obtain ⟨F, hF, hcong, hFmem⟩ := hp' y hly hy
      refine ⟨F, hF, ?_, hFmem⟩
      have hdiff : ν (translatedTruncLE y (aeval V Θ) - translatedTruncLE y b) = ⊥ := by
        rw [hbdef, ← map_sub]
        exact degree_translatedTruncLE_sub_strictTail_eq_bot hly _
      have hsplit : translatedTruncLE y b - aeval V F =
          -(translatedTruncLE y (aeval V Θ) - translatedTruncLE y b) +
            (translatedTruncLE y (aeval V Θ) - aeval V F) := by ring
      rw [hsplit]
      apply le_bot_iff.mp
      exact ((ν).map_add_le_max _ _).trans (by rw [(ν).map_neg, hdiff, hcong, max_self])
    · refine ⟨0, fun d hd ↦ absurd hd (by simp), ?_, ?_⟩
      · rw [translatedTruncLE_strictTail_eq_zero (not_lt.mp hly), map_zero, sub_zero,
          (ν).map_zero]
      · rw [MvPolynomial.componentsGE_zero]
        exact Ideal.zero_mem _
  obtain ⟨P, hP, hPsep⟩ :=
    NatOrdinal.exists_cofactorDegree_of_forall_partGE_le σQ ρQ τ μ hσ hgrade hwin
  have hmem := homogeneousClass_mem_span_of_properly_locallyIdeal U hUmono hUopen hUconv
    hUbase xg hV hVbounds α hgen hinj Q σQ hQ τ μ hτμ hμα P hP hPsep b hbBounds
    (aeval xg Θ) hbrep hlocal
  exact exists_eq_sum_mul_of_class_mem_span xg (fun i ↦ (hV i).mem_rangeLof) hgen hinj
    Q σQ hQ hμα hΘ hmem

end HahnSeries.Nonpositive
