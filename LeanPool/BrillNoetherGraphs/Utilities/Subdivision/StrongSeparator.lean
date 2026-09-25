/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.RankOne
public import Mathlib.Tactic

/-!
# A kernel interface for the strong-separator rank-one lemma

Van Dobben de Bruyn--Gijswijt, Lemma 2.6, says that a divisor which reaches
every vertex of a strong separator has rank at least one.  The usual graph
theoretic definition asks that every component of the complement be a tree
and that a separator vertex have at most one edge into each component.

This file isolates the proof from a missing connected-component/path API for
`CFGraph`.  `StrongSeparatorCertificate` is a transparent, slightly stronger
finite certificate.  For every proper enlargement `R` of the separator it
provides one complementary cell `C`, an anchor on its boundary, the
one-edge-per-boundary-vertex condition, and the sole cut consequence of the
paths through the tree `C` used in the paper proof.  No rank or winnability
claim occurs in the certificate.

For an ordinary strong separator, choose a component of the complement of
`R`.  It is a subtree of an original complementary tree.  Its unique paths
give `pathCut`, while acyclicity gives `oneEdge`.  Formalizing that standard
component-to-certificate construction, in particular for subdivided cores,
is deliberately left as future graph-plumbing work; the soundness theorem
below is complete and uses only the public `qReduced` API.
-/

@[expose] public section

namespace Utilities.Certificate.StrongSeparator

open Finset

variable {G : CFGraph}

/-- The divisor class of `D` reaches `v` after one chip is removed. -/
def Reaches (G : CFGraph) (D : CFDiv G) (v : G.V) : Prop :=
  winnable G (D - oneChip v)

/-- Total edge multiplicity from `v` into `C`, as an integer. -/
def intoMultiplicity (G : CFGraph) (C : Finset G.V) (v : G.V) : ℤ :=
  ∑ x ∈ C, (numEdges G v x : ℤ)

/-- A vertex outside `C` is on its boundary when it has a positive-multiplicity
edge into `C`. -/
def IsBoundary (G : CFGraph) (C : Finset G.V) (v : G.V) : Prop :=
  ∃ x ∈ C, 0 < numEdges G v x

/-- Borrow once on every vertex of `C`. -/
def borrowScript (C : Finset G.V) : firingScript G :=
  fun v => if v ∈ C then -1 else 0

theorem intoMultiplicity_nonneg (C : Finset G.V) (v : G.V) :
    0 ≤ intoMultiplicity G C v := by
  exact Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _

theorem edge_le_intoMultiplicity {C : Finset G.V} {v x : G.V}
    (hx : x ∈ C) :
    (numEdges G v x : ℤ) ≤ intoMultiplicity G C v := by
  exact Finset.single_le_sum
    (fun y _ => Int.natCast_nonneg (numEdges G v y)) hx

theorem edge_le_outdeg_S {A : Finset G.V} {v x : G.V}
    (hx : x ∉ A) :
    (numEdges G v x : ℤ) ≤ outdegreeSet G A v := by
  unfold outdegreeSet
  apply Finset.single_le_sum
    (fun y _ => Int.natCast_nonneg (numEdges G v y))
  simp [hx]

theorem intoMultiplicity_eq_zero_of_not_boundary
    {C : Finset G.V} {v : G.V} (h : ¬IsBoundary G C v) :
    intoMultiplicity G C v = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  have hzero : numEdges G v x = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hpos
    exact h ⟨x, hx, hpos⟩
  simp [hzero]

theorem prin_indicator_script_of_mem {A : Finset G.V} {v : G.V}
    (hv : v ∈ A) :
    prin G (indicatorScript G A) v = -outdegreeSet G A v := by
  change
    (∑ u : G.V, (indicatorScript G A u - indicatorScript G A v) *
      (numEdges G v u : ℤ)) = _
  rw [show indicatorScript G A v = 1 by simp [indicatorScript, hv]]
  rw [outdegreeSet, ← Finset.sum_neg_distrib]
  rw [← Finset.sum_subset (Finset.subset_univ Aᶜ)]
  · apply Finset.sum_congr rfl
    intro u hu
    have huA : u ∉ A := by simpa using hu
    simp [indicatorScript, huA]
  · intro u _ hu
    have huA : u ∈ A := by simpa using hu
    simp [indicatorScript, huA]

theorem prin_indicator_script_of_not_mem {A : Finset G.V} {v : G.V}
    (hv : v ∉ A) :
    prin G (indicatorScript G A) v = intoMultiplicity G A v := by
  change
    (∑ u : G.V, (indicatorScript G A u - indicatorScript G A v) *
      (numEdges G v u : ℤ)) = _
  rw [show indicatorScript G A v = 0 by simp [indicatorScript, hv]]
  simp only [sub_zero, intoMultiplicity]
  calc
    (∑ u : G.V, indicatorScript G A u * (numEdges G v u : ℤ)) =
        ∑ u ∈ A, indicatorScript G A u * (numEdges G v u : ℤ) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ A)
      intro u _ hu
      simp [indicatorScript, hu]
    _ = ∑ u ∈ A, (numEdges G v u : ℤ) := by
      apply Finset.sum_congr rfl
      intro u hu
      simp [indicatorScript, hu]

theorem borrowScript_eq_neg_indicator_script (C : Finset G.V) :
    borrowScript C = -(indicatorScript G C : firingScript G) := by
  funext v
  by_cases hv : v ∈ C <;> simp [borrowScript, indicatorScript, hv]

theorem prin_borrowScript_of_mem {C : Finset G.V} {v : G.V}
    (hv : v ∈ C) :
    prin G (borrowScript C) v = outdegreeSet G C v := by
  rw [borrowScript_eq_neg_indicator_script, map_neg, Pi.neg_apply,
    prin_indicator_script_of_mem hv]
  simp

theorem prin_borrowScript_of_not_mem {C : Finset G.V} {v : G.V}
    (hv : v ∉ C) :
    prin G (borrowScript C) v = -intoMultiplicity G C v := by
  rw [borrowScript_eq_neg_indicator_script, map_neg, Pi.neg_apply,
    prin_indicator_script_of_not_mem hv]

/-- Removing a chip at the reduction vertex preserves reducedness. -/
theorem qReduced_sub_one_chip {q : G.V} {D : CFDiv G}
    (hReduced : qReduced G q D) :
    qReduced G q (D - oneChip q) := by
  refine ⟨?_, ?_⟩
  · intro v hv
    simp [oneChip, hv, hReduced.1 v hv]
  · intro A hA hNonempty hLegal
    apply hReduced.2 A hA hNonempty
    intro v hvA
    have hvq : v ≠ q := fun hvq => hA (hvq ▸ hvA)
    simpa [oneChip, hvq] using hLegal v hvA

/-- Subtracting the same chip from linearly equivalent divisors preserves
linear equivalence. -/
theorem linearEquiv_sub_one_chip {D E : CFDiv G}
    (hEquiv : linearEquiv G D E) (v : G.V) :
    linearEquiv G (D - oneChip v) (E - oneChip v) := by
  unfold linearEquiv at hEquiv ⊢
  have hDifference :
      (E - oneChip v) - (D - oneChip v) = E - D := by
    abel
  rwa [hDifference]

/-- An effective representative carrying a chip at `v` proves that the
original divisor reaches `v`. -/
theorem reaches_of_effective_representative {D E : CFDiv G} {v : G.V}
    (hEquiv : linearEquiv G D E) (hEffective : effective E)
    (hChip : 1 ≤ E v) :
    Reaches G D v := by
  apply winnable_equiv_winnable G (E - oneChip v) (D - oneChip v)
  · apply winnable_of_effective
    intro x
    by_cases hx : x = v
    · subst x
      simp only [Pi.sub_apply, oneChip, ↓reduceIte, Int.sub_nonneg]
      omega
    · simpa [oneChip, hx] using hEffective x
  · exact (linearEquiv_sub_one_chip hEquiv v).symm

/-- The finite complementary cell used by the strong-separator argument. -/
structure ExpansionCell (G : CFGraph) (R : Finset G.V) where
  /-- The nonempty finite complementary cell, disjoint from the reached set `R`. -/
  carrier : Finset G.V
  nonempty : carrier.Nonempty
  disjoint : Disjoint carrier R
  /-- A reached boundary vertex in `R` used as the anchor for expanding into the complementary
  cell. -/
  anchor : G.V
  anchor_mem : anchor ∈ R
  anchor_boundary : IsBoundary G carrier anchor
  /-- Every edge leaving the cell lands in the reached enlargement. -/
  closed : ∀ {x y : G.V}, x ∈ carrier → y ∉ carrier →
    0 < numEdges G x y → y ∈ R
  /-- A reached vertex has at most one edge, counted with multiplicity, into
  this complementary cell. -/
  oneEdge : ∀ {y : G.V}, y ∈ R → intoMultiplicity G carrier y ≤ 1
  /-- The cut consequence of the path from the anchor to any other boundary
  vertex through the complementary tree. -/
  pathCut : ∀ {t : G.V}, t ∈ R → IsBoundary G carrier t →
    ∀ A : Finset G.V, anchor ∈ A → t ∉ A →
      (∃ x ∈ carrier, x ∉ A ∧
        ∃ y ∈ A, 0 < numEdges G x y) ∨
      (∃ x ∈ carrier, x ∈ A ∧
        ∃ y, y ∉ A ∧ 0 < numEdges G x y)

/-- A transparent strong-separator certificate: every proper enlargement of
`S` has a complementary cell with the exact tree/path cut data above. -/
def StrongSeparatorCertificate (G : CFGraph) (S : Finset G.V) : Prop :=
  ∀ R : Finset G.V, S ⊆ R → R.Nonempty → R ≠ Finset.univ →
    Nonempty (ExpansionCell G R)

/-- Adding an explicit principal divisor does not change a divisor class. -/
theorem linearEquiv_add_prin (D : CFDiv G) (script : firingScript G) :
    linearEquiv G D (D + prin G script) := by
  unfold linearEquiv
  rw [add_sub_cancel_left]
  exact (principal_iff_eq_prin G (prin G script)).2 ⟨script, rfl⟩

/-- Kernel-checked strong-separator lemma (discrete form of
van Dobben de Bruyn--Gijswijt, Lemma 2.6).

The proof enlarges `S` to the finite set of all vertices reached by `D`.  A
certificate cell for a hypothetical proper enlargement then supplies a new
reached vertex, a contradiction. -/
theorem rank_ge_one_of_strongSeparatorCertificate
    (hConnected : graphConnected G) {S : Finset G.V}
    (hSNonempty : S.Nonempty)
    (hSeparator : StrongSeparatorCertificate G S)
    {D : CFDiv G}
    (hReaches : ∀ s ∈ S, Reaches G D s) :
    rank G D ≥ 1 := by
  classical
  let R : Finset G.V :=
    Finset.univ.filter fun v => Reaches G D v
  have hSsub : S ⊆ R := by
    intro s hs
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hReaches s hs
  have hRNonempty : R.Nonempty := hSNonempty.mono hSsub
  have hRuniv : R = Finset.univ := by
    by_contra hProper
    let cell : ExpansionCell G R :=
      Classical.choice (hSeparator R hSsub hRNonempty hProper)
    have hAnchorReach : Reaches G D cell.anchor := by
      have := cell.anchor_mem
      simpa only [R, Finset.mem_filter, Finset.mem_univ, true_and] using this
    obtain ⟨Dred, hEquiv, hReduced⟩ :=
      exists_q_reduced_representative hConnected cell.anchor D
    have hWinReducedSub :
        winnable G (Dred - oneChip cell.anchor) :=
      winnable_equiv_winnable G
        (D - oneChip cell.anchor) (Dred - oneChip cell.anchor)
        hAnchorReach (linearEquiv_sub_one_chip hEquiv cell.anchor)
    have hReducedSub :
        qReduced G cell.anchor (Dred - oneChip cell.anchor) :=
      qReduced_sub_one_chip hReduced
    have hEffectiveSub : effective (Dred - oneChip cell.anchor) :=
      effective_of_winnable_and_q_reduced G cell.anchor _
        hWinReducedSub hReducedSub
    have hEffectiveRed : effective Dred := by
      intro v
      by_cases hv : v = cell.anchor
      · subst v
        have h := hEffectiveSub cell.anchor
        simp only [Pi.sub_apply, oneChip, ↓reduceIte, Int.sub_nonneg] at h
        omega
      · simpa [oneChip, hv] using hEffectiveSub v
    have hAnchorChip : 1 ≤ Dred cell.anchor := by
      have h := hEffectiveSub cell.anchor
      simp only [Pi.sub_apply, oneChip, ↓reduceIte, Int.sub_nonneg] at h
      omega
    have hPositiveMemR {v : G.V} (hv : 1 ≤ Dred v) : v ∈ R := by
      have hReach : Reaches G D v :=
        reaches_of_effective_representative hEquiv hEffectiveRed hv
      simpa only [R, Finset.mem_filter, Finset.mem_univ, true_and]
    have hZeroCarrier (v : G.V) (hv : v ∈ cell.carrier) : Dred v = 0 := by
      have hvNotR : v ∉ R := by
        intro hvR
        exact (Finset.disjoint_left.mp cell.disjoint) hv hvR
      have hvNonneg := hEffectiveRed v
      by_contra hvZero
      have hvPositive : 1 ≤ Dred v := by omega
      exact hvNotR (hPositiveMemR hvPositive)
    have hAnchorNotCarrier : cell.anchor ∉ cell.carrier := by
      intro hs
      exact (Finset.disjoint_left.mp cell.disjoint) hs cell.anchor_mem
    by_cases hAllBoundaryChips :
        ∀ y : G.V, y ∈ R → IsBoundary G cell.carrier y → 1 ≤ Dred y
    · let script : firingScript G := borrowScript cell.carrier
      let E : CFDiv G := Dred + prin G script
      have hEffectiveE : effective E := by
        intro v
        by_cases hvCarrier : v ∈ cell.carrier
        · change 0 ≤ Dred v + prin G (borrowScript cell.carrier) v
          rw [prin_borrowScript_of_mem hvCarrier]
          exact add_nonneg (hEffectiveRed v)
            (outdeg_S_nonneg G cell.carrier v)
        · change 0 ≤ Dred v + prin G (borrowScript cell.carrier) v
          rw [prin_borrowScript_of_not_mem hvCarrier]
          by_cases hvR : v ∈ R
          · by_cases hvBoundary : IsBoundary G cell.carrier v
            · have hChip := hAllBoundaryChips v hvR hvBoundary
              have hOneEdge := cell.oneEdge hvR
              omega
            · rw [intoMultiplicity_eq_zero_of_not_boundary hvBoundary]
              simpa using hEffectiveRed v
          · have hvBoundary : ¬IsBoundary G cell.carrier v := by
              intro hBoundary
              obtain ⟨x, hxCarrier, hxv⟩ := hBoundary
              have hxv' : 0 < numEdges G x v := by
                rwa [num_edges_symmetric]
              exact hvR (cell.closed hxCarrier hvCarrier hxv')
            rw [intoMultiplicity_eq_zero_of_not_boundary hvBoundary]
            simpa using hEffectiveRed v
      obtain ⟨x, hxCarrier, hAnchorX⟩ := cell.anchor_boundary
      have hXAnchor : 0 < numEdges G x cell.anchor := by
        rwa [num_edges_symmetric]
      have hEdgeInt : 1 ≤ (numEdges G x cell.anchor : ℤ) := by
        exact_mod_cast hXAnchor
      have hOutPositive : 1 ≤ outdegreeSet G cell.carrier x :=
        le_trans hEdgeInt (edge_le_outdeg_S hAnchorNotCarrier)
      have hEChip : 1 ≤ E x := by
        change 1 ≤ Dred x + prin G (borrowScript cell.carrier) x
        rw [prin_borrowScript_of_mem hxCarrier, hZeroCarrier x hxCarrier]
        simpa using hOutPositive
      have hDE : linearEquiv G D E :=
        hEquiv.trans (linearEquiv_add_prin Dred script)
      have hxReach : Reaches G D x :=
        reaches_of_effective_representative hDE hEffectiveE hEChip
      have hxR : x ∈ R := by
        simpa only [R, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ((Finset.disjoint_left.mp cell.disjoint) hxCarrier hxR).elim
    · push Not at hAllBoundaryChips
      obtain ⟨t, htR, htBoundary, htNoChip⟩ := hAllBoundaryChips
      have htZero : Dred t = 0 := by
        have := hEffectiveRed t
        omega
      have htReach : Reaches G D t := by
        simpa only [R, Finset.mem_filter, Finset.mem_univ, true_and] using htR
      have hNotTReduced : ¬qReduced G t Dred := by
        intro hTReduced
        have hWinTSub : winnable G (Dred - oneChip t) :=
          winnable_equiv_winnable G (D - oneChip t)
            (Dred - oneChip t) htReach
            (linearEquiv_sub_one_chip hEquiv t)
        have hEffTSub : effective (Dred - oneChip t) :=
          effective_of_winnable_and_q_reduced G t _ hWinTSub
            (qReduced_sub_one_chip hTReduced)
        have h := hEffTSub t
        simp [oneChip, htZero] at h
      have hTqEffective : qEffective t Dred := by
        intro v _
        exact hEffectiveRed v
      have hBurnFailure :
          ¬(∀ A : Finset G.V, t ∉ A → A.Nonempty → ¬legalSet G Dred A) := by
        intro hBurn
        exact hNotTReduced ⟨hTqEffective, hBurn⟩
      push Not at hBurnFailure
      obtain ⟨A, htNotA, hANonempty, hLegal⟩ := hBurnFailure
      have hAnchorA : cell.anchor ∈ A := by
        by_contra hAnchorNotA
        exact hReduced.2 A hAnchorNotA hANonempty hLegal
      have hEffectiveFire :
          effective (Dred + prin G (indicatorScript G A)) := by
        rw [← set_firing_eq_add_prin_indicator_script]
        exact effective_set_firing_of_legal_set G hEffectiveRed hLegal
      rcases cell.pathCut htR htBoundary A hAnchorA htNotA with
        hIncoming | hOutgoing
      · obtain ⟨x, hxCarrier, hxNotA, y, hyA, hxy⟩ := hIncoming
        have hEdgeInt : 1 ≤ (numEdges G x y : ℤ) := by
          exact_mod_cast hxy
        have hIntoPositive : 1 ≤ intoMultiplicity G A x :=
          le_trans hEdgeInt (edge_le_intoMultiplicity hyA)
        have hFiredChip :
            1 ≤ (Dred + prin G (indicatorScript G A)) x := by
          rw [Pi.add_apply, prin_indicator_script_of_not_mem hxNotA,
            hZeroCarrier x hxCarrier]
          simpa using hIntoPositive
        have hDFired :
            linearEquiv G D (Dred + prin G (indicatorScript G A)) :=
          hEquiv.trans (linearEquiv_add_prin Dred (indicatorScript G A))
        have hxReach : Reaches G D x :=
          reaches_of_effective_representative hDFired hEffectiveFire
            hFiredChip
        have hxR : x ∈ R := by
          simpa only [R, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ((Finset.disjoint_left.mp cell.disjoint) hxCarrier hxR).elim
      · obtain ⟨x, hxCarrier, hxA, y, hyNotA, hxy⟩ := hOutgoing
        have hEdgeInt : 1 ≤ (numEdges G x y : ℤ) := by
          exact_mod_cast hxy
        have hOutPositive : 1 ≤ outdegreeSet G A x :=
          le_trans hEdgeInt (edge_le_outdeg_S hyNotA)
        have hNoDebtX := hLegal x hxA
        rw [hZeroCarrier x hxCarrier] at hNoDebtX
        omega
  apply (rank_geq_iff G D 1).mp
  intro E hE
  obtain ⟨q, rfl⟩ :=
    effective_degree_one_eq_one_chip hE.1 hE.2
  have hqR : q ∈ R := by
    rw [hRuniv]
    simp
  -- `Finset.mem_filter` on a `q ∈ R` produced by `rw [hRuniv]; simp` no longer
  -- normalizes cleanly through a `simp only` that also tries to unfold the
  -- local `let R` (Mathlib v4.33): extract the predicate directly instead.
  exact (Finset.mem_filter.mp hqR).2

end Utilities.Certificate.StrongSeparator
