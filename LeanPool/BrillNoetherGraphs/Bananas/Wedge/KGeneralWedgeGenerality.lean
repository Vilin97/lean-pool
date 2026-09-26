/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.AffineReduction
public import LeanPool.BrillNoetherGraphs.Bananas.Classification.SciWeierstrass
public import LeanPool.BrillNoetherGraphs.Bananas.Sections.SectionSixDefinitions
public import LeanPool.BrillNoetherGraphs.Bananas.Wedge.WedgeSubmodularity

/-!
# Gluing a general marked graph to a graph with general transmission

This file proves Theorem 6.6 (`thm:glueBNGtoKGT`) of the paper.  The exact
transmission permutation of a wedge divisor is the Demazure product of the
factor permutations (`WedgeSubmodularity`); Proposition 6.13 bounds its
sign-changing inversions, and Proposition 6.10 identifies those inversions
with the size of the Weierstrass partition at the surviving mark.
-/

@[expose] public section

namespace Bananas

open Utilities

section Generic

/-- Convert the sign-changing-inversion bound furnished by Proposition 6.13
into the corresponding Weierstrass-size bound.  Keeping this divisor algebra
at an abstract graph prevents concrete wedge vertex types from unfolding
during elaboration. -/
theorem weierstrassSize_le_genus_of_sci_le
    {G : CFGraph} (u v : G.V) (hG : _root_.graphConnected G)
    (D : CFDiv G) (tau : ℤ → ℤ)
    (hTau : IsTransmissionPermutation (mark G u v) D tau)
    (hSci : (sci tau : ℤ) ≤ genus G) :
    (weierstrassSize hG v D : ℤ) ≤ genus G := by
  rw [← sci_eq_weierstrassSize u v hG D tau hTau]
  exact hSci

end Generic

/-- Paper Theorem 6.6 (`thm:glueBNGtoKGT`).

The first twice-marking is used only to supply a submodular transmission
permutation for each divisor on `G`, as in the paper.  The marked
Brill--Noether hypothesis itself concerns only the gluing vertex `x`.
-/
theorem onceMarkedBrillNoetherGeneral_vertexWedge_of_kGeneralTransmission
    (G H : CFGraph) (u x : G.V) (y v : H.V)
    (hGconn : _root_.graphConnected G)
    (hHconn : _root_.graphConnected H)
    (hGsub : AllSubmodular (mark G u x))
    (hGgeneral : OnceMarkedBrillNoetherGeneral G x)
    {k : ℕ} (hK : KGeneralTransmission (mark H y v) k)
    (hbudget : genus G + genus H < (k : ℤ)) :
    OnceMarkedBrillNoetherGeneral
      (vertexWedge G H x y) (wedgeRightVertex G H x y v) := by
  classical
  let W := vertexWedge G H x y
  let wv : W.V := wedgeRightVertex G H x y v
  have hWconn : _root_.graphConnected W :=
    graph_connected_vertexWedge G H x y hGconn hHconn
  intro lambda hCensus
  let Q : CFDiv W := Classical.choose hCensus
  have hRows : ∀ i : ℕ,
      rank W (Q + ((i : ℤ) + genus W - deg Q -
        (onceMarkedPart lambda i : ℤ)) • oneChip wv) ≥ (i : ℤ) :=
    Classical.choose_spec hCensus
  let D : CFDiv G := wedgeRestrictLeftDivisor G H x y Q
  let E : CFDiv H := wedgeRestrictRightDivisor G H x y Q
  have hQ : wedgeAddDivisor G H x y D E = Q :=
    wedgeAddDivisor_restrict G H x y Q
  obtain ⟨tau, hTau⟩ := exists_transmissionPermutation_of_submodular
    (mark G u x) D hGconn (hGsub D)
  obtain ⟨sigma, hSigma, hSigmaAffine, hSigmaCount⟩ :=
    hK.exists_affine_transmission E
  obtain ⟨alpha, beta, hAlpha, hBeta, hWedge⟩ :=
    exists_isTransmissionPermutation_wedgeAddDivisor_star
      G H x y hGconn hHconn D E u v tau sigma hTau hSigma
  have hAlphaSci : (sci alpha.func : ℤ) ≤ genus G := by
    have hSize : (weierstrassSize hGconn x D : ℤ) ≤ genus G :=
      hGgeneral (weierstrassPartition hGconn x D)
        (onceMarkedCensusContains_weierstrassPartition hGconn x D)
    have hSci := sci_eq_weierstrassSize u x hGconn D tau hTau
    rw [hAlpha, hSci]
    exact hSize
  have hGenusH : 0 ≤ genus H := genus_nonneg_of_graph_connected H hHconn
  have hBetaCount : (kInversionCount k beta.func : ℤ) ≤ genus H := by
    rw [hBeta]
    have hCast : ((Int.toNat (genus H) : ℕ) : ℤ) = genus H := by
      exact Int.toNat_of_nonneg hGenusH
    have hSigmaCountZ : (kInversionCount k sigma : ℤ) ≤
        (Int.toNat (genus H) : ℤ) := by
      exact_mod_cast hSigmaCount
    rwa [hCast] at hSigmaCountZ
  have hStarSci : (sci (alpha ⋆ beta).func : ℤ) ≤ genus G + genus H := by
    apply le_trans (sci_star_le k alpha beta (by simpa [hBeta] using hSigmaAffine) ?_)
    · exact add_le_add hAlphaSci hBetaCount
    · omega
  have hWedge' : IsTransmissionPermutation
      (mark W (Sum.inl u) wv) Q (alpha ⋆ beta).func := by
    rw [hQ] at hWedge
    exact hWedge
  have hWedgeSize : (weierstrassSize hWconn wv Q : ℤ) ≤ genus W := by
    apply weierstrassSize_le_genus_of_sci_le (G := W)
      (Sum.inl u) wv hWconn Q (alpha ⋆ beta).func hWedge'
    simpa only [W, genus_vertexWedge] using hStarSci
  have hContained : lambda ≤ weierstrassPartition hWconn wv Q :=
    census_partition_le_weierstrassPartition hWconn wv Q lambda hRows
  have hCard : lambda.card ≤ weierstrassSize hWconn wv Q :=
    Finset.card_le_card
      (YoungDiagram.cells_subset_iff.mp hContained)
  have hCardZ : (lambda.card : ℤ) ≤
      (weierstrassSize hWconn wv Q : ℤ) := by
    exact_mod_cast hCard
  simpa only [W] using le_trans hCardZ hWedgeSize

/-- The once-marked corollary immediately following Theorem 6.6: if the
period is larger than the genus, forgetting the first mark of a graph with
`k`-general transmission leaves a Brill--Noether general marked graph.

We prove this directly by taking the identity as the left Demazure factor;
this is equivalent to the paper's specialization of Theorem 6.6 to a
one-vertex first graph, without choosing a separate model of that graph. -/
theorem onceMarkedBrillNoetherGeneral_of_kGeneralTransmission
    {G : CFGraph} (u v : G.V)
    (hGconn : _root_.graphConnected G)
    {k : ℕ} (hK : KGeneralTransmission (mark G u v) k)
    (hbudget : genus G < (k : ℤ)) :
    OnceMarkedBrillNoetherGeneral G v := by
  classical
  intro lambda hCensus
  let D : CFDiv G := Classical.choose hCensus
  have hRows : ∀ i : ℕ,
      rank G (D + ((i : ℤ) + genus G - deg D -
        (onceMarkedPart lambda i : ℤ)) • oneChip v) ≥ (i : ℤ) :=
    Classical.choose_spec hCensus
  obtain ⟨tau, hTau, hAffine, hCount⟩ :=
    hK.exists_affine_transmission D
  obtain ⟨beta, hBeta, _hRank⟩ :=
    exists_aspPerm_rank_eq_of_isTransmissionPermutation
      u v hGconn D tau hTau
  have hGenus : 0 ≤ genus G := genus_nonneg_of_graph_connected G hGconn
  have hCountZ : (kInversionCount k beta.func : ℤ) ≤ genus G := by
    rw [hBeta]
    have hCount' : (kInversionCount k tau : ℤ) ≤
        (Int.toNat (genus G) : ℤ) := by
      exact_mod_cast hCount
    rwa [Int.toNat_of_nonneg hGenus] at hCount'
  have hSci : (sci beta.func : ℤ) ≤ genus G := by
    have hSciId : sci AspPerm.id.func = 0 := by
      exact sci_id
    have hStar := sci_star_le k AspPerm.id beta
      (by simpa [hBeta] using hAffine) (by rw [hSciId]; norm_num; omega)
    rw [AspPerm.id_star] at hStar
    rw [hSciId, Nat.cast_zero, zero_add] at hStar
    exact le_trans hStar hCountZ
  have hSize : (weierstrassSize hGconn v D : ℤ) ≤ genus G :=
    weierstrassSize_le_genus_of_sci_le
      u v hGconn D beta.func (by simpa [hBeta] using hTau) hSci
  have hContained : lambda ≤ weierstrassPartition hGconn v D :=
    census_partition_le_weierstrassPartition hGconn v D lambda hRows
  have hCard : lambda.card ≤ weierstrassSize hGconn v D :=
    Finset.card_le_card (YoungDiagram.cells_subset_iff.mp hContained)
  have hCardZ : (lambda.card : ℤ) ≤
      (weierstrassSize hGconn v D : ℤ) := by
    exact_mod_cast hCard
  exact le_trans hCardZ hSize

end Bananas
