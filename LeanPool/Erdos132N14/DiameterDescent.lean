/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132N14.PublishedInputs

/-!
# Pair budget and endpoint deletion at fourteen points

Starting from failure of the two-low-multiplicity conclusion, this module
derives the exact multiplicity profile `(1, 15, 15, 15, 15, 15, 15)`.
It then deletes one endpoint of the unique pair in the first class and proves
that the realized-distance set is exactly the old set with that class erased.
-/

namespace LeanPool.Erdos132N14

open scoped BigOperators

noncomputable section

/-- The fourteen-point assertion in the first clause of Erdős Problem 132. -/
def Erdos132ForFourteen (P : Configuration (Fin 14)) : Prop :=
  2 ≤ (P.lowMultiplicityDistances Finset.univ 14).card

theorem pairs_univ_fin_fourteen_card :
    (pairs (Finset.univ : Finset (Fin 14))).card = 91 := by
  decide

/-- Exact information forced by a hypothetical failure at fourteen points. -/
structure FourteenFailureExactProfile (P : Configuration (Fin 14)) where
  /-- The unique low-multiplicity realized distance. -/
  rareDistance : ℝ
  rareDistance_mem : rareDistance ∈ P.realizedDistances Finset.univ
  realizedDistance_card : (P.realizedDistances Finset.univ).card = 7
  rareMultiplicity : P.distanceMultiplicity Finset.univ rareDistance = 1
  otherMultiplicity : ∀ d ∈ P.realizedDistances Finset.univ,
    d ≠ rareDistance → P.distanceMultiplicity Finset.univ d = 15
  /-- The unique increasing pair realizing the rare distance. -/
  rarePair : Fin 14 × Fin 14
  rarePairFiber :
    (pairs (Finset.univ : Finset (Fin 14))).filter
      (fun e ↦ P.pairDistance e = rareDistance) = {rarePair}

theorem fourteen_failure_exact_profile
    (hopfPannwitz : HopfPannwitzLowMultiplicityDistance14)
    (publishedCardinality : PublishedAtMostSixDistanceCardinalityBound)
    (P : Configuration (Fin 14)) (hfailure : ¬Erdos132ForFourteen P) :
    Nonempty (FourteenFailureExactProfile P) := by
  obtain ⟨rareDistance, hrareMem, hrareLe⟩ := hopfPannwitz P
  let D := P.realizedDistances Finset.univ
  have hrareLow : rareDistance ∈ P.lowMultiplicityDistances Finset.univ 14 := by
    exact Finset.mem_filter.mpr ⟨hrareMem, hrareLe⟩
  have hotherLower :
      ∀ d ∈ D.erase rareDistance, 15 ≤ P.distanceMultiplicity Finset.univ d := by
    intro d hd
    have hdD : d ∈ D := Finset.mem_of_mem_erase hd
    have hdne : d ≠ rareDistance := Finset.ne_of_mem_erase hd
    by_contra hnot
    have hdLe : P.distanceMultiplicity Finset.univ d ≤ 14 := by omega
    have hdLow : d ∈ P.lowMultiplicityDistances Finset.univ 14 := by
      exact Finset.mem_filter.mpr ⟨hdD, hdLe⟩
    have honeLt : 1 < (P.lowMultiplicityDistances Finset.univ 14).card :=
      Finset.one_lt_card.mpr
        ⟨rareDistance, hrareLow, d, hdLow, fun h ↦ hdne h.symm⟩
    apply hfailure
    change 2 ≤ (P.lowMultiplicityDistances Finset.univ 14).card
    omega
  have hbudget :
      ∑ d ∈ D, P.distanceMultiplicity Finset.univ d = 91 := by
    rw [Configuration.sum_distanceMultiplicity, pairs_univ_fin_fourteen_card]
  have hrarePos : 0 < P.distanceMultiplicity Finset.univ rareDistance :=
    (P.distanceMultiplicity_pos_iff Finset.univ rareDistance).mpr hrareMem
  have hsumEraseLower :
      15 * (D.erase rareDistance).card ≤
        ∑ d ∈ D.erase rareDistance, P.distanceMultiplicity Finset.univ d := by
    calc
      15 * (D.erase rareDistance).card = ∑ _d ∈ D.erase rareDistance, 15 := by
        simp [mul_comm]
      _ ≤ ∑ d ∈ D.erase rareDistance, P.distanceMultiplicity Finset.univ d :=
        Finset.sum_le_sum hotherLower
  have hcardLower : 7 ≤ D.card := by
    by_contra hnot
    have hcardLe : D.card ≤ 6 := by omega
    change (P.realizedDistances Finset.univ).card ≤ 6 at hcardLe
    have hcardinality : (Finset.univ : Finset (Fin 14)).card ≤ 13 :=
      publishedCardinality (ι := Fin 14) P Finset.univ hcardLe
    norm_num at hcardinality
  have hcardUpper : D.card ≤ 7 := by
    have heraseCard : (D.erase rareDistance).card = D.card - 1 :=
      Finset.card_erase_of_mem hrareMem
    have hcardPos : 0 < D.card := Finset.card_pos.mpr ⟨rareDistance, hrareMem⟩
    have hsplit := Finset.sum_erase_add D
      (fun d ↦ P.distanceMultiplicity Finset.univ d) hrareMem
    rw [hbudget] at hsplit
    omega
  have hcard : D.card = 7 := by omega
  have heraseCard : (D.erase rareDistance).card = 6 := by
    rw [Finset.card_erase_of_mem hrareMem, hcard]
  have hsplit := Finset.sum_erase_add D
    (fun d ↦ P.distanceMultiplicity Finset.univ d) hrareMem
  rw [hbudget] at hsplit
  have hsumErase :
      ∑ d ∈ D.erase rareDistance, P.distanceMultiplicity Finset.univ d = 90 := by
    omega
  have hrareMultiplicity :
      P.distanceMultiplicity Finset.univ rareDistance = 1 := by
    omega
  have hotherMultiplicity :
      ∀ d ∈ D, d ≠ rareDistance → P.distanceMultiplicity Finset.univ d = 15 := by
    intro d hdD hdne
    have hdErase : d ∈ D.erase rareDistance := Finset.mem_erase.mpr ⟨hdne, hdD⟩
    have hdLower := hotherLower d hdErase
    have hwithoutLower :
        15 * ((D.erase rareDistance).erase d).card ≤
          ∑ x ∈ (D.erase rareDistance).erase d,
            P.distanceMultiplicity Finset.univ x := by
      calc
        15 * ((D.erase rareDistance).erase d).card =
            ∑ _x ∈ (D.erase rareDistance).erase d, 15 := by simp [mul_comm]
        _ ≤ ∑ x ∈ (D.erase rareDistance).erase d,
            P.distanceMultiplicity Finset.univ x := by
          apply Finset.sum_le_sum
          intro x hx
          exact hotherLower x (Finset.mem_of_mem_erase hx)
    have hwithoutCard : ((D.erase rareDistance).erase d).card = 5 := by
      rw [Finset.card_erase_of_mem hdErase, heraseCard]
    have hsplitOther := Finset.sum_erase_add (D.erase rareDistance)
      (fun x ↦ P.distanceMultiplicity Finset.univ x) hdErase
    rw [hsumErase] at hsplitOther
    omega
  obtain ⟨rarePair, hrarePair⟩ := Finset.card_eq_one.mp hrareMultiplicity
  exact ⟨{
    rareDistance := rareDistance
    rareDistance_mem := hrareMem
    realizedDistance_card := hcard
    rareMultiplicity := hrareMultiplicity
    otherMultiplicity := hotherMultiplicity
    rarePair := rarePair
    rarePairFiber := hrarePair
  }⟩

namespace FourteenFailureExactProfile

variable {P : Configuration (Fin 14)} (profile : FourteenFailureExactProfile P)

/-- The deleted endpoint of the unique rare pair. -/
def deletedVertex : Fin 14 := profile.rarePair.1

/-- The other endpoint of the unique rare pair. -/
def retainedEndpoint : Fin 14 := profile.rarePair.2

/-- The thirteen labels left after endpoint deletion. -/
def remaining : Finset (Fin 14) := Finset.univ.erase profile.deletedVertex

theorem rarePair_mem : profile.rarePair ∈ pairs (Finset.univ : Finset (Fin 14)) := by
  have hmem : profile.rarePair ∈
      (pairs (Finset.univ : Finset (Fin 14))).filter
        (fun e ↦ P.pairDistance e = profile.rareDistance) := by
    rw [profile.rarePairFiber]
    simp
  exact (Finset.mem_filter.mp hmem).1

theorem rarePair_distance : P.pairDistance profile.rarePair = profile.rareDistance := by
  have hmem : profile.rarePair ∈
      (pairs (Finset.univ : Finset (Fin 14))).filter
        (fun e ↦ P.pairDistance e = profile.rareDistance) := by
    rw [profile.rarePairFiber]
    simp
  exact (Finset.mem_filter.mp hmem).2

theorem retainedEndpoint_mem_remaining :
    profile.retainedEndpoint ∈ profile.remaining := by
  have hlt := (Finset.mem_filter.mp profile.rarePair_mem).2
  simp [remaining, deletedVertex, retainedEndpoint, ne_of_gt hlt]

theorem remaining_card : profile.remaining.card = 13 := by
  simp [remaining, deletedVertex]

theorem remaining_pairs_card : (pairs profile.remaining).card = 78 := by
  have hvNot : profile.deletedVertex ∉ profile.remaining := by
    simp [remaining]
  have huniv : insert profile.deletedVertex profile.remaining = Finset.univ := by
    simp [remaining]
  have hpairs := pairs_insert hvNot
  rw [huniv] at hpairs
  have hcard := congrArg Finset.card hpairs
  rw [Finset.card_union_of_disjoint
    (pairs_disjoint_insertionPairs hvNot)] at hcard
  have hinsertionCard :
      (insertionPairs profile.deletedVertex profile.remaining).card = 13 := by
    rw [insertionPairs, Finset.card_image_of_injective _
      (pairWith_injective profile.deletedVertex), profile.remaining_card]
  rw [pairs_univ_fin_fourteen_card, hinsertionCard] at hcard
  omega

/-- Deleting the endpoint removes exactly the unique rare distance class. -/
theorem erase_endpoint_realizedDistances_eq_erase :
    P.realizedDistances profile.remaining =
      (P.realizedDistances Finset.univ).erase profile.rareDistance := by
  apply Finset.Subset.antisymm
  · intro d hd
    have hdFull := P.realizedDistances_mono (Finset.subset_univ _) hd
    apply Finset.mem_erase.mpr
    refine ⟨?_, hdFull⟩
    intro hdr
    obtain ⟨e, he, hedistance⟩ :=
      (P.mem_realizedDistances_iff profile.remaining d).mp hd
    have heFiber : e ∈
        (pairs (Finset.univ : Finset (Fin 14))).filter
          (fun f ↦ P.pairDistance f = profile.rareDistance) := by
      apply Finset.mem_filter.mpr
      exact ⟨Configuration.pairs_mono (Finset.subset_univ _) he,
        hedistance.trans hdr⟩
    have heq : e = profile.rarePair := by
      rw [profile.rarePairFiber] at heFiber
      simpa using heFiber
    have hfirst := (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1
    rw [heq] at hfirst
    simp [remaining, deletedVertex] at hfirst
  · intro d hd
    have hdne : d ≠ profile.rareDistance := (Finset.mem_erase.mp hd).1
    have hdFull : d ∈ P.realizedDistances Finset.univ := (Finset.mem_erase.mp hd).2
    have hfullMultiplicity := profile.otherMultiplicity d hdFull hdne
    have hinsertionLe :
        P.insertionMultiplicity profile.deletedVertex profile.remaining d ≤ 12 := by
      change (profile.remaining.filter fun w ↦
        dist (P.point profile.deletedVertex) (P.point w) = d).card ≤ 12
      rw [← show (profile.remaining.erase profile.retainedEndpoint).card = 12 by
        rw [Finset.card_erase_of_mem profile.retainedEndpoint_mem_remaining,
          profile.remaining_card]]
      apply Finset.card_le_card
      intro w hw
      have hw' := Finset.mem_filter.mp hw
      apply Finset.mem_erase.mpr
      refine ⟨?_, hw'.1⟩
      intro hretained
      have hdistance :
          dist (P.point profile.deletedVertex) (P.point profile.retainedEndpoint) =
            profile.rareDistance := by
        simpa [Configuration.pairDistance, deletedVertex, retainedEndpoint] using
          profile.rarePair_distance
      rw [hretained, hdistance] at hw'
      exact hdne hw'.2.symm
    have hvNot : profile.deletedVertex ∉ profile.remaining := by
      simp [remaining]
    have hinsert := P.distanceMultiplicity_insert hvNot d
    have huniv : insert profile.deletedVertex profile.remaining = Finset.univ := by
      simp [remaining, deletedVertex]
    rw [huniv, hfullMultiplicity] at hinsert
    have hremainingPos : 0 < P.distanceMultiplicity profile.remaining d := by omega
    exact (P.distanceMultiplicity_pos_iff profile.remaining d).mp hremainingPos

theorem remaining_realizedDistance_card :
    (P.realizedDistances profile.remaining).card = 6 := by
  rw [profile.erase_endpoint_realizedDistances_eq_erase,
    Finset.card_erase_of_mem profile.rareDistance_mem,
    profile.realizedDistance_card]

end FourteenFailureExactProfile

end

end LeanPool.Erdos132N14
