/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.SplitTruncation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CardinalTruncation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrderType

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.DomainOrderType
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IterateOrderType

/-!
# Cardinal bounds under leading-class splitting

This module proves the forward support bounds needed to restrict LM24's leading-class Hahn
splitting to `κ`-bounded series. Closed-class restriction cannot enlarge support. Flattening the
split series recovers a reindexing of that restriction, so both its outer support and every inner
coefficient support have cardinality no larger than the original support.
-/

public noncomputable section

open Cardinal FiniteArchimedeanClass

namespace HahnSeries.Nonpositive

variable {K G R : Type*}
variable [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module K G] [IsOrderedModule K G]
variable [Field R]

/-- Restricting the closed-class truncation cannot increase support order type. -/
theorem supportOrderType_TClosed_le (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) :
    (TClosed (K := K) c x).supportOrderType ≤ (x : R⟦G⟧).supportOrderType := by
  rw [TClosed_eq]
  exact (HahnSeries.supportOrderType_restrictDomain_le (closedBallOrderEmbedding c)
    ((T (K := K) c x : Nonpositive G R) : R⟦G⟧)).trans
      (HahnSeries.supportOrderType_mono (support_T_subset c x))

/-- Closed-class restriction does not increase support cardinality. -/
theorem cardSupp_TClosed_le (c : FiniteArchimedeanClass G) (x : Nonpositive G R) :
    (TClosed (K := K) c x).cardSupp ≤ (x : R⟦G⟧).cardSupp := by
  rw [cardSupp, cardSupp]
  let f : ↥(TClosed (K := K) c x).support → ↥(x : R⟦G⟧).support := fun g ↦
    ⟨g.1.1, by
      rw [mem_support]
      have hg := (mem_support _ _).mp g.2
      rw [TClosed_coeff, coeff_T_of_mem c x g.1.2] at hg
      exact hg⟩
  apply Cardinal.mk_le_of_injective (f := f)
  intro a b h
  dsimp only [f] at h
  have hv : a.1.1 = b.1.1 :=
    congrArg (fun z : ↥(x : R⟦G⟧).support ↦ z.1) h
  exact Subtype.ext (Subtype.ext hv)

/-- Flattening the Archimedean split is its ordered reindexing of the closed-ball series. -/
theorem iterateRingEquiv_archimedeanSplitRingEquiv
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (x : R⟦closedBall K c⟧) :
    HahnSeries.iterateRingEquiv (HahnSeries.archimedeanSplitRingEquiv u c x) =
      HahnSeries.embDomainRingEquiv
        (HahnEmbedding.ArchimedeanStrata.closedBallEquivStratumLexBall u c) x := by
  ext p
  rw [show p = toLex ((ofLex p).1, (ofLex p).2) by simp]
  rw [HahnSeries.iterateRingEquiv_coeff,
    HahnSeries.archimedeanSplitRingEquiv_coeff]
  let q := HahnEmbedding.ArchimedeanStrata.stratumLexBallEquivClosedBall u c
    (toLex ((ofLex p).1, (ofLex p).2))
  let e := HahnEmbedding.ArchimedeanStrata.closedBallEquivStratumLexBall u c
  have hp : toLex ((ofLex p).1, (ofLex p).2) = e q := by
    simp [q, e]
  rw [hp, HahnSeries.embDomainRingEquiv_coeff]
  simp [q, e]

/-- The outer support of an Archimedean split is no larger than the unsplit support. -/
theorem cardSupp_archimedeanSplitRingEquiv_outer_le
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (x : R⟦closedBall K c⟧) :
    (HahnSeries.archimedeanSplitRingEquiv u c x).cardSupp ≤ x.cardSupp := by
  calc
    _ ≤ (HahnSeries.iterateRingEquiv
      (HahnSeries.archimedeanSplitRingEquiv u c x)).cardSupp :=
      HahnSeries.cardSupp_outer_le_cardSupp_iterateRingEquiv _
    _ = x.cardSupp := by
      rw [iterateRingEquiv_archimedeanSplitRingEquiv]
      exact HahnSeries.cardSupp_embDomainRingEquiv _ _

/-- The split truncation's outer support order type is no larger than the original support order
type. -/
theorem supportOrderType_splitTruncation_le
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) :
    ((splitTruncation u c x : Nonpositive (u.stratum c) R⟦ball K c⟧) :
      (R⟦ball K c⟧)⟦u.stratum c⟧).supportOrderType ≤
        (x : R⟦G⟧).supportOrderType := by
  rw [coe_splitTruncation]
  calc
    (HahnSeries.archimedeanSplitRingEquiv u c (TClosed c x)).supportOrderType ≤
        (HahnSeries.iterateRingEquiv
          (HahnSeries.archimedeanSplitRingEquiv u c (TClosed c x))).supportOrderType :=
      HahnSeries.supportOrderType_outer_le_iterateRingEquiv _
    _ = (HahnSeries.embDomainRingEquiv
        (HahnEmbedding.ArchimedeanStrata.closedBallEquivStratumLexBall u c)
          (TClosed c x)).supportOrderType := by
      rw [iterateRingEquiv_archimedeanSplitRingEquiv]
    _ = (TClosed (K := K) c x).supportOrderType :=
      HahnSeries.supportOrderType_embDomainRingEquiv _ _
    _ ≤ (x : R⟦G⟧).supportOrderType := supportOrderType_TClosed_le c x

/-- Leading-class splitting cannot increase LM24 degree. -/
theorem degree_splitTruncation_le
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) :
    HahnSeries.degree
        ((splitTruncation u c x : Nonpositive (u.stratum c) R⟦ball K c⟧) :
          (R⟦ball K c⟧)⟦u.stratum c⟧) ≤
      HahnSeries.degree (x : R⟦G⟧) := by
  rw [HahnSeries.degree_eq_cantorDegree, HahnSeries.degree_eq_cantorDegree]
  exact Ordinal.cantorDegree_mono (supportOrderType_splitTruncation_le u c x)

/-- Every inner coefficient support of an Archimedean split is no larger than the unsplit
support. -/
theorem cardSupp_archimedeanSplitRingEquiv_coeff_le
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (x : R⟦closedBall K c⟧) (s : u.stratum c) :
    ((HahnSeries.archimedeanSplitRingEquiv u c x).coeff s).cardSupp ≤ x.cardSupp := by
  calc
    _ ≤ (HahnSeries.iterateRingEquiv
      (HahnSeries.archimedeanSplitRingEquiv u c x)).cardSupp :=
      HahnSeries.cardSupp_coeff_le_cardSupp_iterateRingEquiv _ s
    _ = x.cardSupp := by
      rw [iterateRingEquiv_archimedeanSplitRingEquiv]
      exact HahnSeries.cardSupp_embDomainRingEquiv _ _

/-- The split truncation's outer support is no larger than the original support. -/
theorem cardSupp_splitTruncation_outer_le
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) :
    ((splitTruncation u c x : Nonpositive (u.stratum c) R⟦ball K c⟧) :
      (R⟦ball K c⟧)⟦u.stratum c⟧).cardSupp ≤ (x : R⟦G⟧).cardSupp := by
  rw [coe_splitTruncation]
  exact (cardSupp_archimedeanSplitRingEquiv_outer_le u c (TClosed c x)).trans
    (cardSupp_TClosed_le c x)

/-- Every coefficient of the split truncation has support no larger than the original support. -/
theorem cardSupp_splitTruncation_coeff_le
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) (s : u.stratum c) :
    ((((splitTruncation u c x : Nonpositive (u.stratum c) R⟦ball K c⟧) :
      (R⟦ball K c⟧)⟦u.stratum c⟧).coeff s).cardSupp) ≤ (x : R⟦G⟧).cardSupp := by
  rw [coe_splitTruncation]
  exact (cardSupp_archimedeanSplitRingEquiv_coeff_le u c (TClosed c x) s).trans
    (cardSupp_TClosed_le c x)

/-- The split truncation with each inner coefficient bundled in the `κ`-bounded Hahn field. -/
def splitTruncationCardSuppLT {κ : Cardinal}
    [Fact (ℵ₀ < κ)]
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) (hx : (x : R⟦G⟧).cardSupp < κ) :
    Nonpositive (u.stratum c)
      (CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ)) := by
  let y := splitTruncation u c x
  let y' : (CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ))⟦u.stratum c⟧ :=
    { coeff := fun s ↦ ⟨(y : (R⟦ball K c⟧)⟦u.stratum c⟧).coeff s,
        (cardSupp_splitTruncation_coeff_le u c x s).trans_lt hx⟩
      isPWO_support' := by
        have heq : Function.support (fun s ↦
            (⟨(y : (R⟦ball K c⟧)⟦u.stratum c⟧).coeff s,
              (cardSupp_splitTruncation_coeff_le u c x s).trans_lt hx⟩ :
                CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ))) =
            (y : (R⟦ball K c⟧)⟦u.stratum c⟧).support := by
          ext s
          rw [HahnSeries.mem_support]
          constructor
          · intro h hzero
            apply h
            apply Subtype.ext
            exact hzero
          · intro h hzero
            apply h
            exact congrArg Subtype.val hzero
        rw [heq]
        exact (y : (R⟦ball K c⟧)⟦u.stratum c⟧).isPWO_support }
  exact ⟨y', by
    intro s hs
    have hs' : s ∈ (y : (R⟦ball K c⟧)⟦u.stratum c⟧).support := by
      rw [HahnSeries.mem_support] at hs ⊢
      intro hzero
      apply hs
      apply Subtype.ext
      exact hzero
    exact support_subset y hs'⟩

/-- Coercing a coefficient of the bounded split truncation recovers the corresponding full
inner Hahn coefficient. -/
@[simp]
theorem coe_coeff_splitTruncationCardSuppLT {κ : Cardinal}
    [Fact (ℵ₀ < κ)]
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) (hx : (x : R⟦G⟧).cardSupp < κ) (s : u.stratum c) :
    ((((splitTruncationCardSuppLT u c x hx : Nonpositive (u.stratum c)
      (CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ))) :
        (CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ))⟦u.stratum c⟧).coeff s :
          R⟦ball K c⟧)) =
      ((splitTruncation u c x : Nonpositive (u.stratum c) R⟦ball K c⟧) :
        (R⟦ball K c⟧)⟦u.stratum c⟧).coeff s := by
  rfl

/-- Bundling the inner coefficients with their cardinal bounds does not change the outer
support. -/
theorem support_splitTruncationCardSuppLT {κ : Cardinal}
    [Fact (ℵ₀ < κ)]
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) (hx : (x : R⟦G⟧).cardSupp < κ) :
    ((splitTruncationCardSuppLT u c x hx : Nonpositive (u.stratum c)
      (CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ))) :
        (CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ))⟦u.stratum c⟧).support =
      ((splitTruncation u c x : Nonpositive (u.stratum c) R⟦ball K c⟧) :
        (R⟦ball K c⟧)⟦u.stratum c⟧).support := by
  ext s
  rw [HahnSeries.mem_support, HahnSeries.mem_support]
  constructor
  · intro hs hs0
    apply hs
    apply Subtype.ext
    exact hs0
  · intro hs hs0
    apply hs
    exact congrArg Subtype.val hs0

/-- The bounded split truncation has the same outer support order type as the unrestricted
split. -/
theorem supportOrderType_splitTruncationCardSuppLT {κ : Cardinal}
    [Fact (ℵ₀ < κ)]
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) (hx : (x : R⟦G⟧).cardSupp < κ) :
    ((splitTruncationCardSuppLT u c x hx : Nonpositive (u.stratum c)
      (CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ))) :
        (CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ))⟦u.stratum c⟧).supportOrderType =
      ((splitTruncation u c x : Nonpositive (u.stratum c) R⟦ball K c⟧) :
        (R⟦ball K c⟧)⟦u.stratum c⟧).supportOrderType := by
  rw [HahnSeries.supportOrderType_eq_setOrderType,
    HahnSeries.supportOrderType_eq_setOrderType]
  exact Set.IsPWO.orderType_congr _ _
    (support_splitTruncationCardSuppLT u c x hx)

/-- Cardinal-bounded leading-class splitting cannot increase LM24 degree. -/
theorem degree_splitTruncationCardSuppLT_le {κ : Cardinal}
    [Fact (ℵ₀ < κ)]
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) (hx : (x : R⟦G⟧).cardSupp < κ) :
    HahnSeries.degree
        ((splitTruncationCardSuppLT u c x hx : Nonpositive (u.stratum c)
          (CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ))) :
            (CardSuppLTField (G := ↥(ball K c)) (R := R)
              (κ := κ))⟦u.stratum c⟧) ≤
      HahnSeries.degree (x : R⟦G⟧) := by
  rw [HahnSeries.degree_eq_cantorDegree, HahnSeries.degree_eq_cantorDegree,
    supportOrderType_splitTruncationCardSuppLT]
  exact Ordinal.cantorDegree_mono (supportOrderType_splitTruncation_le u c x)

/-- The bounded split truncation's constant coefficient is the bounded open-class
truncation. -/
theorem coe_constantCoeff_splitTruncationCardSuppLT {κ : Cardinal}
    [Fact (ℵ₀ < κ)]
    (u : HahnEmbedding.ArchimedeanStrata K G) (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) (hx : (x : R⟦G⟧).cardSupp < κ) :
    ((constantCoeff (R := CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ))
      (splitTruncationCardSuppLT u c x hx) :
        CardSuppLTField (G := ↥(ball K c)) (R := R) (κ := κ)) : R⟦ball K c⟧) =
      tauBall c x := by
  rw [constantCoeff_apply, coe_coeff_splitTruncationCardSuppLT]
  rw [← constantCoeff_apply]
  exact constantCoeff_splitTruncation u c x

end HahnSeries.Nonpositive
