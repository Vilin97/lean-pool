/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Refinement.CardinalTruncationClosedClass
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CardinalTruncationDomainEmbedding
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.ConvexQuotientSplitting
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Order.ArchimedeanBall
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Refinement.ConvexRestrictionFactorization

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Transporting refinement from a closed quotient class

Closed-class restriction after convex quotient regrouping is ambient restriction to the preimage
of that class ball. This identifies exact quotient refinements with retained ambient factors and
allows truncation-divisibility to lift the two required divisibilities.
-/

public noncomputable section

open scoped HahnSeries

universe u v w

namespace HahnSeries.CardSuppLTTruncationIntegerPart

private theorem eq_symm_mul_symm_of_map_eq_mul
    {A B : Type*} [Semiring A] [Semiring B] (E : A ≃+* B)
    {t : A} {e f : B} (h : E t = e * f) : t = E.symm e * E.symm f := by
  apply E.injective
  have he : E (E.symm e) = e := E.apply_symm_apply e
  have hf : E (E.symm f) = f := E.apply_symm_apply f
  exact h.trans ((congrArg₂ (· * ·) he.symm hf.symm).trans (E.map_mul _ _).symm)

variable {G : Type u} {R : Type v} {K : Type w} {κ : Cardinal.{u}}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Field K] [Module K G] [Field R]
variable [Fact (Cardinal.aleph0 < κ)] [Fact κ.IsRegular]

/-- Restriction to a closed quotient class is ambient restriction to the preimage of its closed
ball. -/
@[blueprint "lem:quotient-regrouping-closed-ball-restriction"
  (phase := "Refinement over Archimedean classes")
  (title := "Closed-ball restriction under quotient regrouping")
  (statement := /--
    Let $P$ be a convex subspace of an ordered vector space $G$, and regroup a
    bounded Hahn series first by exponents in $G/P$ and then by exponents in
    $P$.  For an Archimedean class $q$ of $G/P$, restriction of the regrouped
    series to the closed ball of $q$ is the regrouping of the original series
    restricted to the inverse image of that ball in $G$.
  -/)
  (proof := /--
    Compare the coefficient at an outer exponent $\bar g\in G/P$ and an inner
    exponent $p\in P$.  If $\bar g$ lies in the closed ball of $q$, both sides
    have the coefficient of the unique exponent of $G$ represented by
    $(\bar g,p)$; otherwise both coefficients are zero.
  -/)]
theorem convexQuotientSplit_filter_eq_closed_class_restrict
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] (Z : Subring R)
    (q : FiniteArchimedeanClass (G ⧸ P))
    (x t : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (ht : (t : R⟦G⟧) = @HahnSeries.filter R G _ _
      (· ∈ (FiniteArchimedeanClass.closedBallAddSubgroup q).comap
        P.mkQ.toAddMonoidHom) (Classical.decPred _) (x : R⟦G⟧)) :
    cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z t =
      closedClassRestrict
        (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z) q
        (cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z x) := by
  classical
  let D := FiniteArchimedeanClass.closedBallAddSubgroup q
  apply Subtype.ext
  apply Subtype.ext
  ext z p
  have hsplit : convexQuotientSplitRingEquiv P (t : R⟦G⟧) =
      HahnSeries.filter (· ∈ D) (convexQuotientSplitRingEquiv P (x : R⟦G⟧)) := by
    rw [ht]
    exact convexQuotientSplitRingEquiv_filter_comap P D (x : R⟦G⟧)
  have hz := congrArg (fun y : (R⟦P⟧)⟦G ⧸ P⟧ ↦ (y.coeff z).coeff p) hsplit
  rw [HahnSeries.coeff_filter] at hz
  have htcoeff := congrArg
    (fun y : (R⟦P⟧)⟦G ⧸ P⟧ ↦ (y.coeff z).coeff p)
    (boundedOuterCoefficientInclusion_split P t.1)
  rw [boundedOuterCoefficientInclusion_coeff] at htcoeff
  rw [coe_cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv]
  rw [htcoeff]
  rw [CardSuppLTTruncationIntegerPart.coe_closedClassRestrict,
    Nonpositive.closedClassRestrict_coeff]
  by_cases hzD : z ∈ D
  · rw [if_pos hzD]
    change ((convexQuotientSplitRingEquiv P (t : R⟦G⟧)).coeff z).coeff p = _
    have hxcoeff := congrArg
      (fun y : (R⟦P⟧)⟦G ⧸ P⟧ ↦ (y.coeff z).coeff p)
      (boundedOuterCoefficientInclusion_split P x.1)
    rw [boundedOuterCoefficientInclusion_coeff] at hxcoeff
    rw [CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom]
    rw [coe_cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv]
    rw [hxcoeff]
    simpa only [D, if_pos hzD] using hz
  · rw [if_neg hzD]
    change ((convexQuotientSplitRingEquiv P (t : R⟦G⟧)).coeff z).coeff p = 0
    simpa only [D, if_neg hzD, HahnSeries.coeff_zero] using hz

private theorem ambient_factorization_of_closed_class_factorization
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] (Z : Subring R)
    (q : FiniteArchimedeanClass (G ⧸ P))
    (a t : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (ht : t = restrictToAddSubgroup Z
      ((FiniteArchimedeanClass.closedBallAddSubgroup q).comap P.mkQ.toAddMonoidHom) a)
    (ht0 : t ≠ 0)
    (e f : cardSuppLTTruncationIntegerPart (G := G ⧸ P)
      (R := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ)
      (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z))
    (ha : closedClassRestrict
      (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z) q
        (cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z a) = e * f) :
    let E := cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv
      (R := R) (κ := κ) P Z
    E t = e * f ∧ t = E.symm e * E.symm f ∧ e ≠ 0 ∧ f ≠ 0 := by
  let E := cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv
    (R := R) (κ := κ) P Z
  have hEt : E t = e * f := by
    rw [convexQuotientSplit_filter_eq_closed_class_restrict P Z q a t]
    · exact ha
    · simp only [ht, coe_restrictToAddSubgroup]
  have htef : t = E.symm e * E.symm f := eq_symm_mul_symm_of_map_eq_mul E hEt
  have he0 : e ≠ 0 := fun he ↦ ht0 (by simp only [htef, he, map_zero, zero_mul])
  have hf0 : f ≠ 0 := fun hf ↦ ht0 (by simp only [htef, hf, map_zero, mul_zero])
  exact ⟨hEt, htef, he0, hf0⟩

private theorem nonpositive_factor_supports_subset_closed_ball
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] (Z : Subring R)
    (q : FiniteArchimedeanClass (G ⧸ P))
    (a t : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (ht : t = restrictToAddSubgroup Z
      ((FiniteArchimedeanClass.closedBallAddSubgroup q).comap P.mkQ.toAddMonoidHom) a)
    (e f : cardSuppLTTruncationIntegerPart (G := G ⧸ P)
      (R := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ)
      (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z))
    (hEt : cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z t = e * f)
    (he0 : e ≠ 0) (hf0 : f ≠ 0) :
    let InnerPart := cardSuppLTTruncationIntegerPart
      (G := P) (R := R) (κ := κ) Z
    let eN := toNonpositiveRingHom InnerPart e
    let fN := toNonpositiveRingHom InnerPart f
    let D := FiniteArchimedeanClass.closedBallAddSubgroup q
    (eN : (CardSuppLTField (G := P) (R := R) (κ := κ))⟦G ⧸ P⟧).support ⊆
        (D : Set (G ⧸ P)) ∧
      (fN : (CardSuppLTField (G := P) (R := R) (κ := κ))⟦G ⧸ P⟧).support ⊆
        (D : Set (G ⧸ P)) := by
  let E := cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv
    (R := R) (κ := κ) P Z
  let InnerPart := cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z
  let eN := toNonpositiveRingHom InnerPart e
  let fN := toNonpositiveRingHom InnerPart f
  let D := FiniteArchimedeanClass.closedBallAddSubgroup q
  have heN0 : eN ≠ 0 := by
    intro heN
    apply he0
    exact toNonpositiveRingHom_injective InnerPart (heN.trans (map_zero _).symm)
  have hfN0 : fN ≠ 0 := by
    intro hfN
    apply hf0
    exact toNonpositiveRingHom_injective InnerPart (hfN.trans (map_zero _).symm)
  have hprodD : ((eN * fN : Nonpositive (G ⧸ P)
      (CardSuppLTField (G := P) (R := R) (κ := κ))) :
        (CardSuppLTField (G := P) (R := R) (κ := κ))⟦G ⧸ P⟧).support ⊆
      (D : Set (G ⧸ P)) := by
    have hraw : eN * fN = toNonpositiveRingHom InnerPart (E t) := by
      let F := toNonpositiveRingHom
        (G := G ⧸ P) (R := CardSuppLTField (G := P) (R := R) (κ := κ))
        (κ := κ) InnerPart
      change F e * F f = F (E t)
      exact (F.map_mul e f).symm.trans (congrArg F hEt.symm)
    rw [hraw, coe_toNonpositiveRingHom,
      support_cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv]
    apply support_convexQuotientSplitRingEquiv_subset_iff P D (t : R⟦G⟧) |>.mpr
    intro z hz
    rw [ht, coe_restrictToAddSubgroup, HahnSeries.support_filter] at hz
    exact hz.2
  exact Nonpositive.support_subset_convex_of_mul_support_subset
    (FiniteArchimedeanClass.closedBall_ordConnected q) heN0 hfN0 hprodD

private theorem support_symm_subset_comap_of_nonpositive_support_subset
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] (Z : Subring R)
    (D : AddSubgroup (G ⧸ P))
    (x : cardSuppLTTruncationIntegerPart (G := G ⧸ P)
      (R := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ)
      (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z))
    (hx : ((toNonpositiveRingHom
      (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z) x :
        Nonpositive (G ⧸ P) (CardSuppLTField (G := P) (R := R) (κ := κ))) :
      (CardSuppLTField (G := P) (R := R) (κ := κ))⟦G ⧸ P⟧).support ⊆ D) :
    ((cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv
      (R := R) (κ := κ) P Z).symm x : R⟦G⟧).support ⊆
        (D.comap P.mkQ.toAddMonoidHom : Set G) := by
  let E := cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv
    (R := R) (κ := κ) P Z
  let xA := E.symm x
  let InnerPart := cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z
  let xN := toNonpositiveRingHom InnerPart x
  apply support_convexQuotientSplitRingEquiv_subset_iff P D (xA : R⟦G⟧) |>.mp
  have hxEq : E xA = x := E.apply_symm_apply x
  have hsupp : (convexQuotientSplitRingEquiv P (xA : R⟦G⟧)).support =
      (xN : (CardSuppLTField (G := P) (R := R) (κ := κ))⟦G ⧸ P⟧).support := by
    rw [← support_cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z xA,
      hxEq, coe_toNonpositiveRingHom]
  rw [hsupp]
  exact hx

private theorem ambient_factor_dvd_of_closed_class_factorization
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] (Z : Subring R)
    (q : FiniteArchimedeanClass (G ⧸ P))
    (x : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (y z : cardSuppLTTruncationIntegerPart (G := G ⧸ P)
      (R := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ)
      (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z))
    (hxy : closedClassRestrict
      (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z) q
        (cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z x) = y * z)
    (hy0 : y ≠ 0)
    (hySupp : ((cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv
      (R := R) (κ := κ) P Z).symm y : R⟦G⟧).support ⊆
        ((FiniteArchimedeanClass.closedBallAddSubgroup q).comap
          P.mkQ.toAddMonoidHom : Set G)) :
    (cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv
      (R := R) (κ := κ) P Z).symm y ∣ x := by
  classical
  let E := cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv
    (R := R) (κ := κ) P Z
  let D := FiniteArchimedeanClass.closedBallAddSubgroup q
  let C : AddSubgroup G := D.comap P.mkQ.toAddMonoidHom
  let yA := E.symm y
  let zA := E.symm z
  let xC := restrictToAddSubgroup Z C x
  have hEx : E xC = y * z := by
    rw [convexQuotientSplit_filter_eq_closed_class_restrict P Z q x xC]
    · exact hxy
    · simp only [xC, C, D, coe_restrictToAddSubgroup]
  have hxC : xC = yA * zA := eq_symm_mul_symm_of_map_eq_mul E hEx
  have hC : (C : Set G).OrdConnected :=
    (FiniteArchimedeanClass.closedBall_ordConnected q).preimage_mono
      (fun _ _ huv ↦ ConvexQuotient.mk_le_mk huv)
  have hyA0 : yA ≠ 0 := by
    intro hyA0
    apply hy0
    rw [← E.apply_symm_apply y, show E.symm y = 0 from hyA0, map_zero]
  apply dvd_of_restriction_factorization Z hC yA zA x hySupp hyA0
  have hraw := congrArg (fun w : cardSuppLTTruncationIntegerPart
    (G := G) (R := R) (κ := κ) Z ↦ (w : R⟦G⟧)) hxC
  calc
    HahnSeries.filter (· ∈ C) (x : R⟦G⟧) = (xC : R⟦G⟧) := by
      exact (coe_restrictToAddSubgroup Z C x).symm
    _ = ((yA * zA : cardSuppLTTruncationIntegerPart
        (G := G) (R := R) (κ := κ) Z) : R⟦G⟧) := hraw
    _ = (yA : R⟦G⟧) * (zA : R⟦G⟧) := rfl

private theorem ambient_factors_supported_of_closed_class_factorization
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] (Z : Subring R)
    (q : FiniteArchimedeanClass (G ⧸ P))
    (a t : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (ht : t = restrictToAddSubgroup Z
      ((FiniteArchimedeanClass.closedBallAddSubgroup q).comap P.mkQ.toAddMonoidHom) a)
    (ht0 : t ≠ 0)
    (e f : cardSuppLTTruncationIntegerPart (G := G ⧸ P)
      (R := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ)
      (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z))
    (ha : closedClassRestrict
      (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z) q
        (cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z a) = e * f) :
    let E := cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv
      (R := R) (κ := κ) P Z
    let D := FiniteArchimedeanClass.closedBallAddSubgroup q
    let C : AddSubgroup G := D.comap P.mkQ.toAddMonoidHom
    let eA := E.symm e
    let fA := E.symm f
    t = eA * fA ∧ e ≠ 0 ∧ f ≠ 0 ∧
      (eA : R⟦G⟧).support ⊆ (C : Set G) ∧
      (fA : R⟦G⟧).support ⊆ (C : Set G) := by
  classical
  let E :=
    cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv (R := R) (κ := κ) P Z
  let D := FiniteArchimedeanClass.closedBallAddSubgroup q
  let C : AddSubgroup G := D.comap P.mkQ.toAddMonoidHom
  let eA := E.symm e
  let fA := E.symm f
  have hfactor := ambient_factorization_of_closed_class_factorization
    P Z q a t ht ht0 e f ha
  dsimp only at hfactor
  obtain ⟨hEt, htef, he0, hf0⟩ := hfactor
  have hsupp := nonpositive_factor_supports_subset_closed_ball
    P Z q a t ht e f hEt he0 hf0
  dsimp only at hsupp
  have heSupp : (eA : R⟦G⟧).support ⊆ (C : Set G) :=
    support_symm_subset_comap_of_nonpositive_support_subset P Z D e hsupp.1
  have hfSupp : (fA : R⟦G⟧).support ⊆ (C : Set G) :=
    support_symm_subset_comap_of_nonpositive_support_subset P Z D f hsupp.2
  exact ⟨htef, he0, hf0, heSupp, hfSupp⟩

private theorem ambient_factors_dvd_of_closed_class_factorizations
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] (Z : Subring R)
    (q : FiniteArchimedeanClass (G ⧸ P))
    (c d : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (e f g h : cardSuppLTTruncationIntegerPart (G := G ⧸ P)
      (R := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ)
      (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z))
    (hc : closedClassRestrict
      (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z) q
        (cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z c) = e * g)
    (hd : closedClassRestrict
      (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z) q
        (cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z d) = f * h)
    (he0 : e ≠ 0) (hf0 : f ≠ 0)
    (heSupp : ((cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv
      (R := R) (κ := κ) P Z).symm e : R⟦G⟧).support ⊆
        ((FiniteArchimedeanClass.closedBallAddSubgroup q).comap
          P.mkQ.toAddMonoidHom : Set G))
    (hfSupp : ((cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv
      (R := R) (κ := κ) P Z).symm f : R⟦G⟧).support ⊆
        ((FiniteArchimedeanClass.closedBallAddSubgroup q).comap
          P.mkQ.toAddMonoidHom : Set G)) :
    (cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv
      (R := R) (κ := κ) P Z).symm e ∣ c ∧
    (cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv
      (R := R) (κ := κ) P Z).symm f ∣ d := by
  constructor
  · exact ambient_factor_dvd_of_closed_class_factorization
      P Z q c e g hc he0 heSupp
  · exact ambient_factor_dvd_of_closed_class_factorization
      P Z q d f h hd hf0 hfSupp

/-- An exact quotient-class refinement transports to a factorisation of the retained ambient
block, with the two factors dividing the corresponding ambient right-hand factors. -/
@[blueprint "lem:closed-class-refinement-transport"
  (phase := "Refinement over Archimedean classes")
  (title := "Transport of refinement from a quotient Archimedean class")
  (statement := /--
    Let $P$ be a convex subspace of an ordered vector space $G$, let $q$ be a
    nonzero Archimedean class of $G/P$, and let $t\ne0$ be the restriction of
    $a$ to the inverse image of the closed ball of $q$.  If the closed-ball
    restrictions of $a,c,d$ in the iterated Hahn field factor as
    \[
      a_q=ef,\qquad c_q=eg,\qquad d_q=fh,
    \]
    then there are $e_A,f_A\in Z+R((G^{<0}))_\kappa$ such that
    $t=e_Af_A$, $e_A\mid c$, and $f_A\mid d$.
  -/)
  (proof := /--
    By \ref{lem:quotient-regrouping-closed-ball-restriction}, the Hahn-field
    isomorphism obtained by regrouping exponents along $P$ identifies
    closed-ball restriction in $G/P$ with restriction to its inverse image in
    $G$.  Transport $e$ and $f$ back through this isomorphism.
    Since their product is supported in the retained convex subgroup,
    \ref{lem:convex-support-of-factors} confines both supports there.  Apply
    \ref{lem:divisibility-from-convex-restriction} to the restricted
    factorisations of $c$ and $d$ to obtain $e_A\mid c$ and $f_A\mid d$ in the
    ambient integer part.
  -/)]
theorem exists_factor_refinement_of_closed_class_refinement
    (P : Submodule K G) [P.toAddSubgroup.IsConvex] (Z : Subring R)
    (q : FiniteArchimedeanClass (G ⧸ P))
    (a c d t : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z)
    (ht : t = restrictToAddSubgroup Z
      ((FiniteArchimedeanClass.closedBallAddSubgroup q).comap P.mkQ.toAddMonoidHom) a)
    (ht0 : t ≠ 0)
    (e f g h : cardSuppLTTruncationIntegerPart (G := G ⧸ P)
      (R := CardSuppLTField (G := P) (R := R) (κ := κ)) (κ := κ)
      (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z))
    (ha : closedClassRestrict
      (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z) q
        (cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z a) = e * f)
    (hc : closedClassRestrict
      (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z) q
        (cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z c) = e * g)
    (hd : closedClassRestrict
      (cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z) q
        (cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv P Z d) = f * h) :
    ∃ eA fA : cardSuppLTTruncationIntegerPart (G := G) (R := R) (κ := κ) Z,
      t = eA * fA ∧ eA ∣ c ∧ fA ∣ d := by
  classical
  let E :=
    cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv (R := R) (κ := κ) P Z
  let eA := E.symm e
  let fA := E.symm f
  have hfactor :=
    ambient_factors_supported_of_closed_class_factorization P Z q a t ht ht0 e f ha
  dsimp only at hfactor
  obtain ⟨htef, he0, hf0, heSupp, hfSupp⟩ := hfactor
  have hdvd :=
    ambient_factors_dvd_of_closed_class_factorizations
      P Z q c d e f g h hc hd he0 hf0 heSupp hfSupp
  exact ⟨eA, fA, htef, hdvd.1, hdvd.2⟩

end HahnSeries.CardSuppLTTruncationIntegerPart
