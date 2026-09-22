/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Refinement.CardinalTruncationClosedClass
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CardinalTruncationDomainEmbedding
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CharZero
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Refinement.LimitTailRefinement
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.FiniteClassPrimality

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Exact refinement at a support class in a Hahn tail quotient

Cauchy completeness gives refinement modulo series bounded away from zero in the common-tail
quotient.
Cofinality selects an outer support class where the four equations become exact. Finite-class
primality normalizes the inner residues. The normalization takes place when the bounded Hahn field
on the common tail is the fraction field of its bounded Hahn integer part.
-/

public noncomputable section

open Cardinal FiniteArchimedeanClass
open scoped HahnSeries

universe u v

namespace HahnSeries.CardSuppLTTruncationIntegerPart

private theorem mk_finiteArchimedeanClasses_lt
    {G : Type u} {R : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Field R] {κ : Cardinal} [Fact (ℵ₀ < κ)] {Z : Subring R}
    (a : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := G) (R := R) (κ := κ) Z)
    (T₀ : Set (ArchimedeanClass G))
    (hT₀ : T₀ ⊆ ArchimedeanClass.mk '' (a : HahnSeries G R).support) :
    #{q : FiniteArchimedeanClass G | q.1 ∈ T₀} < κ := by
  let T : Set (FiniteArchimedeanClass G) := {q | q.1 ∈ T₀}
  have supportRep_exists (q : T) : ∃ g : (a : HahnSeries G R).support,
      ArchimedeanClass.mk (g : G) = q.1.1 := by
    obtain ⟨g, hg, hgq⟩ := hT₀ q.2
    exact ⟨⟨g, hg⟩, hgq⟩
  let supportRep (q : T) : (a : HahnSeries G R).support :=
    Classical.choose (supportRep_exists q)
  have supportRep_spec (q : T) :
      ArchimedeanClass.mk (supportRep q : G) = q.1.1 :=
    Classical.choose_spec (supportRep_exists q)
  have supportRep_injective : Function.Injective supportRep := by
    intro q r hqr
    apply Subtype.ext
    apply Subtype.ext
    exact (supportRep_spec q).symm.trans
      ((congrArg (fun z : (a : HahnSeries G R).support ↦
        ArchimedeanClass.mk (z : G)) hqr).trans (supportRep_spec r))
  exact (Cardinal.mk_le_of_injective supportRep_injective).trans_lt a.1.2

/-- A bounded nonpositive four-factor refinement after restriction to one closed
Archimedean class in a specified family. -/
private def HasNonpositiveClosedClassRefinement
    {G : Type u} {K : Type v}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Field K] {κ : Cardinal} [Fact (ℵ₀ < κ)]
    (S : Subring K) (U : Set (FiniteArchimedeanClass G))
    (a b c d : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := G) (R := K) (κ := κ) S) : Prop :=
  ∃ q ∈ U, ∃ e f g h : HahnSeries.Nonpositive G K,
    HahnSeries.Nonpositive.closedClassRestrict q
        (HahnSeries.CardSuppLTTruncationIntegerPart.toNonpositiveRingHom S a) =
      HahnSeries.Nonpositive.closedClassRestrict q e *
        HahnSeries.Nonpositive.closedClassRestrict q f ∧
    HahnSeries.Nonpositive.closedClassRestrict q
        (HahnSeries.CardSuppLTTruncationIntegerPart.toNonpositiveRingHom S b) =
      HahnSeries.Nonpositive.closedClassRestrict q g *
        HahnSeries.Nonpositive.closedClassRestrict q h ∧
    HahnSeries.Nonpositive.closedClassRestrict q
        (HahnSeries.CardSuppLTTruncationIntegerPart.toNonpositiveRingHom S c) =
      HahnSeries.Nonpositive.closedClassRestrict q e *
        HahnSeries.Nonpositive.closedClassRestrict q g ∧
    HahnSeries.Nonpositive.closedClassRestrict q
        (HahnSeries.CardSuppLTTruncationIntegerPart.toNonpositiveRingHom S d) =
      HahnSeries.Nonpositive.closedClassRestrict q f *
        HahnSeries.Nonpositive.closedClassRestrict q h ∧
    (e : HahnSeries G K).cardSupp < κ ∧
    (f : HahnSeries G K).cardSupp < κ ∧
    (g : HahnSeries G K).cardSupp < κ ∧
    (h : HahnSeries G K).cardSupp < κ

/-- A bounded Hahn-integer-part equation over a complete tail quotient admits a bounded
nonpositive refinement after restriction to a coinitial closed class. -/
private theorem exists_nonpositive_closed_class_refinement_of_complete_tail_quotient
    {G : Type u} {K : Type v}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module ℚ G] [PosSMulMono ℚ G]
    [Field K] [CharZero K]
    {κ : Cardinal} [Fact (ℵ₀ < κ)] [Fact κ.IsRegular]
    (T : Set (FiniteArchimedeanClass G)) [Nonempty T]
    (hT : ∀ c ∈ T, ∃ d ∈ T, c < d)
    [CompleteSpace (FiniteArchimedeanClass.TailQuotient T)]
    (hTcard : #T < κ)
    (S : Subring K)
    (a b c d : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := FiniteArchimedeanClass.TailQuotient T) (R := K) (κ := κ) S)
    (habcd : a * b = c * d)
    {U : Set (FiniteArchimedeanClass (FiniteArchimedeanClass.TailQuotient T))}
    (hU : IsCofinal U) :
    HasNonpositiveClosedClassRefinement S U a b c d := by
  let toN := HahnSeries.CardSuppLTTruncationIntegerPart.toNonpositiveRingHom
    (G := FiniteArchimedeanClass.TailQuotient T) (R := K) (κ := κ) S
  have hnonpositive : toN a * toN b = toN c * toN d := by
    simpa only [map_mul] using congrArg toN habcd
  have cardSupp_toN_lt (x : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := FiniteArchimedeanClass.TailQuotient T) (R := K) (κ := κ) S) :
      ((toN x : HahnSeries.Nonpositive
        (FiniteArchimedeanClass.TailQuotient T) K) :
          HahnSeries (FiniteArchimedeanClass.TailQuotient T) K).cardSupp < κ := by
    have hx := (HahnSeries.mem_cardSuppLTSubfield
      (Γ := FiniteArchimedeanClass.TailQuotient T) (R := K) (κ := κ)).mp x.1.2
    simpa only [toN,
      HahnSeries.CardSuppLTTruncationIntegerPart.coe_toNonpositiveRingHom] using hx
  rw [HasNonpositiveClosedClassRefinement]
  exact HahnSeries.Nonpositive.exists_closed_class_refinement_of_complete_tail_quotient
    T hT hTcard (toN a) (toN b) (toN c) (toN d)
    (cardSupp_toN_lt a) (cardSupp_toN_lt b) (cardSupp_toN_lt c) (cardSupp_toN_lt d)
    hnonpositive hU

/-- Regrouping an equation along a limit tail produces a bounded nonpositive refinement at a
support class of the first factor. -/
private theorem exists_nonpositive_refinement_at_support_class
    {G : Type u} {R : Type v}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module ℚ G] [PosSMulMono ℚ G]
    [Field R] [CharZero R]
    {κ : Cardinal} [Fact (ℵ₀ < κ)] [Fact κ.IsRegular]
    (Z : Subring R)
    (T₀ T₁ : Set (ArchimedeanClass G))
    (hT₀gt : ∀ a ∈ T₀, ∃ b ∈ T₀, a < b)
    (a b c d : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := G) (R := R) (κ := κ) Z)
    (habcd : a * b = c * d)
    (haclasses : ArchimedeanClass.mk '' (a : HahnSeries G R).support = T₀ ∪ T₁)
    [Nonempty {q : FiniteArchimedeanClass G | q.1 ∈ T₀}]
    [CompleteSpace (FiniteArchimedeanClass.TailQuotient
      {q : FiniteArchimedeanClass G | q.1 ∈ T₀})] :
    let T : Set (FiniteArchimedeanClass G) := {q | q.1 ∈ T₀}
    let P := FiniteArchimedeanClass.tailSubmodule ℚ T
    let S := HahnSeries.cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z
    let E := HahnSeries.cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv
      (R := R) (κ := κ) P Z
    let U : Set (FiniteArchimedeanClass (FiniteArchimedeanClass.TailQuotient T)) :=
      {q | q.1 ∈ ArchimedeanClass.mk ''
        (HahnSeries.convexQuotientSplitRingEquiv P (a : HahnSeries G R)).support}
    HasNonpositiveClosedClassRefinement S U (E a) (E b) (E c) (E d) := by
  classical
  let T : Set (FiniteArchimedeanClass G) := {q | q.1 ∈ T₀}
  let P := FiniteArchimedeanClass.tailSubmodule ℚ T
  let InnerField := HahnSeries.CardSuppLTField (G := P) (R := R) (κ := κ)
  let S := HahnSeries.cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z
  let E := HahnSeries.cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv
    (R := R) (κ := κ) P Z
  let A := E a
  let B := E b
  let C := E c
  let D := E d
  have hABCD : A * B = C * D := by
    simpa only [A, B, C, D, map_mul] using congrArg E habcd
  have hT : ∀ x ∈ T, ∃ y ∈ T, x < y := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hT₀gt x.1 hx
    obtain ⟨z, hz, hyz⟩ := hT₀gt y hy
    exact ⟨⟨y, ne_top_of_lt hyz⟩, hy, hxy⟩
  let U : Set (FiniteArchimedeanClass (FiniteArchimedeanClass.TailQuotient T)) :=
    {q | q.1 ∈ ArchimedeanClass.mk ''
      (HahnSeries.convexQuotientSplitRingEquiv P (a : HahnSeries G R)).support}
  have hU : IsCofinal U := HahnSeries.isCofinal_supportArchimedeanClasses_convexQuotientSplit
    T₀ T₁ hT₀gt (a : HahnSeries G R) haclasses
  have hTcard : #T < κ := by
    apply mk_finiteArchimedeanClasses_lt (Z := Z) a T₀
    intro q hq
    rw [haclasses]
    exact Or.inl hq
  exact exists_nonpositive_closed_class_refinement_of_complete_tail_quotient
    T hT hTcard S A B C D hABCD hU

/-- The first factor has the primal residue and nonvanishing closed-class restrictions needed
to normalize refinements over a specified family of classes. -/
private def HasClosedClassNormalization
    {G : Type u} {K : Type v}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Field K] {κ : Cardinal} [Fact (ℵ₀ < κ)]
    (S : Subring K) (U : Set (FiniteArchimedeanClass G))
    (a b c d : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := G) (R := K) (κ := κ) S) : Prop :=
  a * b = c * d ∧
  IsPrimal (⟨(a : K⟦G⟧).coeff 0,
    ((HahnSeries.mem_cardSuppLTTruncationIntegerPart (Z := S)).mp a.2).2⟩ : S) ∧
  Subring.fracSubring S = ⊤ ∧
  ∀ q ∈ U, closedClassRestrict S q a ≠ 0

/-- The normalization hypotheses turn every bounded nonpositive closed-class refinement into one
inside the cardinal-bounded Hahn integer part. -/
private theorem exists_integer_part_refinement_of_nonpositive_refinement
    {G : Type u} {K : Type v}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Field K] {κ : Cardinal} [Fact (ℵ₀ < κ)] [Fact κ.IsRegular]
    (S : Subring K) (U : Set (FiniteArchimedeanClass G))
    (a b c d : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := G) (R := K) (κ := κ) S)
    (href : HasNonpositiveClosedClassRefinement S U a b c d)
    (hnorm : HasClosedClassNormalization S U a b c d) :
    ∃ q ∈ U, ∃ E F H₁ H₂ : HahnSeries.cardSuppLTTruncationIntegerPart
        (G := G) (R := K) (κ := κ) S,
      closedClassRestrict S q a = E * F ∧
      closedClassRestrict S q b = H₁ * H₂ ∧
      closedClassRestrict S q c = E * H₁ ∧
      closedClassRestrict S q d = F * H₂ := by
  rw [HasNonpositiveClosedClassRefinement] at href
  rw [HasClosedClassNormalization] at hnorm
  obtain ⟨habcd, haS, hfrac, hnonzero⟩ := hnorm
  obtain ⟨q, hq, e, f, g, h, hea, heb, hec, hed, hecard, hfcard, hgcard, hhcard⟩ := href
  obtain ⟨E, F, H₁, H₂, hEA, hEB, hEC, hED⟩ :=
    exists_refinement_closedClassRestrict_of_ambient
      S q a b c d haS hfrac (hnonzero q hq) habcd e f g h
      hecard hfcard hgcard hhcard hea heb hec hed
  exact ⟨q, hq, E, F, H₁, H₂, hEA, hEB, hEC, hED⟩

/-- Regrouping along the common tail supplies the normalization hypotheses at every support class
of the first factor. -/
private theorem has_closed_class_normalization_at_support_classes
    {G : Type u} {R : Type v}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module ℚ G] [PosSMulMono ℚ G]
    [Field R]
    {κ : Cardinal} [Fact (ℵ₀ < κ)] [Fact κ.IsRegular]
    (Z : Subring R)
    (hfinite : ∀ y : HahnSeries.cardSuppLTTruncationIntegerPart
        (G := G) (R := R) (κ := κ) Z,
      (ArchimedeanClass.mk '' (y : HahnSeries G R).support).Finite → IsPrimal y)
    (T₀ T₁ : Set (ArchimedeanClass G))
    (hT₀gt : ∀ a ∈ T₀, ∃ b ∈ T₀, a < b) (hT₁ : T₁.Finite)
    (a b c d : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := G) (R := R) (κ := κ) Z)
    (habcd : a * b = c * d)
    (haclasses : ArchimedeanClass.mk '' (a : HahnSeries G R).support = T₀ ∪ T₁)
    (htailfrac :
      Subring.fracSubring (HahnSeries.cardSuppLTTruncationIntegerPart
        (G := FiniteArchimedeanClass.tailSubmodule ℚ
          {q : FiniteArchimedeanClass G | q.1 ∈ T₀})
        (R := R) (κ := κ) Z) = ⊤) :
    let T : Set (FiniteArchimedeanClass G) := {q | q.1 ∈ T₀}
    let P := FiniteArchimedeanClass.tailSubmodule ℚ T
    let S := HahnSeries.cardSuppLTTruncationIntegerPart
      (G := P) (R := R) (κ := κ) Z
    let E := HahnSeries.cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv
      (R := R) (κ := κ) P Z
    let U : Set (FiniteArchimedeanClass (FiniteArchimedeanClass.TailQuotient T)) :=
      {q | q.1 ∈ ArchimedeanClass.mk ''
        (HahnSeries.convexQuotientSplitRingEquiv P (a : HahnSeries G R)).support}
    HasClosedClassNormalization S U (E a) (E b) (E c) (E d) := by
  let T : Set (FiniteArchimedeanClass G) := {q | q.1 ∈ T₀}
  let P := FiniteArchimedeanClass.tailSubmodule ℚ T
  let InnerField := HahnSeries.CardSuppLTField (G := P) (R := R) (κ := κ)
  let S := HahnSeries.cardSuppLTTruncationIntegerPart (G := P) (R := R) (κ := κ) Z
  let E := HahnSeries.cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv
    (R := R) (κ := κ) P Z
  let A := E a
  let B := E b
  let C := E c
  let D := E d
  rw [HasClosedClassNormalization]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [A, B, C, D, map_mul] using congrArg E habcd
  · exact isPrimal_coeff_zero_convexQuotientSplitRingEquiv_of_ambient_finiteClasses
      Z hfinite T₀ T₁ hT₀gt hT₁ a haclasses.le
  · exact htailfrac
  · intro q hq
    apply closedClassRestrict_ne_zero_of_mem_image_mk_support S q A
    rw [HahnSeries.support_cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv]
    exact hq

/-- Select an outer class met by the support and refine all four closed-class restrictions. -/
@[blueprint "thm:support-class-refinement"
  (phase := "Refinement over Archimedean classes")
  (title := "Refinement at a quotient Archimedean class")
  (statement := /--
    Let $a,b,c,d\in Z+R((G^{<0}))_\kappa$ satisfy $ab=cd$. Suppose that the
    Archimedean classes met by the support of $a$ are $T_0\cup T_1$, where
    $T_1$ is finite, and $T_0$ contains a non-zero class and has no greatest
    element. Assume primality for every series whose support meets only
    finitely many Archimedean classes. Assume that the quotient by the common
    tail below $T_0$ is Cauchy complete for its additive uniformity, and that
    the $\kappa$-bounded Hahn field on the common tail is the fraction field of
    its corresponding $\kappa$-bounded integer part. Then some Archimedean
    class of the quotient met by the support of $a$ admits an exact four-factor
    refinement of the restrictions of $a,b,c,d$ to its closed Archimedean ball.
  -/)
  (proof := /--
    Regroup each series as a series on the common-tail quotient.  The support
    classes of $a$ are cofinal there, so
    \ref{thm:complete-tail-quotient-refinement} gives an exact refinement at
    one class met by that support.  Primality of the inner constant term and
    its descent to the convex common tail use
    \ref{lem:convex-support-of-factors}: every nonzero factor of a series
    supported in that tail is supported there.  This primality together with
    the common-tail fraction-field hypothesis supplies the hypotheses of
    \ref{lem:closed-class-refinement-normalization}, which normalises the four
    quotient factors inside the bounded Hahn integer part.
  -/)]
theorem exists_closed_class_refinement_at_support_class
    {G : Type u} {R : Type v}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module ℚ G] [PosSMulMono ℚ G]
    [Field R] [CharZero R]
    {κ : Cardinal} [Fact (ℵ₀ < κ)] [Fact κ.IsRegular]
    (Z : Subring R)
    (hfinite : ∀ y : HahnSeries.cardSuppLTTruncationIntegerPart
        (G := G) (R := R) (κ := κ) Z,
      (ArchimedeanClass.mk '' (y : HahnSeries G R).support).Finite → IsPrimal y)
    (T₀ T₁ : Set (ArchimedeanClass G))
    (hT₀gt : ∀ a ∈ T₀, ∃ b ∈ T₀, a < b) (hT₁ : T₁.Finite)
    (a b c d : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := G) (R := R) (κ := κ) Z)
    (habcd : a * b = c * d)
    (haclasses : ArchimedeanClass.mk '' (a : HahnSeries G R).support = T₀ ∪ T₁)
    [Nonempty {q : FiniteArchimedeanClass G | q.1 ∈ T₀}]
    [CompleteSpace (FiniteArchimedeanClass.TailQuotient
      {q : FiniteArchimedeanClass G | q.1 ∈ T₀})]
    (htailfrac :
      Subring.fracSubring (HahnSeries.cardSuppLTTruncationIntegerPart
        (G := FiniteArchimedeanClass.tailSubmodule ℚ
          {q : FiniteArchimedeanClass G | q.1 ∈ T₀})
        (R := R) (κ := κ) Z) = ⊤) :
    let T : Set (FiniteArchimedeanClass G) := {q | q.1 ∈ T₀}
    let P := FiniteArchimedeanClass.tailSubmodule ℚ T
    let S := HahnSeries.cardSuppLTTruncationIntegerPart
      (G := P) (R := R) (κ := κ) Z
    let E := HahnSeries.cardSuppLTTruncationIntegerPartConvexQuotientSplitRingEquiv
      (R := R) (κ := κ) P Z
    ∃ q : FiniteArchimedeanClass (FiniteArchimedeanClass.TailQuotient T),
      q.1 ∈ ArchimedeanClass.mk ''
        (HahnSeries.convexQuotientSplitRingEquiv P (a : HahnSeries G R)).support ∧
      ∃ e f g h : HahnSeries.cardSuppLTTruncationIntegerPart
          (G := FiniteArchimedeanClass.TailQuotient T)
          (R := HahnSeries.CardSuppLTField (G := P) (R := R) (κ := κ))
          (κ := κ) S,
        closedClassRestrict S q (E a) = e * f ∧
        closedClassRestrict S q (E b) = g * h ∧
        closedClassRestrict S q (E c) = e * g ∧
        closedClassRestrict S q (E d) = f * h := by
  apply exists_integer_part_refinement_of_nonpositive_refinement
  · exact exists_nonpositive_refinement_at_support_class
      Z T₀ T₁ hT₀gt a b c d habcd haclasses
  · exact has_closed_class_normalization_at_support_classes
      Z hfinite T₀ T₁ hT₀gt hT₁ a b c d habcd haclasses htailfrac

end HahnSeries.CardSuppLTTruncationIntegerPart
