/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.SupportArchimedeanClasses
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Refinement.SupportClassFactorization
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Refinement.SupportClassRefinement
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Refinement.ClosedClassRefinementTransport

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Primality from common-tail quotients

The induction rank is the order type of the Archimedean classes met by the non-zero support. A
supplied theorem handles the case in which this set is finite. At every infinite rank, the classes
split into a non-zero limit initial segment and a finite final segment. Cauchy completeness of the
quotient by the common tail below the limit segment, together with primality for every series whose
support meets only finitely many Archimedean classes and the hypothesis that the κ-bounded integer
part on the common tail has the required fraction field, gives an exact refinement at a class met by
the support. Factoring off the resulting divisor strictly lowers the rank, so ordinal induction
proves that every element is primal.
-/

public noncomputable section

open Cardinal FiniteArchimedeanClass
open HahnSeries.CardSuppLTTruncationIntegerPart
open scoped HahnSeries

universe u v

namespace HahnSeries.CardSuppLTTruncationIntegerPart

/-- The common-tail hypotheses extend finite-class primality to every cardinal-bounded Hahn
integer-part series. -/
@[blueprint "thm:limit-tail-primality"
  (phase := "Refinement over Archimedean classes")
  (title := "Transfinite extension of finite-class primality")
  (statement := /--
    Let $G$ be an ordered rational vector space, $R$ a field of characteristic
    zero, $\kappa>\aleph_0$ a regular cardinal, and $Z\subseteq R$ a subring.
    Assume that every element of $Z+R((G^{<0}))_\kappa$ meeting only finitely
    many Archimedean classes is primal.  For every nonempty set $T$ of nonzero
    Archimedean classes with no least member in the magnitude order and
    cardinality less than $\kappa$, assume that the quotient by the common tail
    below $T$ is Cauchy complete for its additive uniformity and that the
    bounded Hahn field on the common tail is the fraction field of its bounded
    Hahn integer part.  Then every element of
    $Z+R((G^{<0}))_\kappa$ is primal.
  -/)
  (proof := /--
    Induct on the order type of the nonzero Archimedean support classes.  The
    finite case is the hypothesis.  Otherwise split the class set into a limit
    initial segment and a finite final segment.  By
    \ref{thm:support-class-refinement}, an equation $ad=bc$ has an exact
    refinement at a quotient class met by the support of $a$.
    By \ref{lem:support-class-factorisation}, factoring off the corresponding
    retained block leaves a cofactor with strictly smaller support-class order
    type.  The induction hypothesis makes that cofactor primal, while
    \ref{lem:closed-class-refinement-transport} transports the quotient
    refinement to the ambient integer part.  These two refinements prove that
    $a$ is primal.
  -/)]
theorem isPrimal_of_finite_classes_and_limit_tail_conditions
    {G : Type u} {R : Type v}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module ℚ G] [PosSMulMono ℚ G]
    [Field R] [CharZero R]
    {κ : Cardinal} [Fact (ℵ₀ < κ)] [Fact κ.IsRegular]
    (Z : Subring R)
    (hfinite : ∀ y : HahnSeries.cardSuppLTTruncationIntegerPart
        (G := G) (R := R) (κ := κ) Z,
      (ArchimedeanClass.mk '' (y : HahnSeries G R).support).Finite → IsPrimal y)
    (hcomplete : ∀ (T : Set (FiniteArchimedeanClass G)), T.Nonempty →
      (∀ c ∈ T, ∃ d ∈ T, c < d) →
      (#T < κ) →
      Nonempty (CompleteSpace (FiniteArchimedeanClass.TailQuotient T)))
    (htailfrac : ∀ (T : Set (FiniteArchimedeanClass G)), T.Nonempty →
      (∀ c ∈ T, ∃ d ∈ T, c < d) →
      (#T < κ) →
      Subring.fracSubring (HahnSeries.cardSuppLTTruncationIntegerPart
        (G := FiniteArchimedeanClass.tailSubmodule ℚ T)
        (R := R) (κ := κ) Z) = ⊤)
    (a : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := G) (R := R) (κ := κ) Z) : IsPrimal a := by
  classical
  let S := HahnSeries.cardSuppLTTruncationIntegerPart
    (G := G) (R := R) (κ := κ) Z
  let toN := toNonpositiveRingHom (G := G) (R := R) (κ := κ) Z
  let rank : S → Ordinal := fun x ↦
    (HahnSeries.Nonpositive.isPWO_nonzeroSupportArchimedeanClasses (toN x)).orderType
  have hind : ∀ o : Ordinal, ∀ x : S, rank x = o → IsPrimal x := by
    intro o
    induction o using WellFoundedLT.induction with
    | ind o ih =>
        intro x hxrank
        by_cases hx0 : x = 0
        · rw [hx0]
          exact isPrimal_zero
        let xN := toN x
        rcases xN.isPWO_supportArchimedeanClasses.finite_or_exists_limit_initial_finite_final
            with hfiniteClasses | ⟨T₀, T₁, hT₀pwo, _hT₁pwo, hT₀sub, _hT₁sub, _hbefore,
              hT₀limit, hT₁finite, hclasses⟩
        · apply hfinite x
          simpa only [xN, toN, coe_toNonpositiveRingHom] using hfiniteClasses
        · have hT₀gt : ∀ c ∈ T₀, ∃ d ∈ T₀, c < d := fun c hc ↦
            hT₀pwo.exists_gt_of_isSuccLimit_orderType hT₀limit hc
          have hxclasses : ArchimedeanClass.mk '' (x : HahnSeries G R).support = T₀ ∪ T₁ := by
            simpa only [xN, toN, coe_toNonpositiveRingHom] using hclasses
          let T : Set (FiniteArchimedeanClass G) := {c | c.1 ∈ T₀}
          have hTne : T.Nonempty := by
            have hT₀ne : T₀.Nonempty := by
              by_contra hne
              rw [Set.not_nonempty_iff_eq_empty] at hne
              exact hT₀limit.ne_bot (hT₀pwo.orderType_eq_zero.mpr hne)
            obtain ⟨c, hc⟩ := hT₀ne
            obtain ⟨d, _hd, hcd⟩ := hT₀gt c hc
            exact ⟨⟨c, ne_top_of_lt hcd⟩, hc⟩
          let : Nonempty T :=
            ⟨⟨Classical.choose hTne, Classical.choose_spec hTne⟩⟩
          have hTgt : ∀ c ∈ T, ∃ d ∈ T, c < d := by
            intro c hc
            obtain ⟨d, hd, hcd⟩ := hT₀gt c.1 hc
            obtain ⟨e, _he, hde⟩ := hT₀gt d hd
            exact ⟨⟨d, ne_top_of_lt hde⟩, hd, hcd⟩
          have hTcard : #T < κ := by
            calc
              #T = #(Subtype.val '' T) := (Cardinal.mk_image_eq Subtype.val_injective).symm
              _ ≤ #T₀ := Cardinal.mk_le_mk_of_subset fun _ h ↦ by
                obtain ⟨c, hc, rfl⟩ := h
                exact hc
              _ ≤ #(ArchimedeanClass.mk '' (x : HahnSeries G R).support) :=
                Cardinal.mk_le_mk_of_subset fun c hc ↦ by
                  rw [hxclasses]
                  exact Or.inl hc
              _ ≤ #(x : HahnSeries G R).support := Cardinal.mk_image_le
              _ < κ := x.1.2
          let : CompleteSpace (FiniteArchimedeanClass.TailQuotient T) :=
            Classical.choice (hcomplete T hTne hTgt hTcard)
          let P := FiniteArchimedeanClass.tailSubmodule ℚ T
          intro b c hdiv
          obtain ⟨d, hprod⟩ := hdiv
          have heq : x * d = b * c := hprod.symm
          obtain ⟨q, hqocc, e, f, g, h, hxe, _hde, hbe, hce⟩ :=
            exists_closed_class_refinement_at_support_class Z hfinite
              T₀ T₁ hT₀gt hT₁finite x d b c heq hxclasses
              (htailfrac T hTne hTgt hTcard)
          have hqocc' : q.1 ∈ ArchimedeanClass.mk ''
              (Submodule.Quotient.mk (p := P) '' (x : HahnSeries G R).support) := by
            obtain ⟨z, hz, hzq⟩ := hqocc
            have hsupp := HahnSeries.support_convexQuotientSplitRingEquiv P
              (x : HahnSeries G R)
            rw [hsupp] at hz
            obtain ⟨r, hr, hzr⟩ := hz
            exact ⟨z, ⟨r, hr, hzr⟩, hzq⟩
          let C : AddSubgroup G :=
            (FiniteArchimedeanClass.closedBallAddSubgroup q).comap P.mkQ.toAddMonoidHom
          have hfilter0 : HahnSeries.filter (· ∈ C) (x : HahnSeries G R) ≠ 0 := by
            obtain ⟨z, ⟨r, hr, hqr⟩, hzq⟩ := hqocc'
            intro hzero
            have hcoeff := congrArg (fun y : HahnSeries G R ↦ y.coeff r) hzero
            rw [HahnSeries.coeff_filter, ite_eq_left] at hcoeff
            · exact (HahnSeries.mem_support _ _).mp hr hcoeff
            · change P.mkQ r ∈ FiniteArchimedeanClass.closedBallAddSubgroup q
              apply FiniteArchimedeanClass.mem_closedBallAddSubgroup_iff.mpr
              intro _hr0
              change q.1 ≤ ArchimedeanClass.mk (P.mkQ r)
              change P.mkQ r = z at hqr
              rw [hqr, hzq]
          obtain ⟨t, w, ht, hfac, hrank⟩ :=
            exists_factor_with_smaller_support_class_orderType
              Z T q x hqocc' hfilter0
          have ht' : t = restrictToAddSubgroup Z C x := by
            apply Subtype.ext
            apply Subtype.ext
            exact ht.trans (coe_restrictToAddSubgroup Z C x).symm
          have ht0 : t ≠ 0 := fun htzero ↦ hx0 (by rw [hfac, htzero, zero_mul])
          obtain ⟨eA, fA, htef, heb, hfc⟩ :=
            exists_factor_refinement_of_closed_class_refinement
              P Z q x b c t ht' ht0 e f g h hxe hbe hce
          have hw : IsPrimal w := by
            apply ih (rank w)
            · rw [← hxrank]
              exact hrank
            · rfl
          exact exists_primalRefinement_of_factor_refinement
            hx0 heq hfac htef heb hfc hw
  exact hind (rank a) a rfl

/-- Conditions `(A1)`--`(A3)` at finite Archimedean classes, together with the two
common-tail hypotheses at limit families, make every element of the bounded Hahn integer part
primal. -/
@[blueprint "thm:hahn-integer-part-primality"
  (phase := "Refinement over Archimedean classes")
  (title := "Primality under finite-class and common-tail hypotheses")
  (statement := /--
    Let $G$ be an ordered rational vector space, $R$ a field of characteristic
    zero, $\kappa>\aleph_0$ a regular cardinal, and $Z\subseteq R$ a
    pre-Schreier subring.  At every nonzero Archimedean class, choose an
    additive complement to the strict inner ball that is order additively
    isomorphic to $\mathbb R$.  Assume that each strict inner ball either has
    cofinality at least $\kappa$, or is zero and every element of $R$ is a
    fraction of elements of $Z$.

    For every nonempty set $T$ of fewer than $\kappa$ nonzero Archimedean
    classes having no least member in the magnitude order, let $H_T$ be the
    rational subspace of exponents lying beyond every class in $T$.  Assume
    that $G/H_T$ is Cauchy complete for its additive uniformity and that the
    bounded Hahn field on $H_T$ is the fraction field of its bounded Hahn
    integer part.  Then every element of
    $Z+R((G^{<0}))_\kappa$ is primal.
  -/)
  (proof := /--
    By \ref{thm:finite-support-classes-primality}, assumptions
    $(A1)_\sigma$--$(A3)$ make every series meeting finitely many Archimedean
    classes primal.  Apply \ref{thm:limit-tail-primality} to extend this result
    to arbitrary support-class order type.
  -/)]
theorem isPrimal_of_finite_class_assumptions_and_limit_tail_conditions
    {G : Type u} {R : Type v}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module ℚ G] [IsOrderedModule ℚ G]
    [Field R] [CharZero R]
    {κ : Cardinal} [Fact (ℵ₀ < κ)] [Fact κ.IsRegular]
    (Z : Subring R) [DecompositionMonoid Z]
    (s : HahnEmbedding.ArchimedeanStrata ℚ G)
    (hA1 : ∀ c : FiniteArchimedeanClass G, LM24.AssumptionA1AtFiniteClass s c)
    (hA2 : ∀ c : FiniteArchimedeanClass G,
      LM24.AssumptionA2AtFiniteClass (K := ℚ) κ Z c)
    (hcomplete : ∀ (T : Set (FiniteArchimedeanClass G)), T.Nonempty →
      (∀ c ∈ T, ∃ d ∈ T, c < d) →
      (#T < κ) →
      Nonempty (CompleteSpace (FiniteArchimedeanClass.TailQuotient T)))
    (htailfrac : ∀ (T : Set (FiniteArchimedeanClass G)), T.Nonempty →
      (∀ c ∈ T, ∃ d ∈ T, c < d) →
      (#T < κ) →
      Subring.fracSubring (HahnSeries.cardSuppLTTruncationIntegerPart
        (G := FiniteArchimedeanClass.tailSubmodule ℚ T)
        (R := R) (κ := κ) Z) = ⊤)
    (a : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := G) (R := R) (κ := κ) Z) : IsPrimal a := by
  apply isPrimal_of_finite_classes_and_limit_tail_conditions Z
  · intro y hy
    apply HahnSeries.Nonpositive.isPrimal_of_supportArchimedeanClasses_finite
      Z s (fun c ↦ (LM24.assumptionA1AtFiniteClass_iff s c).mp (hA1 c)) hA2 y
    rw [supportArchimedeanClasses_toNonpositiveRingHom]
    exact hy
  · exact hcomplete
  · exact htailfrac

end HahnSeries.CardSuppLTTruncationIntegerPart
