/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Refinement.LimitTailRefinement
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Refinement.ConvexRestrictionFactorization
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Order.ArchimedeanBall

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Factoring at a support class in a tail quotient

After regrouping along a common tail, a class met by the support determines a nonzero convex
restriction. Factoring off that restriction leaves an integral cofactor whose nonzero support
classes have strictly smaller order type.
-/

public noncomputable section

open Cardinal
open scoped HahnSeries

universe u v

namespace HahnSeries.CardSuppLTTruncationIntegerPart

open Classical in
/-- Factoring at a tail-quotient class met by the support strictly lowers the order type of the
nonzero support classes of the complementary factor. -/
@[blueprint "lem:support-class-factorisation"
  (phase := "Refinement over Archimedean classes")
  (title := "Factorisation at a quotient Archimedean class")
  (statement := /--
    Let $T$ be a set of nonzero Archimedean classes of an ordered rational
    vector space $G$, and let $q$ be a nonzero Archimedean class of the quotient
    of $G$ by the common tail below $T$.  Suppose the support of
    $b\in Z+R((G^{<0}))_\kappa$ meets $q$ and the restriction $t$ of $b$ to
    the inverse image of the closed ball of $q$ is nonzero.  Then
    \[
      b=tw,
    \]
    where the order type of the nonzero Archimedean support classes of $w$ is
    strictly smaller than that of $b$.
  -/)
  (proof := /--
    By \ref{lem:factorisation-by-convex-restriction}, the retained restriction
    gives a factorisation $b=tw$, and every nonzero class met by $w$ is also met
    by $b$.  The quotient class $q$ and
    \ref{lem:tail-quotient-class-bounds-support-classes} bound all those classes
    strictly below one class met by $b$.  The strict order-type inequality
    follows from \ref{lem:support-class-order-type-strict-decrease}.
  -/)]
theorem exists_factor_with_smaller_support_class_orderType
    {G : Type u} {R : Type v}
    [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [Module ℚ G] [PosSMulMono ℚ G]
    [Field R]
    {κ : Cardinal} [Fact (ℵ₀ < κ)]
    (Z : Subring R)
    (T : Set (FiniteArchimedeanClass G))
    (q : FiniteArchimedeanClass (FiniteArchimedeanClass.TailQuotient T))
    (b : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := G) (R := R) (κ := κ) Z)
    (hqocc : q.1 ∈ ArchimedeanClass.mk ''
      (Submodule.Quotient.mk (p := FiniteArchimedeanClass.tailSubmodule ℚ T) ''
        (b : HahnSeries G R).support))
    (hne : HahnSeries.filter
      (· ∈ (FiniteArchimedeanClass.closedBallAddSubgroup q).comap
        (FiniteArchimedeanClass.tailSubmodule ℚ T).mkQ.toAddMonoidHom)
      (b : HahnSeries G R) ≠ 0) :
    ∃ t w : HahnSeries.cardSuppLTTruncationIntegerPart
        (G := G) (R := R) (κ := κ) Z,
      (t : HahnSeries G R) = HahnSeries.filter
        (· ∈ (FiniteArchimedeanClass.closedBallAddSubgroup q).comap
          (FiniteArchimedeanClass.tailSubmodule ℚ T).mkQ.toAddMonoidHom)
        (b : HahnSeries G R) ∧
      b = t * w ∧
      (HahnSeries.Nonpositive.isPWO_nonzeroSupportArchimedeanClasses
          (toNonpositiveRingHom Z w)).orderType <
      (HahnSeries.Nonpositive.isPWO_nonzeroSupportArchimedeanClasses
          (toNonpositiveRingHom Z b)).orderType := by
  classical
  let P := FiniteArchimedeanClass.tailSubmodule ℚ T
  let C : AddSubgroup G :=
    (FiniteArchimedeanClass.closedBallAddSubgroup q).comap P.mkQ.toAddMonoidHom
  let : C.IsConvex := by
    constructor
    exact (FiniteArchimedeanClass.closedBall_ordConnected q).preimage_mono
      (fun _ _ h ↦ ConvexQuotient.mk_le_mk h)
  obtain ⟨t, w, ht, hfac, _hw0, hwC, hwocc⟩ :=
    exists_factorization_by_restriction Z
      (inferInstance : C.IsConvex).ordConnected b hne
  refine ⟨t, w, ht, hfac, ?_⟩
  let bN := toNonpositiveRingHom Z b
  let wN := toNonpositiveRingHom Z w
  obtain ⟨c, hc, hsub⟩ :=
    HahnSeries.exists_nonzeroSupportClass_bound_tailQuotient
      T q (b : HahnSeries G R).support (w : HahnSeries G R).support hqocc
      (by
        intro g hg hg0
        exact hwC g hg hg0)
      hwocc
  have hc' : c ∈ bN.nonzeroSupportArchimedeanClasses := by
    rw [HahnSeries.Nonpositive.mem_nonzeroSupportArchimedeanClasses_iff]
    obtain ⟨g, ⟨hg, hg0⟩, hgc⟩ := hc
    exact ⟨g, by simpa only [bN, coe_toNonpositiveRingHom] using hg,
      by simpa only [Set.mem_singleton_iff] using hg0, hgc⟩
  apply HahnSeries.Nonpositive.orderType_nonzeroSupportArchimedeanClasses_lt bN wN hc'
  intro d hd
  rw [HahnSeries.Nonpositive.mem_nonzeroSupportArchimedeanClasses_iff] at hd
  obtain ⟨g, hg, hg0, hgd⟩ := hd
  have hg' : g ∈ (w : HahnSeries G R).support := by
    simpa only [wN, coe_toNonpositiveRingHom] using hg
  have hd' := hsub ⟨g, ⟨hg', by simpa only [Set.mem_singleton_iff] using hg0⟩, hgd⟩
  refine ⟨?_, hd'.2⟩
  rw [HahnSeries.Nonpositive.mem_nonzeroSupportArchimedeanClasses_iff]
  obtain ⟨z, ⟨hz, hz0⟩, hzd⟩ := hd'.1
  exact ⟨z, by simpa only [bN, coe_toNonpositiveRingHom] using hz,
    by simpa only [Set.mem_singleton_iff] using hz0, hzd⟩

end HahnSeries.CardSuppLTTruncationIntegerPart
