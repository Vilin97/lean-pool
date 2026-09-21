/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Nonpositive
public import Mathlib.RingTheory.HahnSeries.Multiplication

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Factors supported in a convex exponent subgroup

If a product of two nonzero nonpositive Hahn series is supported in a convex subgroup of the
exponents, then both factors are supported there. Their lowest exponents add to the lowest
exponent of the product. Convexity first puts each lowest exponent in the subgroup, then puts
every later nonpositive support exponent there as well.
-/

universe u v

public noncomputable section

namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type v}
variable [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G] [Field K]

/-- Nonzero nonpositive factors of a series supported in a convex exponent subgroup are
themselves supported in that subgroup. -/
@[blueprint "lem:convex-support-of-factors"
  (phase := "Finitely many Archimedean classes")
  (title := "Convexity of the supports of factors")
  (statement := /--
    Let $H$ be a convex subgroup of a linearly ordered abelian group $G$.  If
    $a,b\in K((G^{\le0}))$ are nonzero and
    $\operatorname{supp}(ab)\subseteq H$, then
    \[
      \operatorname{supp}(a)\subseteq H,
      \qquad
      \operatorname{supp}(b)\subseteq H.
    \]
  -/)
  (proof := /--
    The least support exponents satisfy
    $\min\operatorname{supp}(ab)=\min\operatorname{supp}(a)+
    \min\operatorname{supp}(b)$.  This sum and zero lie in $H$, while both
    summands are nonpositive, so convexity puts each least exponent in $H$.
    Every later support exponent lies between its least exponent and zero and
    therefore also belongs to $H$.
  -/)]
theorem support_subset_convex_of_mul_support_subset
    {H : AddSubgroup G} (hH : (H : Set G).OrdConnected)
    {a b : Nonpositive G K} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (habH : ((a * b : Nonpositive G K) : K⟦G⟧).support ⊆ (H : Set G)) :
    (a : K⟦G⟧).support ⊆ (H : Set G) ∧ (b : K⟦G⟧).support ⊆ (H : Set G) := by
  have ha0' : (a : K⟦G⟧) ≠ 0 := fun h ↦ ha0 (Subtype.ext h)
  have hb0' : (b : K⟦G⟧) ≠ 0 := fun h ↦ hb0 (Subtype.ext h)
  have hab0' : ((a * b : Nonpositive G K) : K⟦G⟧) ≠ 0 := mul_ne_zero ha0' hb0'
  have habOrder : (a : K⟦G⟧).order + (b : K⟦G⟧).order ∈ H := by
    rw [← HahnSeries.order_mul_of_ne_zero (mul_ne_zero
      (HahnSeries.leadingCoeff_ne_zero.mpr ha0')
      (HahnSeries.leadingCoeff_ne_zero.mpr hb0'))]
    apply habH
    exact (HahnSeries.mem_support _ _).mpr
      (HahnSeries.coeff_order_eq_zero.not.mpr hab0')
  have haOrderMem : (a : K⟦G⟧).order ∈ (a : K⟦G⟧).support :=
    (HahnSeries.mem_support _ _).mpr (HahnSeries.coeff_order_eq_zero.not.mpr ha0')
  have hbOrderMem : (b : K⟦G⟧).order ∈ (b : K⟦G⟧).support :=
    (HahnSeries.mem_support _ _).mpr (HahnSeries.coeff_order_eq_zero.not.mpr hb0')
  have haOrderH : (a : K⟦G⟧).order ∈ H := by
    apply hH.out habOrder H.zero_mem
    constructor
    · simpa using add_le_add_left (support_subset b hbOrderMem) (a : K⟦G⟧).order
    · exact support_subset a haOrderMem
  have hbOrderH : (b : K⟦G⟧).order ∈ H := by
    apply hH.out habOrder H.zero_mem
    constructor
    · simpa [add_comm] using
        add_le_add_left (support_subset a haOrderMem) (b : K⟦G⟧).order
    · exact support_subset b hbOrderMem
  constructor
  · intro g hg
    apply hH.out haOrderH H.zero_mem
    exact ⟨HahnSeries.order_le_of_coeff_ne_zero ((HahnSeries.mem_support _ _).mp hg),
      support_subset a hg⟩
  · intro g hg
    apply hH.out hbOrderH H.zero_mem
    exact ⟨HahnSeries.order_le_of_coeff_ne_zero ((HahnSeries.mem_support _ _).mp hg),
      support_subset b hg⟩

end HahnSeries.Nonpositive
