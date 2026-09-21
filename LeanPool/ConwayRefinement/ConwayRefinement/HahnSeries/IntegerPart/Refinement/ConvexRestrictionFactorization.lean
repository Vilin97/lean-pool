/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.CardinalTruncation
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.SubgroupSupport
public import Mathlib.Algebra.Group.Subgroup.Order
public import Mathlib.Algebra.Order.Archimedean.Class
public import Mathlib.Order.Interval.Set.OrdConnected

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Divisibility descends from a convex restriction

A divisor supported in a convex subgroup of the exponents divides a series as soon as it divides
the convex restriction: the discarded part has all its exponents nonpositive and outside the
subgroup, so multiplying it by the inverse of the divisor keeps every exponent nonpositive and
outside the subgroup, hence away from zero. The cofactor therefore stays in the integral part.

This is the step by which a refinement obtained after restricting at a support class is
transported back to the original divisibility.
-/

public noncomputable section

open scoped HahnSeries

namespace HahnSeries.ConvexRestriction

variable {G K : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [Field K]

private theorem add_nonpos_of_mem_of_nonpos_of_not_mem {C : AddSubgroup G}
    (hC : (C : Set G).OrdConnected) {a b : G}
    (ha : a ∈ C) (hb : b ≤ 0) (hbC : b ∉ C) : a + b ≤ 0 := by
  by_contra h
  have hab : 0 < a + b := lt_of_not_ge h
  apply hbC
  have hba : 0 < b + a := by simpa only [add_comm] using hab
  exact hC.out (C.neg_mem ha) C.zero_mem ⟨(neg_lt_iff_pos_add.mpr hba).le, hb⟩

/-- Adding an exponent in a convex subgroup to one outside it preserves the outside exponent's
Archimedean class. -/
private theorem archimedeanClass_add_eq_right_of_mem_of_not_mem {C : AddSubgroup G}
    (hC : (C : Set G).OrdConnected) {i j : G} (hi : i ∈ C) (hj : j ∉ C) :
    ArchimedeanClass.mk (i + j) = ArchimedeanClass.mk j := by
  apply ArchimedeanClass.mk_add_eq_mk_right
  rw [ArchimedeanClass.mk_lt_mk]
  intro n
  apply lt_of_not_ge
  intro hji
  have habsi : |i| ∈ C := abs_mem_iff.mpr hi
  have hni : n • |i| ∈ C := C.nsmul_mem habsi n
  have habsj : |j| ∈ C := hC.out C.zero_mem hni ⟨abs_nonneg j, hji⟩
  exact hj (abs_mem_iff.mp habsj)

open Classical in
/-- **Truncation-divisibility.** A nonzero divisor supported in a convex subgroup divides a
series with nonpositive support as soon as it divides the convex restriction, and the cofactor
stays in the integral part: nonpositive support with constant coefficient in the coefficient
subring. The discarded part has all exponents outside the subgroup, so dividing it by the
subgroup-supported divisor keeps every exponent nonpositive and nonzero. -/
private theorem exists_integral_cofactor {C : AddSubgroup G}
    (hC : (C : Set G).OrdConnected) (Z : Subring K)
    {q c w : K⟦G⟧} (hq : q.support ⊆ (C : Set G)) (hq0 : q ≠ 0)
    (hc : c.support ⊆ Set.Iic 0)
    (hw : w.support ⊆ Set.Iic 0) (hw0 : w.coeff 0 ∈ Z)
    (heq : HahnSeries.filter (· ∈ C) c = q * w) :
    ∃ w' : K⟦G⟧, w'.support ⊆ Set.Iic 0 ∧ w'.coeff 0 ∈ Z ∧ c = q * w' := by
  classical
  set r : K⟦G⟧ := HahnSeries.filter (fun g ↦ g ∉ C) c with hr
  have hsplit : HahnSeries.filter (· ∈ C) c + r = c := HahnSeries.filter_add_filter_not _ c
  have hrsupp : ∀ g ∈ r.support, g ≤ 0 ∧ g ∉ C := by
    intro g hg
    rw [hr, HahnSeries.support_filter] at hg
    exact ⟨hc hg.1, hg.2⟩
  -- The inverse of the divisor stays supported in the subgroup.
  have hone : (1 : K⟦G⟧).support ⊆ (C : Set G) := by
    intro g hg
    have hg0 : g = 0 := by
      simpa only [HahnSeries.support_one, Set.mem_singleton_iff] using hg
    exact hg0 ▸ C.zero_mem
  have hinv : (q⁻¹ : K⟦G⟧).support ⊆ (C : Set G) :=
    HahnSeries.support_subset_of_mul_eq (f := (1 : K⟦G⟧)) hq hq0 hone
      (mul_inv_cancel₀ hq0).symm
  -- The discarded part divided by the divisor keeps nonpositive, nonzero exponents.
  have hprod : ∀ g ∈ ((q⁻¹ : K⟦G⟧) * r).support, g ≤ 0 ∧ g ∉ C := by
    intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := HahnSeries.support_mul_subset hg
    obtain ⟨hb0, hbC⟩ := hrsupp b hb
    refine ⟨add_nonpos_of_mem_of_nonpos_of_not_mem hC (hinv ha) hb0 hbC, ?_⟩
    intro hab
    exact hbC (by simpa using C.sub_mem hab (hinv ha))
  refine ⟨w + q⁻¹ * r, ?_, ?_, ?_⟩
  · intro g hg
    rcases HahnSeries.support_add_subset _ _ hg with h | h
    · exact hw h
    · exact (hprod g h).1
  · have hzero : ((q⁻¹ : K⟦G⟧) * r).coeff 0 = 0 := by
      by_contra hne
      exact (hprod 0 ((HahnSeries.mem_support _ _).mpr hne)).2 C.zero_mem
    rw [HahnSeries.coeff_add, hzero, add_zero]
    exact hw0
  · rw [mul_add, ← heq, ← mul_assoc, mul_inv_cancel₀ hq0, one_mul, hsplit]

open Classical in
/-- **The class-block factorisation.** An integral series with a nonzero convex restriction is
that restriction times an integral series whose constant coefficient is one and whose remaining
exponents all lie outside the subgroup. An induction over support classes can therefore split an
integral series into blocks and, with primality of each block, conclude primality of the whole by
`IsPrimal.mul`. -/
private theorem exists_complementary_factor {C : AddSubgroup G}
    (hC : (C : Set G).OrdConnected) {b : K⟦G⟧} (hb : b.support ⊆ Set.Iic 0)
    (hne : HahnSeries.filter (· ∈ C) b ≠ 0) :
    ∃ w : K⟦G⟧, w.support ⊆ Set.Iic 0 ∧ w.coeff 0 = 1 ∧
      (∀ g ∈ w.support, g ≠ 0 → g ∉ C) ∧
      (∀ g ∈ w.support, g ≠ 0 →
        ArchimedeanClass.mk g ∈ ArchimedeanClass.mk '' b.support) ∧
      b = HahnSeries.filter (· ∈ C) b * w := by
  classical
  set q : K⟦G⟧ := HahnSeries.filter (· ∈ C) b with hq_def
  set r : K⟦G⟧ := HahnSeries.filter (fun g ↦ g ∉ C) b with hr_def
  have hsplit : q + r = b := HahnSeries.filter_add_filter_not _ b
  have hqC : q.support ⊆ (C : Set G) := by
    intro g hg
    rw [hq_def, HahnSeries.support_filter] at hg
    exact hg.2
  have hrsupp : ∀ g ∈ r.support, g ≤ 0 ∧ g ∉ C := by
    intro g hg
    rw [hr_def, HahnSeries.support_filter] at hg
    exact ⟨hb hg.1, hg.2⟩
  have hone : (1 : K⟦G⟧).support ⊆ (C : Set G) := by
    intro g hg
    have hg0 : g = 0 := by
      simpa only [HahnSeries.support_one, Set.mem_singleton_iff] using hg
    exact hg0 ▸ C.zero_mem
  have hinv : (q⁻¹ : K⟦G⟧).support ⊆ (C : Set G) :=
    HahnSeries.support_subset_of_mul_eq (f := (1 : K⟦G⟧)) hqC hne hone
      (mul_inv_cancel₀ hne).symm
  have hprod : ∀ g ∈ ((q⁻¹ : K⟦G⟧) * r).support, g ≤ 0 ∧ g ∉ C := by
    intro g hg
    obtain ⟨a, ha, c', hc', rfl⟩ := HahnSeries.support_mul_subset hg
    obtain ⟨hc0, hcC⟩ := hrsupp c' hc'
    refine ⟨add_nonpos_of_mem_of_nonpos_of_not_mem hC (hinv ha) hc0 hcC, ?_⟩
    intro hab
    exact hcC (by simpa using C.sub_mem hab (hinv ha))
  have hzero : ((q⁻¹ : K⟦G⟧) * r).coeff 0 = 0 := by
    by_contra hnz
    exact (hprod 0 ((HahnSeries.mem_support _ _).mpr hnz)).2 C.zero_mem
  refine ⟨1 + q⁻¹ * r, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases HahnSeries.support_add_subset _ _ hg with h | h
    · have hg0 : g = 0 := by
        simpa only [HahnSeries.support_one, Set.mem_singleton_iff] using h
      exact hg0 ▸ Set.mem_Iic.mpr le_rfl
    · exact Set.mem_Iic.mpr (hprod g h).1
  · rw [HahnSeries.coeff_add, HahnSeries.coeff_one, if_pos rfl, hzero, add_zero]
  · intro g hg hg0
    rcases HahnSeries.support_add_subset _ _ hg with h | h
    · exact absurd (by
        simpa only [HahnSeries.support_one, Set.mem_singleton_iff] using h) hg0
    · exact (hprod g h).2
  · intro g hg hg0
    rcases HahnSeries.support_add_subset _ _ hg with h | h
    · exact absurd (by
        simpa only [HahnSeries.support_one, Set.mem_singleton_iff] using h) hg0
    · obtain ⟨i, hi, j, hj, hij⟩ := HahnSeries.support_mul_subset h
      have hiC : i ∈ C := hinv hi
      have hjr : j ∈ r.support := hj
      have hjb : j ∈ b.support := by
        rw [hr_def, HahnSeries.support_filter] at hjr
        exact hjr.1
      have hjC : j ∉ C := (hrsupp j hj).2
      refine ⟨j, hjb, ?_⟩
      rw [← hij]
      exact (archimedeanClass_add_eq_right_of_mem_of_not_mem hC hiC hjC).symm
  · rw [mul_add, mul_one, ← mul_assoc, mul_inv_cancel₀ hne, one_mul, hsplit]

end HahnSeries.ConvexRestriction

namespace HahnSeries.CardSuppLTTruncationIntegerPart

open Cardinal

variable {G K : Type*} {κ : Cardinal}
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Field K] [Fact (aleph0 < κ)]

/-- Restrict a bounded truncation-integer-part series to an exponent subgroup. -/
def restrictToAddSubgroup (Z : Subring K) (C : AddSubgroup G)
    (x : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := K) (κ := κ) Z) :
    HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := K) (κ := κ) Z := by
  classical
  let xf : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ) :=
    ⟨HahnSeries.filter (· ∈ C) (x : K⟦G⟧),
      (HahnSeries.mem_cardSuppLTSubfield (Γ := G) (R := K) (κ := κ)).mpr
        ((HahnSeries.cardSupp_mono (HahnSeries.support_filter_subset _ _)).trans_lt x.1.2)⟩
  have hxmem := (HahnSeries.mem_cardSuppLTTruncationIntegerPart (Z := Z)).mp x.2
  exact ⟨xf, by
    rw [HahnSeries.mem_cardSuppLTTruncationIntegerPart]
    refine ⟨(HahnSeries.support_filter_subset _ _).trans hxmem.1, ?_⟩
    change (HahnSeries.filter (· ∈ C) (x : K⟦G⟧)).coeff 0 ∈ Z
    rw [HahnSeries.coeff_filter, if_pos C.zero_mem]
    exact hxmem.2⟩

open Classical in
/-- The subgroup restriction package has the expected underlying Hahn series. -/
@[simp]
theorem coe_restrictToAddSubgroup (Z : Subring K) (C : AddSubgroup G)
    (x : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := K) (κ := κ) Z) :
    (restrictToAddSubgroup Z C x : K⟦G⟧) = HahnSeries.filter (· ∈ C) (x : K⟦G⟧) :=
  (rfl)

open Classical in
/-- A nonzero bounded integer-part factor supported in a convex subgroup divides an ambient
bounded integer-part series as soon as it factors the convex restriction. -/
@[blueprint "lem:divisibility-from-convex-restriction"
  (phase := "Refinement over Archimedean classes")
  (title := "Divisibility from a convex restriction")
  (statement := /--
    Let $C$ be a convex subgroup of an ordered abelian group $G$, and let
    $q,w,x\in Z+K((G^{<0}))_\kappa$.  Suppose $q\ne0$,
    $\operatorname{supp}(q)\subseteq C$, and
    \[
      x_{\vert C}=qw.
    \]
    Then $q\mid x$ in $Z+K((G^{<0}))_\kappa$.
  -/)
  (proof := /--
    Divide $x$ by $q$ in the bounded Hahn field.  On $C$ the quotient is $w$.
    Outside $C$, convexity and nonpositivity keep every exponent of the
    quotient strictly negative; the constant coefficient is therefore the
    constant coefficient of $w$ and lies in $Z$.  Hence the quotient belongs
    to the bounded Hahn integer part.
  -/)]
theorem dvd_of_restriction_factorization
    (Z : Subring K) {C : AddSubgroup G} (hC : (C : Set G).OrdConnected)
    (q w x : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := G) (R := K) (κ := κ) Z)
    (hqsupp : (q : K⟦G⟧).support ⊆ (C : Set G)) (hq0 : q ≠ 0)
    (heq : HahnSeries.filter (· ∈ C) (x : K⟦G⟧) = (q * w : K⟦G⟧)) :
    q ∣ x := by
  have hqraw : (q : K⟦G⟧) ≠ 0 := fun h ↦ hq0 (Subtype.ext (Subtype.ext h))
  have hxmem := (HahnSeries.mem_cardSuppLTTruncationIntegerPart (Z := Z)).mp x.2
  have hwmem := (HahnSeries.mem_cardSuppLTTruncationIntegerPart (Z := Z)).mp w.2
  obtain ⟨v, hv, hv0, hxv⟩ :=
    HahnSeries.ConvexRestriction.exists_integral_cofactor hC Z hqsupp hqraw
      hxmem.1 hwmem.1 hwmem.2 heq
  let vf : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ) :=
    (x : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ)) /
      (q : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ))
  have hvraw : (vf : K⟦G⟧) = v := by
    change (x : K⟦G⟧) / (q : K⟦G⟧) = v
    rw [hxv, mul_comm, mul_div_assoc, div_self hqraw, mul_one]
  let vI : HahnSeries.cardSuppLTTruncationIntegerPart
      (G := G) (R := K) (κ := κ) Z := ⟨vf, by
    rw [HahnSeries.mem_cardSuppLTTruncationIntegerPart, hvraw]
    exact ⟨hv, hv0⟩⟩
  refine ⟨vI, ?_⟩
  apply Subtype.ext
  change (x : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ)) =
    (q : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ)) * vf
  have hqfield : (q : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ)) ≠ 0 :=
    fun h ↦ hq0 (Subtype.ext h)
  rw [mul_comm, div_mul_cancel₀ _ hqfield]

open Classical in
/-- Factor a bounded truncation-integer-part series by its nonzero restriction to a convex
exponent subgroup. The complementary factor remains bounded, has constant coefficient one, and
all its nonzero support exponents lie outside the subgroup in classes met by the original
support. -/
@[blueprint "lem:factorisation-by-convex-restriction"
  (phase := "Refinement over Archimedean classes")
  (title := "Factorisation by a convex restriction")
  (statement := /--
    Let $C$ be a convex subgroup of an ordered abelian group $G$, and let
    $b\in Z+K((G^{<0}))_\kappa$ have nonzero restriction $t=b_{\vert C}$.
    Then
    \[
      b=tw
    \]
    for some $w\in Z+K((G^{<0}))_\kappa$ with constant coefficient $1$.
    Every nonzero exponent in $\operatorname{supp}(w)$ lies outside $C$, and
    its Archimedean class is met by $\operatorname{supp}(b)$.
  -/)
  (proof := /--
    Divide $b$ by its nonzero restriction $t$ in the bounded Hahn field.  The
    quotient has constant coefficient $1$.  Convexity separates the discarded
    support from $C$; the Hahn inverse expansion shows that each class appearing
    in the quotient already appears in the support of $b$.  Thus the quotient
    remains in the bounded Hahn integer part and has the stated support.
  -/)]
theorem exists_factorization_by_restriction
    (Z : Subring K) {C : AddSubgroup G} (hC : (C : Set G).OrdConnected)
    (b : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := K) (κ := κ) Z)
    (hne : HahnSeries.filter (· ∈ C) (b : K⟦G⟧) ≠ 0) :
    ∃ t w : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := K) (κ := κ) Z,
      (t : K⟦G⟧) = HahnSeries.filter (· ∈ C) (b : K⟦G⟧) ∧
      b = t * w ∧
      (w : K⟦G⟧).coeff 0 = 1 ∧
      (∀ g ∈ (w : K⟦G⟧).support, g ≠ 0 → g ∉ C) ∧
      (∀ g ∈ (w : K⟦G⟧).support, g ≠ 0 →
        ArchimedeanClass.mk g ∈ ArchimedeanClass.mk '' (b : K⟦G⟧).support) := by
  have hbmem := (HahnSeries.mem_cardSuppLTTruncationIntegerPart (Z := Z)).mp b.2
  obtain ⟨wraw, hws, hw0, hwC, hwocc, hfac⟩ :=
    HahnSeries.ConvexRestriction.exists_complementary_factor hC hbmem.1 hne
  let tf : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ) :=
    ⟨HahnSeries.filter (· ∈ C) (b : K⟦G⟧),
      (HahnSeries.mem_cardSuppLTSubfield (Γ := G) (R := K) (κ := κ)).mpr
        ((HahnSeries.cardSupp_mono (HahnSeries.support_filter_subset _ _)).trans_lt b.1.2)⟩
  have ht0 : (tf : K⟦G⟧).coeff 0 = (b : K⟦G⟧).coeff 0 := by
    rw [HahnSeries.coeff_filter, if_pos C.zero_mem]
  let t : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := K) (κ := κ) Z :=
    ⟨tf, by
      rw [HahnSeries.mem_cardSuppLTTruncationIntegerPart]
      exact ⟨(HahnSeries.support_filter_subset _ _).trans hbmem.1, ht0 ▸ hbmem.2⟩⟩
  have htfield0 : (t : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ)) ≠ 0 := by
    intro ht
    apply hne
    exact congrArg (fun z : HahnSeries.CardSuppLTField
      (G := G) (R := K) (κ := κ) ↦ (z : K⟦G⟧)) ht
  let wf : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ) :=
    (b : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ)) /
      (t : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ))
  have hwraw : (wf : K⟦G⟧) = wraw := by
    change (b : K⟦G⟧) / (t : K⟦G⟧) = wraw
    rw [hfac, mul_comm, mul_div_assoc, div_self]
    · exact mul_one _
    · intro ht
      apply htfield0
      exact Subtype.ext ht
  let w : HahnSeries.cardSuppLTTruncationIntegerPart (G := G) (R := K) (κ := κ) Z :=
    ⟨wf, by
      rw [HahnSeries.mem_cardSuppLTTruncationIntegerPart, hwraw]
      exact ⟨hws, hw0 ▸ Z.one_mem⟩⟩
  refine ⟨t, w, rfl, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    change (b : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ)) =
      (t : HahnSeries.CardSuppLTField (G := G) (R := K) (κ := κ)) * wf
    rw [mul_comm, div_mul_cancel₀ _ htfield0]
  · simpa only [w, hwraw] using hw0
  · simpa only [w, hwraw] using hwC
  · simpa only [w, hwraw] using hwocc

end HahnSeries.CardSuppLTTruncationIntegerPart
