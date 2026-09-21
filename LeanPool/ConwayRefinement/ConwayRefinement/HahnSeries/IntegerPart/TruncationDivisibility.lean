/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.ReducedDivisibility

/-!
# Divisibility and leading-class truncation

This module formalizes LM24, Proposition 8.2.1 at the leading class of a nonconstant
nonpositive Hahn series. The discarded tail is divisible by the original series: restrict the
divisor to its closed Archimedean ball, invert it in that Hahn field, and embed the inverse back.
If `x` is a discarded negative exponent and `y` belongs to the embedded inverse, then the class
of `x` strictly dominates that of `y`; consequently `x < -y` and `x + y < 0`.
-/

public noncomputable section

namespace HahnSeries.Nonpositive

open FiniteArchimedeanClass

variable {K G R : Type*}
variable [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
variable [Module K G] [IsOrderedModule K G]
variable [Field R]

private def closedBallEmbedding (c : FiniteArchimedeanClass G) : closedBall K c ↪o G where
  toFun := (↑)
  inj' := Subtype.val_injective
  map_rel_iff' := Iff.rfl

private theorem support_T_subset_closedBall (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) :
    ((T (K := K) c x : Nonpositive G R) : R⟦G⟧).support ⊆ closedBall K c := by
  intro g hg
  by_contra hnot
  exact hg (coeff_T_of_not_mem (K := K) c x hnot)

private theorem support_sub_T_disjoint_closedBall (c : FiniteArchimedeanClass G)
    (x : Nonpositive G R) :
    (((x - T (K := K) c x : Nonpositive G R) : R⟦G⟧).support) ∩
      closedBall K c = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro g hg
  rw [Set.mem_inter_iff] at hg
  obtain ⟨hgSupport, hgClosed⟩ := hg
  rw [HahnSeries.mem_support] at hgSupport
  change (((x : R⟦G⟧) - (T (K := K) c x : Nonpositive G R)).coeff g) ≠ 0 at hgSupport
  rw [HahnSeries.coeff_sub, coeff_T_of_mem (K := K) c x hgClosed,
    sub_self] at hgSupport
  exact hgSupport rfl

private theorem support_embeddedClosedBallInverse_add_tail_subset_Iio
    (c : FiniteArchimedeanClass G) (b x : Nonpositive G R) :
    ((HahnSeries.embDomain (closedBallEmbedding (K := K) c)
        (HahnSeries.restrictDomain (closedBallEmbedding (K := K) c) (b : R⟦G⟧))⁻¹) *
      ((x - T (K := K) c x : Nonpositive G R) : R⟦G⟧)).support ⊆ Set.Iio 0 := by
  intro g hg
  obtain ⟨y, hy, z, hz, rfl⟩ := HahnSeries.support_mul_subset hg
  obtain ⟨y', _, hy'⟩ := HahnSeries.support_embDomain_subset hy
  subst y
  have hyClosed : (y' : G) ∈ closedBall K c := y'.2
  have hzTail : z ∉ closedBall K c := by
    intro hzClosed
    have hdisjoint := support_sub_T_disjoint_closedBall (K := K) c x
    have : z ∈ (((x - T (K := K) c x : Nonpositive G R) : R⟦G⟧).support) ∩
        closedBall K c := ⟨hz, hzClosed⟩
    rw [hdisjoint] at this
    exact this
  have hzNonpos : z ≤ 0 := support_subset (x - T (K := K) c x) hz
  have hz0 : z ≠ 0 := fun h ↦ hzTail (h ▸ zero_mem _)
  by_cases hy0 : (y' : G) = 0
  · change (y' : G) + z < 0
    simpa [hy0] using lt_of_le_of_ne hzNonpos hz0
  have hclassZ : ArchimedeanClass.mk z < c.val := by
    have hnotle : ¬ c ≤ FiniteArchimedeanClass.mk z hz0 := by
      intro hle
      exact hzTail ((FiniteArchimedeanClass.mem_closedBall_iff K).mpr fun _ ↦ hle)
    exact not_le.mp hnotle
  have hclassY : c.val ≤ ArchimedeanClass.mk (y' : G) := by
    exact (FiniteArchimedeanClass.mem_closedBall_iff K).mp hyClosed hy0
  have hzyClass : ArchimedeanClass.mk z < ArchimedeanClass.mk (-(y' : G)) := by
    rw [ArchimedeanClass.mk_neg]
    exact hclassZ.trans_le hclassY
  have hzy : z < -(y' : G) :=
    ArchimedeanClass.lt_of_mk_lt_mk_of_nonpos hzyClass hzNonpos
  change (y' : G) + z < 0
  have := add_lt_add_left hzy (y' : G)
  simpa [add_comm] using this

/-- Every divisor of a nonzero nonconstant series is supported in the closed ball at the
dividend's leading Archimedean class. Equivalently, truncation at that class fixes the divisor.
This is the factor-control observation used in the first paragraph of LM24, Proposition 9.2.2. -/
theorem T_leadingClass_of_dvd (b : Nonpositive G R) (hb0 : b ≠ 0)
    (horder : (b : R⟦G⟧).order ≠ 0) {a : Nonpositive G R} (ha : a ∣ b) :
    T (K := K) (leadingClass b horder) a = a := by
  obtain ⟨q, hb⟩ := ha
  have ha0 : a ≠ 0 := by
    intro hzero
    apply hb0
    rw [hb, hzero, zero_mul]
  have hq0 : q ≠ 0 := by
    intro hzero
    apply hb0
    rw [hb, hzero, mul_zero]
  apply Subtype.ext
  ext g
  by_cases hcoeff : (a : R⟦G⟧).coeff g = 0
  · by_cases hg : g ∈ closedBall K (leadingClass b horder)
    · rw [coeff_T_of_mem _ a hg, hcoeff]
    · rw [coeff_T_of_not_mem _ a hg, hcoeff]
  · rw [coeff_T_of_mem]
    apply (FiniteArchimedeanClass.mem_closedBall_iff K).mpr
    intro hg0
    apply Subtype.coe_le_coe.mp
    rw [leadingClass_val, FiniteArchimedeanClass.val_mk]
    have haOrderNonpos : (a : R⟦G⟧).order ≤ 0 := by
      exact support_subset a
        ((HahnSeries.mem_support _ _).mpr (HahnSeries.coeff_order_eq_zero.not.mpr
          (fun h ↦ ha0 (Subtype.ext h))))
    have hqOrderNonpos : (q : R⟦G⟧).order ≤ 0 := by
      exact support_subset q
        ((HahnSeries.mem_support _ _).mpr (HahnSeries.coeff_order_eq_zero.not.mpr
          (fun h ↦ hq0 (Subtype.ext h))))
    have hsumLe : (a : R⟦G⟧).order + (q : R⟦G⟧).order ≤
        (a : R⟦G⟧).order := by
      simpa using add_le_add_left hqOrderNonpos (a : R⟦G⟧).order
    have haOrderLe : (a : R⟦G⟧).order ≤ g :=
      HahnSeries.order_le_of_coeff_ne_zero hcoeff
    have hgNonpos : g ≤ 0 :=
      support_subset a ((HahnSeries.mem_support _ _).mpr hcoeff)
    have horderMul : ((a * q : Nonpositive G R) : R⟦G⟧).order =
        (a : R⟦G⟧).order + (q : R⟦G⟧).order := by
      exact HahnSeries.order_mul (fun h ↦ ha0 (Subtype.ext h))
        (fun h ↦ hq0 (Subtype.ext h))
    rw [hb, horderMul]
    have hsumNonzero : (a : R⟦G⟧).order + (q : R⟦G⟧).order ≠ 0 := by
      rw [← horderMul, ← hb]
      exact horder
    simpa [ArchimedeanClass.mk_eq_top_iff.not.mpr hsumNonzero] using
      ArchimedeanClass.min_le_mk_of_le_of_le (hsumLe.trans haOrderLe) hgNonpos

/-- Divisibility by a nonzero series fixed by a closed-class truncation can be tested after that
truncation. The inverse is formed in the Hahn field on the closed ball and embedded back. -/
theorem dvd_iff_dvd_T_of_fixed (sigma : FiniteArchimedeanClass G)
    (b : Nonpositive G R) (hb0 : b ≠ 0) (hbFixed : T (K := K) sigma b = b)
    (c : Nonpositive G R) :
    b ∣ c ↔ b ∣ T (K := K) sigma c := by
  let f := closedBallEmbedding (K := K) sigma
  let br : R⟦closedBall K sigma⟧ := HahnSeries.restrictDomain f (b : R⟦G⟧)
  have hbSupport : (b : R⟦G⟧).support ⊆ Set.range f := by
    rw [← hbFixed]
    intro g hg
    exact ⟨⟨g, support_T_subset_closedBall (K := K) sigma b hg⟩, rfl⟩
  have hembBr : HahnSeries.embDomain f br = (b : R⟦G⟧) :=
    HahnSeries.embDomain_restrictDomain f (b : R⟦G⟧) hbSupport
  have hbr0 : br ≠ 0 := by
    intro hzero
    apply hb0
    apply Subtype.ext
    rw [← hembBr, hzero]
    exact HahnSeries.embDomain_zero
  let qFull : R⟦G⟧ := HahnSeries.embDomain f br⁻¹
  have hbq : (b : R⟦G⟧) * qFull = 1 := by
    rw [← hembBr]
    change HahnSeries.embDomain f br * HahnSeries.embDomain f br⁻¹ = 1
    rw [← HahnSeries.embDomain_mul]
    · rw [mul_inv_cancel₀ hbr0, HahnSeries.embDomain_one]
      rfl
    · intro x y
      rfl
  constructor
  · rintro ⟨e, hce⟩
    refine ⟨T (K := K) sigma e, ?_⟩
    calc
      T (K := K) sigma c = T (K := K) sigma (b * e) := by rw [hce]
      _ = T (K := K) sigma b * T (K := K) sigma e :=
        (T (K := K) sigma).map_mul b e
      _ = b * T (K := K) sigma e := by rw [hbFixed]
  · rintro ⟨e, hTe⟩
    let tail : Nonpositive G R := c - T (K := K) sigma c
    let qTail : Nonpositive G R := ⟨qFull * (tail : R⟦G⟧), by
      intro g hg
      exact (support_embeddedClosedBallInverse_add_tail_subset_Iio sigma b c hg).le⟩
    refine ⟨e + qTail, ?_⟩
    apply Subtype.ext
    change (c : R⟦G⟧) =
      (b : R⟦G⟧) * ((e : R⟦G⟧) + qFull * (tail : R⟦G⟧))
    rw [mul_add, ← mul_assoc, hbq, one_mul]
    change (c : R⟦G⟧) = (b : R⟦G⟧) * (e : R⟦G⟧) +
      ((c : R⟦G⟧) - (T (K := K) sigma c : Nonpositive G R))
    have hTeCoe : ((T (K := K) sigma c : Nonpositive G R) : R⟦G⟧) =
        (b : R⟦G⟧) * (e : R⟦G⟧) := congrArg Subtype.val hTe
    rw [← hTeCoe]
    abel

/-- LM24, Proposition 8.2.1 at the lowest nonzero exponent's Archimedean class. -/
theorem dvd_iff_dvd_T_leadingClass (b : Nonpositive G R) (hb0 : b ≠ 0)
    (horder : (b : R⟦G⟧).order ≠ 0) (c : Nonpositive G R) :
    b ∣ c ↔ b ∣ T (K := K) (leadingClass b horder) c :=
  dvd_iff_dvd_T_of_fixed (leadingClass b horder) b hb0 (T_leadingClass b horder) c

/-- LM24, Proposition 8.2.8 for a reduced series with nonzero lowest exponent: reduction at its
leading Archimedean class preserves exactly the multiples of the series. -/
theorem dvd_iff_dvd_rho_leadingClass
    (u : HahnEmbedding.ArchimedeanStrata K G) (b : Nonpositive G R) (hb0 : b ≠ 0)
    (horder : (b : R⟦G⟧).order ≠ 0) (hbReduced : IsReduced b)
    (c : Nonpositive G R) :
    b ∣ c ↔ b ∣ rho u (leadingClass b horder) c :=
  (dvd_iff_dvd_T_leadingClass b hb0 horder c).trans
    (dvd_T_iff_dvd_rho_leadingClass u b hb0 horder hbReduced c)

end HahnSeries.Nonpositive
