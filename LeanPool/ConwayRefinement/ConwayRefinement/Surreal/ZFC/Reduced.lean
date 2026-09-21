/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ZFC.NormalForm
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ZFC.OmnificInteger
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Reduced
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.CardinalIntegerPart
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.SignedFull

/-!
# Class-coded reducedness and the signed Hahn orientation

The unsigned Conway support formula is equivalent to LM24 reducedness of the signed nonpositive
Hahn series. Negating an exponent preserves its additive Archimedean class, including the zero
class. Consequently the native reducedness predicate on class-coded omnific integers is exactly
the reducedness hypothesis used by the signed Hahn-series theorems.
-/

universe u

public noncomputable section

namespace Surreal.OmnificInteger

/-- LM24 reducedness in the signed orientation is exactly the unsigned Conway-support formula. -/
theorem isReduced_toSignedNonpositiveHahn_iff_support (x : OmnificInteger.{u}) :
    HahnSeries.Nonpositive.IsReduced x.toSignedNonpositiveHahn ↔
      (x : Surreal.{u}) ≠ 0 ∧ ∃ c : ArchimedeanClass Surreal.{u},
        (x : Surreal.{u}).support ∩ ((x : Surreal.{u}) - 1).support ⊆
          {i | ArchimedeanClass.mk i = c} := by
  have hsub : ((x.toSignedNonpositiveHahn - 1 : HahnSeries.Nonpositive Surreal ℝ) :
      HahnSeries Surreal ℝ) = ((x : Surreal) - 1).toSignedFullHahnSeries := by
    calc
      _ = (x.toSignedNonpositiveHahn : HahnSeries Surreal ℝ) - 1 := rfl
      _ = (x : Surreal).toSignedFullHahnSeries - 1 := by
        rw [coe_toSignedNonpositiveHahn]
      _ = ((x : Surreal) - 1).toSignedFullHahnSeries := by
        rw [Surreal.toSignedFullHahnSeries_sub]
        congr 1
        simpa using (Surreal.toSignedFullHahnSeries_realCast (1 : ℝ)).symm
  have hmem (i : Surreal.{u}) :
      i ∈ (x.toSignedNonpositiveHahn : HahnSeries Surreal ℝ).support ↔
        -i ∈ (x : Surreal).support := by
    rw [coe_toSignedNonpositiveHahn, Surreal.mem_support_toSignedFullHahnSeries]
  have hmemSub (i : Surreal.{u}) :
      i ∈ ((x.toSignedNonpositiveHahn - 1 : HahnSeries.Nonpositive Surreal ℝ) :
        HahnSeries Surreal ℝ).support ↔ -i ∈ ((x : Surreal) - 1).support := by
    rw [hsub, Surreal.mem_support_toSignedFullHahnSeries]
  have hzero : x.toSignedNonpositiveHahn ≠ 0 ↔ (x : Surreal) ≠ 0 := by
    constructor
    · intro hx h
      apply hx
      apply Subtype.ext
      rw [coe_toSignedNonpositiveHahn, h, Surreal.toSignedFullHahnSeries_zero]
      rfl
    · intro hx h
      apply hx
      apply Surreal.toSignedFullHahnSeries_injective
      have hraw := congrArg (fun q : HahnSeries.Nonpositive Surreal ℝ ↦
        (q : HahnSeries Surreal ℝ)) h
      rw [coe_toSignedNonpositiveHahn] at hraw
      exact hraw.trans Surreal.toSignedFullHahnSeries_zero.symm
  constructor
  · intro hx
    obtain ⟨hx0, c, hc⟩ := hx.elim
    refine ⟨hzero.mp hx0, c, ?_⟩
    intro i hi
    have hsigned : -i ∈ (x.toSignedNonpositiveHahn : HahnSeries Surreal ℝ).support ∩
        ((x.toSignedNonpositiveHahn - 1 : HahnSeries.Nonpositive Surreal ℝ) :
          HahnSeries Surreal ℝ).support := by
      constructor
      · exact (hmem (-i)).2 (by simpa only [neg_neg] using hi.1)
      · exact (hmemSub (-i)).2 (by simpa only [neg_neg] using hi.2)
    simpa only [Set.mem_setOf_eq, ArchimedeanClass.mk_neg] using hc hsigned
  · rintro ⟨hx0, c, hc⟩
    refine HahnSeries.Nonpositive.isReduced_of_support_inter_support_sub_one_subset
      (hzero.mpr hx0) c ?_
    intro i hi
    have hunsigned : -i ∈ (x : Surreal).support ∩ ((x : Surreal) - 1).support :=
      ⟨(hmem i).1 hi.1, (hmemSub i).1 hi.2⟩
    simpa only [Set.mem_setOf_eq, ArchimedeanClass.mk_neg] using hc hunsigned

end Surreal.OmnificInteger

namespace ZFSet.Surreal.OmnificInteger

/-- Native class-coded reducedness is equivalent to the signed Hahn reducedness hypothesis. -/
theorem isReduced_iff_toSignedNonpositiveHahn (x : OmnificInteger.{u}) :
    ZFSet.Surreal.IsReduced (x : ZFSet.Surreal.{u}) ↔
      HahnSeries.Nonpositive.IsReduced (ringEquiv x).toSignedNonpositiveHahn := by
  rw [ZFSet.Surreal.isReduced_iff_toSurreal,
    _root_.Surreal.OmnificInteger.isReduced_toSignedNonpositiveHahn_iff_support]
  simp only [ringEquiv_apply, coe_toOmnificInteger]

end ZFSet.Surreal.OmnificInteger
