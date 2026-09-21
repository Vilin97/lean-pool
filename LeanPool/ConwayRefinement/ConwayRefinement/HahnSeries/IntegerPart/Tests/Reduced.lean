/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Reduced
public import Mathlib.Algebra.Order.Group.Int

/-!
# API checks for LM24 reducedness

The constant series `3` is reduced because the relevant intersection is supported only at zero.
The two-term series `2 + t⁻¹` is not reduced: both zero and `-1` occur in the support before and
after subtracting one, but zero and a nonzero exponent have different Archimedean classes. This is
the Hahn-series analogue of LM24, Example 8.2.7's non-reduced omnific integer `ω + 2`.
-/

public noncomputable section

namespace Tests

open HahnSeries

/-- The constant nonpositive integer Hahn series `3`. -/
def reducedConstant : Nonpositive ℤ ℤ := Nonpositive.single 0 3 le_rfl

theorem reducedConstant_isReduced : Nonpositive.IsReduced reducedConstant := by
  refine Nonpositive.isReduced_of_support_inter_support_sub_one_subset ?_ ⊤ ?_
  · intro hzero
    have hcoeff := congrArg (fun x : Nonpositive ℤ ℤ ↦ (x : ℤ⟦ℤ⟧).coeff 0) hzero
    rw [show (reducedConstant : ℤ⟦ℤ⟧) = HahnSeries.single 0 3 by
      exact Nonpositive.coe_single 0 3 le_rfl] at hcoeff
    rw [HahnSeries.coeff_single_same] at hcoeff
    norm_num at hcoeff
  · rintro x ⟨hx, _⟩
    have hx0 : x = 0 := by
      apply support_single_subset (R := ℤ)
      rw [show (reducedConstant : ℤ⟦ℤ⟧) = HahnSeries.single 0 3 by
        exact Nonpositive.coe_single 0 3 le_rfl] at hx
      exact hx
    simp [hx0]

/-- The nonpositive Hahn series `2 + t⁻¹`. -/
def nonreducedTwoClass : Nonpositive ℤ ℤ :=
  Nonpositive.single 0 2 le_rfl + Nonpositive.single (-1) 1 (by omega)

theorem nonreducedTwoClass_not_isReduced : ¬Nonpositive.IsReduced nonreducedTwoClass := by
  intro h
  obtain ⟨_, c, hc⟩ := h.elim
  have hzero : ArchimedeanClass.mk (0 : ℤ) = c := hc ⟨by
    rw [HahnSeries.mem_support]
    rw [show (nonreducedTwoClass : ℤ⟦ℤ⟧) =
      HahnSeries.single 0 2 + HahnSeries.single (-1) 1 by
        simp [nonreducedTwoClass]]
    simp, by
    rw [HahnSeries.mem_support]
    rw [show ((nonreducedTwoClass - 1 : Nonpositive ℤ ℤ) : ℤ⟦ℤ⟧) =
      (HahnSeries.single 0 2 + HahnSeries.single (-1) 1) - 1 by
        simp [nonreducedTwoClass]]
    simp⟩
  have hneg : ArchimedeanClass.mk (-1 : ℤ) = c := hc ⟨by
    rw [HahnSeries.mem_support]
    rw [show (nonreducedTwoClass : ℤ⟦ℤ⟧) =
      HahnSeries.single 0 2 + HahnSeries.single (-1) 1 by
        simp [nonreducedTwoClass]]
    simp, by
    rw [HahnSeries.mem_support]
    rw [show ((nonreducedTwoClass - 1 : Nonpositive ℤ ℤ) : ℤ⟦ℤ⟧) =
      (HahnSeries.single 0 2 + HahnSeries.single (-1) 1) - 1 by
        simp [nonreducedTwoClass]]
    simp⟩
  have hcTop : c = ⊤ := hzero.symm.trans ArchimedeanClass.mk_zero
  have hnegTop : ArchimedeanClass.mk (-1 : ℤ) = ⊤ := hneg.trans hcTop
  have := ArchimedeanClass.mk_eq_top_iff.mp hnegTop
  omega

end Tests
