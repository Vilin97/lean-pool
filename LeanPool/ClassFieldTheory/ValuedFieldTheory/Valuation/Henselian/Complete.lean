/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.Complete
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaExtension
/-!
# Complete nonarchimedean absolute values are Henselian

The localization reduction in the ramification-localization argument passes to the completion
of a rank-one nonarchimedean absolute value.  the factorization form of Hensel's lemma already supplies the
degree-controlled factorization statement for every complete
nonarchimedean absolute value.  This file records the direct the primitive factorization definition
consequence used in the henselianity criterion.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

/-- A complete nonarchimedean absolute value satisfies the factorization
form of Hensel's lemma from the primitive factorization definition. -/
theorem henselFactorization_of_complete
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) :
    ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch) := by
  intro f gbar hbar hprimitive hfactor hcoprime
  obtain ⟨G, H, hGH, hGdegree, hGresidue, hHresidue⟩ :=
    henselFactorization_complete_exists_factorization
      v hcomplete hnonarch hprimitive hfactor hcoprime
  have hproduct : gbar * hbar ≠ 0 := by
    rw [← hfactor]
    exact hprimitive
  have hgbar : gbar ≠ 0 := left_ne_zero_of_mul hproduct
  have hhbar : hbar ≠ 0 := right_ne_zero_of_mul hproduct
  have hG : G ≠ 0 := by
    intro hzero
    subst G
    simp at hGresidue
    exact hgbar hGresidue.symm
  have hH : H ≠ 0 := by
    intro hzero
    subst H
    simp at hHresidue
    exact hhbar hHresidue.symm
  have hdegree :
      H.natDegree = f.natDegree - gbar.natDegree := by
    rw [hGH, Polynomial.natDegree_mul hG hH, hGdegree,
      Nat.add_sub_cancel_left]
  exact ⟨G, H, hGdegree, hdegree.le, hGH, hGresidue, hHresidue⟩

/-- A complete nonarchimedean absolute value is Henselian in the exact sense
of the primitive factorization definition. -/
theorem henselianValuation_of_complete
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v) :
    ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (absoluteValueValuationSubring
        v hnonarch).valuation := by
  rw [henselianValuation_iff_henselFactorization v hnonarch]
  exact henselFactorization_of_complete v hcomplete hnonarch

end Valuations
end AlgebraicNumberTheory

end
