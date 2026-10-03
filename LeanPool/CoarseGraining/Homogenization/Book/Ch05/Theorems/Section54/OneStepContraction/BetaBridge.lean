/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.OneStepContraction.GoodScaleInputs
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.Basic

/-! # Beta Bridge -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace OneStepContraction

noncomputable section

/-!
# Beta bridge between Sections 5.3 and 5.4

The current Section 5.3 coarse-fluctuation proof uses half of the Section 5.4
variance exponent.  This file keeps that comparison local to the
one-step-contraction implementation slice.
-/

/-- The Section 5.3 and Section 5.4 beta cores are definitionally the same
minimum of manuscript exponent gaps. -/
theorem section53CoarseFluctuationBetaCore_eq_section54VarianceBetaCore
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBetaCore hP4 =
      VarianceBoundGoodScale.section54VarianceBetaCore hP4 := by
  rfl

/-- The current Section 5.3 beta is a fixed fraction of the Section 5.4
variance beta. -/
theorem section53CoarseFluctuationBeta_eq_quarter_section54VarianceBeta
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta hP4 =
      VarianceBoundGoodScale.section54VarianceBeta hP4 / 4 := by
  unfold Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta
    VarianceBoundGoodScale.section54VarianceBeta
  rw [section53CoarseFluctuationBetaCore_eq_section54VarianceBetaCore hP4]
  ring

/-- The Section 5.3 beta is positive. -/
theorem section53CoarseFluctuationBeta_pos
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 <
      Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta hP4 :=
  Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta_pos hP4

/-- The Section 5.3 beta is no larger than the Section 5.4 variance beta. -/
theorem section53CoarseFluctuationBeta_le_section54VarianceBeta
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta hP4 ≤
      VarianceBoundGoodScale.section54VarianceBeta hP4 := by
  have hrel := section53CoarseFluctuationBeta_eq_quarter_section54VarianceBeta hP4
  have h54_nonneg :
      0 ≤ VarianceBoundGoodScale.section54VarianceBeta hP4 :=
    VarianceBoundGoodScale.section54VarianceBeta_nonneg hP4
  nlinarith

/-- Section 5.4 variance weights are bounded by the slower Section 5.3
coarse-fluctuation weights. -/
theorem varianceWeight_section54VarianceBeta_le_section53CoarseFluctuationBeta
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m j : ℕ) :
    VarianceBoundGoodScale.varianceWeight
        (VarianceBoundGoodScale.section54VarianceBeta hP4) m j ≤
      VarianceBoundGoodScale.varianceWeight
        (Section53.JUpperBoundCoarseFluctuations.section53CoarseFluctuationBeta hP4)
        m j := by
  unfold VarianceBoundGoodScale.varianceWeight
  have hβ :=
    section53CoarseFluctuationBeta_le_section54VarianceBeta hP4
  have hk_nonneg : 0 ≤ ((m - j : ℕ) : ℝ) := by positivity
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) ?_
  nlinarith

end

end OneStepContraction
end Section54
end Ch05
end Book
end Homogenization
