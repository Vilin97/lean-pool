/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.Common

/-! # Basic -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace VarianceBoundGoodScale

noncomputable section

/-!
# Basic scalar parameters for the Section 5.4 variance bound

This file owns the Section 5.4 variance exponent and the elementary scalar
weight used in the beta-weighted fluctuation sum.
-/

/-- The minimum quantity whose half is the exponent `β` in the Section 5.4
variance bound at a good scale. -/
noncomputable def section54VarianceBetaCore {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) : ℝ :=
  min (1 - hP4.sUpper - hP4.sLower)
    (min hP4.sUpper
      (min hP4.sLower
        (min (hP4.sUpper - (d : ℝ) / (hP4.xi : ℝ))
          (hP4.sLower - (d : ℝ) / (hP4.xi : ℝ)))))

/-- The exponent `β` used in
`l.variance.bound.good.scale.homogenization.scale`. -/
noncomputable def section54VarianceBeta {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) : ℝ :=
  section54VarianceBetaCore hP4 / 2

private theorem section54VarianceBetaCore_pos {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 < section54VarianceBetaCore hP4 := by
  have hgap : 0 < 1 - hP4.sUpper - hP4.sLower := by
    linarith [hP4.sum_lt_one]
  have hupper : 0 < hP4.sUpper := hP4.sUpper_pos
  have hlower : 0 < hP4.sLower := hP4.sLower_pos
  have hupper_gain : 0 < hP4.sUpper - (d : ℝ) / (hP4.xi : ℝ) := by
    linarith [hP4.dim_div_xi_lt_sUpper]
  have hlower_gain : 0 < hP4.sLower - (d : ℝ) / (hP4.xi : ℝ) := by
    linarith [hP4.dim_div_xi_lt_sLower]
  unfold section54VarianceBetaCore
  exact lt_min hgap
    (lt_min hupper (lt_min hlower (lt_min hupper_gain hlower_gain)))

/-- The Section 5.4 variance exponent is positive. -/
theorem section54VarianceBeta_pos {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 < section54VarianceBeta hP4 := by
  unfold section54VarianceBeta
  nlinarith [section54VarianceBetaCore_pos hP4]

/-- The Section 5.4 variance exponent is nonnegative. -/
theorem section54VarianceBeta_nonneg {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ section54VarianceBeta hP4 :=
  (section54VarianceBeta_pos hP4).le

private theorem section54VarianceBetaCore_le_sUpper {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    section54VarianceBetaCore hP4 ≤ hP4.sUpper := by
  unfold section54VarianceBetaCore
  exact (min_le_right _ _).trans (min_le_left _ _)

private theorem section54VarianceBetaCore_le_sLower {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    section54VarianceBetaCore hP4 ≤ hP4.sLower := by
  unfold section54VarianceBetaCore
  exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))

private theorem section54VarianceBetaCore_le_sUpper_sub_dim_div_xi {d : ℕ}
    [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    section54VarianceBetaCore hP4 ≤
      hP4.sUpper - (d : ℝ) / (hP4.xi : ℝ) := by
  unfold section54VarianceBetaCore
  exact (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))

private theorem section54VarianceBetaCore_le_sLower_sub_dim_div_xi {d : ℕ}
    [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    section54VarianceBetaCore hP4 ≤
      hP4.sLower - (d : ℝ) / (hP4.xi : ℝ) := by
  unfold section54VarianceBetaCore
  exact (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))

/-- The variance exponent is no larger than the upper regularity exponent. -/
theorem section54VarianceBeta_le_sUpper {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    section54VarianceBeta hP4 ≤ hP4.sUpper := by
  unfold section54VarianceBeta
  have hcore_nonneg : 0 ≤ section54VarianceBetaCore hP4 :=
    (section54VarianceBetaCore_pos hP4).le
  have hcore_le := section54VarianceBetaCore_le_sUpper hP4
  nlinarith

/-- The variance exponent is no larger than the lower regularity exponent. -/
theorem section54VarianceBeta_le_sLower {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    section54VarianceBeta hP4 ≤ hP4.sLower := by
  unfold section54VarianceBeta
  have hcore_nonneg : 0 ≤ section54VarianceBetaCore hP4 :=
    (section54VarianceBetaCore_pos hP4).le
  have hcore_le := section54VarianceBetaCore_le_sLower hP4
  nlinarith

/-- The variance exponent fits inside the upper positive-excess gain. -/
theorem section54VarianceBeta_le_sUpper_sub_dim_div_xi {d : ℕ}
    [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    section54VarianceBeta hP4 ≤
      hP4.sUpper - (d : ℝ) / (hP4.xi : ℝ) := by
  unfold section54VarianceBeta
  have hcore_nonneg : 0 ≤ section54VarianceBetaCore hP4 :=
    (section54VarianceBetaCore_pos hP4).le
  have hcore_le := section54VarianceBetaCore_le_sUpper_sub_dim_div_xi hP4
  nlinarith

/-- The variance exponent fits inside the lower positive-excess gain. -/
theorem section54VarianceBeta_le_sLower_sub_dim_div_xi {d : ℕ}
    [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    section54VarianceBeta hP4 ≤
      hP4.sLower - (d : ℝ) / (hP4.xi : ℝ) := by
  unfold section54VarianceBeta
  have hcore_nonneg : 0 ≤ section54VarianceBetaCore hP4 :=
    (section54VarianceBetaCore_pos hP4).le
  have hcore_le := section54VarianceBetaCore_le_sLower_sub_dim_div_xi hP4
  nlinarith

/-- The variance exponent is strictly below `d / 2`, which leaves room in the
geometric sums. -/
theorem section54VarianceBeta_lt_dim_div_two {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    section54VarianceBeta hP4 < (d : ℝ) / 2 := by
  have hbeta_le := section54VarianceBeta_le_sUpper hP4
  have hupper_lt : hP4.sUpper < 1 := hP4.sUpper_lt_one
  have hd_two : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hP4.two_le_dim
  nlinarith

/-- The beta weight in the variance bound. -/
noncomputable def varianceWeight (β : ℝ) (m j : ℕ) : ℝ :=
  Real.rpow (3 : ℝ) (-β * ((m - j : ℕ) : ℝ))

/-- The beta weight is nonnegative. -/
theorem varianceWeight_nonneg (β : ℝ) (m j : ℕ) :
    0 ≤ varianceWeight β m j := by
  unfold varianceWeight
  exact Real.rpow_nonneg (by norm_num) _

/-- At the top scale, the beta weight is one. -/
@[simp]
theorem varianceWeight_self (β : ℝ) (m : ℕ) :
    varianceWeight β m m = 1 := by
  unfold varianceWeight
  simp

/-- If `j` is above `m`, the `Nat`-truncated beta weight is one. -/
theorem varianceWeight_eq_one_of_le {β : ℝ} {m j : ℕ} (hmj : m ≤ j) :
    varianceWeight β m j = 1 := by
  unfold varianceWeight
  have hsub : m - j = 0 := Nat.sub_eq_zero_of_le hmj
  simp [hsub]

end

end VarianceBoundGoodScale
end Section54
end Ch05
end Book
end Homogenization
