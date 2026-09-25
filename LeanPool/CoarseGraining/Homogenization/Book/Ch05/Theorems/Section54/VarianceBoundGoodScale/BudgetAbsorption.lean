/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.RefinedAssembly
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.VarianceBoundGoodScale.GeometricSum
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section52.Coefficients.RootCoeff

/-! # Budget Absorption -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace VarianceBoundGoodScale

open scoped BigOperators

noncomputable section

/-!
# Absorbing the refined variance budgets

This file controls the deterministic scalar budgets that remain after the
finite-probe assembly.  The key point is that the Rosenthal descendant-average
coefficient is a Section 5.2 large-scale root coefficient with exponent
`β + d / ξ`.
-/

private theorem widetildeThetaAtScale_zero_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ widetildeThetaAtScale P 0 hP4 := by
  simp [widetildeThetaAtScale, Ch04.widetildeThetaAtScale]
  exact mul_nonneg
    (Ch04.LambdaMomentAtScale_nonneg P 0 hP4.xi hP4.sUpper_pos)
    (Ch04.lambdaInvMomentAtScale_nonneg P 0 hP4.xi hP4.sLower_pos)

/-- Coordinate-probe descendant-average budgets are nonnegative. -/
theorem coordinateProbeRefinedDescendantAverageK_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta) (j : ℕ) :
    0 ≤ coordinateProbeRefinedDescendantAverageK hP4 delta j := by
  have htheta : 0 ≤ widetildeThetaAtScale P 0 hP4 :=
    widetildeThetaAtScale_zero_nonneg hP4
  have hK0 : 0 ≤ 2 * ((1 + delta) * widetildeThetaAtScale P 0 hP4) := by
    have hfactor : 0 ≤ 1 + delta := by linarith
    exact mul_nonneg (by norm_num) (mul_nonneg hfactor htheta)
  have hcard_nonneg :
      0 ≤ ((descendantsAtScale (originCube d (j : ℤ)) 0).card : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have hcard_inv_nonneg :
      0 ≤ ((descendantsAtScale (originCube d (j : ℤ)) 0).card : ℝ)⁻¹ :=
    inv_nonneg.mpr hcard_nonneg
  have hcard_rpow_nonneg :
      0 ≤ ((descendantsAtScale (originCube d (j : ℤ)) 0).card : ℝ) ^
          (1 / (hP4.xi : ℝ)) :=
    Real.rpow_nonneg hcard_nonneg _
  have hsqrt_nonneg :
      0 ≤ Real.sqrt ((descendantsAtScale (originCube d (j : ℤ)) 0).card : ℝ) :=
    Real.sqrt_nonneg _
  have hLp_nonneg : 0 ≤ Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi := by
    unfold Ch04.rosenthalDescendantsAtScaleLpConst
    positivity
  have hSqrt_nonneg : 0 ≤ Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi := by
    unfold Ch04.rosenthalDescendantsAtScaleSqrtConst Ch04.rosenthalBennettIntegralConst
      IndependentSums.rosenthalBennettIntegralConst
    positivity
  unfold coordinateProbeRefinedDescendantAverageK
  exact mul_nonneg hcard_inv_nonneg
    (add_nonneg
      (mul_nonneg (mul_nonneg hLp_nonneg hcard_rpow_nonneg) hK0)
      (mul_nonneg (mul_nonneg hSqrt_nonneg hsqrt_nonneg) hK0))

/-- Pair-probe descendant-average budgets are nonnegative. -/
theorem pairProbeRefinedDescendantAverageK_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta) (j : ℕ) :
    0 ≤ pairProbeRefinedDescendantAverageK hP4 delta j := by
  have htheta : 0 ≤ widetildeThetaAtScale P 0 hP4 :=
    widetildeThetaAtScale_zero_nonneg hP4
  have hK0 : 0 ≤ 8 * ((1 + delta) * widetildeThetaAtScale P 0 hP4) := by
    have hfactor : 0 ≤ 1 + delta := by linarith
    exact mul_nonneg (by norm_num) (mul_nonneg hfactor htheta)
  have hcard_nonneg :
      0 ≤ ((descendantsAtScale (originCube d (j : ℤ)) 0).card : ℝ) := by
    exact_mod_cast Nat.zero_le _
  have hcard_inv_nonneg :
      0 ≤ ((descendantsAtScale (originCube d (j : ℤ)) 0).card : ℝ)⁻¹ :=
    inv_nonneg.mpr hcard_nonneg
  have hcard_rpow_nonneg :
      0 ≤ ((descendantsAtScale (originCube d (j : ℤ)) 0).card : ℝ) ^
          (1 / (hP4.xi : ℝ)) :=
    Real.rpow_nonneg hcard_nonneg _
  have hsqrt_nonneg :
      0 ≤ Real.sqrt ((descendantsAtScale (originCube d (j : ℤ)) 0).card : ℝ) :=
    Real.sqrt_nonneg _
  have hLp_nonneg : 0 ≤ Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi := by
    unfold Ch04.rosenthalDescendantsAtScaleLpConst
    positivity
  have hSqrt_nonneg : 0 ≤ Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi := by
    unfold Ch04.rosenthalDescendantsAtScaleSqrtConst Ch04.rosenthalBennettIntegralConst
      IndependentSums.rosenthalBennettIntegralConst
    positivity
  unfold pairProbeRefinedDescendantAverageK
  exact mul_nonneg hcard_inv_nonneg
    (add_nonneg
      (mul_nonneg (mul_nonneg hLp_nonneg hcard_rpow_nonneg) hK0)
      (mul_nonneg (mul_nonneg hSqrt_nonneg hsqrt_nonneg) hK0))

/-- Coordinate probes have Euclidean square norm `1`. -/
@[simp]
theorem dotProduct_coordinateProbe_self
    {d : ℕ} (α : BlockCoord d) :
    dotProduct (fullBlockCoordinateProbe α) (fullBlockCoordinateProbe α) = 1 := by
  rw [← fullBlockQuadratic_one]
  simp

private theorem one_fullBlockMat_isSymm {d : ℕ} :
    (1 : FullBlockMat d).IsSymm := by
  exact Matrix.isSymm_one

/-- Plus probes have Euclidean square norm at most `4`. -/
theorem dotProduct_plusProbe_self_le_four
    {d : ℕ} (α β : BlockCoord d) :
    dotProduct (fullBlockPlusProbe α β) (fullBlockPlusProbe α β) ≤ 4 := by
  by_cases hαβ : α = β
  · subst β
    rw [← fullBlockQuadratic_one]
    rw [fullBlockQuadratic_plusProbe_self]
    simp
  · rw [← fullBlockQuadratic_one]
    rw [fullBlockQuadratic_plusProbe_of_ne one_fullBlockMat_isSymm hαβ]
    norm_num [Matrix.one_apply, hαβ, Ne.symm hαβ]

/-- Minus probes have Euclidean square norm at most `4`. -/
theorem dotProduct_minusProbe_self_le_four
    {d : ℕ} (α β : BlockCoord d) :
    dotProduct (fullBlockMinusProbe α β) (fullBlockMinusProbe α β) ≤ 4 := by
  by_cases hαβ : α = β
  · subst β
    rw [← fullBlockQuadratic_one]
    rw [fullBlockQuadratic_minusProbe_self]
    norm_num
  · rw [← fullBlockQuadratic_one]
    rw [fullBlockQuadratic_minusProbe_of_ne one_fullBlockMat_isSymm hαβ]
    norm_num [Matrix.one_apply, hαβ, Ne.symm hαβ]

/-- A scalar variance budget with probe square norm at most `4` is controlled by
the elementary expression `δ + K + K^2`. -/
theorem refinedScalarProbeVarianceBound_le_basic
    {d : ℕ} {delta K : ℝ} (q : FullBlockVec d)
    (hdelta_nonneg : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hK_nonneg : 0 ≤ K)
    (hq_le : dotProduct q q ≤ 4) :
    refinedScalarProbeVarianceBound delta q K ≤
      256 * (delta + K + K ^ (2 : ℕ)) := by
  let x : ℝ := dotProduct q q
  have hx_nonneg : 0 ≤ x := by
    simpa [x] using dotProduct_self_nonneg q
  have hx_sq_le : x ^ (2 : ℕ) ≤ 16 := by
    have hx_mul : x * x ≤ 4 * x := mul_le_mul_of_nonneg_right (by simpa [x] using hq_le) hx_nonneg
    nlinarith
  have hdelta_sq_le : delta ^ (2 : ℕ) ≤ delta := by
    nlinarith
  have hdelta_x_sq_le : (delta * x) ^ (2 : ℕ) ≤ 16 * delta := by
    have hdelta_sq_nonneg : 0 ≤ delta ^ (2 : ℕ) := sq_nonneg delta
    have hx_sq_nonneg : 0 ≤ x ^ (2 : ℕ) := sq_nonneg x
    have hmul := mul_le_mul hdelta_sq_le hx_sq_le hx_sq_nonneg hdelta_nonneg
    nlinarith
  have hdelta_x2_le : delta * x ^ (2 : ℕ) ≤ 16 * delta := by
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hx_sq_le hdelta_nonneg
  have hxK_le : x * K ≤ 4 * K :=
    mul_le_mul_of_nonneg_right (by simpa [x] using hq_le) hK_nonneg
  unfold refinedScalarProbeVarianceBound
  dsimp [x] at *
  nlinarith

/-- Coordinate scalar budgets obey the uniform elementary bound. -/
theorem coordinateProbeRefinedVarianceBound_le_basic
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (j : ℕ) (α : BlockCoord d) :
    coordinateProbeRefinedVarianceBound hP4 delta j α ≤
      256 *
        (delta + coordinateProbeRefinedDescendantAverageK hP4 delta j +
          coordinateProbeRefinedDescendantAverageK hP4 delta j ^ (2 : ℕ)) := by
  unfold coordinateProbeRefinedVarianceBound
  exact refinedScalarProbeVarianceBound_le_basic
    (fullBlockCoordinateProbe α) hdelta_nonneg hdelta_le_one
    (coordinateProbeRefinedDescendantAverageK_nonneg hP4 hdelta_nonneg j)
    (by simp)

/-- Plus-pair scalar budgets obey the uniform elementary bound. -/
theorem plusProbeRefinedVarianceBound_le_basic
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (j : ℕ) (α β : BlockCoord d) :
    plusProbeRefinedVarianceBound hP4 delta j α β ≤
      256 *
        (delta + pairProbeRefinedDescendantAverageK hP4 delta j +
          pairProbeRefinedDescendantAverageK hP4 delta j ^ (2 : ℕ)) := by
  unfold plusProbeRefinedVarianceBound
  exact refinedScalarProbeVarianceBound_le_basic
    (fullBlockPlusProbe α β) hdelta_nonneg hdelta_le_one
    (pairProbeRefinedDescendantAverageK_nonneg hP4 hdelta_nonneg j)
    (dotProduct_plusProbe_self_le_four α β)

/-- Minus-pair scalar budgets obey the uniform elementary bound. -/
theorem minusProbeRefinedVarianceBound_le_basic
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (j : ℕ) (α β : BlockCoord d) :
    minusProbeRefinedVarianceBound hP4 delta j α β ≤
      256 *
        (delta + pairProbeRefinedDescendantAverageK hP4 delta j +
          pairProbeRefinedDescendantAverageK hP4 delta j ^ (2 : ℕ)) := by
  unfold minusProbeRefinedVarianceBound
  exact refinedScalarProbeVarianceBound_le_basic
    (fullBlockMinusProbe α β) hdelta_nonneg hdelta_le_one
    (pairProbeRefinedDescendantAverageK_nonneg hP4 hdelta_nonneg j)
    (dotProduct_minusProbe_self_le_four α β)

/-- The Section 5.2 large-scale set is the integer copy of `{1, ..., m}`. -/
theorem section52LargeScaleSet_eq_Icc_int (m : ℕ) :
    Section52.section52LargeScaleSet m =
      (Finset.Icc 1 m).image (fun j : ℕ => (j : ℤ)) := by
  classical
  ext n
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨l, hl, rfl⟩
    have hl_lt : l < m := Finset.mem_range.mp hl
    have hle : l ≤ m := Nat.le_of_lt hl_lt
    refine Finset.mem_image.mpr ?_
    refine ⟨m - l, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · omega
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨j, hj, rfl⟩
    have hj_bounds := Finset.mem_Icc.mp hj
    refine Finset.mem_image.mpr ?_
    refine ⟨m - j, ?_, ?_⟩
    · exact Finset.mem_range.mpr (by omega)
    · omega

/-- Reindex a finite sum over manuscript scales as a Section 5.2 large-scale
sum. -/
theorem sum_Icc_int_eq_section52LargeScaleSet_sum (m : ℕ) (F : ℤ → ℝ) :
    (∑ j ∈ Finset.Icc 1 m, F (j : ℤ)) =
      ∑ n ∈ Section52.section52LargeScaleSet m, F n := by
  classical
  rw [section52LargeScaleSet_eq_Icc_int]
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact Int.ofNat.inj hab

private theorem section54VarianceBeta_plus_dim_div_xi_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 ≤ section54VarianceBeta hP4 + (d : ℝ) / (hP4.xi : ℝ) := by
  have hbeta := section54VarianceBeta_nonneg hP4
  have hxi_nonneg : 0 ≤ (hP4.xi : ℝ) := by exact_mod_cast Nat.zero_le hP4.xi
  have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  exact add_nonneg hbeta (div_nonneg hd_nonneg hxi_nonneg)

private theorem section54VarianceBeta_plus_dim_div_xi_gapLp_pos
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 < (d : ℝ) - (section54VarianceBeta hP4 + (d : ℝ) / (hP4.xi : ℝ)) := by
  have hbeta_lt := section54VarianceBeta_lt_dim_div_two hP4
  have hxi_two : (2 : ℝ) ≤ (hP4.xi : ℝ) := by
    exact_mod_cast hP4.two_le_xi
  have hxi_pos : 0 < (hP4.xi : ℝ) := by
    exact_mod_cast hP4.xi_pos
  have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hdiv_le : (d : ℝ) / (hP4.xi : ℝ) ≤ (d : ℝ) / 2 := by
    exact div_le_div_of_nonneg_left hd_nonneg (by norm_num) hxi_two
  nlinarith

private theorem section54VarianceBeta_plus_dim_div_xi_gapSqrt_pos
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 <
      ((d : ℝ) / 2) + (d : ℝ) / (hP4.xi : ℝ) -
        (section54VarianceBeta hP4 + (d : ℝ) / (hP4.xi : ℝ)) := by
  have hbeta_lt := section54VarianceBeta_lt_dim_div_two hP4
  nlinarith

/-- Sum of the Section 5.2 large-scale root coefficient at the exponent
`β + d/ξ`, where its scale decay is exactly `3^{-β m}`. -/
theorem section52LargeScaleRootCoeff_sum_le_beta_decay
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (m : ℕ) :
    let s : ℝ := section54VarianceBeta hP4 + (d : ℝ) / (hP4.xi : ℝ)
    (∑ n ∈ Section52.section52LargeScaleSet m,
        Section52.section52LargeScaleRootCoeff d hP4.xi s m n) ≤
      ((2 * Ch04.rosenthalDescendantsAtScaleLpConst d 0 hP4.xi *
            geometricDiscount s 1) *
          (geometricDiscount ((d : ℝ) - s) 1)⁻¹ +
        (2 * Ch04.rosenthalDescendantsAtScaleSqrtConst d 0 hP4.xi *
            geometricDiscount s 1) *
          (geometricDiscount (((d : ℝ) / 2) + (d : ℝ) / (hP4.xi : ℝ) - s) 1)⁻¹) *
        Real.rpow (3 : ℝ) (-(section54VarianceBeta hP4) * (m : ℝ)) := by
  dsimp only
  have hraw :=
    Section52.section52LargeScaleRootCoeff_scale_sum_le_geometricDiscount
      (d := d) (ξ := hP4.xi)
      (s := section54VarianceBeta hP4 + (d : ℝ) / (hP4.xi : ℝ)) m
      (section54VarianceBeta_plus_dim_div_xi_nonneg hP4)
      (section54VarianceBeta_plus_dim_div_xi_gapLp_pos hP4)
      (section54VarianceBeta_plus_dim_div_xi_gapSqrt_pos hP4)
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hraw

/-- The scalar budget left after compressing the finite-probe matrix estimate. -/
noncomputable def refinedVarianceBasicBudget
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (delta : ℝ) (j : ℕ) : ℝ :=
  delta +
    coordinateProbeRefinedDescendantAverageK hP4 delta j +
      coordinateProbeRefinedDescendantAverageK hP4 delta j ^ (2 : ℕ) +
    pairProbeRefinedDescendantAverageK hP4 delta j +
      pairProbeRefinedDescendantAverageK hP4 delta j ^ (2 : ℕ)

/-- Dimension-only finite-probe constant for the refined variance budget. -/
noncomputable def refinedMatrixBudgetConst (d : ℕ) : ℝ :=
  ((Fintype.card (BlockCoord d) : ℝ) ^ (6 : ℕ)) * (54 * 256)

private theorem refinedVarianceBasicBudget_nonneg
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta) (j : ℕ) :
    0 ≤ refinedVarianceBasicBudget hP4 delta j := by
  have hcoord := coordinateProbeRefinedDescendantAverageK_nonneg hP4 hdelta_nonneg j
  have hpair := pairProbeRefinedDescendantAverageK_nonneg hP4 hdelta_nonneg j
  unfold refinedVarianceBasicBudget
  nlinarith [sq_nonneg (coordinateProbeRefinedDescendantAverageK hP4 delta j),
    sq_nonneg (pairProbeRefinedDescendantAverageK hP4 delta j)]

/-- The per-scale matrix budget is bounded by the compressed scalar budget. -/
theorem refinedMatrixVarianceScaleBound_le_basicBudget
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (j : ℕ) :
    refinedMatrixVarianceScaleBound hP4 delta j ≤
      refinedMatrixBudgetConst d * refinedVarianceBasicBudget hP4 delta j := by
  classical
  let B : ℝ := refinedVarianceBasicBudget hP4 delta j
  let c : ℝ := (Fintype.card (BlockCoord d) : ℝ)
  have hB_nonneg : 0 ≤ B := by
    simpa [B] using refinedVarianceBasicBudget_nonneg hP4 hdelta_nonneg j
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hcoordBudget :
      delta + coordinateProbeRefinedDescendantAverageK hP4 delta j +
          coordinateProbeRefinedDescendantAverageK hP4 delta j ^ (2 : ℕ) ≤ B := by
    have hpair := pairProbeRefinedDescendantAverageK_nonneg hP4 hdelta_nonneg j
    dsimp [B, refinedVarianceBasicBudget]
    nlinarith [sq_nonneg (pairProbeRefinedDescendantAverageK hP4 delta j)]
  have hpairBudget :
      delta + pairProbeRefinedDescendantAverageK hP4 delta j +
          pairProbeRefinedDescendantAverageK hP4 delta j ^ (2 : ℕ) ≤ B := by
    have hcoord := coordinateProbeRefinedDescendantAverageK_nonneg hP4 hdelta_nonneg j
    dsimp [B, refinedVarianceBasicBudget]
    nlinarith [sq_nonneg (coordinateProbeRefinedDescendantAverageK hP4 delta j)]
  have hcoord_le : ∀ α : BlockCoord d,
      coordinateProbeRefinedVarianceBound hP4 delta j α ≤ 256 * B := by
    intro α
    exact (coordinateProbeRefinedVarianceBound_le_basic hP4 hdelta_nonneg hdelta_le_one j α).trans
      (mul_le_mul_of_nonneg_left hcoordBudget (by norm_num))
  have hplus_le : ∀ α β : BlockCoord d,
      plusProbeRefinedVarianceBound hP4 delta j α β ≤ 256 * B := by
    intro α β
    exact (plusProbeRefinedVarianceBound_le_basic hP4 hdelta_nonneg hdelta_le_one j α β).trans
      (mul_le_mul_of_nonneg_left hpairBudget (by norm_num))
  have hminus_le : ∀ α β : BlockCoord d,
      minusProbeRefinedVarianceBound hP4 delta j α β ≤ 256 * B := by
    intro α β
    exact (minusProbeRefinedVarianceBound_le_basic hP4 hdelta_nonneg hdelta_le_one j α β).trans
      (mul_le_mul_of_nonneg_left hpairBudget (by norm_num))
  let T : BlockCoord d → BlockCoord d → ℝ := fun α β =>
    3 *
      (coordinateProbeRefinedVarianceBound hP4 delta j α +
        (if α = β then
          16 * coordinateProbeRefinedVarianceBound hP4 delta j α
        else
          plusProbeRefinedVarianceBound hP4 delta j α β) +
        (if α = β then
          0
        else
          minusProbeRefinedVarianceBound hP4 delta j α β))
  have hT : ∀ α β : BlockCoord d, T α β ≤ 54 * 256 * B := by
    intro α β
    by_cases hαβ : α = β
    · subst β
      have hcα := hcoord_le α
      simp [T]
      nlinarith
    · have hcα := hcoord_le α
      have hpαβ := hplus_le α β
      have hmαβ := hminus_le α β
      simp [T, hαβ]
      nlinarith
  have hsumβ : ∀ α : BlockCoord d,
      (∑ β : BlockCoord d, T α β) ≤ c * (54 * 256 * B) := by
    intro α
    calc
      (∑ β : BlockCoord d, T α β) ≤
          ∑ _β : BlockCoord d, 54 * 256 * B :=
        Finset.sum_le_sum fun β _hβ => hT α β
      _ = c * (54 * 256 * B) := by
        simp [c]
  have hsumα :
      (∑ α : BlockCoord d, c * ∑ β : BlockCoord d, T α β) ≤
        c * (c * (c * (54 * 256 * B))) := by
    calc
      (∑ α : BlockCoord d, c * ∑ β : BlockCoord d, T α β) ≤
          ∑ _α : BlockCoord d, c * (c * (54 * 256 * B)) := by
        refine Finset.sum_le_sum ?_
        intro α _hα
        exact mul_le_mul_of_nonneg_left (hsumβ α) hc_nonneg
      _ = c * (c * (c * (54 * 256 * B))) := by
        simp [c, mul_assoc]
  have hinside :
      c * (∑ α : BlockCoord d, c * ∑ β : BlockCoord d, T α β) ≤
        c * (c * (c * (c * (54 * 256 * B)))) := by
    have hstep := mul_le_mul_of_nonneg_left hsumα hc_nonneg
    simpa [mul_assoc] using hstep
  calc
    refinedMatrixVarianceScaleBound hP4 delta j =
        c ^ (2 : ℕ) *
          (c * (∑ α : BlockCoord d, c * ∑ β : BlockCoord d, T α β)) := by
      simp [refinedMatrixVarianceScaleBound, c, T]
    _ ≤ c ^ (2 : ℕ) * (c * (c * (c * (c * (54 * 256 * B))))) :=
      mul_le_mul_of_nonneg_left hinside (sq_nonneg c)
    _ = refinedMatrixBudgetConst d * refinedVarianceBasicBudget hP4 delta j := by
      simp [refinedMatrixBudgetConst, refinedVarianceBasicBudget, B, c]
      ring

end

end VarianceBoundGoodScale
end Section54
end Ch05
end Book
end Homogenization
