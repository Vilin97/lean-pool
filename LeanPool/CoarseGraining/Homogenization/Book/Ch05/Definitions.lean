/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.Expectations
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.MomentFactorBounds
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.Scalarization

/-! # Definitions -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05

/-!
# Chapter 5 definitions reboot

This file is the active Chapter 5 definition surface.  Add definitions here
only when they are manuscript-facing and not merely proof plumbing.
-/

noncomputable section

/-- The parameter-only part of the Chapter 5 quantitative coarse-grained
ellipticity input `(P4)`.

This record remembers only the manuscript parameters and inequalities for
`s_1`, `s_2`, and `\xi`; it deliberately contains no law-specific
integrability data.  It is useful for stating constants with the manuscript
dependency `C(d,s_1,s_2,\xi)`. -/
structure QuantitativeCoarseGrainedEllipticityParams (d : ℕ) : Type where
  sUpper : ℝ
  sLower : ℝ
  xi : ℕ
  two_le_dim : 2 ≤ d
  sUpper_nonneg : 0 ≤ sUpper
  sUpper_lt_one : sUpper < 1
  sLower_nonneg : 0 ≤ sLower
  sLower_lt_one : sLower < 1
  xi_gt_two_mul_dim : (2 * d : ℝ) < (xi : ℝ)
  sum_lt_one : sUpper + sLower < 1
  dim_div_xi_lt_min : (d : ℝ) / (xi : ℝ) < min sUpper sLower

namespace QuantitativeCoarseGrainedEllipticityParams

/-- The exponent `xi` in the parameter-only `(P4)` data is positive. -/
theorem xi_pos {d : ℕ} (params : QuantitativeCoarseGrainedEllipticityParams d) :
    0 < params.xi := by
  have hd_nonneg : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hxi_pos_real : (0 : ℝ) < (params.xi : ℝ) := by
    nlinarith [params.xi_gt_two_mul_dim, hd_nonneg]
  exact_mod_cast hxi_pos_real

/-- The exponent `xi` in the parameter-only `(P4)` data is at least two. -/
theorem two_le_xi {d : ℕ} (params : QuantitativeCoarseGrainedEllipticityParams d) :
    2 ≤ params.xi := by
  have hd_one : (1 : ℝ) ≤ (d : ℝ) := by
    have hd_nat : 1 ≤ d := le_trans (by norm_num : 1 ≤ 2) params.two_le_dim
    exact_mod_cast hd_nat
  have htwo_le_two_d : (2 : ℝ) ≤ 2 * (d : ℝ) := by nlinarith
  have htwo_lt_xi : (2 : ℝ) < (params.xi : ℝ) :=
    lt_of_le_of_lt htwo_le_two_d params.xi_gt_two_mul_dim
  exact_mod_cast htwo_lt_xi.le

/-- The upper regularity exponent in the parameter-only `(P4)` data is
positive. -/
theorem sUpper_pos {d : ℕ} (params : QuantitativeCoarseGrainedEllipticityParams d) :
    0 < params.sUpper := by
  have hd_pos_nat : 0 < d := lt_of_lt_of_le (by norm_num : 0 < 2) params.two_le_dim
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos_nat
  have hxi_pos_real : (0 : ℝ) < (params.xi : ℝ) := by
    exact_mod_cast params.xi_pos
  have hdiv_pos : 0 < (d : ℝ) / (params.xi : ℝ) := div_pos hd_pos hxi_pos_real
  exact lt_trans hdiv_pos
    (lt_of_lt_of_le params.dim_div_xi_lt_min (min_le_left _ _))

/-- The lower regularity exponent in the parameter-only `(P4)` data is
positive. -/
theorem sLower_pos {d : ℕ} (params : QuantitativeCoarseGrainedEllipticityParams d) :
    0 < params.sLower := by
  have hd_pos_nat : 0 < d := lt_of_lt_of_le (by norm_num : 0 < 2) params.two_le_dim
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos_nat
  have hxi_pos_real : (0 : ℝ) < (params.xi : ℝ) := by
    exact_mod_cast params.xi_pos
  have hdiv_pos : 0 < (d : ℝ) / (params.xi : ℝ) := div_pos hd_pos hxi_pos_real
  exact lt_trans hdiv_pos
    (lt_of_lt_of_le params.dim_div_xi_lt_min (min_le_right _ _))

/-- The parameter-only `(P4)` lower endpoint gives `d / xi < sUpper`. -/
theorem dim_div_xi_lt_sUpper {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    (d : ℝ) / (params.xi : ℝ) < params.sUpper :=
  lt_of_lt_of_le params.dim_div_xi_lt_min (min_le_left _ _)

/-- The parameter-only `(P4)` lower endpoint gives `d / xi < sLower`. -/
theorem dim_div_xi_lt_sLower {d : ℕ}
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    (d : ℝ) / (params.xi : ℝ) < params.sLower :=
  lt_of_lt_of_le params.dim_div_xi_lt_min (min_le_right _ _)

end QuantitativeCoarseGrainedEllipticityParams

/-- The Chapter 5 quantitative coarse-grained ellipticity input `(P4)`.

The fields `sUpper`, `sLower`, and `xi` are the manuscript parameters
`s_1`, `s_2`, and `\xi`.  The last two fields encode finiteness of the unit-cube
moments in `(P4)` as integrability of the corresponding powers. -/
structure QuantitativeCoarseGrainedEllipticity {d : ℕ} [NeZero d]
    (P : Ch04.RestrictionCoeffLaw d) : Type where
  sUpper : ℝ
  sLower : ℝ
  xi : ℕ
  two_le_dim : 2 ≤ d
  sUpper_nonneg : 0 ≤ sUpper
  sUpper_lt_one : sUpper < 1
  sLower_nonneg : 0 ≤ sLower
  sLower_lt_one : sLower < 1
  xi_gt_two_mul_dim : (2 * d : ℝ) < (xi : ℝ)
  sum_lt_one : sUpper + sLower < 1
  dim_div_xi_lt_min : (d : ℝ) / (xi : ℝ) < min sUpper sLower
  upper_moment_integrable :
    MeasureTheory.Integrable
      (fun a : RegCoeffField d =>
        (Ch04.LambdaSqCoeffField (originCube d (0 : ℤ)) sUpper (.finite 1) a) ^ xi) P
  lower_inv_moment_integrable :
    MeasureTheory.Integrable
      (fun a : RegCoeffField d =>
        ((Ch04.lambdaSqCoeffField (originCube d (0 : ℤ)) sLower (.finite 1) a)⁻¹) ^ xi) P

namespace QuantitativeCoarseGrainedEllipticity

/-- Forget the law-specific integrability part of `(P4)`, retaining only the
manuscript parameters and inequalities. -/
def params {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    QuantitativeCoarseGrainedEllipticityParams d where
  sUpper := hP4.sUpper
  sLower := hP4.sLower
  xi := hP4.xi
  two_le_dim := hP4.two_le_dim
  sUpper_nonneg := hP4.sUpper_nonneg
  sUpper_lt_one := hP4.sUpper_lt_one
  sLower_nonneg := hP4.sLower_nonneg
  sLower_lt_one := hP4.sLower_lt_one
  xi_gt_two_mul_dim := hP4.xi_gt_two_mul_dim
  sum_lt_one := hP4.sum_lt_one
  dim_div_xi_lt_min := hP4.dim_div_xi_lt_min

@[simp]
theorem params_sUpper {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    hP4.params.sUpper = hP4.sUpper := rfl

@[simp]
theorem params_sLower {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    hP4.params.sLower = hP4.sLower := rfl

@[simp]
theorem params_xi {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    hP4.params.xi = hP4.xi := rfl

/-- The exponent `xi` in `(P4)` is positive. -/
theorem xi_pos {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 < hP4.xi := by
  have hd_nonneg : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hxi_pos_real : (0 : ℝ) < (hP4.xi : ℝ) := by
    nlinarith [hP4.xi_gt_two_mul_dim, hd_nonneg]
  exact_mod_cast hxi_pos_real

/-- The exponent `xi` in `(P4)` is at least two. -/
theorem two_le_xi {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    2 ≤ hP4.xi := by
  have hd_one : (1 : ℝ) ≤ (d : ℝ) := by
    have hd_nat : 1 ≤ d := le_trans (by norm_num : 1 ≤ 2) hP4.two_le_dim
    exact_mod_cast hd_nat
  have htwo_le_two_d : (2 : ℝ) ≤ 2 * (d : ℝ) := by nlinarith
  have htwo_lt_xi : (2 : ℝ) < (hP4.xi : ℝ) :=
    lt_of_le_of_lt htwo_le_two_d hP4.xi_gt_two_mul_dim
  exact_mod_cast htwo_lt_xi.le

/-- The upper regularity exponent in `(P4)` is positive. -/
theorem sUpper_pos {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 < hP4.sUpper := by
  have hd_pos_nat : 0 < d := lt_of_lt_of_le (by norm_num : 0 < 2) hP4.two_le_dim
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos_nat
  have hxi_pos_real : (0 : ℝ) < (hP4.xi : ℝ) := by
    exact_mod_cast hP4.xi_pos
  have hdiv_pos : 0 < (d : ℝ) / (hP4.xi : ℝ) := div_pos hd_pos hxi_pos_real
  exact lt_trans hdiv_pos
    (lt_of_lt_of_le hP4.dim_div_xi_lt_min (min_le_left _ _))

/-- The lower regularity exponent in `(P4)` is positive. -/
theorem sLower_pos {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 < hP4.sLower := by
  have hd_pos_nat : 0 < d := lt_of_lt_of_le (by norm_num : 0 < 2) hP4.two_le_dim
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos_nat
  have hxi_pos_real : (0 : ℝ) < (hP4.xi : ℝ) := by
    exact_mod_cast hP4.xi_pos
  have hdiv_pos : 0 < (d : ℝ) / (hP4.xi : ℝ) := div_pos hd_pos hxi_pos_real
  exact lt_trans hdiv_pos
    (lt_of_lt_of_le hP4.dim_div_xi_lt_min (min_le_right _ _))

/-- The P4 lower endpoint gives `d / xi < sUpper`. -/
theorem dim_div_xi_lt_sUpper {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    (d : ℝ) / (hP4.xi : ℝ) < hP4.sUpper :=
  lt_of_lt_of_le hP4.dim_div_xi_lt_min (min_le_left _ _)

/-- The P4 lower endpoint gives `d / xi < sLower`. -/
theorem dim_div_xi_lt_sLower {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    (d : ℝ) / (hP4.xi : ℝ) < hP4.sLower :=
  lt_of_lt_of_le hP4.dim_div_xi_lt_min (min_le_right _ _)

/-- The upper geometric-series denominator in the Section 5.2 moment lemma is
positive under `(P4)`. -/
theorem upperMomentDenom_pos {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 < ((d : ℝ) / 2) + (d : ℝ) / (hP4.xi : ℝ) - hP4.sUpper := by
  have hd_two : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hP4.two_le_dim
  have hd_half : (1 : ℝ) ≤ (d : ℝ) / 2 := by nlinarith
  have hd_nonneg : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hxi_nonneg : (0 : ℝ) ≤ (hP4.xi : ℝ) := by exact_mod_cast Nat.zero_le hP4.xi
  have hdiv_nonneg : 0 ≤ (d : ℝ) / (hP4.xi : ℝ) :=
    div_nonneg hd_nonneg hxi_nonneg
  linarith [hP4.sUpper_lt_one]

/-- The lower geometric-series denominator in the Section 5.2 moment lemma is
positive under `(P4)`. -/
theorem lowerMomentDenom_pos {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    0 < ((d : ℝ) / 2) + (d : ℝ) / (hP4.xi : ℝ) - hP4.sLower := by
  have hd_two : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hP4.two_le_dim
  have hd_half : (1 : ℝ) ≤ (d : ℝ) / 2 := by nlinarith
  have hd_nonneg : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
  have hxi_nonneg : (0 : ℝ) ≤ (hP4.xi : ℝ) := by exact_mod_cast Nat.zero_le hP4.xi
  have hdiv_nonneg : 0 ≤ (d : ℝ) / (hP4.xi : ℝ) :=
    div_nonneg hd_nonneg hxi_nonneg
  linarith [hP4.sLower_lt_one]

end QuantitativeCoarseGrainedEllipticity

/-- The scalar contrast `Theta_n = \bar\sigma_n \bar\sigma_{*,n}^{-1}`,
read from the Chapter 4 structural-law scalar surface. -/
noncomputable def thetaAtScale {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (n : ℤ) : ℝ :=
  hP.thetaAtScale hStruct n

@[simp]
theorem thetaAtScale_eq {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (n : ℤ) :
    thetaAtScale hP hStruct n = hP.thetaAtScale hStruct n :=
  rfl

/-- The high-moment contrast `widetildeTheta_n` with the parameters supplied by
the Chapter 5 quantitative ellipticity input. -/
noncomputable def widetildeThetaAtScale {d : ℕ} [NeZero d]
    (P : Ch04.RestrictionCoeffLaw d) (n : ℤ)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) : ℝ :=
  Ch04.widetildeThetaAtScale P n hP4.sUpper hP4.sLower hP4.xi

@[simp]
theorem widetildeThetaAtScale_eq {d : ℕ} [NeZero d]
    (P : Ch04.RestrictionCoeffLaw d) (n : ℤ)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) :
    widetildeThetaAtScale P n hP4 =
      Ch04.widetildeThetaAtScale P n hP4.sUpper hP4.sLower hP4.xi :=
  rfl

/-- The positive excess of the upper ellipticity moment over the unit-scale
structural-law scalar upper coefficient. -/
noncomputable def LambdaPositiveExcessMomentAtScale {d : ℕ} [NeZero d]
    (P : Ch04.RestrictionCoeffLaw d) (n : ℤ) (s : ℝ) (ξ : ℕ)
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) : ℝ :=
  Ch04.annealedMomentRoot P ξ
    (fun a : RegCoeffField d =>
      max
        (Ch04.LambdaSqCoeffField (originCube d n) s (.finite 1) a -
          hP.barSigmaAtScale hStruct 0)
        0)

@[simp]
theorem LambdaPositiveExcessMomentAtScale_eq {d : ℕ} [NeZero d]
    (P : Ch04.RestrictionCoeffLaw d) (n : ℤ) (s : ℝ) (ξ : ℕ)
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) :
    LambdaPositiveExcessMomentAtScale P n s ξ hP hStruct =
      Ch04.annealedMomentRoot P ξ
        (fun a : RegCoeffField d =>
          max
            (Ch04.LambdaSqCoeffField (originCube d n) s (.finite 1) a -
              hP.barSigmaAtScale hStruct 0)
            0) :=
  rfl

/-- The positive excess of the lower inverse ellipticity moment over the
unit-scale structural-law inverse-star coefficient. -/
noncomputable def lambdaInvPositiveExcessMomentAtScale {d : ℕ} [NeZero d]
    (P : Ch04.RestrictionCoeffLaw d) (n : ℤ) (s : ℝ) (ξ : ℕ)
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) : ℝ :=
  Ch04.annealedMomentRoot P ξ
    (fun a : RegCoeffField d =>
      max
        ((Ch04.lambdaSqCoeffField (originCube d n) s (.finite 1) a)⁻¹ -
          (hP.barSigmaStarAtScale hStruct 0)⁻¹)
        0)

@[simp]
theorem lambdaInvPositiveExcessMomentAtScale_eq {d : ℕ} [NeZero d]
    (P : Ch04.RestrictionCoeffLaw d) (n : ℤ) (s : ℝ) (ξ : ℕ)
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) :
    lambdaInvPositiveExcessMomentAtScale P n s ξ hP hStruct =
      Ch04.annealedMomentRoot P ξ
        (fun a : RegCoeffField d =>
          max
            ((Ch04.lambdaSqCoeffField (originCube d n) s (.finite 1) a)⁻¹ -
              (hP.barSigmaStarAtScale hStruct 0)⁻¹)
            0) :=
  rfl

/-- The displayed positive-excess coefficient in Section 5.2:
`C xi / (d / 2 + d / xi - s) * 3^{-(s - d / xi)m}`. -/
noncomputable def section52MomentBoundCoeff
    (d ξ : ℕ) (C s : ℝ) (m : ℕ) : ℝ :=
  C * (ξ : ℝ) / (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - s) *
    Real.rpow (3 : ℝ) (-(s - (d : ℝ) / (ξ : ℝ)) * (m : ℝ))

/-- The corrected two-exponent Section 5.2 moment-loss factor
`\Gamma_{s,r,\xi}`.  Here `s` is the unit-scale source exponent and `r` is the
tracked exponent at scale `m`. -/
noncomputable def section52MomentLossCoeff
    (d ξ : ℕ) (s r : ℝ) : ℝ :=
  s⁻¹ ^ 2 *
    ((ξ : ℝ) / (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - r) +
      (r - s)⁻¹ ^ 2)

/-- The corrected two-exponent positive-excess coefficient in Section 5.2:
`C Gamma_{s,r,xi} * 3^{-(r - d / xi)m}`. -/
noncomputable def section52TwoExponentMomentBoundCoeff
    (d ξ : ℕ) (C s r : ℝ) (m : ℕ) : ℝ :=
  C * section52MomentLossCoeff d ξ s r *
    Real.rpow (3 : ℝ) (-(r - (d : ℝ) / (ξ : ℝ)) * (m : ℝ))

/-- The displayed `widetildeTheta` error coefficient in Section 5.2:
`C xi^2 3^{-(sMin - d / xi)m}`. -/
noncomputable def section52WidetildeThetaErrorCoeff
    (d ξ : ℕ) (C sMin : ℝ) (m : ℕ) : ℝ :=
  C * (ξ : ℝ) ^ 2 *
    Real.rpow (3 : ℝ) (-(sMin - (d : ℝ) / (ξ : ℝ)) * (m : ℝ))

/-- The combined coefficient before the common Section 5.2
`widetildeTheta` scale. -/
noncomputable def section52WidetildeThetaCombinedCoeff
    (d ξ : ℕ) (CUpper CLower sUpper sLower : ℝ) : ℝ :=
  CUpper / (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - sUpper) +
    CLower / (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - sLower) +
      (CUpper / (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - sUpper)) *
        (CLower / (((d : ℝ) / 2) + (d : ℝ) / (ξ : ℝ) - sLower))

/-- The annealed additivity defect
`tau_{n,k}(p,q) = E[J(cu_k,p,q)] - E[J(cu_n,p,q)]`. -/
noncomputable def tauAtScale {d : ℕ}
    (P : Ch04.RestrictionCoeffLaw d) (n k : ℤ) (p q : Vec d) : ℝ :=
  Ch04.annealedResponseJAtScale P k p q -
    Ch04.annealedResponseJAtScale P n p q

@[simp]
theorem tauAtScale_eq {d : ℕ}
    (P : Ch04.RestrictionCoeffLaw d) (n k : ℤ) (p q : Vec d) :
    tauAtScale P n k p q =
      Ch04.annealedResponseJAtScale P k p q -
        Ch04.annealedResponseJAtScale P n p q :=
  rfl

/-- The scalar geometric mean
`\widehat\sigma_m = (\bar\sigma_m \bar\sigma_{*,m})^{1/2}`. -/
noncomputable def sigmaHatAtScale {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ) : ℝ :=
  Real.sqrt (hP.barSigmaAtScale hStruct m * hP.barSigmaStarAtScale hStruct m)

@[simp]
theorem sigmaHatAtScale_eq {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ) :
    sigmaHatAtScale hP hStruct m =
      Real.sqrt (hP.barSigmaAtScale hStruct m * hP.barSigmaStarAtScale hStruct m) :=
  rfl

/-- The special vector `p_e = \widehat\sigma_m^{-1/2} e`. -/
noncomputable def specialPAtScale {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ)
    (e : Vec d) : Vec d :=
  Real.rpow (sigmaHatAtScale hP hStruct m) (-(1 / 2 : ℝ)) • e

@[simp]
theorem specialPAtScale_eq {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ)
    (e : Vec d) :
    specialPAtScale hP hStruct m e =
      Real.rpow (sigmaHatAtScale hP hStruct m) (-(1 / 2 : ℝ)) • e :=
  rfl

/-- The special vector `q_e = \widehat\sigma_m^{1/2} e`. -/
noncomputable def specialQAtScale {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ)
    (e : Vec d) : Vec d :=
  Real.rpow (sigmaHatAtScale hP hStruct m) (1 / 2 : ℝ) • e

@[simp]
theorem specialQAtScale_eq {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ)
    (e : Vec d) :
    specialQAtScale hP hStruct m e =
      Real.rpow (sigmaHatAtScale hP hStruct m) (1 / 2 : ℝ) • e :=
  rfl

/-- The scalar centering term
`1/2 * (\bar\sigma_{*,m}^{-1} q - p) · (q - \bar\sigma_m p)`. -/
noncomputable def scalarizedResponseCenteringTerm {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ)
    (p q : Vec d) : ℝ :=
  (1 / 2 : ℝ) *
    vecDot (((hP.barSigmaStarAtScale hStruct m)⁻¹ • q) - p)
      (q - hP.barSigmaAtScale hStruct m • p)

@[simp]
theorem scalarizedResponseCenteringTerm_eq {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ)
    (p q : Vec d) :
    scalarizedResponseCenteringTerm hP hStruct m p q =
      (1 / 2 : ℝ) *
        vecDot (((hP.barSigmaStarAtScale hStruct m)⁻¹ • q) - p)
          (q - hP.barSigmaAtScale hStruct m • p) :=
  rfl

/-- The scalarized expectation formula for the annealed response:
`1/2 q · \bar\sigma_*^{-1} q - p · q + 1/2 p · \bar\sigma p`. -/
noncomputable def expectedJScalarFormula {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ)
    (p q : Vec d) : ℝ :=
  (1 / 2 : ℝ) * vecDot q ((hP.barSigmaStarAtScale hStruct m)⁻¹ • q) -
    vecDot p q +
    (1 / 2 : ℝ) * vecDot p (hP.barSigmaAtScale hStruct m • p)

@[simp]
theorem expectedJScalarFormula_eq {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ)
    (p q : Vec d) :
    expectedJScalarFormula hP hStruct m p q =
      (1 / 2 : ℝ) * vecDot q ((hP.barSigmaStarAtScale hStruct m)⁻¹ • q) -
        vecDot p q +
        (1 / 2 : ℝ) * vecDot p (hP.barSigmaAtScale hStruct m • p) :=
  rfl

/-- The scalarized formula for
`tau_{n,k}(p,q) = E[J(cu_k,p,q)] - E[J(cu_n,p,q)]`. -/
noncomputable def tauScalarFormula {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (n k : ℤ)
    (p q : Vec d) : ℝ :=
  (1 / 2 : ℝ) *
      vecDot p ((hP.barSigmaAtScale hStruct k - hP.barSigmaAtScale hStruct n) • p) +
    (1 / 2 : ℝ) *
      vecDot q (((hP.barSigmaStarAtScale hStruct k)⁻¹ -
        (hP.barSigmaStarAtScale hStruct n)⁻¹) • q)

@[simp]
theorem tauScalarFormula_eq {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (n k : ℤ)
    (p q : Vec d) :
    tauScalarFormula hP hStruct n k p q =
      (1 / 2 : ℝ) *
          vecDot p ((hP.barSigmaAtScale hStruct k - hP.barSigmaAtScale hStruct n) • p) +
        (1 / 2 : ℝ) *
          vecDot q (((hP.barSigmaStarAtScale hStruct k)⁻¹ -
            (hP.barSigmaStarAtScale hStruct n)⁻¹) • q) :=
  rfl

/-- The scalarized expectation of the centered response:
`1/2 p · ((Theta_m - 1) q)`. -/
noncomputable def centeredResponseExpectationFormula {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ)
    (p q : Vec d) : ℝ :=
  (1 / 2 : ℝ) * vecDot p ((thetaAtScale hP hStruct m - 1) • q)

@[simp]
theorem centeredResponseExpectationFormula_eq {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ)
    (p q : Vec d) :
    centeredResponseExpectationFormula hP hStruct m p q =
      (1 / 2 : ℝ) * vecDot p ((thetaAtScale hP hStruct m - 1) • q) :=
  rfl

/-- The centered scalar response observable on a deterministic cube, with the
centering scale supplied separately. -/
noncomputable def restrictionCenteredResponseJObservableCubeSet {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ)
    (Q : TriadicCube d) (p q : Vec d) : RegCoeffField d → ℝ :=
  fun a =>
    Ch04.restrictionResponseJObservableCubeSet Q p q a -
      scalarizedResponseCenteringTerm hP hStruct m p q

@[simp]
theorem restrictionCenteredResponseJObservableCubeSet_apply {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ)
    (Q : TriadicCube d) (p q : Vec d) (a : RegCoeffField d) :
    restrictionCenteredResponseJObservableCubeSet hP hStruct m Q p q a =
      Ch04.restrictionResponseJObservableCubeSet Q p q a -
        scalarizedResponseCenteringTerm hP hStruct m p q :=
  rfl

/-- The centered adjoint scalar response observable on a deterministic cube. -/
noncomputable def restrictionCenteredResponseJStarObservableCubeSet {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ)
    (Q : TriadicCube d) (p q : Vec d) : RegCoeffField d → ℝ :=
  fun a =>
    Ch04.restrictionResponseJObservableCubeSet Q p q (adjointReg a) -
      scalarizedResponseCenteringTerm hP hStruct m p q

@[simp]
theorem restrictionCenteredResponseJStarObservableCubeSet_apply {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ)
    (Q : TriadicCube d) (p q : Vec d) (a : RegCoeffField d) :
    restrictionCenteredResponseJStarObservableCubeSet hP hStruct m Q p q a =
      Ch04.restrictionResponseJObservableCubeSet Q p q (adjointReg a) -
        scalarizedResponseCenteringTerm hP hStruct m p q :=
  rfl

/-- The expected centered scalar response on the origin cube at scale `m`. -/
noncomputable def expectedCenteredResponseJAtScale {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ)
    (p q : Vec d) : ℝ :=
  ∫ a, restrictionCenteredResponseJObservableCubeSet hP hStruct m (originCube d m) p q a ∂P

/-- The expected centered adjoint scalar response on the origin cube at scale
`m`. -/
noncomputable def expectedCenteredResponseJStarAtScale {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P) (m : ℤ)
    (p q : Vec d) : ℝ :=
  ∫ a, restrictionCenteredResponseJStarObservableCubeSet hP hStruct m (originCube d m) p q a ∂P

/-- The first ceiling contribution in the annealed entry scale, depending on
the unit-scale value of `widetildeTheta`. -/
noncomputable def annealedConvergenceEntryScaleBound {d : ℕ} [NeZero d]
    (P : Ch04.RestrictionCoeffLaw d)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (C : ℝ) : ℕ :=
  Nat.ceil (C * (Real.log (2 + widetildeThetaAtScale P (0 : ℤ) hP4)) ^ 2)

/-- The second ceiling contribution in the annealed entry scale, depending on
the target perturbative accuracy `sigma`. -/
noncomputable def annealedConvergenceSigmaTailScale
    {d : ℕ} [NeZero d] (P : Ch04.RestrictionCoeffLaw d)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (C sigma : ℝ) : ℕ :=
  Nat.ceil (C * (hP4.xi : ℝ) * (sigma⁻¹ ^ (4 : ℕ)) * |Real.log sigma| *
    Real.log (2 + sigma⁻¹ ^ (4 : ℕ) * (hP4.xi : ℝ) *
      widetildeThetaAtScale P (0 : ℤ) hP4))

/-- The entry scale `N_sigma` from the main annealed convergence theorem. -/
noncomputable def annealedEntryScale {d : ℕ} [NeZero d]
    (P : Ch04.RestrictionCoeffLaw d)
  (hP4 : QuantitativeCoarseGrainedEllipticity P)
  (C sigma : ℝ) : ℕ :=
  annealedConvergenceEntryScaleBound P hP4 C +
    annealedConvergenceSigmaTailScale P hP4 C sigma

/-- The algebraic-decay entry scale `N_0` in Theorem
`t.annealed.convergence`.

This is the two-ceiling scale used after the perturbative entry scale has been
dilated to unit scale and the small-contrast algebraic iteration has been
applied. -/
noncomputable def annealedAlgebraicEntryScale {d : ℕ} [NeZero d]
    (P : Ch04.RestrictionCoeffLaw d)
    (hP4 : QuantitativeCoarseGrainedEllipticity P) (C : ℝ) : ℕ :=
  Nat.ceil (C * (Real.log (2 + widetildeThetaAtScale P (0 : ℤ) hP4)) ^ 2) +
    Nat.ceil (C * (hP4.xi : ℝ) *
      Real.log (2 + C * (hP4.xi : ℝ) *
        widetildeThetaAtScale P (0 : ℤ) hP4))

end

end Ch05
end Book
end Homogenization
