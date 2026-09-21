/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationAssemblyRHS
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Basic

/-! # Homogenization Assembly Optimized -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open scoped ENNReal MatrixOrder

/-!
# Depth optimization for the public quenched homogenization comparison

This file turns the scale-separated compressed RHS of
`HomogenizationAssemblyRHS.lean` into the manuscript-shaped RHS of the public
theorem: a single constant, a single power of the minimal-scale ratio
`3^m / X`, and the two natural data norms.  The localization depth `j` is
chosen as `3^{r j} ≈ ((3^m / X)^{α/2})^{1/2}`, which makes every term of the
compressed RHS decay like `(3^m / X)^{-α/8}`.

The file also records that the finite quenched tail exponent is nondecreasing
in its discount parameter, so that the interpolated stochastic exponent
`min (η(τ)) (η(τ/2))` collapses to `η(τ/2)`.
-/

noncomputable section

/-! ## Monotonicity of the finite tail exponent -/

theorem finiteQuenchedTailExponent_le_of_le
    {d : ℕ} [NeZero d] {σ t₁ t₂ : ℝ}
    (hσ : 0 < σ) (ht₁ : 0 < t₁) (h12 : t₁ ≤ t₂) :
    finiteQuenchedTailExponent d σ t₁ ≤ finiteQuenchedTailExponent d σ t₂ := by
  have hd : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hb : 0 < (d : ℝ) / 2 := by positivity
  have ht₂ : 0 < t₂ := lt_of_lt_of_le ht₁ h12
  have hτ : 0 < finiteQuenchedTailTau σ := finiteQuenchedTailTau_pos hσ
  have hden₁ :
      0 < σ * t₁ + finiteQuenchedTailTau σ * ((d : ℝ) / 2 - t₁) :=
    finiteQuenchedTailDen_pos hb hσ ht₁
  have hden₂ :
      0 < σ * t₂ + finiteQuenchedTailTau σ * ((d : ℝ) / 2 - t₂) :=
    finiteQuenchedTailDen_pos hb hσ ht₂
  set τ : ℝ := finiteQuenchedTailTau σ with hτ_def
  set b : ℝ := (d : ℝ) / 2 with hb_def
  have hkey :
      σ * τ * b * t₂ * (σ * t₁ + τ * (b - t₁)) -
          σ * τ * b * t₁ * (σ * t₂ + τ * (b - t₂)) =
        σ * τ ^ (2 : ℕ) * b ^ (2 : ℕ) * (t₂ - t₁) := by
    ring
  have hgap : 0 ≤ σ * τ ^ (2 : ℕ) * b ^ (2 : ℕ) * (t₂ - t₁) := by
    have h21 : 0 ≤ t₂ - t₁ := sub_nonneg.mpr h12
    positivity
  dsimp [finiteQuenchedTailExponent, interpolatedQuenchedTailExponent]
  rw [div_le_div_iff₀ hden₁ hden₂]
  nlinarith [hkey, hgap]

/-! ## Norms of the scalar comparison matrix -/

theorem assemblyConstantCoeffMatrixOfScalar_norm
    {d : ℕ} [NeZero d] {σ0 : ℝ} (hσ0 : 0 < σ0) :
    Ch03.constantCoeffMatrixNorm
        (assemblyConstantCoeffMatrixOfScalar (d := d) σ0 hσ0) = σ0 := by
  dsimp [Ch03.constantCoeffMatrixNorm, assemblyConstantCoeffMatrixOfScalar,
    scalarConstantCoeffMatrix]
  rw [Ch02.matrixNorm_eq_matrixOperatorNorm]
  exact Ch02.matrixOperatorNorm_smul_one_eq_of_nonneg hσ0.le

theorem assemblyConstantCoeffMatrixOfScalar_normHalf
    {d : ℕ} [NeZero d] {σ0 : ℝ} (hσ0 : 0 < σ0) :
    Ch03.constantCoeffMatrixNormHalf
        (assemblyConstantCoeffMatrixOfScalar (d := d) σ0 hσ0) =
      Real.sqrt σ0 := by
  dsimp [Ch03.constantCoeffMatrixNormHalf]
  rw [show Ch02.matrixNorm
        (assemblyConstantCoeffMatrixOfScalar (d := d) σ0 hσ0).matrix = σ0 from
      assemblyConstantCoeffMatrixOfScalar_norm hσ0]
  rw [Real.sqrt_eq_rpow]

/-! ## The optimized localization depth -/

/-- The depth `j ≈ (α/(4r)) log_3 (3^m / X)`, which balances the gradient and
forcing terms of the compressed two-exponent RHS. -/
def assemblyOptimizedDepth {d : ℕ} (α r : ℝ) (X : RegCoeffField d → ℝ)
    (aω : RegCoeffField d) (m : ℕ) : ℕ :=
  ⌈α * Real.log ((3 : ℝ) ^ m / X aω) / (4 * r * Real.log 3)⌉₊

theorem rpow_le_rpow_three_of_div_le {α r Y : ℝ} {J : ℕ}
    (hr : 0 < r) (hY : 1 ≤ Y)
    (hJ : α * Real.log Y / (4 * r * Real.log 3) ≤ (J : ℝ)) :
    Y ^ (α / 4) ≤ (3 : ℝ) ^ (r * (J : ℝ)) := by
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le one_pos hY
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hden : 0 < 4 * r * Real.log 3 := by positivity
  have hnum : α * Real.log Y ≤ (J : ℝ) * (4 * r * Real.log 3) :=
    (div_le_iff₀ hden).mp hJ
  have hkey :
      Real.log Y * (α / 4) ≤ Real.log 3 * (r * (J : ℝ)) := by
    nlinarith [hnum]
  calc
    Y ^ (α / 4) = Real.exp (Real.log Y * (α / 4)) :=
      Real.rpow_def_of_pos hY0 _
    _ ≤ Real.exp (Real.log 3 * (r * (J : ℝ))) := Real.exp_le_exp.mpr hkey
    _ = (3 : ℝ) ^ (r * (J : ℝ)) :=
      (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3) _).symm

theorem rpow_three_le_of_le_div_add_one {α r Y : ℝ} {J : ℕ}
    (hα : 0 ≤ α) (hr : 0 < r) (hr1 : r ≤ 1) (hY : 1 ≤ Y)
    (hJ : (J : ℝ) ≤ α * Real.log Y / (4 * r * Real.log 3) + 1) :
    (3 : ℝ) ^ (r * (J : ℝ)) ≤ 3 * Y ^ (α / 4) := by
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le one_pos hY
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hden : 0 < 4 * r * Real.log 3 := by positivity
  have hnum : (J : ℝ) * (4 * r * Real.log 3) ≤
      α * Real.log Y + 4 * r * Real.log 3 := by
    have := mul_le_mul_of_nonneg_right hJ hden.le
    calc
      (J : ℝ) * (4 * r * Real.log 3)
          ≤ (α * Real.log Y / (4 * r * Real.log 3) + 1) *
              (4 * r * Real.log 3) := this
      _ = α * Real.log Y + 4 * r * Real.log 3 := by
          field_simp
  have hkey :
      Real.log 3 * (r * (J : ℝ)) ≤
        Real.log 3 + Real.log Y * (α / 4) := by
    nlinarith [hnum, mul_le_mul_of_nonneg_right hr1 hlog3.le]
  calc
    (3 : ℝ) ^ (r * (J : ℝ)) = Real.exp (Real.log 3 * (r * (J : ℝ))) :=
      Real.rpow_def_of_pos (by norm_num) _
    _ ≤ Real.exp (Real.log 3 + Real.log Y * (α / 4)) :=
      Real.exp_le_exp.mpr hkey
    _ = 3 * Y ^ (α / 4) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3),
        Real.rpow_def_of_pos hY0]

/-! ## The manuscript-shaped RHS -/

/-- Manuscript-shaped RHS of the public quenched homogenization comparison
theorem: a single constant, a single power of the minimal-scale ratio, the
energy of `u` weighted by `sqrt σ0`, and the scale-normalized positive Besov
seminorm of the force. -/
def assemblyHomogenizationComparisonRHSOfScalar {d : ℕ} [NeZero d]
    (σ0 : ℝ) (hσ0 : 0 < σ0)
    (C α r₂ : ℝ) (X : RegCoeffField d → ℝ)
    (aω : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField aω)
    (m : ℕ) (g : Vec d → Vec d)
    (w : assemblyComparisonDatumOfScalar σ0 hσ0 aω ha m g) : ℝ :=
  C * ((3 : ℝ) ^ m / X aω) ^ (-α) *
    (Real.sqrt σ0 *
        Ch03.h1EnergyNormOnCube (assemblyOriginCube d m)
          (assemblyCoeffFamily aω ha) w.u +
      Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo
        (assemblyOriginCube d m) r₂ g)

/-- Finite-`sigma` wrapper for the manuscript-shaped RHS. -/
def assemblyHomogenizationComparisonRHS {d : ℕ} [NeZero d]
    {P : Ch04.RestrictionCoeffLaw d} (hP : Ch04.RestrictionLawCarrier P)
    (hStruct : Ch04.RestrictionStructuralLaw P)
    (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct)
    (C α r₂ : ℝ) (X : RegCoeffField d → ℝ)
    (aω : RegCoeffField d) (ha : Ch04.AELocallyUniformlyEllipticField aω)
    (m : ℕ) (g : Vec d → Vec d)
    (w : assemblyComparisonDatum hP hStruct hΓ aω ha m g) : ℝ :=
  assemblyHomogenizationComparisonRHSOfScalar
    (barSigmaLimit hP hStruct) hΓ.barSigmaLimit_pos
    C α r₂ X aω ha m g w

/-! ## Compression of the two-exponent RHS at the optimized depth -/

/-- At the optimized depth, the compressed two-exponent RHS is dominated by
the manuscript-shaped RHS with exponent `α/8`.  The constant is uniform in
the background scalar `σ0`, the random scale, the realization, the scale `m`,
and the data. -/
theorem exists_compressedTwoExponentRHS_le_homogenizationComparisonRHS
    (d : ℕ) [NeZero d] {Ccg α τ s r r₂ : ℝ}
    (hCcg : 0 < Ccg) (hα : 0 < α) (hτ : 0 < τ) (hτr : τ < r)
    (hs : 0 < s) (hr : 0 < r) (hrs : r < s / 2) (hs_one : s < 1)
    (hrr₂ : 3 / 2 * r ≤ r₂) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {σ0 : ℝ} (hσ0 : 0 < σ0) (X : RegCoeffField d → ℝ) (aω : RegCoeffField d)
        (ha : Ch04.AELocallyUniformlyEllipticField aω) (m : ℕ)
        (g : Vec d → Vec d)
        (w : assemblyComparisonDatumOfScalar σ0 hσ0 aω ha m g),
        1 ≤ X aω → X aω ≤ (3 : ℝ) ^ m →
        Ch03.ForceBesovRegularity (assemblyOriginCube d m) r₂ g →
        assemblyCompressedTwoExponentRHSOfScalar σ0 hσ0 Ccg α τ s r r₂ X aω ha
            m (assemblyOptimizedDepth α r X aω m) g w ≤
          assemblyHomogenizationComparisonRHSOfScalar σ0 hσ0 C (α / 8) r₂
            X aω ha m g w := by
  have hr_half : r < 1 / 2 := by nlinarith
  have hr1 : r ≤ 1 := by nlinarith
  have hcard : 0 < (Fintype.card (Fin d) : ℝ) := by
    rw [Fintype.card_fin]
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  -- geometric discount signs
  have hgeom_nonneg : ∀ {a : ℝ}, 0 ≤ a → 0 ≤ Ch02.geometricDiscount a 1 := by
    intro a ha
    dsimp [Ch02.geometricDiscount]
    have h31 : (3 : ℝ) ^ (-a * 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by nlinarith)
    linarith
  have hgeom_nonneg₂ : ∀ {a : ℝ}, 0 ≤ a → 0 ≤ Ch02.geometricDiscount a 2 := by
    intro a ha
    dsimp [Ch02.geometricDiscount]
    have h31 : (3 : ℝ) ^ (-a * 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by nlinarith)
    linarith
  -- the deterministic constants
  set DB : ℝ := assemblyErrorDiscount τ r * assemblyAmplitude d τ with hDB_def
  set KM : ℝ :=
    2 * (Fintype.card (Fin d) : ℝ) *
      ((assemblyEllipticityDiscount τ r * assemblyAmplitude d τ) ^ (2 : ℕ) + 1)
    with hKM_def
  have hamp_nonneg : 0 ≤ assemblyAmplitude d τ := by
    dsimp [assemblyAmplitude]
    exact mul_nonneg
      (le_trans (Real.sqrt_nonneg _)
        (le_max_left (assemblyResponseConstant d) (assemblyNegativeConstant d τ)))
      (Real.rpow_nonneg (by norm_num) _)
  have hDB_nonneg : 0 ≤ DB := by
    rw [hDB_def]
    refine mul_nonneg ?_ hamp_nonneg
    dsimp [assemblyErrorDiscount]
    refine Real.rpow_nonneg ?_ _
    exact mul_nonneg (hgeom_nonneg hr.le)
      (inv_nonneg.mpr (hgeom_nonneg (by linarith)))
  have hKM_pos : 0 < KM := by
    rw [hKM_def]
    positivity
  set K₁ : ℝ := 3 * r⁻¹ * DB with hK₁_def
  set K₂ : ℝ :=
    Real.rpow r (-(5 / 2 : ℝ)) * Real.sqrt KM * DB +
      Real.rpow r (-(5 / 2 : ℝ)) * KM + Real.rpow r (-3 : ℝ) * KM
    with hK₂_def
  have hK₁_nonneg : 0 ≤ K₁ := by
    rw [hK₁_def]
    exact mul_nonneg (by positivity) hDB_nonneg
  have hK₂_pos : 0 < K₂ := by
    rw [hK₂_def]
    have h₁ : 0 ≤ Real.rpow r (-(5 / 2 : ℝ)) * Real.sqrt KM * DB :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hr.le _) (Real.sqrt_nonneg _))
        hDB_nonneg
    have h₂ : 0 ≤ Real.rpow r (-(5 / 2 : ℝ)) * KM :=
      mul_nonneg (Real.rpow_nonneg hr.le _) hKM_pos.le
    have h₃ : 0 < Real.rpow r (-3 : ℝ) * KM :=
      mul_pos (Real.rpow_pos_of_pos hr _) hKM_pos
    linarith
  have houter_pos : 0 < s⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ := by
    have h12 : 0 < (1 / 2 : ℝ) - r := by linarith
    positivity
  refine ⟨s⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ * Ccg * (K₁ + K₂),
    by positivity, ?_⟩
  intro σ0 hσ0 X aω ha m g w hX1 hXm hg
  have hX0 : 0 < X aω := lt_of_lt_of_le one_pos hX1
  set Y : ℝ := (3 : ℝ) ^ m / X aω with hY_def
  have hY1 : 1 ≤ Y := (one_le_div hX0).mpr hXm
  have hY0 : 0 < Y := lt_of_lt_of_le one_pos hY1
  set J : ℕ := assemblyOptimizedDepth α r X aω m with hJ_def
  -- ceiling bounds for the optimized depth
  have hJ_arg_nonneg : 0 ≤ α * Real.log Y / (4 * r * Real.log 3) := by
    have hlogY : 0 ≤ Real.log Y := Real.log_nonneg hY1
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    positivity
  have hJ_lower : α * Real.log Y / (4 * r * Real.log 3) ≤ (J : ℝ) := by
    rw [hJ_def]
    dsimp [assemblyOptimizedDepth]
    rw [← hY_def]
    exact Nat.le_ceil _
  have hJ_upper : (J : ℝ) ≤ α * Real.log Y / (4 * r * Real.log 3) + 1 := by
    rw [hJ_def]
    dsimp [assemblyOptimizedDepth]
    rw [← hY_def]
    exact (Nat.ceil_lt_add_one hJ_arg_nonneg).le
  have hDWlow : Y ^ (α / 4) ≤ (3 : ℝ) ^ (r * (J : ℝ)) :=
    rpow_le_rpow_three_of_div_le hr hY1 hJ_lower
  have hDWup : (3 : ℝ) ^ (r * (J : ℝ)) ≤ 3 * Y ^ (α / 4) :=
    rpow_three_le_of_le_div_add_one hα.le hr hr1 hY1 hJ_upper
  -- the minimal-scale decay
  have hdec_eq : assemblyMinimalScaleDecay α X aω m = Y ^ (-(α / 2)) := by
    dsimp [assemblyMinimalScaleDecay]
    rw [← hY_def, Real.sqrt_eq_rpow, ← Real.rpow_mul hY0.le,
      show -α * (1 / 2 : ℝ) = -(α / 2) by ring]
  have hdec_nonneg : 0 ≤ assemblyMinimalScaleDecay α X aω m :=
    Real.sqrt_nonneg _
  have hdec_le_one : assemblyMinimalScaleDecay α X aω m ≤ 1 := by
    rw [hdec_eq]
    exact Real.rpow_le_one_of_one_le_of_nonpos hY1 (by linarith)
  set Z : ℝ := Y ^ (-(α / 8)) with hZ_def
  have hZ_nonneg : 0 ≤ Z := Real.rpow_nonneg hY0.le _
  -- product bounds for the depth weights
  have hprod₁ :
      Ch03.coarseGrainingDepthWeight r J * assemblyMinimalScaleDecay α X aω m
        ≤ 3 * Z := by
    dsimp [Ch03.coarseGrainingDepthWeight, Real.rpow_eq_pow]
    rw [hdec_eq]
    calc
      (3 : ℝ) ^ (r * (J : ℝ)) * Y ^ (-(α / 2))
          ≤ 3 * Y ^ (α / 4) * Y ^ (-(α / 2)) :=
        mul_le_mul_of_nonneg_right hDWup (Real.rpow_nonneg hY0.le _)
      _ = 3 * Y ^ (α / 4 + -(α / 2)) := by
        rw [mul_assoc, ← Real.rpow_add hY0]
      _ = 3 * Y ^ (-(α / 4)) := by
        rw [show α / 4 + -(α / 2) = -(α / 4) by ring]
      _ ≤ 3 * Z := by
        rw [hZ_def]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)) (by norm_num)
  have hhalf_ge :
      Y ^ (α / 8) ≤ (3 : ℝ) ^ (r * (J : ℝ) * (1 / 2 : ℝ)) := by
    have h1 : (Y ^ (α / 4)) ^ (1 / 2 : ℝ) ≤
        ((3 : ℝ) ^ (r * (J : ℝ))) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hY0.le _) hDWlow (by norm_num)
    calc
      Y ^ (α / 8) = (Y ^ (α / 4)) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_mul hY0.le, show α / 4 * (1 / 2 : ℝ) = α / 8 by ring]
      _ ≤ ((3 : ℝ) ^ (r * (J : ℝ))) ^ (1 / 2 : ℝ) := h1
      _ = (3 : ℝ) ^ (r * (J : ℝ) * (1 / 2 : ℝ)) := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hprod₂ :
      Ch03.coarseGrainingDepthWeight r J *
          Ch03.coarseGrainingDepthInvWeight r₂ J ≤ Z := by
    dsimp [Ch03.coarseGrainingDepthInvWeight, Ch03.coarseGrainingDepthWeight,
      Real.rpow_eq_pow]
    rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    have hexp : r * (J : ℝ) + -(r₂ * (J : ℝ)) ≤
        -(r * (J : ℝ) * (1 / 2 : ℝ)) := by
      have hJ_nonneg : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
      have hgap : 0 ≤ (r₂ - 3 / 2 * r) * (J : ℝ) :=
        mul_nonneg (by linarith) hJ_nonneg
      have hid : r * (J : ℝ) + -(r₂ * (J : ℝ)) =
          -(r * (J : ℝ) * (1 / 2 : ℝ)) - (r₂ - 3 / 2 * r) * (J : ℝ) := by
        ring
      linarith
    calc
      (3 : ℝ) ^ (r * (J : ℝ) + -(r₂ * (J : ℝ)))
          ≤ (3 : ℝ) ^ (-(r * (J : ℝ) * (1 / 2 : ℝ))) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = ((3 : ℝ) ^ (r * (J : ℝ) * (1 / 2 : ℝ)))⁻¹ :=
        Real.rpow_neg (by norm_num) _
      _ ≤ (Y ^ (α / 8))⁻¹ :=
        inv_anti₀ (Real.rpow_pos_of_pos hY0 _) hhalf_ge
      _ = Z := by
        rw [hZ_def, ← Real.rpow_neg hY0.le]
  have hprod₃ :
      Ch03.coarseGrainingDepthHalfWeight r J *
          (Ch03.coarseGrainingDepthWeight r J *
            assemblyMinimalScaleDecay α X aω m) *
          Ch03.coarseGrainingDepthInvWeight r₂ J ≤ Z := by
    dsimp [Ch03.coarseGrainingDepthHalfWeight,
      Ch03.coarseGrainingDepthWeight, Ch03.coarseGrainingDepthInvWeight,
      Real.rpow_eq_pow]
    rw [hdec_eq, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
    have hcollapse :
        (3 : ℝ) ^ (r / 2 * (J : ℝ)) *
            ((3 : ℝ) ^ (r * (J : ℝ)) * Y ^ (-(α / 2))) *
            (3 : ℝ) ^ (-(r₂ * (J : ℝ))) =
          (3 : ℝ) ^ (r / 2 * (J : ℝ) + r * (J : ℝ) + -(r₂ * (J : ℝ))) *
            Y ^ (-(α / 2)) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3),
        Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      ring
    rw [hcollapse]
    have hthree_le_one :
        (3 : ℝ) ^ (r / 2 * (J : ℝ) + r * (J : ℝ) + -(r₂ * (J : ℝ))) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
      have hJ_nonneg : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
      have hgap : 0 ≤ (r₂ - 3 / 2 * r) * (J : ℝ) :=
        mul_nonneg (by linarith) hJ_nonneg
      have hid : r / 2 * (J : ℝ) + r * (J : ℝ) + -(r₂ * (J : ℝ)) =
          -((r₂ - 3 / 2 * r) * (J : ℝ)) := by
        ring
      linarith
    have hY_le : Y ^ (-(α / 2)) ≤ Z := by
      rw [hZ_def]
      exact Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
    calc
      (3 : ℝ) ^ (r / 2 * (J : ℝ) + r * (J : ℝ) + -(r₂ * (J : ℝ))) *
          Y ^ (-(α / 2))
          ≤ 1 * Y ^ (-(α / 2)) :=
        mul_le_mul_of_nonneg_right hthree_le_one (Real.rpow_nonneg hY0.le _)
      _ = Y ^ (-(α / 2)) := one_mul _
      _ ≤ Z := hY_le
  -- envelope bounds
  have hB₁_eq :
      assemblyErrorEnvelope (d := d) α τ r X aω m =
        DB * assemblyMinimalScaleDecay α X aω m := by
    dsimp [assemblyErrorEnvelope]
  have hM_nonneg : 0 ≤ assemblyEllipticityEnvelope (d := d) α τ r X aω m := by
    dsimp [assemblyEllipticityEnvelope]
    positivity
  have hM_le : assemblyEllipticityEnvelope (d := d) α τ r X aω m ≤ KM := by
    dsimp [assemblyEllipticityEnvelope, assemblyEllipticityErrorEnvelope]
    rw [hKM_def]
    have hsq :
        (assemblyEllipticityDiscount τ r * assemblyAmplitude d τ *
            assemblyMinimalScaleDecay α X aω m) ^ (2 : ℕ) ≤
          (assemblyEllipticityDiscount τ r * assemblyAmplitude d τ) ^ (2 : ℕ) := by
      rw [mul_pow]
      have hdecsq : assemblyMinimalScaleDecay α X aω m ^ (2 : ℕ) ≤ 1 := by
        calc
          assemblyMinimalScaleDecay α X aω m ^ (2 : ℕ)
              ≤ 1 ^ (2 : ℕ) := pow_le_pow_left₀ hdec_nonneg hdec_le_one 2
          _ = 1 := one_pow 2
      exact mul_le_of_le_one_right (sq_nonneg _) hdecsq
    have hcard_nonneg : 0 ≤ 2 * (Fintype.card (Fin d) : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) hcard_nonneg
  have hsqrtM_le :
      Real.sqrt (assemblyEllipticityEnvelope (d := d) α τ r X aω m) ≤
        Real.sqrt KM := Real.sqrt_le_sqrt hM_le
  -- the constant matrix norms
  have hH_eq :
      Ch03.constantCoeffMatrixNormHalf
          (assemblyConstantCoeffMatrixOfScalar (d := d) σ0 hσ0) =
        Real.sqrt σ0 := assemblyConstantCoeffMatrixOfScalar_normHalf hσ0
  have hN_eq :
      Ch03.constantCoeffMatrixNorm
          (assemblyConstantCoeffMatrixOfScalar (d := d) σ0 hσ0) = σ0 :=
    assemblyConstantCoeffMatrixOfScalar_norm hσ0
  -- combine sqrt σ0 with the lower ellipticity envelope
  have hHL_eq :
      Real.sqrt σ0 *
          assemblyLowerEllipticityEnvelopeOfScalar σ0 α τ r X aω m =
        Real.sqrt (assemblyEllipticityEnvelope (d := d) α τ r X aω m) := by
    dsimp [assemblyLowerEllipticityEnvelopeOfScalar]
    rw [← Real.sqrt_mul hσ0.le, ← mul_assoc, mul_inv_cancel₀ hσ0.ne', one_mul]
  -- data signs
  have hE_nonneg :
      0 ≤ Ch03.h1EnergyNormOnCube (assemblyOriginCube d m)
        (assemblyCoeffFamily aω ha) w.u := by
    dsimp [Ch03.h1EnergyNormOnCube]
    positivity
  have hG_nonneg :
      0 ≤ Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo
        (assemblyOriginCube d m) r₂ g :=
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
      hg
  have hsqrtσ0E_nonneg :
      0 ≤ Real.sqrt σ0 *
        Ch03.h1EnergyNormOnCube (assemblyOriginCube d m)
          (assemblyCoeffFamily aω ha) w.u :=
    mul_nonneg (Real.sqrt_nonneg _) hE_nonneg
  have hDIW_nonneg : 0 ≤ Ch03.coarseGrainingDepthInvWeight r₂ J := by
    dsimp [Ch03.coarseGrainingDepthInvWeight, Ch03.coarseGrainingDepthWeight]
    positivity
  have hDW_nonneg : 0 ≤ Ch03.coarseGrainingDepthWeight r J := by
    dsimp [Ch03.coarseGrainingDepthWeight]
    positivity
  have hDHW_nonneg : 0 ≤ Ch03.coarseGrainingDepthHalfWeight r J := by
    dsimp [Ch03.coarseGrainingDepthHalfWeight]
    positivity
  -- abbreviations for the goal
  set E : ℝ :=
    Ch03.h1EnergyNormOnCube (assemblyOriginCube d m)
      (assemblyCoeffFamily aω ha) w.u with hE_def
  set G : ℝ :=
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo
      (assemblyOriginCube d m) r₂ g with hG_def
  set DW : ℝ := Ch03.coarseGrainingDepthWeight r J with hDW_def
  set DHW : ℝ := Ch03.coarseGrainingDepthHalfWeight r J with hDHW_def
  set DIW : ℝ := Ch03.coarseGrainingDepthInvWeight r₂ J with hDIW_def
  set dec : ℝ := assemblyMinimalScaleDecay α X aω m with hdec_def
  set M : ℝ := assemblyEllipticityEnvelope (d := d) α τ r X aω m with hM_def
  set L : ℝ := assemblyLowerEllipticityEnvelopeOfScalar σ0 α τ r X aω m
    with hL_def
  -- the four summands of the compressed bracket
  have hS₁ :
      r⁻¹ * Real.sqrt σ0 * (DW * (DB * dec)) * E ≤ K₁ * Z * (Real.sqrt σ0 * E) := by
    have hstep : DW * (DB * dec) ≤ DB * (3 * Z) := by
      calc
        DW * (DB * dec) = DB * (DW * dec) := by ring
        _ ≤ DB * (3 * Z) := mul_le_mul_of_nonneg_left hprod₁ hDB_nonneg
    calc
      r⁻¹ * Real.sqrt σ0 * (DW * (DB * dec)) * E
          ≤ r⁻¹ * Real.sqrt σ0 * (DB * (3 * Z)) * E := by
        refine mul_le_mul_of_nonneg_right ?_ hE_nonneg
        exact mul_le_mul_of_nonneg_left hstep
          (mul_nonneg (inv_nonneg.mpr hr.le) (Real.sqrt_nonneg _))
      _ = K₁ * Z * (Real.sqrt σ0 * E) := by
        rw [hK₁_def]; ring
  have hS₂ :
      Real.rpow r (-(5 / 2 : ℝ)) * Real.sqrt σ0 * DHW * L * (DW * (DB * dec)) *
          (DIW * G) ≤
        Real.rpow r (-(5 / 2 : ℝ)) * Real.sqrt KM * DB * Z * G := by
    have hfact :
        Real.rpow r (-(5 / 2 : ℝ)) * Real.sqrt σ0 * DHW * L *
            (DW * (DB * dec)) * (DIW * G) =
          Real.rpow r (-(5 / 2 : ℝ)) * (Real.sqrt σ0 * L) * DB *
            (DHW * (DW * dec) * DIW) * G := by
      ring
    rw [hfact, hHL_eq]
    calc
      Real.rpow r (-(5 / 2 : ℝ)) * Real.sqrt M * DB *
          (DHW * (DW * dec) * DIW) * G
          ≤ Real.rpow r (-(5 / 2 : ℝ)) * Real.sqrt M * DB * Z * G := by
        refine mul_le_mul_of_nonneg_right ?_ hG_nonneg
        exact mul_le_mul_of_nonneg_left hprod₃
          (mul_nonneg
            (mul_nonneg (Real.rpow_nonneg hr.le _) (Real.sqrt_nonneg _))
            hDB_nonneg)
      _ ≤ Real.rpow r (-(5 / 2 : ℝ)) * Real.sqrt KM * DB * Z * G := by
        refine mul_le_mul_of_nonneg_right ?_ hG_nonneg
        refine mul_le_mul_of_nonneg_right ?_ hZ_nonneg
        refine mul_le_mul_of_nonneg_right ?_ hDB_nonneg
        exact mul_le_mul_of_nonneg_left hsqrtM_le (Real.rpow_nonneg hr.le _)
  have hS₃ :
      Real.rpow r (-(5 / 2 : ℝ)) * DW * M * (DIW * G) ≤
        Real.rpow r (-(5 / 2 : ℝ)) * KM * Z * G := by
    have hfact :
        Real.rpow r (-(5 / 2 : ℝ)) * DW * M * (DIW * G) =
          Real.rpow r (-(5 / 2 : ℝ)) * M * (DW * DIW) * G := by
      ring
    rw [hfact]
    calc
      Real.rpow r (-(5 / 2 : ℝ)) * M * (DW * DIW) * G
          ≤ Real.rpow r (-(5 / 2 : ℝ)) * M * Z * G := by
        refine mul_le_mul_of_nonneg_right ?_ hG_nonneg
        exact mul_le_mul_of_nonneg_left hprod₂
          (mul_nonneg (Real.rpow_nonneg hr.le _) hM_nonneg)
      _ ≤ Real.rpow r (-(5 / 2 : ℝ)) * KM * Z * G := by
        refine mul_le_mul_of_nonneg_right ?_ hG_nonneg
        refine mul_le_mul_of_nonneg_right ?_ hZ_nonneg
        exact mul_le_mul_of_nonneg_left hM_le (Real.rpow_nonneg hr.le _)
  have hS₄ :
      Real.rpow r (-3 : ℝ) * DW * σ0 * (σ0⁻¹ * M) * (DIW * G) ≤
        Real.rpow r (-3 : ℝ) * KM * Z * G := by
    have hfact :
        Real.rpow r (-3 : ℝ) * DW * σ0 * (σ0⁻¹ * M) * (DIW * G) =
          Real.rpow r (-3 : ℝ) * (σ0 * σ0⁻¹) * M * (DW * DIW) * G := by
      ring
    rw [hfact, mul_inv_cancel₀ hσ0.ne']
    calc
      Real.rpow r (-3 : ℝ) * 1 * M * (DW * DIW) * G
          ≤ Real.rpow r (-3 : ℝ) * 1 * M * Z * G := by
        refine mul_le_mul_of_nonneg_right ?_ hG_nonneg
        exact mul_le_mul_of_nonneg_left hprod₂
          (mul_nonneg (mul_nonneg (Real.rpow_nonneg hr.le _) one_pos.le)
            hM_nonneg)
      _ ≤ Real.rpow r (-3 : ℝ) * KM * Z * G := by
        refine mul_le_mul_of_nonneg_right ?_ hG_nonneg
        refine mul_le_mul_of_nonneg_right ?_ hZ_nonneg
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left hM_le (Real.rpow_nonneg hr.le _)
  -- the bracket bound
  have hbracket :
      r⁻¹ * Real.sqrt σ0 * (DW * (DB * dec)) * E +
          (Real.rpow r (-(5 / 2 : ℝ)) * Real.sqrt σ0 * DHW * L *
              (DW * (DB * dec)) +
            Real.rpow r (-(5 / 2 : ℝ)) * DW * M +
            Real.rpow r (-3 : ℝ) * DW * σ0 * (σ0⁻¹ * M)) *
          (DIW * G) ≤
        (K₁ + K₂) * Z * (Real.sqrt σ0 * E + G) := by
    have hsum :
        r⁻¹ * Real.sqrt σ0 * (DW * (DB * dec)) * E +
            (Real.rpow r (-(5 / 2 : ℝ)) * Real.sqrt σ0 * DHW * L *
                (DW * (DB * dec)) +
              Real.rpow r (-(5 / 2 : ℝ)) * DW * M +
              Real.rpow r (-3 : ℝ) * DW * σ0 * (σ0⁻¹ * M)) *
            (DIW * G) =
          r⁻¹ * Real.sqrt σ0 * (DW * (DB * dec)) * E +
            (Real.rpow r (-(5 / 2 : ℝ)) * Real.sqrt σ0 * DHW * L *
                (DW * (DB * dec)) * (DIW * G) +
              Real.rpow r (-(5 / 2 : ℝ)) * DW * M * (DIW * G) +
              Real.rpow r (-3 : ℝ) * DW * σ0 * (σ0⁻¹ * M) * (DIW * G)) := by
      ring
    rw [hsum]
    have hsplit :
        K₁ * Z * (Real.sqrt σ0 * E) +
            (Real.rpow r (-(5 / 2 : ℝ)) * Real.sqrt KM * DB * Z * G +
              Real.rpow r (-(5 / 2 : ℝ)) * KM * Z * G +
              Real.rpow r (-3 : ℝ) * KM * Z * G) =
          K₁ * Z * (Real.sqrt σ0 * E) + K₂ * Z * G := by
      rw [hK₂_def]; ring
    have hmain := add_le_add hS₁ (add_le_add (add_le_add hS₂ hS₃) hS₄)
    rw [hsplit] at hmain
    refine hmain.trans ?_
    have hexpand :
        (K₁ + K₂) * Z * (Real.sqrt σ0 * E + G) =
          K₁ * Z * (Real.sqrt σ0 * E) + K₂ * Z * G +
            (K₂ * Z * (Real.sqrt σ0 * E) + K₁ * Z * G) := by
      ring
    rw [hexpand]
    have h₁ : 0 ≤ K₂ * Z * (Real.sqrt σ0 * E) :=
      mul_nonneg (mul_nonneg hK₂_pos.le hZ_nonneg) hsqrtσ0E_nonneg
    have h₂ : 0 ≤ K₁ * Z * G :=
      mul_nonneg (mul_nonneg hK₁_nonneg hZ_nonneg) hG_nonneg
    linarith
  -- assemble
  have hgoal :
      assemblyCompressedTwoExponentRHSOfScalar σ0 hσ0 Ccg α τ s r r₂ X aω ha
          m J g w =
        s⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ *
          (Ccg *
            (r⁻¹ * Real.sqrt σ0 * (DW * (DB * dec)) * E +
              (Real.rpow r (-(5 / 2 : ℝ)) * Real.sqrt σ0 * DHW * L *
                  (DW * (DB * dec)) +
                Real.rpow r (-(5 / 2 : ℝ)) * DW * M +
                Real.rpow r (-3 : ℝ) * DW * σ0 * (σ0⁻¹ * M)) *
              (DIW * G))) := by
    dsimp [assemblyCompressedTwoExponentRHSOfScalar]
    rw [hH_eq, hN_eq, hB₁_eq]
  have htarget :
      assemblyHomogenizationComparisonRHSOfScalar σ0 hσ0
          (s⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ * Ccg * (K₁ + K₂))
          (α / 8) r₂ X aω ha m g w =
        s⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ * Ccg *
          ((K₁ + K₂) * Z * (Real.sqrt σ0 * E + G)) := by
    dsimp [assemblyHomogenizationComparisonRHSOfScalar]
    rw [hE_def, hG_def, hZ_def, hY_def]
    ring
  rw [hgoal, htarget]
  calc
    s⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ *
        (Ccg *
          (r⁻¹ * Real.sqrt σ0 * (DW * (DB * dec)) * E +
            (Real.rpow r (-(5 / 2 : ℝ)) * Real.sqrt σ0 * DHW * L *
                (DW * (DB * dec)) +
              Real.rpow r (-(5 / 2 : ℝ)) * DW * M +
              Real.rpow r (-3 : ℝ) * DW * σ0 * (σ0⁻¹ * M)) *
            (DIW * G)))
        ≤ s⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ *
            (Ccg * ((K₁ + K₂) * Z * (Real.sqrt σ0 * E + G))) := by
      refine mul_le_mul_of_nonneg_left ?_ houter_pos.le
      exact mul_le_mul_of_nonneg_left hbracket hCcg.le
    _ = s⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ * Ccg *
          ((K₁ + K₂) * Z * (Real.sqrt σ0 * E + G)) := by
      ring

end

end Section57
end Ch05
end Book
end Homogenization
