/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationAssemblyRHS

/-! # Homogenization Assembly Endpoint -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open scoped ENNReal MatrixOrder

/-!
# Endpoint assembly for the public quenched homogenization theorem

This file packages the `Γ∞` endpoint controls into the same scalar-background
Ch3 assembly interface used by the finite-`sigma` branch.
-/

noncomputable section

/-- Endpoint assembly of the Ch3 comparison theorem with the collapsed
minimal-scale controls needed to bound every random coefficient in its RHS. -/
theorem exists_homogenizationComparison_controlledFactors_uniformEndpoint_expLogSq
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Ccg α : ℝ, 0 < Ccg ∧ 0 < α ∧
      α < max params.sUpper params.sLower ∧
      ∀ {τ s r : ℝ},
        max params.sUpper params.sLower < τ / 2 →
        α < τ / 2 →
        τ ≤ 1 →
        0 < s →
        0 < r →
        r < s / 2 →
        s < 1 →
        τ < r →
        let η : ℝ := ((d : ℕ) : ℝ)
        ∃ Cscale : ℝ, 0 < Cscale ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct),
            hInf.params = params →
            ∃ X : RegCoeffField d → ℝ,
              IsBigO P (gammaSigma η) X
                (Real.exp
                  (Cscale * (Real.log (2 + hInf.thetaHat)) ^ (2 : ℕ))) ∧
              (∀ aω, 1 ≤ X aω) ∧
                ∀ᵐ aω ∂P,
                  ∀ (ha : Ch04.AELocallyUniformlyEllipticField aω)
                    {m j : ℕ} {g : Vec d → Vec d},
                    (w : assemblyComparisonDatumOfScalar
                      (barSigmaLimit hP hStruct)
                      (hInf.toGammaSigma 1 zero_lt_one).barSigmaLimit_pos
                      aω ha m g) →
                    X aω ≤ (3 : ℝ) ^ m →
                    Ch03.ForceBesovRegularity (assemblyOriginCube d m) r g →
                    assemblyControlledFactorsConclusionOfScalar
                      (barSigmaLimit hP hStruct)
                      (hInf.toGammaSigma 1 zero_lt_one).barSigmaLimit_pos
                      Ccg α τ s r X aω ha m j g w := by
  obtain ⟨Ccg, hCcg_pos, hCcg⟩ :=
    (Ch03.generalCoarseGrainingL2TwoExponentTheory d).exists_constant
  obtain ⟨α, hα_pos, hαmax, hEbase⟩ :=
    exists_homogenizationErrorOnOriginCube_uniformEndpoint_expLogSq
      (d := d) params
  refine ⟨Ccg, α, hCcg_pos, hα_pos, hαmax, ?_⟩
  intro τ s r hτ_half hατ_half hτ_le_one hs_pos hr_pos hrs hs_lt_one hτr
  dsimp only
  have hτ2_pos : 0 < τ / 2 :=
    (max_sUpper_sLower_pos params).trans hτ_half
  have hτ_pos : 0 < τ := by linarith
  have hη_pos : 0 < ((d : ℕ) : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2)
      params.two_le_dim
  have hrq₁ : 0 ≤ r * (1 : ℝ) := by nlinarith
  have hδq₁ : 0 < (r - τ / 2) * (1 : ℝ) := by nlinarith
  have hrq₂ : 0 ≤ (r / 2) * (2 : ℝ) := by nlinarith
  have hδq₂ : 0 < (r / 2 - τ / 2) * (2 : ℝ) := by nlinarith
  obtain ⟨C₁, hC₁_pos, hLaw₁⟩ :=
    hEbase (τ := τ) (r := r) (q := 1)
      hτ_half hατ_half hτ_le_one hrq₁ hδq₁
      (by norm_num : (0 : ℝ) < 1)
  obtain ⟨C₂, hC₂_pos, hLaw₂⟩ :=
    hEbase (τ := τ) (r := r / 2) (q := 2)
      hτ_half hατ_half hτ_le_one hrq₂ hδq₂
      (by norm_num : (0 : ℝ) < 2)
  let η : ℝ := ((d : ℕ) : ℝ)
  let Cscale : ℝ :=
    4 * max 0 (Real.log ((3 * Real.log (2 : ℝ)) ^ η⁻¹)) +
      max C₁ C₂
  have hCscale_pos : 0 < Cscale := by
    dsimp [Cscale]
    have hnonneg :
        0 ≤ 4 * max 0
          (Real.log ((3 * Real.log (2 : ℝ)) ^ η⁻¹)) := by
      positivity
    have hmax_pos : 0 < max C₁ C₂ := hC₁_pos.trans_le (le_max_left C₁ C₂)
    nlinarith
  refine ⟨Cscale, hCscale_pos, ?_⟩
  intro P hP hStruct hInf hparams
  let : IsProbabilityMeasure P := hP.isProbability
  obtain ⟨X₁, hX₁O, hX₁_one, hX₁ae⟩ :=
    hLaw₁ hP hStruct hInf hparams
  obtain ⟨X₂, hX₂O, hX₂_one, hX₂ae⟩ :=
    hLaw₂ hP hStruct hInf hparams
  let X : RegCoeffField d → ℝ := fun aω => max (X₁ aω) (X₂ aω)
  have hXO :
      IsBigO P (gammaSigma η) X
        (Real.exp
          (Cscale * (Real.log (2 + hInf.thetaHat)) ^ (2 : ℕ))) := by
    simpa [X, Cscale, η] using
      isBigO_gammaSigma_max_two_expLogSq
        (μ := P) (η := η) (C₁ := C₁) (C₂ := C₂)
        (θ := hInf.thetaHat) (by simpa [η] using hη_pos)
        hInf.thetaHat_pos hX₁O hX₂O
  refine ⟨X, hXO, ?_, ?_⟩
  · intro aω
    dsimp [X]
    exact (hX₁_one aω).trans (le_max_left _ _)
  filter_upwards [hX₁ae, hX₂ae] with aω hX₁point hX₂point
  intro ha m j g
  let hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct :=
    hInf.toGammaSigma 1 zero_lt_one
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField aω ha
  let Q : TriadicCube d := originCube d ((m : ℕ) : ℤ)
  let σ0 : ℝ := barSigmaLimit hP hStruct
  let hσ0 : 0 < σ0 := hΓ.barSigmaLimit_pos
  let a0 : Ch03.ConstantCoeffMatrix d := scalarConstantCoeffMatrix σ0 hσ0
  intro w hXm hg
  let Cresp : ℝ :=
    Real.sqrt
      (4 * (Fintype.card (BlockCoord d) : ℝ) *
        (Fintype.card (NormalizedProbeIndex d) : ℝ))
  let Cneg : ℝ :=
    (Ch02.geometricDiscount (τ / 2) 1)⁻¹ *
      (2 * Real.sqrt ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)))
  let A : ℝ := max Cresp Cneg * Real.rpow (3 : ℝ) (τ / 2)
  let R : ℝ := Real.sqrt (((3 : ℝ) ^ m / X aω) ^ (-α))
  let G₁ : ℝ :=
    Real.rpow
      (Ch02.geometricDiscount r 1 *
        (Ch02.geometricDiscount (r - τ / 2) 1)⁻¹)
      (1 / (1 : ℝ))
  let G₂ : ℝ :=
    Real.rpow
      (Ch02.geometricDiscount (r / 2) 2 *
        (Ch02.geometricDiscount (r / 2 - τ / 2) 2)⁻¹)
      (1 / 2 : ℝ)
  let B₁ : ℝ := G₁ * A * R
  let B₂ : ℝ := G₂ * A * R
  let M : ℝ := 2 * (Fintype.card (Fin d) : ℝ) * (B₂ ^ (2 : ℕ) + 1)
  have hX₁_le_X : X₁ aω ≤ X aω := by
    dsimp [X]
    exact le_max_left _ _
  have hX₂_le_X : X₂ aω ≤ X aω := by
    dsimp [X]
    exact le_max_right _ _
  have hX₁m : X₁ aω ≤ (3 : ℝ) ^ m := hX₁_le_X.trans hXm
  have hX₂m : X₂ aω ≤ (3 : ℝ) ^ m := hX₂_le_X.trans hXm
  have hX₁_pos : 0 < X₁ aω :=
    lt_of_lt_of_le zero_lt_one (hX₁_one aω)
  have hX₂_pos : 0 < X₂ aω :=
    lt_of_lt_of_le zero_lt_one (hX₂_one aω)
  have hX_pos : 0 < X aω := lt_of_lt_of_le hX₁_pos hX₁_le_X
  have hpowm_pos : 0 < (3 : ℝ) ^ m := by positivity
  have hR₁_le_R :
      Real.sqrt (((3 : ℝ) ^ m / X₁ aω) ^ (-α)) ≤ R := by
    dsimp [R]
    exact sqrt_rpow_neg_div_mono_of_le
      hpowm_pos hX₁_pos hX_pos hX₁_le_X hα_pos
  have hR₂_le_R :
      Real.sqrt (((3 : ℝ) ^ m / X₂ aω) ^ (-α)) ≤ R := by
    dsimp [R]
    exact sqrt_rpow_neg_div_mono_of_le
      hpowm_pos hX₂_pos hX_pos hX₂_le_X hα_pos
  have hdisc_r_nonneg : 0 ≤ Ch02.geometricDiscount r 1 := by
    simpa [Ch02.geometricDiscount_eq_old] using
      Homogenization.geometricDiscount_nonneg hrq₁
  have hdisc_delta₁_pos : 0 < Ch02.geometricDiscount (r - τ / 2) 1 := by
    simpa [Ch02.geometricDiscount_eq_old] using
      Homogenization.geometricDiscount_pos hδq₁
  have hG₁_nonneg : 0 ≤ G₁ := by
    dsimp [G₁]
    exact Real.rpow_nonneg
      (mul_nonneg hdisc_r_nonneg
        (inv_nonneg.mpr hdisc_delta₁_pos.le)) _
  have hdisc_r₂_nonneg : 0 ≤ Ch02.geometricDiscount (r / 2) 2 := by
    simpa [Ch02.geometricDiscount_eq_old] using
      Homogenization.geometricDiscount_nonneg hrq₂
  have hdisc_delta₂_pos :
      0 < Ch02.geometricDiscount (r / 2 - τ / 2) 2 := by
    simpa [Ch02.geometricDiscount_eq_old] using
      Homogenization.geometricDiscount_pos hδq₂
  have hG₂_nonneg : 0 ≤ G₂ := by
    dsimp [G₂]
    exact Real.rpow_nonneg
      (mul_nonneg hdisc_r₂_nonneg
        (inv_nonneg.mpr hdisc_delta₂_pos.le)) _
  have hdisc_tau_pos : 0 < Ch02.geometricDiscount (τ / 2) 1 := by
    simpa [Ch02.geometricDiscount_eq_old] using
      Homogenization.geometricDiscount_pos
        (by nlinarith : 0 < (τ / 2) * (1 : ℝ))
  have hCresp_nonneg : 0 ≤ Cresp := by
    dsimp [Cresp]
    positivity
  have hCneg_nonneg : 0 ≤ Cneg := by
    dsimp [Cneg]
    exact mul_nonneg (inv_nonneg.mpr hdisc_tau_pos.le) (by positivity)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (hCresp_nonneg.trans (le_max_left Cresp Cneg))
      (by positivity)
  have hB₁_nonneg : 0 ≤ B₁ := by
    dsimp [B₁]
    exact mul_nonneg (mul_nonneg hG₁_nonneg hA_nonneg) (Real.sqrt_nonneg _)
  have hB₂_nonneg : 0 ≤ B₂ := by
    dsimp [B₂]
    exact mul_nonneg (mul_nonneg hG₂_nonneg hA_nonneg) (Real.sqrt_nonneg _)
  have hcomparison :
      Ch03.homogenizationComparisonNegativeBesovLHS Q F a0 s w.u w.v ≤
        Ch03.generalCoarseGrainingL2TwoExponentRHS
          Ccg Q F a0 s r r j g w.u := by
    exact
      hCcg (Q := Q) (a := F) (a0 := a0) (s := s) (r := r)
        (r₂ := r) (j := j) (g := g)
        (scalarConstantCoeffMatrix_isPositiveScalarMatrix hσ0) w
        hs_pos hr_pos hrs hs_lt_one le_rfl hg
  have hparent₁ :
      Ch02.HomogenizationErrorOnCube Q r
          Ch02.MultiscaleExponent.infinity (.finite 1) F a0.matrix ≤ B₁ := by
    have hraw := hX₁point ha (m := m) hX₁m
    have hraw' :
        Ch02.HomogenizationErrorOnCube Q r
            Ch02.MultiscaleExponent.infinity (.finite 1) F a0.matrix ≤
          G₁ * A *
            Real.sqrt (((3 : ℝ) ^ m / X₁ aω) ^ (-α)) := by
      simpa [Q, F, σ0, hσ0, a0, Cresp, Cneg, A, G₁,
        scalarConstantCoeffMatrix_matrix] using hraw
    calc
      Ch02.HomogenizationErrorOnCube Q r
          Ch02.MultiscaleExponent.infinity (.finite 1) F a0.matrix
          ≤ G₁ * A *
              Real.sqrt (((3 : ℝ) ^ m / X₁ aω) ^ (-α)) := hraw'
      _ ≤ G₁ * A * R :=
          mul_le_mul_of_nonneg_left hR₁_le_R
            (mul_nonneg hG₁_nonneg hA_nonneg)
      _ = B₁ := rfl
  have hdepth_base :=
    coarseGrainingHomogenizationErrorAtDepth_le_depthWeight_mul_parent
      (Q := Q) (a := F) (a0 := a0) (s := r) hr_pos j
  have hdepth_weight_nonneg : 0 ≤ Ch03.coarseGrainingDepthWeight r j := by
    dsimp [Ch03.coarseGrainingDepthWeight]
    positivity
  have hdepth :
      Ch03.coarseGrainingHomogenizationErrorAtDepth Q F a0 r j ≤
        Ch03.coarseGrainingDepthWeight r j * B₁ := by
    calc
      Ch03.coarseGrainingHomogenizationErrorAtDepth Q F a0 r j
          ≤ Ch03.coarseGrainingDepthWeight r j *
              Ch02.HomogenizationErrorOnCube Q r
                Ch02.MultiscaleExponent.infinity (.finite 1) F a0.matrix :=
            hdepth_base
      _ ≤ Ch03.coarseGrainingDepthWeight r j * B₁ :=
            mul_le_mul_of_nonneg_left hparent₁ hdepth_weight_nonneg
  have hparent₂ :
      Ch02.HomogenizationErrorOnCube Q (r / 2)
          Ch02.MultiscaleExponent.infinity (.finite 2) F
          (scalarMatrix (d := d) σ0) ≤ B₂ := by
    have hraw := hX₂point ha (m := m) hX₂m
    have hraw' :
        Ch02.HomogenizationErrorOnCube Q (r / 2)
            Ch02.MultiscaleExponent.infinity (.finite 2) F
            (scalarMatrix (d := d) σ0) ≤
          G₂ * A *
            Real.sqrt (((3 : ℝ) ^ m / X₂ aω) ^ (-α)) := by
      simpa [Q, F, σ0, Cresp, Cneg, A, G₂] using hraw
    calc
      Ch02.HomogenizationErrorOnCube Q (r / 2)
          Ch02.MultiscaleExponent.infinity (.finite 2) F
          (scalarMatrix (d := d) σ0)
          ≤ G₂ * A *
              Real.sqrt (((3 : ℝ) ^ m / X₂ aω) ^ (-α)) := hraw'
      _ ≤ G₂ * A * R :=
          mul_le_mul_of_nonneg_left hR₂_le_R
            (mul_nonneg hG₂_nonneg hA_nonneg)
      _ = B₂ := rfl
  have hr_half_pos : 0 < r / 2 := half_pos hr_pos
  have hweighted :
      max (σ0⁻¹ * Ch02.LambdaSq Q (r / 2) (.finite 2) F)
          (σ0 * (Ch02.lambdaSq Q (r / 2) (.finite 2) F)⁻¹) ≤ M := by
    simpa [M, B₂] using
      weightedEllipticity_finite_two_le_of_homogenizationError_bound
        (Q := Q) (a := F) (s := r / 2) (σ := σ0) (B := B₂)
        hr_half_pos hσ0 hparent₂
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hlambda_inv :
      (Ch02.lambdaSq Q (r / 2) (.finite 2) F)⁻¹ ≤ σ0⁻¹ * M :=
    lambdaSq_inv_le_inv_sigma_mul_of_weightedEllipticity_le
      (Q := Q) (a := F) (s := r / 2) (σ := σ0) (M := M)
      hσ0 hweighted
  have hsqrt_product :
      Real.sqrt (Ch02.LambdaSq Q (r / 2) (.finite 2) F) *
          Real.sqrt ((Ch02.lambdaSq Q (r / 2) (.finite 2) F)⁻¹) ≤ M :=
    sqrt_LambdaSq_mul_sqrt_lambdaSq_inv_le_of_weightedEllipticity_le
      (Q := Q) (a := F) (s := r / 2) (σ := σ0) (M := M)
      hr_half_pos hσ0 hM_nonneg hweighted
  exact ⟨hcomparison, hdepth, hweighted, hlambda_inv, hsqrt_product⟩

/-- Endpoint two-exponent assembly of the repaired Ch3 comparison theorem. -/
theorem exists_homogenizationComparison_controlledFactors_twoExponent_uniformEndpoint_expLogSq
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Ccg α : ℝ, 0 < Ccg ∧ 0 < α ∧
      α < max params.sUpper params.sLower ∧
      ∀ {τ s r r₂ : ℝ},
        max params.sUpper params.sLower < τ / 2 →
        α < τ / 2 →
        τ ≤ 1 →
        0 < s →
        0 < r →
        r < s / 2 →
        s < 1 →
        τ < r →
        r ≤ r₂ →
        let η : ℝ := ((d : ℕ) : ℝ)
        ∃ Cscale : ℝ, 0 < Cscale ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct),
            hInf.params = params →
            ∃ X : RegCoeffField d → ℝ,
              IsBigO P (gammaSigma η) X
                (Real.exp
                  (Cscale * (Real.log (2 + hInf.thetaHat)) ^ (2 : ℕ))) ∧
              (∀ aω, 1 ≤ X aω) ∧
                ∀ᵐ aω ∂P,
                  ∀ (ha : Ch04.AELocallyUniformlyEllipticField aω)
                    {m j : ℕ} {g : Vec d → Vec d},
                    (w : assemblyComparisonDatumOfScalar
                      (barSigmaLimit hP hStruct)
                      (hInf.toGammaSigma 1 zero_lt_one).barSigmaLimit_pos
                      aω ha m g) →
                    X aω ≤ (3 : ℝ) ^ m →
                    Ch03.ForceBesovRegularity (assemblyOriginCube d m) r₂ g →
                    assemblyControlledFactorsTwoExponentConclusionOfScalar
                      (barSigmaLimit hP hStruct)
                      (hInf.toGammaSigma 1 zero_lt_one).barSigmaLimit_pos
                      Ccg α τ s r r₂ X aω ha m j g w := by
  obtain ⟨Ccg, hCcg_pos, hCcg⟩ :=
    (Ch03.generalCoarseGrainingL2TwoExponentTheory d).exists_constant
  obtain ⟨_, α, _, hα_pos, hαmax, hcontrolled⟩ :=
    exists_homogenizationComparison_controlledFactors_uniformEndpoint_expLogSq
      (d := d) params
  refine ⟨Ccg, α, hCcg_pos, hα_pos, hαmax, ?_⟩
  intro τ s r r₂ hτ_half hατ_half hτ_le_one hs_pos hr_pos
    hrs hs_lt_one hτr hr₂
  dsimp only
  obtain ⟨Cscale, hCscale, hlaw⟩ :=
    hcontrolled hτ_half hατ_half hτ_le_one hs_pos hr_pos
      hrs hs_lt_one hτr
  refine ⟨Cscale, hCscale, ?_⟩
  intro P hP hStruct hInf hparams
  obtain ⟨X, hXO, hXone, hAE⟩ :=
    hlaw hP hStruct hInf hparams
  refine ⟨X, hXO, hXone, ?_⟩
  filter_upwards [hAE] with aω hpoint
  intro ha m j g w hXm hg₂
  let Q : TriadicCube d := assemblyOriginCube d m
  let F : Ch02.TriadicCoeffFamily d := assemblyCoeffFamily aω ha
  let σ0 : ℝ := barSigmaLimit hP hStruct
  let hσ0 : 0 < σ0 := (hInf.toGammaSigma 1 zero_lt_one).barSigmaLimit_pos
  let a0 : Ch03.ConstantCoeffMatrix d :=
    assemblyConstantCoeffMatrixOfScalar σ0 hσ0
  have hg₁ : Ch03.ForceBesovRegularity Q r g := by
    dsimp [Q]
    exact hg₂.of_exponent_le hr₂
  have hlegacy :
      assemblyControlledFactorsConclusionOfScalar
        σ0 hσ0 _ α τ s r X aω ha m j g w :=
    hpoint ha w hXm (by simpa [Q, σ0, hσ0] using hg₁)
  have hcomparison :
      Ch03.homogenizationComparisonNegativeBesovLHS Q F a0 s w.u w.v ≤
        Ch03.generalCoarseGrainingL2TwoExponentRHS
          Ccg Q F a0 s r r₂ j g w.u := by
    exact
      hCcg (Q := Q) (a := F) (a0 := a0) (s := s) (r := r)
        (r₂ := r₂) (j := j) (g := g)
        (by
          dsimp [a0, assemblyConstantCoeffMatrixOfScalar]
          exact scalarConstantCoeffMatrix_isPositiveScalarMatrix hσ0)
        w hs_pos hr_pos hrs hs_lt_one hr₂ hg₂
  dsimp [assemblyControlledFactorsTwoExponentConclusionOfScalar,
    Q, F, σ0, hσ0, a0]
  dsimp [assemblyControlledFactorsConclusionOfScalar, Q, F, σ0, hσ0, a0]
    at hlegacy
  rcases hlegacy with ⟨_, hdepth, hweighted, hlambda_inv, hsqrt_product⟩
  exact ⟨hcomparison, hdepth, hweighted, hlambda_inv, hsqrt_product⟩

/-- Endpoint homogenization comparison above one collapsed minimal scale, using
the repaired scale-separated forcing exponent. -/
theorem exists_homogenizationComparison_compressedTwoExponentRHS_uniformEndpoint_expLogSq
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Ccg α : ℝ, 0 < Ccg ∧ 0 < α ∧
      α < max params.sUpper params.sLower ∧
      ∀ {τ s r r₂ : ℝ},
        max params.sUpper params.sLower < τ / 2 →
        α < τ / 2 →
        τ ≤ 1 →
        0 < s →
        0 < r →
        r < s / 2 →
        s < 1 →
        τ < r →
        r ≤ r₂ →
        let η : ℝ := ((d : ℕ) : ℝ)
        ∃ Cscale : ℝ, 0 < Cscale ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hInf : GammaInfinityCoarseGrainedEllipticity P hP hStruct),
            hInf.params = params →
            ∃ X : RegCoeffField d → ℝ,
              IsBigO P (gammaSigma η) X
                (Real.exp
                  (Cscale * (Real.log (2 + hInf.thetaHat)) ^ (2 : ℕ))) ∧
              (∀ aω, 1 ≤ X aω) ∧
                ∀ᵐ aω ∂P,
                  ∀ (ha : Ch04.AELocallyUniformlyEllipticField aω)
                    {m j : ℕ} {g : Vec d → Vec d}
                    (w : assemblyComparisonDatumOfScalar
                      (barSigmaLimit hP hStruct)
                      (hInf.toGammaSigma 1 zero_lt_one).barSigmaLimit_pos
                      aω ha m g),
                    X aω ≤ (3 : ℝ) ^ m →
                    Ch03.ForceBesovRegularity (assemblyOriginCube d m) r₂ g →
                    Ch03.homogenizationComparisonNegativeBesovLHS
                        (assemblyOriginCube d m) (assemblyCoeffFamily aω ha)
                        (assemblyConstantCoeffMatrixOfScalar
                          (barSigmaLimit hP hStruct)
                          (hInf.toGammaSigma 1 zero_lt_one).barSigmaLimit_pos)
                        s w.u w.v ≤
                      assemblyCompressedTwoExponentRHSOfScalar
                        (barSigmaLimit hP hStruct)
                        (hInf.toGammaSigma 1 zero_lt_one).barSigmaLimit_pos
                        Ccg α τ s r r₂ X aω ha m j g w := by
  obtain ⟨Ccg, α, hCcg, hα, hαmax, hcontrolled⟩ :=
    exists_homogenizationComparison_controlledFactors_twoExponent_uniformEndpoint_expLogSq
      (d := d) params
  refine ⟨Ccg, α, hCcg, hα, hαmax, ?_⟩
  intro τ s r r₂ hτ hατ hτ_one hs hr hrs hs_one hτr hr₂
  dsimp only
  obtain ⟨Cscale, hCscale, hlaw⟩ :=
    hcontrolled hτ hατ hτ_one hs hr hrs hs_one hτr hr₂
  refine ⟨Cscale, hCscale, ?_⟩
  intro P hP hStruct hInf hparams
  obtain ⟨X, hXO, hXone, hAE⟩ :=
    hlaw hP hStruct hInf hparams
  refine ⟨X, hXO, hXone, ?_⟩
  simpa using
    ae_homogenizationComparison_compressedTwoExponentRHSOfScalar_of_ae_controlledFactors
      (P := P)
      (σ0 := barSigmaLimit hP hStruct)
      (hInf.toGammaSigma 1 zero_lt_one).barSigmaLimit_pos
      (Ccg := Ccg) (α := α) (τ := τ) (s := s) (r := r)
      (r₂ := r₂) (X := X) hCcg hs hr hrs hs_one hAE

end

end Section57
end Ch05
end Book
end Homogenization
