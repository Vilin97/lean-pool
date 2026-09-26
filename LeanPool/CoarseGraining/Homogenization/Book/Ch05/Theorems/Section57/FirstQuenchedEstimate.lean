/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.AnnealedJLimit

/-! # First Quenched Estimate -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums

/-!
# The concentration step for the first quenched estimate

This file records the part of Corollary `c.first.quenched.estimate` which is
already supplied by the Chapter 4 concentration lemma: a unit-scale Γσ tail for
the chosen deterministic block vectors propagates to larger scales around the
corresponding annealed response.  The remaining Section 5.7 work is to produce
that unit-scale tail and the annealed bound for the limiting normalization
`\overline A`.
-/

noncomputable section

/-- Concentration plus deterministic annealed domination, in the form used by
the first quenched estimate.

The constant is chosen before the law `Pμ`, so it is independent of the
probability measure. -/
theorem firstQuenchedEstimate_concentrationStep
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ) (hσ_le_two : σ ≤ 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Pμ : Ch04.RestrictionCoeffLaw d} [IsProbabilityMeasure Pμ],
        Ch04.RestrictionLawCarrier Pμ → Ch04.RestrictionStationaryLaw Pμ →
        Ch04.RestrictionUnitRangeDependentLaw Pμ →
      ∀ (P Qv : BlockVec d) {θ : ℝ},
        0 < θ →
        IsBigO Pμ (gammaSigma σ)
          (Ch04.blockJObservableCubeSetBlockVec (originCube d 0) P Qv) θ →
      ∀ {n m : ℤ}, 0 ≤ n → n < m → ∀ {R : ℝ},
        (∫ b,
          Ch04.blockJObservableCubeSetBlockVec (originCube d n) P Qv b ∂Pμ) ≤ R →
        IsBigOWith Pμ (gammaSigma σ)
          (fun a =>
            Ch04.blockJObservableCubeSetBlockVec (originCube d m) P Qv a - R)
          (C * (3 : ℝ) ^ (-(d : ℝ) / 2 * (Int.toNat (m - n) : ℝ)) * θ) := by
  obtain ⟨C, hC_pos, hC⟩ :=
    Ch04.concentration_of_blockJObservableCubeSetBlockVec
      (d := d) hσ_pos hσ_le_two
  refine ⟨C, hC_pos, ?_⟩
  intro Pμ hPμ_inst hPμ hstat hunit P Qv θ hθ_pos htail n m hn hnm R hR
  let : IsProbabilityMeasure Pμ := hPμ_inst
  have hfluct :
      IsBigOWith Pμ (gammaSigma σ)
        (fun a =>
          Ch04.blockJObservableCubeSetBlockVec (originCube d m) P Qv a -
            ∫ b,
              Ch04.blockJObservableCubeSetBlockVec (originCube d n) P Qv b ∂Pμ)
        (C * (3 : ℝ) ^ (-(d : ℝ) / 2 * (Int.toNat (m - n) : ℝ)) * θ) :=
    hC hθ_pos hPμ hstat hunit P Qv htail hn hnm
  exact hfluct.of_le fun a => by
    linarith

/-- First quenched concentration step for the limiting normalization
`\overline A`: the unit-cube Γσ tail from `(P5)` propagates from scale `n` to
scale `m`, centered at any deterministic upper bound for the annealed response
at scale `n`, with the concentration exponent truncated to `σ ∧ 2`.

The constant is chosen after `d, σ` and before the law, hence is independent of
the probability measure and of the Γσ scale `thetaHat`. -/
theorem firstQuenchedEstimate_limitNormalized_concentration
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Pμ : Ch04.RestrictionCoeffLaw d}
        (hPμ : Ch04.RestrictionLawCarrier Pμ)
        (hStruct : Ch04.RestrictionStructuralLaw Pμ)
        (hΓ : GammaSigmaCoarseGrainedEllipticity Pμ hPμ hStruct),
        hΓ.sigma = σ →
      ∀ (e : FullBlockVec d),
        (∀ α : BlockCoord d, |e α| ≤ 1) →
      ∀ {n m : ℤ}, 0 ≤ n → n < m → ∀ {R : ℝ},
        (∫ b,
          limitNormalizedBlockJObservable hPμ hStruct (originCube d n) e b ∂Pμ) ≤ R →
        IsBigOWith Pμ (gammaSigma (min σ 2))
          (fun a =>
            limitNormalizedBlockJObservable hPμ hStruct (originCube d m) e a - R)
          (C * (3 : ℝ) ^ (-(d : ℝ) / 2 * (Int.toNat (m - n) : ℝ)) *
            (thetaAtScale hPμ hStruct (0 : ℤ) * hΓ.thetaHat)) := by
  have hσconc_pos : 0 < min σ 2 := by
    exact lt_min hσ_pos (by norm_num : (0 : ℝ) < 2)
  have hσconc_le_two : min σ 2 ≤ 2 := min_le_right σ 2
  obtain ⟨Cconc, hCconc_pos, hconc⟩ :=
    firstQuenchedEstimate_concentrationStep (d := d)
      hσconc_pos hσconc_le_two
  let Cdim : ℝ := (Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)
  let C : ℝ := Cconc * Cdim
  have hcard_pos : 0 < (Fintype.card (BlockCoord d) : ℝ) := by
    exact_mod_cast
      (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (BlockCoord d)))
  have hCdim_pos : 0 < Cdim := by
    dsimp [Cdim]
    exact pow_pos hcard_pos 2
  refine ⟨C, mul_pos hCconc_pos hCdim_pos, ?_⟩
  intro Pμ hPμ hStruct hΓ hσ_eq e he n m hn hnm R hR
  let : IsProbabilityMeasure Pμ := hPμ.isProbability
  let Pvec : BlockVec d := scalarLimitInvSqrtBlockVec hPμ hStruct e
  let Qvec : BlockVec d := scalarLimitSqrtBlockVec hPμ hStruct e
  let base : ℝ := thetaAtScale hPμ hStruct (0 : ℤ) * hΓ.thetaHat
  let θ : ℝ := Cdim * base
  have hθ0_one :
      1 ≤ thetaAtScale hPμ hStruct (0 : ℤ) := by
    simpa using
      Section54.GoodScale.one_le_thetaAtScale_of_P4
        hPμ hStruct hΓ.toQuantitativeCoarseGrainedEllipticity 0
  have hθ0_pos : 0 < thetaAtScale hPμ hStruct (0 : ℤ) :=
    lt_of_lt_of_le zero_lt_one hθ0_one
  have hbase_pos : 0 < base := by
    dsimp [base]
    exact mul_pos hθ0_pos hΓ.thetaHat_pos
  have hθ_pos : 0 < θ := by
    dsimp [θ]
    exact mul_pos hCdim_pos hbase_pos
  have htail :
      IsBigO Pμ (gammaSigma (min σ 2))
        (Ch04.blockJObservableCubeSetBlockVec (originCube d 0) Pvec Qvec) θ := by
    have htail0 := hΓ.limitNormalizedBlockJObservable_unit_isBigO e he
    have htailσ :
        IsBigO Pμ (gammaSigma σ)
          (Ch04.blockJObservableCubeSetBlockVec (originCube d 0) Pvec Qvec)
          θ := by
      simpa [limitNormalizedBlockJObservable, Pvec, Qvec, θ, Cdim, base, hσ_eq]
        using htail0
    exact Ch04.IsBigO.gammaSigma_mono_exponent
      (μ := Pμ) (ρ := min σ 2) (σ := σ)
      (min_le_left σ 2) htailσ
  have hR' :
      (∫ b,
        Ch04.blockJObservableCubeSetBlockVec (originCube d n) Pvec Qvec b ∂Pμ) ≤ R := by
    simpa [limitNormalizedBlockJObservable, Pvec, Qvec] using hR
  have hstep :
      IsBigOWith Pμ (gammaSigma (min σ 2))
        (fun a =>
          Ch04.blockJObservableCubeSetBlockVec (originCube d m) Pvec Qvec a - R)
        (Cconc * (3 : ℝ) ^ (-(d : ℝ) / 2 * (Int.toNat (m - n) : ℝ)) * θ) :=
    hconc hPμ hStruct.stationary hStruct.unit_range Pvec Qvec
      hθ_pos htail hn hnm hR'
  let decay : ℝ :=
    (3 : ℝ) ^ (-(d : ℝ) / 2 * (Int.toNat (m - n) : ℝ))
  have hscale :
      Cconc * decay * θ = C * decay * base := by
    dsimp [C, θ]
    ring
  rw [hscale] at hstep
  simpa [limitNormalizedBlockJObservable, Pvec, Qvec, C, base, decay] using hstep

/-- Corollary `c.first.quenched.estimate`, in the limiting scalar
normalization used by Section 5.7, with the quenched fluctuation controlled in
the `Γ_{σ ∧ 2}` class.

The fluctuation constant, the annealed entry constant, and the algebraic
exponent are selected before the law `Pμ`.  The entry scale is the deterministic
annealed scale associated to `Centry`; after that shift, the annealed theorem
controls the deterministic centering and the Γσ concentration estimate gives
the quenched fluctuation term. -/
theorem firstQuenchedEstimate_limitNormalized
    {d : ℕ} [NeZero d] {σ : ℝ}
    (hσ_pos : 0 < σ)
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Cfluct Centry α : ℝ, 0 < Cfluct ∧ 0 < Centry ∧ 0 < α ∧
      ∀ {Pμ : Ch04.RestrictionCoeffLaw d}
        (hPμ : Ch04.RestrictionLawCarrier Pμ)
        (hStruct : Ch04.RestrictionStructuralLaw Pμ)
        (hΓ : GammaSigmaCoarseGrainedEllipticity Pμ hPμ hStruct),
        hΓ.sigma = σ → hΓ.params = params →
      ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
      ∀ {n m : ℕ}, n < m →
        let N0 : ℕ :=
          annealedAlgebraicEntryScale Pμ
            hΓ.toQuantitativeCoarseGrainedEllipticity Centry
        IsBigOWith Pμ (gammaSigma (min σ 2))
          (fun a =>
            limitNormalizedBlockJObservable hPμ hStruct
                (originCube d ((N0 + m : ℕ) : ℤ)) e a -
              Real.rpow (3 : ℝ) (-α * (n : ℝ)))
          (Cfluct *
            (3 : ℝ) ^
              (-(d : ℝ) / 2 *
                (Int.toNat
                  (((N0 + m : ℕ) : ℤ) - ((N0 + n : ℕ) : ℤ)) : ℝ)) *
            hΓ.thetaHat ^ (2 : ℕ)) := by
  obtain ⟨Cconc, hCconc_pos, hconc⟩ :=
    firstQuenchedEstimate_limitNormalized_concentration
      (d := d) hσ_pos
  let G : ℝ := Ch04.gammaMomentConst σ * (params.xi : ℝ) ^ σ⁻¹
  have hGammaConst_pos : 0 < Ch04.gammaMomentConst σ := by
    simpa [Ch04.gammaMomentConst] using
      IndependentSums.gammaMomentConst_pos hσ_pos
  have hparams_xi_pos : 0 < (params.xi : ℝ) := by
    exact_mod_cast params.xi_pos
  have hG_pos : 0 < G := by
    dsimp [G]
    exact mul_pos hGammaConst_pos (Real.rpow_pos_of_pos hparams_xi_pos _)
  obtain ⟨Centry, α, hCentry_pos, hα_pos, hannealed⟩ :=
    Section51.annealedConvergence_homogenizationScale params
  refine ⟨Cconc * G, Centry, α, mul_pos hCconc_pos hG_pos,
    hCentry_pos, hα_pos, ?_⟩
  intro Pμ hPμ hStruct hΓ hσ_eq hparams e he_norm n m hnm
  let : IsProbabilityMeasure Pμ := hPμ.isProbability
  let N0 : ℕ :=
    annealedAlgebraicEntryScale Pμ
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  have he_coord : ∀ β : BlockCoord d, |e β| ≤ 1 :=
    abs_fullBlockVec_coord_le_one_of_dotProduct_le_one e he_norm
  have hP4_params :
      hΓ.toQuantitativeCoarseGrainedEllipticity.params = params := by
    have hparams_eq :
        hΓ.toQuantitativeCoarseGrainedEllipticity.params = hΓ.params := by
      simp [GammaSigmaCoarseGrainedEllipticity.toQuantitativeCoarseGrainedEllipticity,
        GammaSigmaCoarseGrainedEllipticity.toQuantitativeCoarseGrainedEllipticity_of_barSigmaAtScale_zero_pos,
        QuantitativeCoarseGrainedEllipticity.params]
    rw [hparams_eq]
    exact hparams
  have htheta :
      thetaAtScale hPμ hStruct ((N0 + n : ℕ) : ℤ) ≤
        1 + Real.rpow (3 : ℝ) (-α * (n : ℝ)) := by
    have h :=
      hannealed hPμ hStruct
        hΓ.toQuantitativeCoarseGrainedEllipticity hP4_params n
    simpa [N0] using h
  have hcenter :
      (∫ b,
        limitNormalizedBlockJObservable hPμ hStruct
          (originCube d ((N0 + n : ℕ) : ℤ)) e b ∂Pμ) ≤
        Real.rpow (3 : ℝ) (-α * (n : ℝ)) := by
    have hJ :=
      hΓ.integral_limitNormalizedBlockJObservable_le_thetaAtScale_sub_one
        (N0 + n) e he_norm
    linarith
  have hn_nonneg : 0 ≤ ((N0 + n : ℕ) : ℤ) := by
    exact_mod_cast Nat.zero_le (N0 + n)
  have hnm_int : ((N0 + n : ℕ) : ℤ) < ((N0 + m : ℕ) : ℤ) := by
    exact_mod_cast Nat.add_lt_add_left hnm N0
  let decay : ℝ :=
    (3 : ℝ) ^
      (-(d : ℝ) / 2 *
        (Int.toNat
          (((N0 + m : ℕ) : ℤ) - ((N0 + n : ℕ) : ℤ)) : ℝ))
  have hraw :
      IsBigOWith Pμ (gammaSigma (min σ 2))
        (fun a =>
          limitNormalizedBlockJObservable hPμ hStruct
              (originCube d ((N0 + m : ℕ) : ℤ)) e a -
            Real.rpow (3 : ℝ) (-α * (n : ℝ)))
        (Cconc * decay * (thetaAtScale hPμ hStruct (0 : ℤ) * hΓ.thetaHat)) := by
    simpa [N0, decay] using
    hconc hPμ hStruct hΓ hσ_eq e he_coord hn_nonneg hnm_int hcenter
  have htheta_le : thetaAtScale hPμ hStruct (0 : ℤ) ≤ G * hΓ.thetaHat := by
    have h := hΓ.thetaAtScale_zero_le_gammaMomentScale
    simpa [G, hσ_eq, hparams] using h
  have hdecay_nonneg : 0 ≤ decay := by
    dsimp [decay]
    positivity
  have hscale_le :
      Cconc * decay * (thetaAtScale hPμ hStruct (0 : ℤ) * hΓ.thetaHat) ≤
        (Cconc * G) * decay * hΓ.thetaHat ^ (2 : ℕ) := by
    have htheta_mul :
        thetaAtScale hPμ hStruct (0 : ℤ) * hΓ.thetaHat ≤
          (G * hΓ.thetaHat) * hΓ.thetaHat := by
      exact mul_le_mul_of_nonneg_right htheta_le hΓ.thetaHat_pos.le
    calc
      Cconc * decay * (thetaAtScale hPμ hStruct (0 : ℤ) * hΓ.thetaHat)
          ≤ Cconc * decay * ((G * hΓ.thetaHat) * hΓ.thetaHat) := by
            exact mul_le_mul_of_nonneg_left htheta_mul
              (mul_nonneg hCconc_pos.le hdecay_nonneg)
      _ = (Cconc * G) * decay * hΓ.thetaHat ^ (2 : ℕ) := by
            ring
  exact hraw.mono_scale hscale_le

/-- Uniform-in-`σ` version of `firstQuenchedEstimate_limitNormalized`.

The annealed entry constant and algebraic exponent are chosen before the
finite moment exponent `σ`.  Only the fluctuation constant is selected after
`σ`, reflecting that the concentration step depends on the moment class while
the annealed algebraic rate only uses the existence of a finite moment. -/
theorem firstQuenchedEstimate_limitNormalized_uniformAnnealedExponent
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ Centry a : ℝ, 0 < Centry ∧ 0 < a ∧
      ∀ {σ : ℝ}, 0 < σ →
        ∃ Cfluct : ℝ, 0 < Cfluct ∧
          ∀ {Pμ : Ch04.RestrictionCoeffLaw d}
            (hPμ : Ch04.RestrictionLawCarrier Pμ)
            (hStruct : Ch04.RestrictionStructuralLaw Pμ)
            (hΓ : GammaSigmaCoarseGrainedEllipticity Pμ hPμ hStruct),
            hΓ.sigma = σ → hΓ.params = params →
          ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
          ∀ {n m : ℕ}, n < m →
            let N0 : ℕ :=
              annealedAlgebraicEntryScale Pμ
                hΓ.toQuantitativeCoarseGrainedEllipticity Centry
            IsBigOWith Pμ (gammaSigma (min σ 2))
              (fun aω =>
                limitNormalizedBlockJObservable hPμ hStruct
                    (originCube d ((N0 + m : ℕ) : ℤ)) e aω -
                  Real.rpow (3 : ℝ) (-a * (n : ℝ)))
              (Cfluct *
                (3 : ℝ) ^
                  (-(d : ℝ) / 2 *
                    (Int.toNat
                      (((N0 + m : ℕ) : ℤ) -
                        ((N0 + n : ℕ) : ℤ)) : ℝ)) *
                hΓ.thetaHat ^ (2 : ℕ)) := by
  obtain ⟨Centry, a, hCentry_pos, ha_pos, hannealed⟩ :=
    Section51.annealedConvergence_homogenizationScale params
  refine ⟨Centry, a, hCentry_pos, ha_pos, ?_⟩
  intro σ hσ_pos
  obtain ⟨Cconc, hCconc_pos, hconc⟩ :=
    firstQuenchedEstimate_limitNormalized_concentration
      (d := d) hσ_pos
  let G : ℝ := Ch04.gammaMomentConst σ * (params.xi : ℝ) ^ σ⁻¹
  have hGammaConst_pos : 0 < Ch04.gammaMomentConst σ := by
    simpa [Ch04.gammaMomentConst] using
      IndependentSums.gammaMomentConst_pos hσ_pos
  have hparams_xi_pos : 0 < (params.xi : ℝ) := by
    exact_mod_cast params.xi_pos
  have hG_pos : 0 < G := by
    dsimp [G]
    exact mul_pos hGammaConst_pos (Real.rpow_pos_of_pos hparams_xi_pos _)
  refine ⟨Cconc * G, mul_pos hCconc_pos hG_pos, ?_⟩
  intro Pμ hPμ hStruct hΓ hσ_eq hparams e he_norm n m hnm
  let : IsProbabilityMeasure Pμ := hPμ.isProbability
  let N0 : ℕ :=
    annealedAlgebraicEntryScale Pμ
      hΓ.toQuantitativeCoarseGrainedEllipticity Centry
  have he_coord : ∀ β : BlockCoord d, |e β| ≤ 1 :=
    abs_fullBlockVec_coord_le_one_of_dotProduct_le_one e he_norm
  have hP4_params :
      hΓ.toQuantitativeCoarseGrainedEllipticity.params = params := by
    have hparams_eq :
        hΓ.toQuantitativeCoarseGrainedEllipticity.params = hΓ.params := by
      simp [GammaSigmaCoarseGrainedEllipticity.toQuantitativeCoarseGrainedEllipticity,
        GammaSigmaCoarseGrainedEllipticity.toQuantitativeCoarseGrainedEllipticity_of_barSigmaAtScale_zero_pos,
        QuantitativeCoarseGrainedEllipticity.params]
    rw [hparams_eq]
    exact hparams
  have htheta :
      thetaAtScale hPμ hStruct ((N0 + n : ℕ) : ℤ) ≤
        1 + Real.rpow (3 : ℝ) (-a * (n : ℝ)) := by
    have h :=
      hannealed hPμ hStruct
        hΓ.toQuantitativeCoarseGrainedEllipticity hP4_params n
    simpa [N0] using h
  have hcenter :
      (∫ b,
        limitNormalizedBlockJObservable hPμ hStruct
          (originCube d ((N0 + n : ℕ) : ℤ)) e b ∂Pμ) ≤
        Real.rpow (3 : ℝ) (-a * (n : ℝ)) := by
    have hJ :=
      hΓ.integral_limitNormalizedBlockJObservable_le_thetaAtScale_sub_one
        (N0 + n) e he_norm
    linarith
  have hn_nonneg : 0 ≤ ((N0 + n : ℕ) : ℤ) := by
    exact_mod_cast Nat.zero_le (N0 + n)
  have hnm_int : ((N0 + n : ℕ) : ℤ) < ((N0 + m : ℕ) : ℤ) := by
    exact_mod_cast Nat.add_lt_add_left hnm N0
  let decay : ℝ :=
    (3 : ℝ) ^
      (-(d : ℝ) / 2 *
        (Int.toNat
          (((N0 + m : ℕ) : ℤ) - ((N0 + n : ℕ) : ℤ)) : ℝ))
  have hraw :
      IsBigOWith Pμ (gammaSigma (min σ 2))
        (fun aω =>
          limitNormalizedBlockJObservable hPμ hStruct
              (originCube d ((N0 + m : ℕ) : ℤ)) e aω -
            Real.rpow (3 : ℝ) (-a * (n : ℝ)))
        (Cconc * decay * (thetaAtScale hPμ hStruct (0 : ℤ) * hΓ.thetaHat)) := by
    simpa [N0, decay] using
    hconc hPμ hStruct hΓ hσ_eq e he_coord hn_nonneg hnm_int hcenter
  have htheta_le : thetaAtScale hPμ hStruct (0 : ℤ) ≤ G * hΓ.thetaHat := by
    have h := hΓ.thetaAtScale_zero_le_gammaMomentScale
    simpa [G, hσ_eq, hparams] using h
  have hdecay_nonneg : 0 ≤ decay := by
    dsimp [decay]
    positivity
  have hscale_le :
      Cconc * decay * (thetaAtScale hPμ hStruct (0 : ℤ) * hΓ.thetaHat) ≤
        (Cconc * G) * decay * hΓ.thetaHat ^ (2 : ℕ) := by
    have htheta_mul :
        thetaAtScale hPμ hStruct (0 : ℤ) * hΓ.thetaHat ≤
          (G * hΓ.thetaHat) * hΓ.thetaHat := by
      exact mul_le_mul_of_nonneg_right htheta_le hΓ.thetaHat_pos.le
    calc
      Cconc * decay * (thetaAtScale hPμ hStruct (0 : ℤ) * hΓ.thetaHat)
          ≤ Cconc * decay * ((G * hΓ.thetaHat) * hΓ.thetaHat) := by
            exact mul_le_mul_of_nonneg_left htheta_mul
              (mul_nonneg hCconc_pos.le hdecay_nonneg)
      _ = (Cconc * G) * decay * hΓ.thetaHat ^ (2 : ℕ) := by
            ring
  exact hraw.mono_scale hscale_le

/-- Note-facing, `xi`-free version of
`firstQuenchedEstimate_limitNormalized_uniformAnnealedExponent`.

The proof chooses the finite moment exponent needed by the older annealed API
internally from `sUpper` and `sLower`; the resulting constants therefore depend
only on the displayed Section 5.7 parameters. -/
theorem firstQuenchedEstimate_limitNormalized_uniformAnnealedExponent_noXi
    {d : ℕ} [NeZero d]
    (params : GammaCoarseGrainedEllipticityParams d) :
    ∃ Centry a : ℝ, 0 < Centry ∧ 0 < a ∧
      ∀ {σ : ℝ}, 0 < σ →
        ∃ Cfluct : ℝ, 0 < Cfluct ∧
          ∀ {Pμ : Ch04.RestrictionCoeffLaw d}
            (hPμ : Ch04.RestrictionLawCarrier Pμ)
            (hStruct : Ch04.RestrictionStructuralLaw Pμ)
            (hΓ : GammaSigmaCoarseGrainedEllipticityNoXi Pμ hPμ hStruct),
            hΓ.sigma = σ → hΓ.params = params →
          ∀ (e : FullBlockVec d), dotProduct e e ≤ 1 →
          ∀ {n m : ℕ}, n < m →
            let N0 : ℕ :=
              annealedAlgebraicEntryScale Pμ
                hΓ.withInternalXi.toQuantitativeCoarseGrainedEllipticity Centry
            IsBigOWith Pμ (gammaSigma (min σ 2))
              (fun aω =>
                limitNormalizedBlockJObservable hPμ hStruct
                    (originCube d ((N0 + m : ℕ) : ℤ)) e aω -
                  Real.rpow (3 : ℝ) (-a * (n : ℝ)))
              (Cfluct *
                (3 : ℝ) ^
                  (-(d : ℝ) / 2 *
                    (Int.toNat
                      (((N0 + m : ℕ) : ℤ) -
                        ((N0 + n : ℕ) : ℤ)) : ℝ)) *
                hΓ.thetaHat ^ (2 : ℕ)) := by
  obtain ⟨Centry, a, hCentry_pos, ha_pos, hfinite⟩ :=
    firstQuenchedEstimate_limitNormalized_uniformAnnealedExponent
      (d := d) params.toQuantitativeParams
  refine ⟨Centry, a, hCentry_pos, ha_pos, ?_⟩
  intro σ hσ
  obtain ⟨Cfluct, hCfluct_pos, hfluct⟩ := hfinite hσ
  refine ⟨Cfluct, hCfluct_pos, ?_⟩
  intro Pμ hPμ hStruct hΓ hσ_eq hparams e he_norm n m hnm
  let hΓold : GammaSigmaCoarseGrainedEllipticity Pμ hPμ hStruct :=
    hΓ.withInternalXi
  have hσ_old : hΓold.sigma = σ := by
    simpa [hΓold] using hσ_eq
  have hparams_old : hΓold.params = params.toQuantitativeParams := by
    dsimp [hΓold, GammaSigmaCoarseGrainedEllipticityNoXi.withInternalXi]
    rw [hparams]
  simpa [hΓold] using
    hfluct hPμ hStruct hΓold hσ_old hparams_old e he_norm hnm

end

end Section57
end Ch05
end Book
end Homogenization
