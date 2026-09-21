/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section57.HomogenizationErrorQuenched

/-! # Ellipticity From Minimal Scale -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section57

open MeasureTheory
open IndependentSums
open scoped ENNReal MatrixOrder

/-!
# Ellipticity control above the Section 5.7 minimal scale

This file is the Phase 3 packaging step for the public homogenization theorem.
It combines the collapsed finite-`q` homogenization-error corollary with the
Chapter 2 lemma that controls multiscale ellipticity from `\mathcal E`.
-/

noncomputable section

private theorem homogenizationErrorOnCube_infinity_two_nonneg
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) (a0 : Mat d) {s : ℝ} (hs : 0 < s) :
    0 ≤ Ch02.HomogenizationErrorOnCube Q s
        Ch02.MultiscaleExponent.infinity (.finite 2) a a0 := by
  unfold Ch02.HomogenizationErrorOnCube Ch02.HomogenizationError
    Ch02.HomogenizationErrorFinite
  refine Real.rpow_nonneg ?_ _
  refine tsum_nonneg ?_
  intro l
  refine mul_nonneg ?_ ?_
  · simpa [Ch02.geometricWeight_eq_old] using
      Homogenization.geometricWeight_nonneg (s := s) (q := 2) l
        (by nlinarith : 0 ≤ s * (2 : ℝ))
  · exact Real.rpow_nonneg
      (Ch02.scaleResponseAtScale_infinity_nonneg Q
        (sub_le_self Q.scale (by exact_mod_cast Nat.zero_le l)) a a0) 2

/-- Deterministic Ch5-facing form of the Ch2 ellipticity-control lemma. -/
theorem weightedEllipticity_finite_two_le_of_homogenizationError_bound
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : Ch02.TriadicCoeffFamily d) {s σ B : ℝ}
    (hs : 0 < s) (hσ : 0 < σ)
    (hE :
      Ch02.HomogenizationErrorOnCube Q s Ch02.MultiscaleExponent.infinity
          (.finite 2) a (scalarMatrix (d := d) σ) ≤ B) :
    max (σ⁻¹ * Ch02.LambdaSq Q s (.finite 2) a)
        (σ * (Ch02.lambdaSq Q s (.finite 2) a)⁻¹) ≤
      2 * (Fintype.card (Fin d) : ℝ) * (B ^ (2 : ℕ) + 1) := by
  let E : ℝ :=
    Ch02.HomogenizationErrorOnCube Q s Ch02.MultiscaleExponent.infinity
      (.finite 2) a (scalarMatrix (d := d) σ)
  have hE_nonneg : 0 ≤ E := by
    simpa [E] using
      homogenizationErrorOnCube_infinity_two_nonneg
        (Q := Q) a (scalarMatrix (d := d) σ) hs
  have hE_sq : E ^ (2 : ℕ) ≤ B ^ (2 : ℕ) :=
    pow_le_pow_left₀ hE_nonneg (by simpa [E] using hE) 2
  have hch2 :=
    Ch02.max_weightedEllipticity_finite_two_le_card_mul_homogenizationError_sq_add_one
      Q a hs hσ
  have hconst_nonneg : 0 ≤ 2 * (Fintype.card (Fin d) : ℝ) := by
    positivity
  calc
    max (σ⁻¹ * Ch02.LambdaSq Q s (.finite 2) a)
        (σ * (Ch02.lambdaSq Q s (.finite 2) a)⁻¹)
        ≤ 2 * (Fintype.card (Fin d) : ℝ) * (E ^ (2 : ℕ) + 1) := by
          simpa [E] using hch2
    _ ≤ 2 * (Fintype.card (Fin d) : ℝ) * (B ^ (2 : ℕ) + 1) := by
          exact mul_le_mul_of_nonneg_left (by nlinarith) hconst_nonneg

theorem lambdaSq_inv_le_inv_sigma_mul_of_weightedEllipticity_le
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : Ch02.TriadicCoeffFamily d) {s σ M : ℝ}
    (hσ : 0 < σ)
    (hM :
      max (σ⁻¹ * Ch02.LambdaSq Q s (.finite 2) a)
          (σ * (Ch02.lambdaSq Q s (.finite 2) a)⁻¹) ≤ M) :
    (Ch02.lambdaSq Q s (.finite 2) a)⁻¹ ≤ σ⁻¹ * M := by
  have hlower :
      σ * (Ch02.lambdaSq Q s (.finite 2) a)⁻¹ ≤ M :=
    (le_max_right _ _).trans hM
  calc
    (Ch02.lambdaSq Q s (.finite 2) a)⁻¹
        = σ⁻¹ * (σ * (Ch02.lambdaSq Q s (.finite 2) a)⁻¹) := by
            field_simp [hσ.ne']
    _ ≤ σ⁻¹ * M :=
        mul_le_mul_of_nonneg_left hlower (inv_nonneg.mpr hσ.le)

theorem sqrt_LambdaSq_mul_sqrt_lambdaSq_inv_le_of_weightedEllipticity_le
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : Ch02.TriadicCoeffFamily d) {s σ M : ℝ}
    (hs : 0 < s) (hσ : 0 < σ) (hM_nonneg : 0 ≤ M)
    (hM :
      max (σ⁻¹ * Ch02.LambdaSq Q s (.finite 2) a)
          (σ * (Ch02.lambdaSq Q s (.finite 2) a)⁻¹) ≤ M) :
    Real.sqrt (Ch02.LambdaSq Q s (.finite 2) a) *
        Real.sqrt ((Ch02.lambdaSq Q s (.finite 2) a)⁻¹) ≤ M := by
  let Lam : ℝ := Ch02.LambdaSq Q s (.finite 2) a
  let linv : ℝ := (Ch02.lambdaSq Q s (.finite 2) a)⁻¹
  have hLam_nonneg : 0 ≤ Lam := by
    dsimp [Lam]
    exact Ch02.LambdaSq_finite_nonneg Q a hs (by norm_num : (1 : ℝ) ≤ 2)
  have hlambda_pos : 0 < Ch02.lambdaSq Q s (.finite 2) a :=
    Ch02.lambdaSq_finite_pos Q a hs (by norm_num : (1 : ℝ) ≤ 2)
  have hlinv_nonneg : 0 ≤ linv := by
    dsimp [linv]
    exact inv_nonneg.mpr hlambda_pos.le
  have hupper_norm : σ⁻¹ * Lam ≤ M := by
    exact (le_max_left _ _).trans hM
  have hlower_norm : σ * linv ≤ M := by
    exact (le_max_right _ _).trans hM
  have hLam_le : Lam ≤ σ * M := by
    have h := mul_le_mul_of_nonneg_left hupper_norm hσ.le
    calc
      Lam = σ * (σ⁻¹ * Lam) := by field_simp [hσ.ne']
      _ ≤ σ * M := h
  have hlinv_le : linv ≤ σ⁻¹ * M := by
    have h := mul_le_mul_of_nonneg_left hlower_norm (inv_nonneg.mpr hσ.le)
    calc
      linv = σ⁻¹ * (σ * linv) := by field_simp [hσ.ne']
      _ ≤ σ⁻¹ * M := h
  have hσM_nonneg : 0 ≤ σ * M := mul_nonneg hσ.le hM_nonneg
  have hrhs_eq :
      Real.sqrt (σ * M) * Real.sqrt (σ⁻¹ * M) = M := by
    rw [← Real.sqrt_mul hσM_nonneg (σ⁻¹ * M)]
    have hprod : (σ * M) * (σ⁻¹ * M) = M ^ (2 : ℕ) := by
      field_simp [hσ.ne']
    rw [hprod, Real.sqrt_sq_eq_abs, abs_of_nonneg hM_nonneg]
  calc
    Real.sqrt Lam * Real.sqrt linv
        ≤ Real.sqrt (σ * M) * Real.sqrt (σ⁻¹ * M) :=
          mul_le_mul (Real.sqrt_le_sqrt hLam_le) (Real.sqrt_le_sqrt hlinv_le)
            (Real.sqrt_nonneg linv) (Real.sqrt_nonneg (σ * M))
    _ = M := hrhs_eq

/-- Finite-`sigma` ellipticity control on origin cubes above the same random
minimal scale as the collapsed finite-`q` `\mathcal E` estimate. -/
theorem exists_weightedEllipticityOnOriginCube_interpolated_expLogSq
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ α : ℝ, 0 < α ∧
      ∀ {σ τ s : ℝ}, 0 < σ →
        max params.sUpper params.sLower < τ / 2 →
        α < τ / 2 →
        τ ≤ 1 →
        0 ≤ s * (2 : ℝ) →
        0 < (s - τ / 2) * (2 : ℝ) →
        let ηJ : ℝ := finiteQuenchedTailExponent d σ τ
        let ηU : ℝ := finiteQuenchedTailExponent d σ (τ / 2)
        let η : ℝ := min ηJ ηU
        ∃ Cscale : ℝ, 0 < Cscale ∧
          ∀ {P : Ch04.RestrictionCoeffLaw d}
            (hP : Ch04.RestrictionLawCarrier P)
            (hStruct : Ch04.RestrictionStructuralLaw P)
            (hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct),
            hΓ.sigma = σ → hΓ.params = params →
            ∃ X : RegCoeffField d → ℝ,
              IsBigO P (gammaSigma η) X
                (Real.exp
                  (Cscale * (Real.log (2 + hΓ.thetaHat)) ^ (2 : ℕ))) ∧
              (∀ aω, 1 ≤ X aω) ∧
                ∀ᵐ aω ∂P,
                  ∀ (ha : Ch04.AELocallyUniformlyEllipticField aω) {m : ℕ},
                    X aω ≤ (3 : ℝ) ^ m →
                    let F : Ch02.TriadicCoeffFamily d :=
                      Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
                        aω ha;
                    let σ0 : ℝ := barSigmaLimit hP hStruct;
                    let Cresp : ℝ :=
                      Real.sqrt
                        (4 * (Fintype.card (BlockCoord d) : ℝ) *
                          (Fintype.card (NormalizedProbeIndex d) : ℝ));
                    let Cneg : ℝ :=
                      (Ch02.geometricDiscount (τ / 2) 1)⁻¹ *
                        (2 * Real.sqrt
                          ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)));
                    let A : ℝ := max Cresp Cneg * Real.rpow (3 : ℝ) (τ / 2);
                    let G : ℝ :=
                      Real.rpow
                        (Ch02.geometricDiscount s 2 *
                          (Ch02.geometricDiscount (s - τ / 2) 2)⁻¹)
                        (1 / 2 : ℝ);
                    let R : ℝ :=
                      Real.sqrt (((3 : ℝ) ^ m / X aω) ^ (-α));
                    let M : ℝ :=
                      2 * (Fintype.card (Fin d) : ℝ) *
                        ((G * A * R) ^ (2 : ℕ) + 1);
                    max (σ0⁻¹ * Ch02.LambdaSq (originCube d ((m : ℕ) : ℤ))
                          s (.finite 2) F)
                        (σ0 * (Ch02.lambdaSq (originCube d ((m : ℕ) : ℤ))
                          s (.finite 2) F)⁻¹) ≤ M ∧
                    (Ch02.lambdaSq (originCube d ((m : ℕ) : ℤ))
                        s (.finite 2) F)⁻¹ ≤ σ0⁻¹ * M ∧
                    Real.sqrt (Ch02.LambdaSq (originCube d ((m : ℕ) : ℤ))
                        s (.finite 2) F) *
                      Real.sqrt ((Ch02.lambdaSq (originCube d ((m : ℕ) : ℤ))
                        s (.finite 2) F)⁻¹) ≤ M := by
  obtain ⟨α, hα_pos, _hαmax, hEbase⟩ :=
    exists_homogenizationErrorOnOriginCube_interpolated_expLogSq
      (d := d) params
  refine ⟨α, hα_pos, ?_⟩
  intro σ τ s hσ_pos hτ_half hατ_half hτ_le_one hs2 hδ2
  dsimp only
  obtain ⟨Cscale, hCscale_pos, hlaw⟩ :=
    hEbase (σ := σ) (τ := τ) (r := s) (q := 2)
      hσ_pos hτ_half hατ_half hτ_le_one hs2 hδ2
      (by norm_num : (0 : ℝ) < 2)
  refine ⟨Cscale, hCscale_pos, ?_⟩
  intro P hP hStruct hΓ hσ_eq hparams
  obtain ⟨X, hXbigO, hXone, hEae⟩ :=
    hlaw hP hStruct hΓ hσ_eq hparams
  refine ⟨X, hXbigO, hXone, ?_⟩
  have hτ2_pos : 0 < τ / 2 :=
    (max_sUpper_sLower_pos params).trans hτ_half
  have hτ_pos : 0 < τ := by linarith
  have hs_pos : 0 < s := by nlinarith
  have hδ_pos : 0 < s - τ / 2 := by nlinarith
  filter_upwards [hEae] with aω hEpoint
  intro ha m hXm
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField aω ha
  let σ0 : ℝ := barSigmaLimit hP hStruct
  let Q : TriadicCube d := originCube d ((m : ℕ) : ℤ)
  let Cresp : ℝ :=
    Real.sqrt
      (4 * (Fintype.card (BlockCoord d) : ℝ) *
        (Fintype.card (NormalizedProbeIndex d) : ℝ))
  let Cneg : ℝ :=
    (Ch02.geometricDiscount (τ / 2) 1)⁻¹ *
      (2 * Real.sqrt ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)))
  let A : ℝ := max Cresp Cneg * Real.rpow (3 : ℝ) (τ / 2)
  let G : ℝ :=
    Real.rpow
      (Ch02.geometricDiscount s 2 *
        (Ch02.geometricDiscount (s - τ / 2) 2)⁻¹)
      (1 / 2 : ℝ)
  let R : ℝ := Real.sqrt (((3 : ℝ) ^ m / X aω) ^ (-α))
  let B : ℝ := G * A * R
  let M : ℝ :=
    2 * (Fintype.card (Fin d) : ℝ) * (B ^ (2 : ℕ) + 1)
  have hσ0_pos : 0 < σ0 := by
    simpa [σ0] using hΓ.barSigmaLimit_pos
  have hX_pos : 0 < X aω := lt_of_lt_of_le zero_lt_one (hXone aω)
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hdisc_s_nonneg : 0 ≤ Ch02.geometricDiscount s 2 := by
    simpa [Ch02.geometricDiscount_eq_old] using
      Homogenization.geometricDiscount_nonneg (by simpa using hs2)
  have hdisc_delta_pos : 0 < Ch02.geometricDiscount (s - τ / 2) 2 := by
    simpa [Ch02.geometricDiscount_eq_old] using
      Homogenization.geometricDiscount_pos (by simpa using hδ2)
  have hG_nonneg : 0 ≤ G := by
    dsimp [G]
    exact Real.rpow_nonneg
      (mul_nonneg hdisc_s_nonneg
        (inv_nonneg.mpr hdisc_delta_pos.le)) _
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
    exact mul_nonneg (hCresp_nonneg.trans (le_max_left Cresp Cneg)) (by positivity)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg hG_nonneg hA_nonneg) hR_nonneg
  have hE_bound :
      Ch02.HomogenizationErrorOnCube Q s Ch02.MultiscaleExponent.infinity
          (.finite 2) F (scalarMatrix (d := d) σ0) ≤ B := by
    simpa [Q, F, σ0, Cresp, Cneg, A, G, R, B] using
      hEpoint ha (m := m) hXm
  have hweighted :
      max (σ0⁻¹ * Ch02.LambdaSq Q s (.finite 2) F)
          (σ0 * (Ch02.lambdaSq Q s (.finite 2) F)⁻¹) ≤ M := by
    simpa [M, B] using
      weightedEllipticity_finite_two_le_of_homogenizationError_bound
        (Q := Q) (a := F) (s := s) (σ := σ0) (B := B)
        hs_pos hσ0_pos hE_bound
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  refine ⟨?_, ?_, ?_⟩
  · simpa [Q, F, σ0, Cresp, Cneg, A, G, R, B, M] using hweighted
  · simpa [Q, F, σ0, Cresp, Cneg, A, G, R, B, M] using
      lambdaSq_inv_le_inv_sigma_mul_of_weightedEllipticity_le
        (Q := Q) (a := F) (s := s) (σ := σ0) (M := M)
        hσ0_pos hweighted
  · simpa [Q, F, σ0, Cresp, Cneg, A, G, R, B, M] using
      sqrt_LambdaSq_mul_sqrt_lambdaSq_inv_le_of_weightedEllipticity_le
        (Q := Q) (a := F) (s := s) (σ := σ0) (M := M)
        hs_pos hσ0_pos hM_nonneg hweighted

/-- Endpoint (`σ = ∞`) ellipticity control on origin cubes above the same
random minimal scale as the endpoint finite-`q` `\mathcal E` estimate. -/
theorem exists_weightedEllipticityOnOriginCube_uniformEndpoint_expLogSq
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ α : ℝ, 0 < α ∧
      ∀ {τ s : ℝ},
        max params.sUpper params.sLower < τ / 2 →
        α < τ / 2 →
        τ ≤ 1 →
        0 ≤ s * (2 : ℝ) →
        0 < (s - τ / 2) * (2 : ℝ) →
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
                  ∀ (ha : Ch04.AELocallyUniformlyEllipticField aω) {m : ℕ},
                    X aω ≤ (3 : ℝ) ^ m →
                    let F : Ch02.TriadicCoeffFamily d :=
                      Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
                        aω ha;
                    let σ0 : ℝ := barSigmaLimit hP hStruct;
                    let Cresp : ℝ :=
                      Real.sqrt
                        (4 * (Fintype.card (BlockCoord d) : ℝ) *
                          (Fintype.card (NormalizedProbeIndex d) : ℝ));
                    let Cneg : ℝ :=
                      (Ch02.geometricDiscount (τ / 2) 1)⁻¹ *
                        (2 * Real.sqrt
                          ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)));
                    let A : ℝ := max Cresp Cneg * Real.rpow (3 : ℝ) (τ / 2);
                    let G : ℝ :=
                      Real.rpow
                        (Ch02.geometricDiscount s 2 *
                          (Ch02.geometricDiscount (s - τ / 2) 2)⁻¹)
                        (1 / 2 : ℝ);
                    let R : ℝ :=
                      Real.sqrt (((3 : ℝ) ^ m / X aω) ^ (-α));
                    let M : ℝ :=
                      2 * (Fintype.card (Fin d) : ℝ) *
                        ((G * A * R) ^ (2 : ℕ) + 1);
                    max (σ0⁻¹ * Ch02.LambdaSq (originCube d ((m : ℕ) : ℤ))
                          s (.finite 2) F)
                        (σ0 * (Ch02.lambdaSq (originCube d ((m : ℕ) : ℤ))
                          s (.finite 2) F)⁻¹) ≤ M ∧
                    (Ch02.lambdaSq (originCube d ((m : ℕ) : ℤ))
                        s (.finite 2) F)⁻¹ ≤ σ0⁻¹ * M ∧
                    Real.sqrt (Ch02.LambdaSq (originCube d ((m : ℕ) : ℤ))
                        s (.finite 2) F) *
                      Real.sqrt ((Ch02.lambdaSq (originCube d ((m : ℕ) : ℤ))
                        s (.finite 2) F)⁻¹) ≤ M := by
  obtain ⟨α, hα_pos, _hαmax, hEbase⟩ :=
    exists_homogenizationErrorOnOriginCube_uniformEndpoint_expLogSq
      (d := d) params
  refine ⟨α, hα_pos, ?_⟩
  intro τ s hτ_half hατ_half hτ_le_one hs2 hδ2
  dsimp only
  obtain ⟨Cscale, hCscale_pos, hlaw⟩ :=
    hEbase (τ := τ) (r := s) (q := 2)
      hτ_half hατ_half hτ_le_one hs2 hδ2
      (by norm_num : (0 : ℝ) < 2)
  refine ⟨Cscale, hCscale_pos, ?_⟩
  intro P hP hStruct hInf hparams
  obtain ⟨X, hXbigO, hXone, hEae⟩ :=
    hlaw hP hStruct hInf hparams
  refine ⟨X, hXbigO, hXone, ?_⟩
  have hτ2_pos : 0 < τ / 2 :=
    (max_sUpper_sLower_pos params).trans hτ_half
  have hτ_pos : 0 < τ := by linarith
  have hs_pos : 0 < s := by nlinarith
  have hδ_pos : 0 < s - τ / 2 := by nlinarith
  filter_upwards [hEae] with aω hEpoint
  intro ha m hXm
  let F : Ch02.TriadicCoeffFamily d :=
    Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField aω ha
  let σ0 : ℝ := barSigmaLimit hP hStruct
  let Q : TriadicCube d := originCube d ((m : ℕ) : ℤ)
  let Cresp : ℝ :=
    Real.sqrt
      (4 * (Fintype.card (BlockCoord d) : ℝ) *
        (Fintype.card (NormalizedProbeIndex d) : ℝ))
  let Cneg : ℝ :=
    (Ch02.geometricDiscount (τ / 2) 1)⁻¹ *
      (2 * Real.sqrt ((Fintype.card (BlockCoord d) : ℝ) ^ (2 : ℕ)))
  let A : ℝ := max Cresp Cneg * Real.rpow (3 : ℝ) (τ / 2)
  let G : ℝ :=
    Real.rpow
      (Ch02.geometricDiscount s 2 *
        (Ch02.geometricDiscount (s - τ / 2) 2)⁻¹)
      (1 / 2 : ℝ)
  let R : ℝ := Real.sqrt (((3 : ℝ) ^ m / X aω) ^ (-α))
  let B : ℝ := G * A * R
  let M : ℝ :=
    2 * (Fintype.card (Fin d) : ℝ) * (B ^ (2 : ℕ) + 1)
  let hΓ : GammaSigmaCoarseGrainedEllipticity P hP hStruct :=
    hInf.toGammaSigma 1 zero_lt_one
  have hσ0_pos : 0 < σ0 := by
    simpa [σ0] using hΓ.barSigmaLimit_pos
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hdisc_s_nonneg : 0 ≤ Ch02.geometricDiscount s 2 := by
    simpa [Ch02.geometricDiscount_eq_old] using
      Homogenization.geometricDiscount_nonneg (by simpa using hs2)
  have hdisc_delta_pos : 0 < Ch02.geometricDiscount (s - τ / 2) 2 := by
    simpa [Ch02.geometricDiscount_eq_old] using
      Homogenization.geometricDiscount_pos (by simpa using hδ2)
  have hG_nonneg : 0 ≤ G := by
    dsimp [G]
    exact Real.rpow_nonneg
      (mul_nonneg hdisc_s_nonneg
        (inv_nonneg.mpr hdisc_delta_pos.le)) _
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
    exact mul_nonneg (hCresp_nonneg.trans (le_max_left Cresp Cneg)) (by positivity)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg hG_nonneg hA_nonneg) hR_nonneg
  have hE_bound :
      Ch02.HomogenizationErrorOnCube Q s Ch02.MultiscaleExponent.infinity
          (.finite 2) F (scalarMatrix (d := d) σ0) ≤ B := by
    simpa [Q, F, σ0, Cresp, Cneg, A, G, R, B] using
      hEpoint ha (m := m) hXm
  have hweighted :
      max (σ0⁻¹ * Ch02.LambdaSq Q s (.finite 2) F)
          (σ0 * (Ch02.lambdaSq Q s (.finite 2) F)⁻¹) ≤ M := by
    simpa [M, B] using
      weightedEllipticity_finite_two_le_of_homogenizationError_bound
        (Q := Q) (a := F) (s := s) (σ := σ0) (B := B)
        hs_pos hσ0_pos hE_bound
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  refine ⟨?_, ?_, ?_⟩
  · simpa [Q, F, σ0, Cresp, Cneg, A, G, R, B, M] using hweighted
  · simpa [Q, F, σ0, Cresp, Cneg, A, G, R, B, M] using
      lambdaSq_inv_le_inv_sigma_mul_of_weightedEllipticity_le
        (Q := Q) (a := F) (s := s) (σ := σ0) (M := M)
        hσ0_pos hweighted
  · simpa [Q, F, σ0, Cresp, Cneg, A, G, R, B, M] using
      sqrt_LambdaSq_mul_sqrt_lambdaSq_inv_le_of_weightedEllipticity_le
        (Q := Q) (a := F) (s := s) (σ := σ0) (M := M)
        hs_pos hσ0_pos hM_nonneg hweighted

end

end Section57
end Ch05
end Book
end Homogenization
