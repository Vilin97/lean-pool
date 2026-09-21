/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.ExactSmallCube.CenteredFactors.LocalAlpha

/-! # Buffered Alpha -/

namespace Homogenization

/-!
# Exact small-cube centered factors: buffered alpha comparison
-/

noncomputable section

open scoped ENNReal

/-- Buffered average-plus-Besov factor-bound comparison for the centered exact
coefficient.  The cutoff is taken at the midpoint radius, while the scale
choice, height, and parent `Alpha` coefficient are still indexed by the full
outer pair `(ρ₁, ρ₂)`. -/
theorem
    coarseCaccioppoliFluxEnergyExactCenteredFactorBounds_buffered_localAcirc_le_alpha_of_scale
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} (a : CoeffField d)
    {s t CeffLocal CeffWork : ℝ} {k j : ℕ} {ρ₁ ρ₂ lam Lam : ℝ}
    {hheight : ℝ → ℝ → ℝ}
    (hCeffLocal : 0 ≤ CeffLocal) (hCeffWork : 0 ≤ CeffWork)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hR : R ∈ descendantsAtDepth Q j)
    (hBsum_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hSigmaSum_t :
      Summable (fun n : ℕ =>
        geometricWeight t 1 n *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)))
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) (hjk : k ≤ j)
    (hscale :
      (2 * coarseCaccioppoliCenteredAverageFront d s CeffLocal +
          4 * coarseCaccioppoliCenteredBesovHessianFront d s CeffLocal +
          2 * coarseCaccioppoliCenteredBesovGradientFront d s CeffLocal) *
          Real.rpow (3 : ℝ) (k : ℝ) ≤
        CeffWork / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂)
    (hheight_le_j : hheight ρ₁ ρ₂ ≤ (j : ℝ)) :
    let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
        (d := d) (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρm)
        (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm) CeffLocal +
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound R s
        (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliCenteredCutoffCoeffFactorBound R s
          (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρm)
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρm)
          (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm)
          (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρm)
          CeffLocal) ≤
      coarseCaccioppoliBoundaryAlphaOfHeight Q a s t CeffWork hheight ρ₁ ρ₂ := by
  dsimp
  let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
  let A : ℝ := 2 * coarseCaccioppoliCenteredAverageFront d s CeffLocal
  let H : ℝ := 4 * coarseCaccioppoliCenteredBesovHessianFront d s CeffLocal
  let G : ℝ := 2 * coarseCaccioppoliCenteredBesovGradientFront d s CeffLocal
  let Pone : ℝ :=
    Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
      Real.rpow (lambdaSq R (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)
  let Psub : ℝ :=
    Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
      Real.rpow (lambdaSq R (1 - s) (.finite 1) a) (-1 / 2 : ℝ)
  let Theta : ℝ := Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)
  let depthTheta : ℝ :=
    Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * (j : ℝ)) * Theta
  let front : ℝ := CeffWork / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂
  have hs1 : s < 1 := by nlinarith [ht, hst]
  have havg_sub :=
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound_localAcircOne_buffered_le_rpow_sub
      (Q := Q) (R := R) (a := a) (s := s) (Ceff := CeffLocal)
      (k := k) (j := j) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
      hCeffLocal hs hR hchoice hlt
  have hbesov_sub :=
    coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound_buffered_localAcirc_le_rpow_sub
      (Q := Q) (R := R) (a := a) (s := s) (Ceff := CeffLocal)
      (k := k) (j := j) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
      hCeffLocal hs hs1 hR hchoice hlt hjk
  have hprod_one :
      Real.rpow (3 : ℝ) (-(j : ℝ)) * Pone ≤ depthTheta := by
    simpa [Pone, Theta, depthTheta] using
      (faithful_centered_descendant_product_one_le_parent_theta
        (Q := Q) (R := R) (j := j) a hs ht hst hEllCube hR hBsum_s hSigmaSum_t)
  have hprod_sub :
      Real.rpow (3 : ℝ) (-(j : ℝ)) * Psub ≤ depthTheta := by
    simpa [Psub, Theta, depthTheta] using
      (faithful_centered_descendant_product_le_parent_theta
        (Q := Q) (R := R) (j := j) a hs ht hst hEllCube hR hBsum_s hSigmaSum_t)
  have hPone_nonneg : 0 ≤ Pone := by
    dsimp [Pone]
    exact mul_nonneg
      (Real.rpow_nonneg (multiscale_ellipticity_LambdaSq_one_nonneg R s a hs.le) _)
      (Real.rpow_nonneg
        (multiscale_ellipticity_lambdaSq_one_nonneg R (1 : ℝ) a (by norm_num)) _)
  have hPsub_nonneg : 0 ≤ Psub := by
    dsimp [Psub]
    exact mul_nonneg
      (Real.rpow_nonneg (multiscale_ellipticity_LambdaSq_one_nonneg R s a hs.le) _)
      (Real.rpow_nonneg
        (multiscale_ellipticity_lambdaSq_one_nonneg R (1 - s) a
          (sub_nonneg.mpr hs1.le)) _)
  have hA_nonneg : 0 ≤ A := by
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (coarseCaccioppoliCenteredAverageFront_nonneg d hCeffLocal hs)
  have hH_nonneg : 0 ≤ H := by
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      (coarseCaccioppoliCenteredBesovHessianFront_nonneg d hCeffLocal hs)
  have hG_nonneg : 0 ≤ G := by
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (coarseCaccioppoliCenteredBesovGradientFront_nonneg d hCeffLocal hs hs1)
  have hTheta_nonneg : 0 ≤ Theta := by
    dsimp [Theta]
    exact Real.rpow_nonneg (thetaRatio_nonneg Q s t a hs.le ht.le) _
  have hdepthTheta_nonneg : 0 ≤ depthTheta := by
    dsimp [depthTheta]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _) hTheta_nonneg
  have hpowk_nonneg : 0 ≤ Real.rpow (3 : ℝ) (k : ℝ) :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hApow_nonneg : 0 ≤ A * Real.rpow (3 : ℝ) (k : ℝ) :=
    mul_nonneg hA_nonneg hpowk_nonneg
  have hHpow_nonneg : 0 ≤ H * Real.rpow (3 : ℝ) (k : ℝ) :=
    mul_nonneg hH_nonneg hpowk_nonneg
  have hGpow_nonneg : 0 ≤ G * Real.rpow (3 : ℝ) (k : ℝ) :=
    mul_nonneg hG_nonneg hpowk_nonneg
  have hden_nonneg : 0 ≤ s * (1 - s) :=
    mul_nonneg hs.le (sub_nonneg.mpr hs1.le)
  have hfront_nonneg : 0 ≤ front := by
    dsimp [front]
    exact mul_nonneg (div_nonneg hCeffWork hden_nonneg)
      (coarseCaccioppoliGapInv_nonneg hlt)
  have hpow_split :
      Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) =
        Real.rpow (3 : ℝ) (k : ℝ) * Real.rpow (3 : ℝ) (-(j : ℝ)) := by
    rw [sub_eq_add_neg]
    exact Real.rpow_add (by norm_num : 0 < (3 : ℝ)) _ _
  have havg_rhs_eq :
      ((d : ℝ) * (((3 / 2 : ℝ) * CeffLocal * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((geometricDiscount s 1)⁻¹ * (geometricDiscount (1 : ℝ) 1)⁻¹)) *
        ((4 * quantitativeCubeCutoffGradientConst d) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)))) *
        Pone =
        A * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone := by
    dsimp [A, coarseCaccioppoliCenteredAverageFront]
    ring
  have hfactor_sub :
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
          (d := d) (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρm)
          (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm) CeffLocal +
        coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound R s
          (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliCenteredCutoffCoeffFactorBound R s
            (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρm)
            (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρm)
            (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm)
            (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρm)
            CeffLocal) ≤
        A * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone +
          (H * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone +
            G * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Psub) := by
    exact add_le_add
      (by simpa [Pone, ρm] using le_trans havg_sub havg_rhs_eq.le)
      (by simpa [H, G, Pone, Psub, ρm] using hbesov_sub)
  have hsub_rhs_eq :
      A * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone +
          (H * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone +
            G * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Psub) =
        (A * Real.rpow (3 : ℝ) (k : ℝ)) *
            (Real.rpow (3 : ℝ) (-(j : ℝ)) * Pone) +
          (H * Real.rpow (3 : ℝ) (k : ℝ)) *
            (Real.rpow (3 : ℝ) (-(j : ℝ)) * Pone) +
          (G * Real.rpow (3 : ℝ) (k : ℝ)) *
            (Real.rpow (3 : ℝ) (-(j : ℝ)) * Psub) := by
    rw [hpow_split]
    ring
  have hterms_to_depth :
      (A * Real.rpow (3 : ℝ) (k : ℝ)) *
            (Real.rpow (3 : ℝ) (-(j : ℝ)) * Pone) +
          (H * Real.rpow (3 : ℝ) (k : ℝ)) *
            (Real.rpow (3 : ℝ) (-(j : ℝ)) * Pone) +
          (G * Real.rpow (3 : ℝ) (k : ℝ)) *
            (Real.rpow (3 : ℝ) (-(j : ℝ)) * Psub) ≤
        ((A + H + G) * Real.rpow (3 : ℝ) (k : ℝ)) * depthTheta := by
    calc
      (A * Real.rpow (3 : ℝ) (k : ℝ)) *
            (Real.rpow (3 : ℝ) (-(j : ℝ)) * Pone) +
          (H * Real.rpow (3 : ℝ) (k : ℝ)) *
            (Real.rpow (3 : ℝ) (-(j : ℝ)) * Pone) +
          (G * Real.rpow (3 : ℝ) (k : ℝ)) *
            (Real.rpow (3 : ℝ) (-(j : ℝ)) * Psub)
          ≤
        (A * Real.rpow (3 : ℝ) (k : ℝ)) * depthTheta +
          (H * Real.rpow (3 : ℝ) (k : ℝ)) * depthTheta +
          (G * Real.rpow (3 : ℝ) (k : ℝ)) * depthTheta := by
            exact add_le_add
              (add_le_add
                (mul_le_mul_of_nonneg_left hprod_one hApow_nonneg)
                (mul_le_mul_of_nonneg_left hprod_one hHpow_nonneg))
              (mul_le_mul_of_nonneg_left hprod_sub hGpow_nonneg)
      _ = ((A + H + G) * Real.rpow (3 : ℝ) (k : ℝ)) * depthTheta := by
            ring
  have hfront_depth :
      ((A + H + G) * Real.rpow (3 : ℝ) (k : ℝ)) * depthTheta ≤
        front * depthTheta := by
    exact mul_le_mul_of_nonneg_right
      (by simpa [A, H, G, front] using hscale) hdepthTheta_nonneg
  have hσ_pos : 0 < coarseCaccioppoliSigma s t :=
    coarseCaccioppoli_sigma_pos hst
  have hexp_le :
      -coarseCaccioppoliSigma s t * (j : ℝ) ≤
        -coarseCaccioppoliSigma s t * hheight ρ₁ ρ₂ := by
    nlinarith
  have hpow_height :
      Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * (j : ℝ)) ≤
        Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * hheight ρ₁ ρ₂) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ (3 : ℝ)) hexp_le
  have hheight_step :
      front * depthTheta ≤
        front * (Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * hheight ρ₁ ρ₂) *
          Theta) := by
    refine mul_le_mul_of_nonneg_left ?_ hfront_nonneg
    dsimp [depthTheta]
    exact mul_le_mul_of_nonneg_right hpow_height hTheta_nonneg
  calc
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
        (d := d) (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρm)
        (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm) CeffLocal +
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound R s
        (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliCenteredCutoffCoeffFactorBound R s
          (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρm)
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρm)
          (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm)
          (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρm)
          CeffLocal)
        ≤ A * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone +
          (H * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone +
            G * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Psub) := hfactor_sub
    _ =
        (A * Real.rpow (3 : ℝ) (k : ℝ)) *
            (Real.rpow (3 : ℝ) (-(j : ℝ)) * Pone) +
          (H * Real.rpow (3 : ℝ) (k : ℝ)) *
            (Real.rpow (3 : ℝ) (-(j : ℝ)) * Pone) +
          (G * Real.rpow (3 : ℝ) (k : ℝ)) *
            (Real.rpow (3 : ℝ) (-(j : ℝ)) * Psub) := hsub_rhs_eq
    _ ≤ ((A + H + G) * Real.rpow (3 : ℝ) (k : ℝ)) * depthTheta :=
          hterms_to_depth
    _ ≤ front * depthTheta := hfront_depth
    _ ≤ front *
        (Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * hheight ρ₁ ρ₂) *
          Theta) := hheight_step
    _ = CeffWork / (s * (1 - s)) *
        coarseCaccioppoliGapInv ρ₁ ρ₂ *
        Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * hheight ρ₁ ρ₂) *
        Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) := by
          dsimp [front, Theta]
          ring
    _ = coarseCaccioppoliBoundaryAlphaOfHeight Q a s t CeffWork hheight ρ₁ ρ₂ := by
          rfl

end

end Homogenization
