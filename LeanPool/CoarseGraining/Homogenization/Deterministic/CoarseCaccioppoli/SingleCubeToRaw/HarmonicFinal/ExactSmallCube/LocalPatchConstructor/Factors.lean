/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.InputSpecializations.LocalPatchNoteRawBridge
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.ExactSmallCube.CenteredFactors
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.QuantitativeCutoffInputs.LocalPatch
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.LocalConstantBranch

/-! # Factors -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# Local-patch exact small-cube factor estimates

This file contains the centered average/Besov factor estimates for the
arbitrary-center local-patch exact small-cube coefficient route.
-/

/-- Average part of the centered exact coefficient for the local-patch
midpoint cutoff.  The local cutoff radius and the extra descendant generation
combine to give the same normalized front as the centered buffered route. -/
theorem
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound_localPatchBuffered_localAcircOne_le_rpow_sub
    {d : ℕ} {Q R : TriadicCube d} (a : CoeffField d) {s Ceff : ℝ}
    {k j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hCeff : 0 ≤ Ceff) (hs : 0 < s)
    (hR : R ∈ descendantsAtDepth Q (j + 1))
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) :
    let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
        (d := d) (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁ ρm)
        (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm) Ceff ≤
      ((d : ℝ) * (((3 / 2 : ℝ) * Ceff * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((geometricDiscount s 1)⁻¹ * (geometricDiscount (1 : ℝ) 1)⁻¹)) *
        ((4 * quantitativeCubeCutoffGradientConst d) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)))) *
        (Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
          Real.rpow (lambdaSq R (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)) := by
  dsimp
  let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
  let cut : ℝ :=
    cubeBesovScaleWeight (-1) R *
      coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁ ρm
  let cutBound : ℝ :=
    (4 * quantitativeCubeCutoffGradientConst d) *
      Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ))
  let K : ℝ :=
    (d : ℝ) * (((3 / 2 : ℝ) * Ceff * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ((geometricDiscount s 1)⁻¹ * (geometricDiscount (1 : ℝ) 1)⁻¹))
  let L : ℝ :=
    Real.rpow (LambdaSqFinite R s 1 a) (1 / 2 : ℝ) *
      Real.rpow (lambdaSqFinite R (1 : ℝ) 1 a) (-1 / 2 : ℝ)
  have hcut : cut ≤ cutBound := by
    simpa [cut, cutBound, ρm] using
      (cubeBesovScaleWeight_neg_one_mul_localPatch_buffered_cutoffGradient_le_rpow_sub
        (Q := Q) (R := R) (k := k) (j := j) hR hchoice hlt)
  have hdiscS_pos : 0 < geometricDiscount s 1 := by
    exact geometricDiscount_pos (by simpa using hs)
  have hdisc1_pos : 0 < geometricDiscount (1 : ℝ) 1 := by
    exact geometricDiscount_pos (by norm_num : 0 < (1 : ℝ) * 1)
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    refine mul_nonneg (by exact_mod_cast Nat.zero_le d : 0 ≤ (d : ℝ)) ?_
    refine mul_nonneg ?_ ?_
    · exact mul_nonneg
        (mul_nonneg (by positivity) hCeff)
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    · exact mul_nonneg (inv_nonneg.mpr hdiscS_pos.le)
        (inv_nonneg.mpr hdisc1_pos.le)
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    simpa [LambdaSq, lambdaSq] using
      (mul_nonneg
        (Real.rpow_nonneg
          (multiscale_ellipticity_LambdaSq_one_nonneg R s a hs.le) _)
        (Real.rpow_nonneg
          (multiscale_ellipticity_lambdaSq_one_nonneg R (1 : ℝ) a (by norm_num)) _))
  have hmain : K * cut * L ≤ K * cutBound * L := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcut hK_nonneg) hL_nonneg
  have hleft :
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
          (d := d) (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁ ρm)
          (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm) Ceff =
        K * cut * L := by
    dsimp [K, cut, L]
    unfold coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
      coarseCaccioppoliLambdaFactor
      coarseCaccioppoliCanonicalGradientAcircOne
      coarseCaccioppoliCanonicalGradientAcirc
    simp only [LambdaSq, lambdaSq]
    ring_nf
    rw [show LambdaSqFinite R s 1 a ^ (1 / 2 : ℝ) =
        Real.rpow (LambdaSqFinite R s 1 a) (1 / 2 : ℝ) by rfl,
      show lambdaSqFinite R (1 : ℝ) 1 a ^ (-1 / 2 : ℝ) =
        Real.rpow (lambdaSqFinite R (1 : ℝ) 1 a) (-1 / 2 : ℝ) by rfl]
    ac_rfl
  have hright :
      K * cutBound * L =
        ((d : ℝ) * (((3 / 2 : ℝ) * Ceff * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            ((geometricDiscount s 1)⁻¹ * (geometricDiscount (1 : ℝ) 1)⁻¹)) *
          ((4 * quantitativeCubeCutoffGradientConst d) *
            Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)))) *
          (Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
            Real.rpow (lambdaSq R (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)) := by
    dsimp [K, cutBound, L]
  calc
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
        (d := d) (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁ ρm)
        (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm) Ceff
        = K * cut * L := hleft
    _ ≤ K * cutBound * L := hmain
    _ =
      ((d : ℝ) * (((3 / 2 : ℝ) * Ceff * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((geometricDiscount s 1)⁻¹ * (geometricDiscount (1 : ℝ) 1)⁻¹)) *
        ((4 * quantitativeCubeCutoffGradientConst d) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)))) *
        (Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
          Real.rpow (lambdaSq R (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)) := hright

/-- Besov/cutoff-product part of the centered exact coefficient for the
local-patch midpoint cutoff. -/
theorem
    coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound_localPatchBuffered_localAcirc_le_rpow_sub
    {d : ℕ} {Q R : TriadicCube d} (a : CoeffField d) {s Ceff : ℝ}
    {k j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hCeff : 0 ≤ Ceff) (hs : 0 < s) (hs1 : s < 1)
    (hR : R ∈ descendantsAtDepth Q (j + 1))
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) (hjk : k ≤ j) :
    let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
    let Pone : ℝ :=
      Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
        Real.rpow (lambdaSq R (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)
    let Psub : ℝ :=
      Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
        Real.rpow (lambdaSq R (1 - s) (.finite 1) a) (-1 / 2 : ℝ)
    coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound R s
        (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliCenteredCutoffCoeffFactorBound R s
          (coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁ ρm)
          (coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁ ρm)
          (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm)
          (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρm) Ceff) ≤
      (4 * coarseCaccioppoliCenteredBesovHessianFront d s Ceff) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone +
        (2 * coarseCaccioppoliCenteredBesovGradientFront d s Ceff) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Psub := by
  dsimp
  let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
  let Hbase : ℝ := coarseCaccioppoliCenteredBesovHessianBase d s Ceff
  let Gbase : ℝ := coarseCaccioppoliCenteredBesovGradientBase d s Ceff
  let WH : ℝ :=
    cubeBesovScaleWeight (-1) R *
      coarseCaccioppoliLocalPatchDescendantCutoffHessianScaleBound Q j ρ₁ ρm
  let WG : ℝ :=
    cubeBesovScaleWeight (-1) R *
      coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁ ρm
  let Pone : ℝ :=
    Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
      Real.rpow (lambdaSq R (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)
  let Psub : ℝ :=
    Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
      Real.rpow (lambdaSq R (1 - s) (.finite 1) a) (-1 / 2 : ℝ)
  have hH :
      WH ≤ (16 * quantitativeCubeCutoffHessianConst d) *
        Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) := by
    simpa [WH, ρm] using
      (cubeBesovScaleWeight_neg_one_mul_localPatchDescendantBufferedCutoffHessianScaleBound_le_rpow_sub
        (Q := Q) (R := R) (k := k) (j := j) hR hchoice hlt hjk)
  have hG :
      WG ≤ (4 * quantitativeCubeCutoffGradientConst d) *
        Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) := by
    simpa [WG, ρm] using
      (cubeBesovScaleWeight_neg_one_mul_localPatch_buffered_cutoffGradient_le_rpow_sub
        (Q := Q) (R := R) (k := k) (j := j) hR hchoice hlt)
  have hdisc_s_pos : 0 < geometricDiscount s 1 := by
    exact geometricDiscount_pos (by simpa using hs)
  have hdisc_one_pos : 0 < geometricDiscount (1 : ℝ) 1 := by
    exact geometricDiscount_pos (by norm_num : 0 < (1 : ℝ) * 1)
  have hdisc_sub_pos : 0 < geometricDiscount (1 - s) 1 := by
    exact geometricDiscount_pos (by nlinarith)
  have hgeomS_nonneg : 0 ≤ (1 - (3 : ℝ) ^ (-s))⁻¹ := by
    have hlt_one : (3 : ℝ) ^ (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    exact inv_nonneg.mpr (sub_nonneg.mpr hlt_one.le)
  have hnote_nonneg :
      0 ≤ ((3 / 2 : ℝ) * Ceff * (3 : ℝ) ^ ((d : ℝ) + 1)) := by
    exact mul_nonneg (mul_nonneg (by positivity) hCeff)
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  have hHbase_nonneg : 0 ≤ Hbase := by
    dsimp [Hbase]
    refine mul_nonneg ?_ ?_
    · refine mul_nonneg ?_ (inv_nonneg.mpr hdisc_s_pos.le)
      exact mul_nonneg (by exact_mod_cast Nat.zero_le d : 0 ≤ (d : ℝ))
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    · refine mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) ?_
      exact mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg hnote_nonneg (inv_nonneg.mpr hdisc_one_pos.le))
  have hGbase_nonneg : 0 ≤ Gbase := by
    dsimp [Gbase]
    refine mul_nonneg ?_ ?_
    · refine mul_nonneg ?_ (inv_nonneg.mpr hdisc_s_pos.le)
      exact mul_nonneg (by exact_mod_cast Nat.zero_le d : 0 ≤ (d : ℝ))
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    · refine mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) ?_
      exact mul_nonneg (mul_nonneg hnote_nonneg hgeomS_nonneg)
        (inv_nonneg.mpr hdisc_sub_pos.le)
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
  have hHterm :
      Hbase * WH * Pone ≤
        (4 * coarseCaccioppoliCenteredBesovHessianFront d s Ceff) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone := by
    have h :=
      mul_le_mul_of_nonneg_left hH hHbase_nonneg
    have h' := mul_le_mul_of_nonneg_right h hPone_nonneg
    calc
      Hbase * WH * Pone ≤
          Hbase * ((16 * quantitativeCubeCutoffHessianConst d) *
            Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ))) * Pone := h'
      _ =
          (4 * coarseCaccioppoliCenteredBesovHessianFront d s Ceff) *
            Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone := by
            dsimp [Hbase, coarseCaccioppoliCenteredBesovHessianFront]
            ring
  have hGterm :
      Gbase * WG * Psub ≤
        (2 * coarseCaccioppoliCenteredBesovGradientFront d s Ceff) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Psub := by
    have h :=
      mul_le_mul_of_nonneg_left hG hGbase_nonneg
    have h' := mul_le_mul_of_nonneg_right h hPsub_nonneg
    calc
      Gbase * WG * Psub ≤
          Gbase * ((4 * quantitativeCubeCutoffGradientConst d) *
            Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ))) * Psub := h'
      _ =
          (2 * coarseCaccioppoliCenteredBesovGradientFront d s Ceff) *
            Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Psub := by
            dsimp [Gbase, coarseCaccioppoliCenteredBesovGradientFront]
            ring
  have hsplit :
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound R s
          (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliCenteredCutoffCoeffFactorBound R s
            (coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁ ρm)
            (coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁ ρm)
            (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm)
            (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρm) Ceff) =
        Hbase * WH * Pone + Gbase * WG * Psub := by
    have hcancel_s :
        cubeBesovScaleWeight (-s) R * cubeBesovScaleWeight s R = 1 :=
      cubeBesovScaleWeight_neg_mul_cubeBesovScaleWeight R s
    have hweight_sub :
        cubeBesovScaleWeight (-s) R * cubeBesovScaleWeight (-(1 - s)) R =
          cubeBesovScaleWeight (-1) R := by
      rw [cubeBesovScaleWeight_mul_eq_add]
      congr 1
      ring
    let Wm : ℝ := cubeBesovScaleWeight (-s) R
    let Wp : ℝ := cubeBesovScaleWeight s R
    let Wo : ℝ := cubeBesovScaleWeight (-1) R
    let Wsub : ℝ := cubeBesovScaleWeight (-(1 - s)) R
    let Pow : ℝ := (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + s)
    let DiscS : ℝ := (geometricDiscount s 1)⁻¹
    let Lam : ℝ := Real.rpow (LambdaSqFinite R s 1 a) (1 / 2 : ℝ)
    let DescH : ℝ := coarseCaccioppoliLocalPatchDescendantCutoffHessianScaleBound Q j ρ₁ ρm
    let Xi : ℝ := coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁ ρm
    let Sqrt : ℝ := Real.sqrt ((1 - Real.rpow (3 : ℝ) (2 * (s - 1)))⁻¹)
    let Note : ℝ := (3 / 2 : ℝ) * Ceff * (3 : ℝ) ^ ((d : ℝ) + 1)
    let Disc1 : ℝ := (geometricDiscount (1 : ℝ) 1)⁻¹
    let DiscSub : ℝ := (geometricDiscount (1 - s) 1)⁻¹
    let Geom : ℝ := (1 - (3 : ℝ) ^ (-s))⁻¹
    let L1 : ℝ := Real.rpow (lambdaSqFinite R (1 : ℝ) 1 a) (-1 / 2 : ℝ)
    let Lsub : ℝ := Real.rpow (lambdaSqFinite R (1 - s) 1 a) (-1 / 2 : ℝ)
    have hcancel : Wm * Wp = 1 := by
      simpa [Wm, Wp] using hcancel_s
    have hsub : Wm * Wsub = Wo := by
      simpa [Wm, Wsub, Wo] using hweight_sub
    have hexpanded :
        coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound R s
            (coarseCaccioppoliLambdaFactor R a s)
            (coarseCaccioppoliLambdaFactor R a s)
            (coarseCaccioppoliCenteredCutoffCoeffFactorBound R s
              (coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁ ρm)
              (coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁ ρm)
              (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm)
              (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρm) Ceff) =
          Pow * Wm * DiscS * Lam *
            (2 * (Wp * (DescH * Sqrt * (Note * (Wo * Disc1 * L1))) +
              Xi * (Note * Geom * (Wsub * DiscSub * Lsub)))) := by
      dsimp [Pow, Wm, Wp, Wo, Wsub, DiscS, Lam, DescH, Xi, Sqrt, Note,
        Disc1, DiscSub, Geom, L1, Lsub]
      unfold coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound
      rw [cubeBesovScaleWeight_mul_centeredCutoffCoeffFactorBound_eq]
      unfold coarseCaccioppoliLambdaFactor
        coarseCaccioppoliCanonicalGradientAcircOne
        coarseCaccioppoliCanonicalGradientAcircOneSub
        coarseCaccioppoliCanonicalGradientAcirc
        LambdaSq lambdaSq
      rw [cubeScaleFactor_mul_coarseCaccioppoliLocalPatchCutoffHessianBound_eq_descendant
        hR ρ₁ ρm]
      ring_nf
      rw [show LambdaSqFinite R s 1 a ^ (1 / 2 : ℝ) =
          Real.rpow (LambdaSqFinite R s 1 a) (1 / 2 : ℝ) by rfl,
        show lambdaSqFinite R (1 : ℝ) 1 a ^ (-1 / 2 : ℝ) =
          Real.rpow (lambdaSqFinite R (1 : ℝ) 1 a) (-1 / 2 : ℝ) by rfl,
        show lambdaSqFinite R (1 - s) 1 a ^ (-1 / 2 : ℝ) =
          Real.rpow (lambdaSqFinite R (1 - s) 1 a) (-1 / 2 : ℝ) by rfl,
        show (3 : ℝ) ^ (-2 + s * 2) = Real.rpow (3 : ℝ) (-2 + s * 2) by rfl]
      ring
    calc
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound R s
          (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliCenteredCutoffCoeffFactorBound R s
            (coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁ ρm)
            (coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁ ρm)
            (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm)
            (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρm) Ceff)
          = Pow * Wm * DiscS * Lam *
            (2 * (Wp * (DescH * Sqrt * (Note * (Wo * Disc1 * L1))) +
              Xi * (Note * Geom * (Wsub * DiscSub * Lsub)))) := hexpanded
      _ =
          Pow * DiscS * (2 * (Sqrt * (Note * Disc1))) *
              (Wo * DescH) * (Lam * L1) +
            Pow * DiscS * (2 * ((Note * Geom) * DiscSub)) *
              (Wo * Xi) * (Lam * Lsub) := by
            calc
              Pow * Wm * DiscS * Lam *
                  (2 * (Wp * (DescH * Sqrt * (Note * (Wo * Disc1 * L1))) +
                    Xi * (Note * Geom * (Wsub * DiscSub * Lsub))))
                  = Pow * DiscS * 2 *
                      ((Wm * Wp) * (Lam * DescH * Sqrt * Note * Wo * Disc1 * L1) +
                        (Wm * Wsub) * (Lam * Xi * Note * Geom * DiscSub * Lsub)) := by
                    ring
              _ =
                  Pow * DiscS * (2 * (Sqrt * (Note * Disc1))) *
                      (Wo * DescH) * (Lam * L1) +
                    Pow * DiscS * (2 * ((Note * Geom) * DiscSub)) *
                      (Wo * Xi) * (Lam * Lsub) := by
                    rw [hcancel, hsub]
                    ring
      _ = Hbase * WH * Pone + Gbase * WG * Psub := by
            dsimp [Hbase, Gbase, WH, WG, Pone, Psub, Pow, DiscS, Lam, DescH,
              Xi, Sqrt, Note, Disc1, DiscSub, Geom, L1, Lsub,
              coarseCaccioppoliCenteredBesovHessianBase,
              coarseCaccioppoliCenteredBesovGradientBase, LambdaSq, lambdaSq]
  calc
    coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound R s
        (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliCenteredCutoffCoeffFactorBound R s
          (coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁ ρm)
          (coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁ ρm)
          (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm)
          (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρm) Ceff)
        = Hbase * WH * Pone + Gbase * WG * Psub := hsplit
    _ ≤ (4 * coarseCaccioppoliCenteredBesovHessianFront d s Ceff) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone +
        (2 * coarseCaccioppoliCenteredBesovGradientFront d s Ceff) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Psub :=
          add_le_add hHterm hGterm

/-- Average-plus-Besov factor-bound comparison for the local-patch centered
exact coefficient.  The extra descendant generation is charged as an extra
factor `3` in the centered-front budget. -/
theorem
    coarseCaccioppoliFluxEnergyExactCenteredFactorBounds_localPatchBuffered_localAcirc_le_alpha_of_scale
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} (a : CoeffField d)
    {s t CeffLocal CeffWork : ℝ} {k j : ℕ} {ρ₁ ρ₂ lam Lam : ℝ}
    {hheight : ℝ → ℝ → ℝ}
    (hCeffLocal : 0 ≤ CeffLocal) (hCeffWork : 0 ≤ CeffWork)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hR : R ∈ descendantsAtDepth Q (j + 1))
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
      (6 * coarseCaccioppoliCenteredAverageFront d s CeffLocal +
          12 * coarseCaccioppoliCenteredBesovHessianFront d s CeffLocal +
          6 * coarseCaccioppoliCenteredBesovGradientFront d s CeffLocal) *
          Real.rpow (3 : ℝ) (k : ℝ) ≤
        CeffWork / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂)
    (hheight_le_j : hheight ρ₁ ρ₂ ≤ (j : ℝ)) :
    let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
        (d := d) (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁ ρm)
        (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm) CeffLocal +
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound R s
        (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliCenteredCutoffCoeffFactorBound R s
          (coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁ ρm)
          (coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁ ρm)
          (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm)
          (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρm)
          CeffLocal) ≤
      coarseCaccioppoliBoundaryAlphaOfHeight Q a s t CeffWork hheight ρ₁ ρ₂ := by
  dsimp
  let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
  let jS : ℝ := ((j + 1 : ℕ) : ℝ)
  let A : ℝ := 6 * coarseCaccioppoliCenteredAverageFront d s CeffLocal
  let H : ℝ := 12 * coarseCaccioppoliCenteredBesovHessianFront d s CeffLocal
  let G : ℝ := 6 * coarseCaccioppoliCenteredBesovGradientFront d s CeffLocal
  let Pone : ℝ :=
    Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
      Real.rpow (lambdaSq R (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)
  let Psub : ℝ :=
    Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
      Real.rpow (lambdaSq R (1 - s) (.finite 1) a) (-1 / 2 : ℝ)
  let Theta : ℝ := Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)
  let depthTheta : ℝ :=
    Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * jS) * Theta
  let front : ℝ := CeffWork / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂
  have hs1 : s < 1 := by nlinarith [ht, hst]
  have hpow_succ :
      Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) =
        3 * Real.rpow (3 : ℝ) ((k : ℝ) - jS) := by
    have hsplit : ((k : ℝ) - (j : ℝ)) = 1 + ((k : ℝ) - jS) := by
      dsimp [jS]
      norm_num
      ring
    have hadd :
        Real.rpow (3 : ℝ) (1 + ((k : ℝ) - jS)) =
          Real.rpow (3 : ℝ) (1 : ℝ) *
            Real.rpow (3 : ℝ) ((k : ℝ) - jS) :=
      Real.rpow_add (by norm_num : 0 < (3 : ℝ)) (1 : ℝ) ((k : ℝ) - jS)
    calc
      Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ))
          = Real.rpow (3 : ℝ) (1 + ((k : ℝ) - jS)) := by rw [hsplit]
      _ = Real.rpow (3 : ℝ) (1 : ℝ) *
            Real.rpow (3 : ℝ) ((k : ℝ) - jS) := hadd
      _ = 3 * Real.rpow (3 : ℝ) ((k : ℝ) - jS) := by norm_num
  have havg_sub :=
    coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound_localPatchBuffered_localAcircOne_le_rpow_sub
      (Q := Q) (R := R) (a := a) (s := s) (Ceff := CeffLocal)
      (k := k) (j := j) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
      hCeffLocal hs hR hchoice hlt
  have hbesov_sub :=
    coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound_localPatchBuffered_localAcirc_le_rpow_sub
      (Q := Q) (R := R) (a := a) (s := s) (Ceff := CeffLocal)
      (k := k) (j := j) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
      hCeffLocal hs hs1 hR hchoice hlt hjk
  have havg_rhs_eq :
      ((d : ℝ) * (((3 / 2 : ℝ) * CeffLocal * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((geometricDiscount s 1)⁻¹ * (geometricDiscount (1 : ℝ) 1)⁻¹)) *
        ((4 * quantitativeCubeCutoffGradientConst d) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)))) *
        Pone =
        A * Real.rpow (3 : ℝ) ((k : ℝ) - jS) * Pone := by
    let Base : ℝ :=
      (d : ℝ) * (((3 / 2 : ℝ) * CeffLocal * (3 : ℝ) ^ ((d : ℝ) + 1)) *
        ((geometricDiscount s 1)⁻¹ * (geometricDiscount (1 : ℝ) 1)⁻¹))
    let Grad : ℝ := quantitativeCubeCutoffGradientConst d
    have hreplace :
        Base * ((4 * Grad) * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ))) * Pone =
          Base * ((4 * Grad) *
            (3 * Real.rpow (3 : ℝ) ((k : ℝ) - jS))) * Pone :=
      congrArg (fun x : ℝ => Base * ((4 * Grad) * x) * Pone) hpow_succ
    change
      Base * ((4 * Grad) * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ))) * Pone =
        (6 * (Base * (2 * Grad))) *
          Real.rpow (3 : ℝ) ((k : ℝ) - jS) * Pone
    calc
      Base * ((4 * Grad) * Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ))) * Pone
          = Base * ((4 * Grad) *
              (3 * Real.rpow (3 : ℝ) ((k : ℝ) - jS))) * Pone := hreplace
      _ = (6 * (Base * (2 * Grad))) *
            Real.rpow (3 : ℝ) ((k : ℝ) - jS) * Pone := by ring
  have hbesov_sub' :
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound R s
        (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliCenteredCutoffCoeffFactorBound R s
          (coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁ ρm)
          (coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁ ρm)
          (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm)
          (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρm) CeffLocal) ≤
        H * Real.rpow (3 : ℝ) ((k : ℝ) - jS) * Pone +
          G * Real.rpow (3 : ℝ) ((k : ℝ) - jS) * Psub := by
    have hH_eq :
        (4 * coarseCaccioppoliCenteredBesovHessianFront d s CeffLocal) *
            Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone =
          H * Real.rpow (3 : ℝ) ((k : ℝ) - jS) * Pone := by
      have hreplace :
          (4 * coarseCaccioppoliCenteredBesovHessianFront d s CeffLocal) *
              Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone =
            (4 * coarseCaccioppoliCenteredBesovHessianFront d s CeffLocal) *
              (3 * Real.rpow (3 : ℝ) ((k : ℝ) - jS)) * Pone :=
        congrArg
          (fun x : ℝ =>
            (4 * coarseCaccioppoliCenteredBesovHessianFront d s CeffLocal) * x *
              Pone) hpow_succ
      calc
        (4 * coarseCaccioppoliCenteredBesovHessianFront d s CeffLocal) *
            Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone
            = (4 * coarseCaccioppoliCenteredBesovHessianFront d s CeffLocal) *
              (3 * Real.rpow (3 : ℝ) ((k : ℝ) - jS)) * Pone := hreplace
        _ = H * Real.rpow (3 : ℝ) ((k : ℝ) - jS) * Pone := by
              dsimp [H]
              ring
    have hG_eq :
        (2 * coarseCaccioppoliCenteredBesovGradientFront d s CeffLocal) *
            Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Psub =
          G * Real.rpow (3 : ℝ) ((k : ℝ) - jS) * Psub := by
      have hreplace :
          (2 * coarseCaccioppoliCenteredBesovGradientFront d s CeffLocal) *
              Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Psub =
            (2 * coarseCaccioppoliCenteredBesovGradientFront d s CeffLocal) *
              (3 * Real.rpow (3 : ℝ) ((k : ℝ) - jS)) * Psub :=
        congrArg
          (fun x : ℝ =>
            (2 * coarseCaccioppoliCenteredBesovGradientFront d s CeffLocal) * x *
              Psub) hpow_succ
      calc
        (2 * coarseCaccioppoliCenteredBesovGradientFront d s CeffLocal) *
            Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Psub
            = (2 * coarseCaccioppoliCenteredBesovGradientFront d s CeffLocal) *
              (3 * Real.rpow (3 : ℝ) ((k : ℝ) - jS)) * Psub := hreplace
        _ = G * Real.rpow (3 : ℝ) ((k : ℝ) - jS) * Psub := by
              dsimp [G]
              ring
    calc
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound R s
          (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliCenteredCutoffCoeffFactorBound R s
            (coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁ ρm)
            (coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁ ρm)
            (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm)
            (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρm) CeffLocal)
          ≤
        (4 * coarseCaccioppoliCenteredBesovHessianFront d s CeffLocal) *
            Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone +
          (2 * coarseCaccioppoliCenteredBesovGradientFront d s CeffLocal) *
            Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Psub := by
            simpa [ρm, Pone, Psub] using hbesov_sub
      _ =
        H * Real.rpow (3 : ℝ) ((k : ℝ) - jS) * Pone +
          G * Real.rpow (3 : ℝ) ((k : ℝ) - jS) * Psub := by
            exact congrArg₂ (fun x y : ℝ => x + y) hH_eq hG_eq
  have hfactor_sub :
      coarseCaccioppoliFluxEnergyExactCenteredAverageCoeffFactorBound
          (d := d) (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁ ρm)
          (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm) CeffLocal +
        coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound R s
          (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliCenteredCutoffCoeffFactorBound R s
            (coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁ ρm)
            (coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁ ρm)
            (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm)
            (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρm)
            CeffLocal) ≤
        A * Real.rpow (3 : ℝ) ((k : ℝ) - jS) * Pone +
          (H * Real.rpow (3 : ℝ) ((k : ℝ) - jS) * Pone +
            G * Real.rpow (3 : ℝ) ((k : ℝ) - jS) * Psub) := by
    exact add_le_add
      (by simpa [Pone, ρm] using le_trans havg_sub havg_rhs_eq.le)
      hbesov_sub'
  have hprod_one :
      Real.rpow (3 : ℝ) (-jS) * Pone ≤ depthTheta := by
    simpa [Pone, Theta, depthTheta, jS] using
      (faithful_centered_descendant_product_one_le_parent_theta
        (Q := Q) (R := R) (j := j + 1) a hs ht hst hEllCube hR
        hBsum_s hSigmaSum_t)
  have hprod_sub :
      Real.rpow (3 : ℝ) (-jS) * Psub ≤ depthTheta := by
    simpa [Psub, Theta, depthTheta, jS] using
      (faithful_centered_descendant_product_le_parent_theta
        (Q := Q) (R := R) (j := j + 1) a hs ht hst hEllCube hR
        hBsum_s hSigmaSum_t)
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
    exact mul_nonneg (by norm_num)
      (coarseCaccioppoliCenteredAverageFront_nonneg d hCeffLocal hs)
  have hH_nonneg : 0 ≤ H := by
    exact mul_nonneg (by norm_num)
      (coarseCaccioppoliCenteredBesovHessianFront_nonneg d hCeffLocal hs)
  have hG_nonneg : 0 ≤ G := by
    exact mul_nonneg (by norm_num)
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
      Real.rpow (3 : ℝ) ((k : ℝ) - jS) =
        Real.rpow (3 : ℝ) (k : ℝ) * Real.rpow (3 : ℝ) (-jS) := by
    rw [sub_eq_add_neg]
    exact Real.rpow_add (by norm_num : 0 < (3 : ℝ)) _ _
  have hsub_rhs_eq :
      A * Real.rpow (3 : ℝ) ((k : ℝ) - jS) * Pone +
          (H * Real.rpow (3 : ℝ) ((k : ℝ) - jS) * Pone +
            G * Real.rpow (3 : ℝ) ((k : ℝ) - jS) * Psub) =
        (A * Real.rpow (3 : ℝ) (k : ℝ)) *
            (Real.rpow (3 : ℝ) (-jS) * Pone) +
          (H * Real.rpow (3 : ℝ) (k : ℝ)) *
            (Real.rpow (3 : ℝ) (-jS) * Pone) +
          (G * Real.rpow (3 : ℝ) (k : ℝ)) *
            (Real.rpow (3 : ℝ) (-jS) * Psub) := by
    rw [hpow_split]
    ring
  have hterms_to_depth :
      (A * Real.rpow (3 : ℝ) (k : ℝ)) *
            (Real.rpow (3 : ℝ) (-jS) * Pone) +
          (H * Real.rpow (3 : ℝ) (k : ℝ)) *
            (Real.rpow (3 : ℝ) (-jS) * Pone) +
          (G * Real.rpow (3 : ℝ) (k : ℝ)) *
            (Real.rpow (3 : ℝ) (-jS) * Psub) ≤
        ((A + H + G) * Real.rpow (3 : ℝ) (k : ℝ)) * depthTheta := by
    calc
      (A * Real.rpow (3 : ℝ) (k : ℝ)) *
            (Real.rpow (3 : ℝ) (-jS) * Pone) +
          (H * Real.rpow (3 : ℝ) (k : ℝ)) *
            (Real.rpow (3 : ℝ) (-jS) * Pone) +
          (G * Real.rpow (3 : ℝ) (k : ℝ)) *
            (Real.rpow (3 : ℝ) (-jS) * Psub)
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
  have hheight_le_jS : hheight ρ₁ ρ₂ ≤ jS := by
    have hj_le_succ : (j : ℝ) ≤ jS := by
      dsimp [jS]
      exact_mod_cast Nat.le_succ j
    exact le_trans hheight_le_j hj_le_succ
  have hσ_pos : 0 < coarseCaccioppoliSigma s t :=
    coarseCaccioppoli_sigma_pos hst
  have hexp_le :
      -coarseCaccioppoliSigma s t * jS ≤
        -coarseCaccioppoliSigma s t * hheight ρ₁ ρ₂ := by
    exact mul_le_mul_of_nonpos_left hheight_le_jS (by linarith)
  have hpow_height :
      Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * jS) ≤
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
        (coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁ ρm)
        (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm) CeffLocal +
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound R s
        (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliLambdaFactor R a s)
        (coarseCaccioppoliCenteredCutoffCoeffFactorBound R s
          (coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁ ρm)
          (coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁ ρm)
          (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm)
          (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρm)
          CeffLocal)
        ≤ A * Real.rpow (3 : ℝ) ((k : ℝ) - jS) * Pone +
          (H * Real.rpow (3 : ℝ) ((k : ℝ) - jS) * Pone +
            G * Real.rpow (3 : ℝ) ((k : ℝ) - jS) * Psub) := hfactor_sub
    _ =
        (A * Real.rpow (3 : ℝ) (k : ℝ)) *
            (Real.rpow (3 : ℝ) (-jS) * Pone) +
          (H * Real.rpow (3 : ℝ) (k : ℝ)) *
            (Real.rpow (3 : ℝ) (-jS) * Pone) +
          (G * Real.rpow (3 : ℝ) (k : ℝ)) *
            (Real.rpow (3 : ℝ) (-jS) * Psub) := hsub_rhs_eq
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

/-- Local-patch exact centered coefficient, with descendant-local canonical
`A^\circ` factors, localized directly to the parent `Alpha` coefficient.  The
cutoff is the translated local patch cutoff on the midpoint radius, so the
descendant lies one generation deeper than the centered buffered route. -/
theorem
    coarseCaccioppoliFluxEnergyExactCenteredCoeff_localPatchBuffered_localAcirc_le_alpha_of_scale
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} (center : Vec d) (a : CoeffField d)
    {s t CeffLocal CeffWork : ℝ} {k j : ℕ} {ρ₁ ρ₂ lam Lam : ℝ}
    {hheight : ℝ → ℝ → ℝ}
    (hρ₁_pos : 0 < ρ₁)
    (hCeffLocal : 0 ≤ CeffLocal) (hCeffWork : 0 ≤ CeffWork)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hR : R ∈ descendantsAtDepth Q (j + 1))
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
      (6 * coarseCaccioppoliCenteredAverageFront d s CeffLocal +
          12 * coarseCaccioppoliCenteredBesovHessianFront d s CeffLocal +
          6 * coarseCaccioppoliCenteredBesovGradientFront d s CeffLocal) *
          Real.rpow (3 : ℝ) (k : ℝ) ≤
        CeffWork / (s * (1 - s)) * coarseCaccioppoliGapInv ρ₁ ρ₂)
    (hheight_le_j : hheight ρ₁ ρ₂ ≤ (j : ℝ)) :
    let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
    coarseCaccioppoliFluxEnergyExactCenteredCoeff R a s
        (scalarCutoffGradientField
          (coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm))
        (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm)
        (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρm)
        (coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁ ρm)
        CeffLocal ≤
      coarseCaccioppoliBoundaryAlphaOfHeight Q a s t CeffWork hheight ρ₁ ρ₂ := by
  dsimp
  let ρm : ℝ := coarseCaccioppoliBufferedCutoffRadius ρ₁ ρ₂
  have hlt_m : ρ₁ < ρm := by
    simpa [ρm] using (coarseCaccioppoliBufferedCutoffRadius_between hlt).1
  have hs1 : s < 1 := by nlinarith [ht, hst]
  have hsumR_s :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) :=
    summable_geometricWeight_maxDescendantBBlockNormAtScale_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j + 1) a s hs.le hR hBsum_s
  have hB_nonneg :
      0 ≤ coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁ ρm := by
    dsimp [coarseCaccioppoliLocalPatchCutoffHessianBound]
    exact div_nonneg (quantitativeCubeCutoffHessianConst_nonneg d) (sq_nonneg _)
  have hAcirc1_nonneg :
      0 ≤ coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm := by
    simpa using coarseCaccioppoliCanonicalGradientAcircOne_nonneg R a ρ₁ ρm
  have hAcircS_nonneg :
      0 ≤ coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρm := by
    simpa using
      coarseCaccioppoliCanonicalGradientAcircOneSub_nonneg R a hs1.le ρ₁ ρm
  have hξ :
      cubeLpNorm R ∞
          (scalarCutoffGradientField
            (coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm)) ≤
        coarseCaccioppoliLocalPatchCutoffGradientBound Q ρ₁ ρm := by
    simpa [ρm, coarseCaccioppoliLocalPatchCutoffGradientBound] using
      coarseCaccioppoliLocalCanonicalFun_cubeLpNorm_infty_gradientField_le_on_cube
        Q R center hρ₁_pos hlt_m
  have hcentered :=
    coarseCaccioppoliFluxEnergyExactCenteredFactorBounds_localPatchBuffered_localAcirc_le_alpha_of_scale
      (Q := Q) (R := R) (a := a) (s := s) (t := t)
      (CeffLocal := CeffLocal) (CeffWork := CeffWork)
      (k := k) (j := j) (ρ₁ := ρ₁) (ρ₂ := ρ₂)
      (hheight := hheight) hCeffLocal hCeffWork hs ht hst hEllCube hR
      hBsum_s hSigmaSum_t hchoice hlt hjk hscale hheight_le_j
  exact
    coarseCaccioppoliFluxEnergyExactCenteredCoeff_le_of_separated_factor_bounds
      R a s CeffLocal
      (scalarCutoffGradientField
        (coarseCaccioppoliLocalCanonicalFun Q center ρ₁ ρm))
      (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm)
      (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρm)
      (coarseCaccioppoliLocalPatchCutoffHessianBound Q ρ₁ ρm)
      hs hCeffLocal hB_nonneg hAcirc1_nonneg hAcircS_nonneg
      (sqrt_coarseBBlockNorm_le_coarseCaccioppoliLambdaFactor R a hs hsumR_s)
      (show
        (geometricDiscount s 1)⁻¹ *
            Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) ≤
          coarseCaccioppoliLambdaFactor R a s by
        simp [coarseCaccioppoliLambdaFactor])
      hξ le_rfl le_rfl le_rfl
      (by simpa [ρm] using hcentered)


end

end Homogenization
