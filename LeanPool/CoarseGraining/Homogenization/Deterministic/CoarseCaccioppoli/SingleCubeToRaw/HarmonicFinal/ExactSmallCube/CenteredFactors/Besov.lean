/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.ExactSmallCube.CenteredFronts
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.InputSpecializations
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.LocalConstantBranch
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.EnergyBridge.CenteredLocalCoefficient
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.QuantitativeCutoffInputs.Setup

/-! # Besov -/

@[expose] public section

namespace Homogenization

/-!
# Exact small-cube centered factors: Besov cutoff pieces
-/

noncomputable section

open scoped ENNReal

/-- The Besov/cutoff-product part of the centered exact coefficient has the two
small-cube cutoff gains appearing in the LaTeX proof.  The Hessian subterm uses
the extra descendant scale in
`cubeBesovScaleWeight_neg_one_mul_descendantCutoffHessianScaleBound_le_rpow_sub`;
the gradient subterm uses
`cubeBesovScaleWeight_neg_one_mul_parent_cutoffGradient_le_rpow_sub`. -/
theorem
    coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound_localAcirc_le_rpow_sub
    {d : ℕ} {Q R : TriadicCube d} (a : CoeffField d) {s Ceff : ℝ}
    {k j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hCeff : 0 ≤ Ceff) (hs : 0 < s) (hs1 : s < 1)
    (hR : R ∈ descendantsAtDepth Q j)
    (hchoice : CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂)
    (hlt : ρ₁ < ρ₂) (hjk : k ≤ j) :
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
          (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂)
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂)
          (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρ₂)
          (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρ₂) Ceff) ≤
      coarseCaccioppoliCenteredBesovHessianFront d s Ceff *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone +
        coarseCaccioppoliCenteredBesovGradientFront d s Ceff *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Psub := by
  dsimp
  let Hbase : ℝ := coarseCaccioppoliCenteredBesovHessianBase d s Ceff
  let Gbase : ℝ := coarseCaccioppoliCenteredBesovGradientBase d s Ceff
  let WH : ℝ :=
    cubeBesovScaleWeight (-1) R *
      coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁ ρ₂
  let WG : ℝ :=
    cubeBesovScaleWeight (-1) R *
      coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂
  let Pone : ℝ :=
    Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
      Real.rpow (lambdaSq R (1 : ℝ) (.finite 1) a) (-1 / 2 : ℝ)
  let Psub : ℝ :=
    Real.rpow (LambdaSq R s (.finite 1) a) (1 / 2 : ℝ) *
      Real.rpow (lambdaSq R (1 - s) (.finite 1) a) (-1 / 2 : ℝ)
  have hH :
      WH ≤ (4 * quantitativeCubeCutoffHessianConst d) *
        Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) := by
    simpa [WH] using
      (cubeBesovScaleWeight_neg_one_mul_descendantCutoffHessianScaleBound_le_rpow_sub
        (Q := Q) (R := R) (k := k) (j := j) hR hchoice hlt hjk)
  have hG :
      WG ≤ (2 * quantitativeCubeCutoffGradientConst d) *
        Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) := by
    simpa [WG] using
      (cubeBesovScaleWeight_neg_one_mul_parent_cutoffGradient_le_rpow_sub
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
        coarseCaccioppoliCenteredBesovHessianFront d s Ceff *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone := by
    have h :=
      mul_le_mul_of_nonneg_left hH hHbase_nonneg
    have h' := mul_le_mul_of_nonneg_right h hPone_nonneg
    calc
      Hbase * WH * Pone ≤
          Hbase * ((4 * quantitativeCubeCutoffHessianConst d) *
            Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ))) * Pone := h'
      _ =
          coarseCaccioppoliCenteredBesovHessianFront d s Ceff *
            Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone := by
            dsimp [Hbase, coarseCaccioppoliCenteredBesovHessianFront]
            ring
  have hGterm :
      Gbase * WG * Psub ≤
        coarseCaccioppoliCenteredBesovGradientFront d s Ceff *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Psub := by
    have h :=
      mul_le_mul_of_nonneg_left hG hGbase_nonneg
    have h' := mul_le_mul_of_nonneg_right h hPsub_nonneg
    calc
      Gbase * WG * Psub ≤
          Gbase * ((2 * quantitativeCubeCutoffGradientConst d) *
            Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ))) * Psub := h'
      _ =
          coarseCaccioppoliCenteredBesovGradientFront d s Ceff *
            Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Psub := by
            dsimp [Gbase, coarseCaccioppoliCenteredBesovGradientFront]
            ring
  have hsplit :
      coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound R s
          (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliLambdaFactor R a s)
          (coarseCaccioppoliCenteredCutoffCoeffFactorBound R s
            (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂)
            (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂)
            (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρ₂)
            (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρ₂) Ceff) =
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
    let DescH : ℝ := coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁ ρ₂
    let Xi : ℝ := coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂
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
              (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂)
              (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂)
              (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρ₂)
              (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρ₂) Ceff) =
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
      rw [cubeScaleFactor_mul_coarseCaccioppoliQuantitativeCutoffHessianBound_eq_descendant
        hR ρ₁ ρ₂]
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
            (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂)
            (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂)
            (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρ₂)
            (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρ₂) Ceff)
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
          (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρ₂)
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρ₂)
          (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρ₂)
          (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρ₂) Ceff)
        = Hbase * WH * Pone + Gbase * WG * Psub := hsplit
    _ ≤ coarseCaccioppoliCenteredBesovHessianFront d s Ceff *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone +
        coarseCaccioppoliCenteredBesovGradientFront d s Ceff *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Psub :=
          add_le_add hHterm hGterm

/-- Buffered version of
`coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound_localAcirc_le_rpow_sub`.
The midpoint cutoff quadruples the Hessian contribution and doubles the
gradient contribution, while the triadic scale is still chosen from the full
outer gap. -/
theorem
    coarseCaccioppoliFluxEnergyExactCenteredBesovCoeffFactorBound_buffered_localAcirc_le_rpow_sub
    {d : ℕ} {Q R : TriadicCube d} (a : CoeffField d) {s Ceff : ℝ}
    {k j : ℕ} {ρ₁ ρ₂ : ℝ}
    (hCeff : 0 ≤ Ceff) (hs : 0 < s) (hs1 : s < 1)
    (hR : R ∈ descendantsAtDepth Q j)
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
          (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρm)
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρm)
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
      coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁ ρm
  let WG : ℝ :=
    cubeBesovScaleWeight (-1) R *
      coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρm
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
      (cubeBesovScaleWeight_neg_one_mul_descendantBufferedCutoffHessianScaleBound_le_rpow_sub
        (Q := Q) (R := R) (k := k) (j := j) hR hchoice hlt hjk)
  have hG :
      WG ≤ (4 * quantitativeCubeCutoffGradientConst d) *
        Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) := by
    simpa [WG, ρm] using
      (cubeBesovScaleWeight_neg_one_mul_parent_buffered_cutoffGradient_le_rpow_sub
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
            (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρm)
            (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρm)
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
    let DescH : ℝ := coarseCaccioppoliDescendantCutoffHessianScaleBound Q j ρ₁ ρm
    let Xi : ℝ := coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρm
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
              (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρm)
              (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρm)
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
      rw [cubeScaleFactor_mul_coarseCaccioppoliQuantitativeCutoffHessianBound_eq_descendant
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
            (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρm)
            (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρm)
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
          (coarseCaccioppoliQuantitativeCutoffGradientBound Q ρ₁ ρm)
          (coarseCaccioppoliQuantitativeCutoffHessianBound Q ρ₁ ρm)
          (coarseCaccioppoliCanonicalGradientAcircOne R a ρ₁ ρm)
          (coarseCaccioppoliCanonicalGradientAcircOneSub R a s ρ₁ ρm) Ceff)
        = Hbase * WH * Pone + Gbase * WG * Psub := hsplit
    _ ≤ (4 * coarseCaccioppoliCenteredBesovHessianFront d s Ceff) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Pone +
        (2 * coarseCaccioppoliCenteredBesovGradientFront d s Ceff) *
          Real.rpow (3 : ℝ) ((k : ℝ) - (j : ℝ)) * Psub :=
          add_le_add hHterm hGterm

end

end Homogenization
