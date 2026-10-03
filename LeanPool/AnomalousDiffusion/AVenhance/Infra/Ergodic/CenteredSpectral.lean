/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.CenteredSpectralCore

/-! The homogeneous dual tests have zero mean, so the spectral estimate
requires only the fast factor's mean. The high remainder is controlled in L2
by test Poincare, without a mean assumption on that remainder. -/

@[expose] public section

namespace AVenhance.Infra.Ergodic
open scoped ContDiff
open MeasureTheory Homogenization AVenhance.Infra.Torus
noncomputable section

private theorem fast_product_low_frequency_pairing_bound :
  ∀ {d N : ℕ},
    (0 : ℕ) < N →
      ∀ {f : Vec d → ℝ} (Cf r : ℝ) {g : Vec d → ℝ},
        let M : ℕ := N / (2 : ℕ);
        let gap : ℝ := (↑N : ℝ) - (↑M : ℝ);
        let K : ℝ := ergodicFourierWeight d;
        let Fnorm : ℝ := (cellAverage fun (x : Vec d) => |f x| ^ (2 : ℕ)) ^ (1 / 2 : ℝ);
        let Gnorm : ℝ := (cellAverage fun (x : Vec d) => |g x| ^ (2 : ℕ)) ^ (1 / 2 : ℝ);
        (0 : ℝ) < gap →
          let lowProd : Vec d → ℝ := fun (x : Vec d) => lowProjection f M x * g x;
          (∫ (x : Vec d) in unitCell d, lowProd x ^ (2 : ℕ)) ^ (1 / 2 : ℝ) ≤
              (Fnorm + (32 : ℝ) * K ^ (1 / 2 : ℝ) * Cf * Real.exp (-r * (↑N : ℝ) / (4096 : ℝ))) *
                  Gnorm →
            homogeneousHMinusOneNorm lowProd ≤
                ENNReal.ofReal
                  (((2 : ℝ) * Real.pi * gap)⁻¹ * (∫ (x : Vec d) in unitCell d, lowProd x ^ (2 :
                      ℕ)) ^ (1 / 2 : ℝ)) →
              ((2 : ℝ) * Real.pi * gap)⁻¹ ≤ (↑N : ℝ)⁻¹ →
                let R : ℝ := K ^ (1 / 2 : ℝ);
                let E : ℝ := Real.exp (-r * (↑N : ℝ) / (4096 : ℝ));
                let lowReal : ℝ := (1 : ℝ) / (↑N : ℝ) * (Fnorm + (32 : ℝ) * R * Cf * E) * Gnorm;
                homogeneousHMinusOneNorm lowProd ≤ ENNReal.ofReal lowReal
    := by
  intro d N hN f Cf r g M gap K Fnorm Gnorm hgapPos lowProd hLowL2Bound hLowDual hcoef R E lowReal
  calc
    _ ≤ ENNReal.ofReal ((2 * Real.pi * gap)⁻¹ *
        (∫ x in Torus.unitCell d, lowProd x ^ 2) ^ (1 / 2 : ℝ)) := hLowDual
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have hc1 : 0 ≤ (2 * Real.pi * gap)⁻¹ := by positivity
      have hc2 : 0 ≤ (∫ x in Torus.unitCell d, lowProd x ^ 2) ^
          (1 / 2 : ℝ) := by positivity
      have hc3 : 0 ≤ (1 / (N : ℝ)) := by positivity
      calc
        _ ≤ (1 / (N : ℝ)) *
            (∫ x in Torus.unitCell d, lowProd x ^ 2) ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (by simpa [one_div] using hcoef) hc2
        _ ≤ (1 / (N : ℝ)) *
            ((Fnorm + 32 * K ^ (1 / 2 : ℝ) * Cf *
              Real.exp (-r * (N : ℝ) / 4096)) * Gnorm) :=
          mul_le_mul_of_nonneg_left hLowL2Bound hc3
        _ = _ := by ring)

private theorem fast_product_constant_pairing_zero :
  ((4 : ℝ) * Real.pi ^ (2 : ℕ))⁻¹ ^ (1 / 2 : ℝ) ≤ (1 : ℝ)
    := by
  rw [← Real.sqrt_eq_rpow]
  apply Real.sqrt_le_one.mpr
  have hpi : 1 ≤ Real.pi := le_trans (by norm_num) Real.two_le_pi
  have hpiSq : 1 ≤ Real.pi ^ 2 := by
    simpa using (sq_le_sq₀ (by norm_num) Real.pi_pos.le).2 hpi
  have hp : 1 ≤ 4 * Real.pi ^ 2 := by
    calc
      1 ≤ Real.pi ^ 2 := hpiSq
      _ = 1 * Real.pi ^ 2 := by ring
      _ ≤ 4 * Real.pi ^ 2 :=
        mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg Real.pi)
  exact inv_le_one_of_one_le₀ hp

private theorem fast_product_negative_sobolev_bound :
  ∀ {d N : ℕ},
    (0 : ℕ) < d →
      (0 : ℕ) < N →
        ∀ {f : Vec d → ℝ} (Cf r : ℝ),
          (0 : ℝ) ≤ Cf →
            ∀ {g : Vec d → ℝ},
              let M : ℕ := N / (2 : ℕ);
              let gap : ℝ := (↑N : ℝ) - (↑M : ℝ);
              let K : ℝ := ergodicFourierWeight d;
              let Fnorm : ℝ := (cellAverage fun (x : Vec d) => |f x| ^ (2 : ℕ)) ^ (1 / 2 : ℝ);
              let Gnorm : ℝ := (cellAverage fun (x : Vec d) => |g x| ^ (2 : ℕ)) ^ (1 / 2 : ℝ);
              let _ : ℝ := (1 : ℝ) + ((64 : ℝ) * K ^ (1 / 2 : ℝ) + (1024 : ℝ) * ((↑d : ℝ) + (1 :
                  ℝ)));
              (0 : ℝ) ≤ K →
                (0 : ℝ) ≤ Fnorm →
                  (0 : ℝ) ≤ Gnorm →
                    (1 : ℝ) ≤ (↑N : ℝ) →
                      (0 : ℝ) < gap →
                        let lowProd : Vec d → ℝ := fun (x : Vec d) => lowProjection f M x * g x;
                        let highProd : Vec d → ℝ := fun (x : Vec d) => highRemainder f M x * g x;
                        LocallyIntegrable lowProd volume →
                          LocallyIntegrable highProd volume →
                            MemLp highProd (2 : ENNReal) (volume.restrict (unitCell d)) ∧
                                MemLp (fun (x : Vec d) => (↑(highProd x) : ℂ)) (2 : ENNReal)
                                  (volume.restrict (unitCell d)) →
                              (∫ (x : Vec d) in unitCell d, lowProd x ^ (2 : ℕ)) ^ (1 / 2 : ℝ) ≤
                                  (Fnorm + (32 : ℝ) * K ^ (1 / 2 : ℝ) * Cf * Real.exp (-r * (↑N :
                                      ℝ) / (4096 : ℝ))) *
                                    Gnorm →
                                (∫ (x : Vec d) in unitCell d, highProd x ^ (2 : ℕ)) ^ (1 / 2 : ℝ) ≤
                                    ((1024 : ℝ) * ((↑d : ℝ) + (1 : ℝ)) * Cf + (32 : ℝ) * K ^ (1 /
                                        2 : ℝ) * Cf) *
                                        Real.exp (-r * (↑N : ℝ) / (4096 : ℝ)) *
                                      Gnorm →
                                  homogeneousHMinusOneNorm lowProd ≤
                                      ENNReal.ofReal
                                        (((2 : ℝ) * Real.pi * gap)⁻¹ *
                                          (∫ (x : Vec d) in unitCell d, lowProd x ^ (2 : ℕ)) ^ (1
                                              / 2 : ℝ)) →
                                    ((2 : ℝ) * Real.pi * gap)⁻¹ ≤ (↑N : ℝ)⁻¹ →
                                      (homogeneousHMinusOneNorm fun (x : Vec d) => f x * g x) ≤
                                        ENNReal.ofReal
                                          (((1 : ℝ) + (64 : ℝ) * ergodicFourierWeight d ^ (1 / 2 :
                                              ℝ) +
                                                    (1024 : ℝ) * ((↑d : ℝ) + (1 : ℝ))) /
                                                  (↑N : ℝ) *
                                                (cellAverage fun (x : Vec d) => |f x| ^ (2 : ℕ)) ^
                                                    (1 / 2 : ℝ) *
                                              (cellAverage fun (x : Vec d) => |g x| ^ (2 : ℕ)) ^
                                                  (1 / 2 : ℝ) +
                                            ((1 : ℝ) + (64 : ℝ) * ergodicFourierWeight d ^ (1 / 2
                                                : ℝ) +
                                                    (1024 : ℝ) * ((↑d : ℝ) + (1 : ℝ))) *
                                                  Cf *
                                                (cellAverage fun (x : Vec d) => |g x| ^ (2 : ℕ)) ^
                                                    (1 / 2 : ℝ) *
                                              Real.exp (-r * (↑N : ℝ) / (4096 : ℝ)))
    := by
  intro d N hd hN f Cf r hCf g M gap K Fnorm Gnorm Cdim hK hFnonneg hGnonneg hNreal hgapPos
      lowProd highProd hLowLI hHighLI hHighCellMem hLowL2Bound hHighL2Bound hLowDual hcoef
  let R : ℝ := K ^ (1 / 2 : ℝ)
  let D : ℝ := 1024 * ((d : ℝ) + 1)
  let E : ℝ := Real.exp (-r * (N : ℝ) / 4096)
  let lowReal : ℝ := (1 / (N : ℝ)) *
    (Fnorm + 32 * R * Cf * E) * Gnorm
  let highReal : ℝ := (D * Cf + 32 * R * Cf) * E * Gnorm
  have hLowDualReal : homogeneousHMinusOneNorm lowProd ≤ ENNReal.ofReal
      lowReal := by
    exact @fast_product_low_frequency_pairing_bound d N hN f Cf r g hgapPos hLowL2Bound hLowDual
        hcoef
  have hHighRealCell : MemLp highProd (ENNReal.ofReal (2 : ℝ))
      ((volume : Measure (Vec d)).restrict (Torus.unitCell d)) := by
    simpa using hHighCellMem.1
  have hHighPoincare := homogeneousHMinusOneNorm_le_of_cellL2 hd hHighRealCell
  have hPconst : ((4 * Real.pi ^ 2)⁻¹) ^ (1 / 2 : ℝ) ≤ 1 := by
    exact @fast_product_constant_pairing_zero
  have hHighDual : homogeneousHMinusOneNorm highProd ≤ ENNReal.ofReal
      highReal := by
    calc
      _ ≤ ENNReal.ofReal ((∫ x in Torus.unitCell d, highProd x ^ 2) ^
          (1 / 2 : ℝ) * ((4 * Real.pi ^ 2)⁻¹) ^ (1 / 2 : ℝ)) := hHighPoincare
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by
        have hnorm : 0 ≤ (∫ x in Torus.unitCell d, highProd x ^ 2) ^
            (1 / 2 : ℝ) := by positivity
        calc
          _ ≤ (∫ x in Torus.unitCell d, highProd x ^ 2) ^
                (1 / 2 : ℝ) := mul_le_of_le_one_right hnorm hPconst
          _ ≤ _ := hHighL2Bound)
  have htriangle := homogeneousHMinusOneNorm_add_le_of_locallyIntegrable hLowLI hHighLI
  have hsumFunctions :
      (fun x => f x * g x) = fun x => lowProd x + highProd x := by
    funext x
    dsimp [lowProd, highProd, highRemainder]
    ring
  have htriangle' : homogeneousHMinusOneNorm (fun x => f x * g x) ≤
      homogeneousHMinusOneNorm lowProd + homogeneousHMinusOneNorm highProd := by
    rw [hsumFunctions]
    exact htriangle
  have hLowRealNonneg : 0 ≤ lowReal := by
    dsimp [lowReal]
    positivity
  have hHighRealNonneg : 0 ≤ highReal := by
    dsimp [highReal]
    positivity
  have hR : 0 ≤ R := by dsimp [R]; exact Real.rpow_nonneg hK _
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hCdim : Cdim = 1 + (64 * R + D) := by rfl
  have hCgeOne : 1 ≤ 1 + (64 * R + D) := by
    exact le_add_of_nonneg_right
      (add_nonneg (mul_nonneg (by norm_num) hR) hD)
  have hNinv : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hNreal
  have hCfirst : (1 / (N : ℝ)) ≤
      (1 + (64 * R + D)) / (N : ℝ) := by
    change 1 * (N : ℝ)⁻¹ ≤ (1 + (64 * R + D)) * (N : ℝ)⁻¹
    exact mul_le_mul_of_nonneg_right hCgeOne (by positivity)
  have hRinv : (32 * R) / (N : ℝ) ≤ 32 * R := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ 32 * R * 1 := mul_le_mul_of_nonneg_left hNinv (by positivity)
      _ = 32 * R := by ring
  have hCerr : 32 * R / (N : ℝ) + D + 32 * R ≤
      1 + (64 * R + D) := by
    calc
      32 * R / (N : ℝ) + D + 32 * R ≤ 32 * R + D + 32 * R := by
        gcongr
      _ = 64 * R + D := by ring
      _ ≤ 1 + (64 * R + D) := le_add_of_nonneg_left (by norm_num)
  have hFGnonneg : 0 ≤ Fnorm * Gnorm := mul_nonneg hFnonneg hGnonneg
  have hCfEGnonneg : 0 ≤ Cf * E * Gnorm :=
    mul_nonneg (mul_nonneg hCf hE) hGnonneg
  have hrealBound :
      (1 / (N : ℝ)) * (Fnorm + 32 * R * Cf * E) * Gnorm +
        (D * Cf + 32 * R * Cf) * E * Gnorm ≤
      ((1 + (64 * R + D)) / (N : ℝ)) * Fnorm * Gnorm +
        (1 + (64 * R + D)) * Cf * Gnorm * E := by
    calc
      _ = (1 / (N : ℝ)) * (Fnorm * Gnorm) +
          (32 * R / (N : ℝ) + D + 32 * R) * (Cf * E * Gnorm) := by ring
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_right hCfirst hFGnonneg)
        (mul_le_mul_of_nonneg_right hCerr hCfEGnonneg)
      _ = _ := by ac_rfl
  have hrealBoundCdim :
      (1 / (N : ℝ)) * (Fnorm + 32 * R * Cf * E) * Gnorm +
        (D * Cf + 32 * R * Cf) * E * Gnorm ≤
      (Cdim / (N : ℝ)) * Fnorm * Gnorm + Cdim * Cf * Gnorm * E := by
    calc
      _ ≤ ((1 + (64 * R + D)) / (N : ℝ)) * Fnorm * Gnorm +
          (1 + (64 * R + D)) * Cf * Gnorm * E := hrealBound
      _ = _ := by rw [hCdim.symm]
  have hsumBound :
      homogeneousHMinusOneNorm lowProd + homogeneousHMinusOneNorm highProd ≤
        ENNReal.ofReal (
          (Cdim / (N : ℝ)) * Fnorm * Gnorm +
          Cdim * Cf * Gnorm * Real.exp (-r * (N : ℝ) / 4096)) := by
    calc
      _ ≤ ENNReal.ofReal lowReal + ENNReal.ofReal highReal :=
              add_le_add hLowDualReal hHighDual
      _ = ENNReal.ofReal (lowReal + highReal) := by
        rw [← ENNReal.ofReal_add hLowRealNonneg hHighRealNonneg]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by
        simpa only [lowReal, highReal, R, D, E] using hrealBoundCdim)
  have hCdimOutput : Cdim =
      1 + 64 * ergodicFourierWeight d ^ (1 / 2 : ℝ) +
        1024 * ((d : ℝ) + 1) := by
    change 1 + (64 * K ^ (1 / 2 : ℝ) + 1024 * ((d : ℝ) + 1)) = _
    have hKdef : K = ergodicFourierWeight d := rfl
    rw [hKdef]
    ring
  calc
    _ ≤ homogeneousHMinusOneNorm lowProd +
        homogeneousHMinusOneNorm highProd := htriangle'
    _ ≤ ENNReal.ofReal
        (Cdim / (N : ℝ) * Fnorm * Gnorm +
          Cdim * Cf * Gnorm * Real.exp (-r * (N : ℝ) / 4096)) := hsumBound
    _ = _ := by
      congr 1
      rw [hCdimOutput]

theorem homogeneousHMinusOneNorm_le_of_fastPeriodicProduct_without_product_mean
    {d N : ℕ} (hd : 0 < d) (hN : 0 < N)
    {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f) (hper : IsZPeriodic f)
    (Cf r : ℝ) (hCf : 0 ≤ Cf) (hr : 0 < r)
    (hderiv : HasCoordinateAnalyticL2Bounds (fun x => (f x : ℂ)) Cf r)
    {g : Vec d → ℝ}
    (hg : LocallyIntegrable g (volume : Measure (Vec d)))
    (hg2 : LocallyIntegrable (fun x => |g x| ^ 2) (volume : Measure (Vec d)))
    (hfast : IsFastPeriodic N g) (hNr : 2 ≤ r * (N : ℝ))
    (hgMean : cellAverage g = 0) :
    homogeneousHMinusOneNorm (fun x => f x * g x) ≤
      ENNReal.ofReal (
        ((1 + 64 * (ergodicFourierWeight d) ^ (1 / 2 : ℝ) +
          1024 * ((d : ℝ) + 1)) / (N : ℝ)) *
          (cellAverage (fun x => |f x| ^ 2)) ^ (1 / 2 : ℝ) *
          (cellAverage (fun x => |g x| ^ 2)) ^ (1 / 2 : ℝ) +
        (1 + 64 * (ergodicFourierWeight d) ^ (1 / 2 : ℝ) +
          1024 * ((d : ℝ) + 1)) * Cf *
          (cellAverage (fun x => |g x| ^ 2)) ^ (1 / 2 : ℝ) *
          Real.exp (-r * (N : ℝ) / 4096)) := by
  classical
  let M : ℕ := N / 2
  let gap : ℝ := (N : ℝ) - (M : ℝ)
  let K : ℝ := ergodicFourierWeight d
  let Fnorm : ℝ := (cellAverage (fun x => |f x| ^ 2)) ^ (1 / 2 : ℝ)
  let Gnorm : ℝ := (cellAverage (fun x => |g x| ^ 2)) ^ (1 / 2 : ℝ)
  let Cdim : ℝ := 1 +
    (64 * K ^ (1 / 2 : ℝ) + 1024 * ((d : ℝ) + 1))
  have hK : 0 ≤ K := by
    dsimp [K]
    rw [ergodicFourierWeight_eq_tsum]
    exact tsum_nonneg fun _ => Real.exp_nonneg _
  have hFnonneg : 0 ≤ Fnorm := by
    dsimp [Fnorm]
    rw [cellAverage_eq_torusUnitCellIntegral]
    exact Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _
  have hGnonneg : 0 ≤ Gnorm := by
    dsimp [Gnorm]
    rw [cellAverage_eq_torusUnitCellIntegral]
    exact Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _
  have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hMbound : 2 * (M : ℝ) ≤ (N : ℝ) := by
    dsimp [M]
    have hnat := Nat.div_mul_le_self N 2
    exact_mod_cast (by nlinarith [hnat] : 2 * (N / 2) ≤ N)
  have hgapHalf : (N : ℝ) / 2 ≤ gap := by
    dsimp [gap]
    linarith [hMbound]
  have hgapPos : 0 < gap := by
    dsimp [gap]
    linarith [hNreal]
  have hgSqLI : LocallyIntegrable (fun x => g x ^ 2)
      (volume : Measure (Vec d)) :=
    hg2.congr (Filter.Eventually.of_forall fun _ => by simp [sq_abs])
  let lowProd : Vec d → ℝ := fun x => lowProjection f M x * g x
  let highProd : Vec d → ℝ := fun x => highRemainder f M x * g x
  have hLowMeas : AEStronglyMeasurable lowProd (volume : Measure (Vec d)) := by
    exact ((lowProjection_contDiff M).continuous.aestronglyMeasurable).mul
      hg.aestronglyMeasurable
  have hHighMeas : AEStronglyMeasurable highProd (volume : Measure (Vec d)) := by
    exact ((highRemainder_contDiff hf M).continuous.aestronglyMeasurable).mul
      hg.aestronglyMeasurable
  have hLowSqLI : LocallyIntegrable (fun x => |lowProd x| ^ 2)
      (volume : Measure (Vec d)) := by
    have hmul := hgSqLI.mul_continuous
      ((lowProjection_contDiff (f := f) M).continuous.pow 2)
    exact hmul.congr (Filter.Eventually.of_forall fun x => by
      simp only [Pi.pow_apply]
      rw [show lowProd x = lowProjection f M x * g x by rfl,
        abs_mul, mul_pow, sq_abs, sq_abs]
      ring)
  have hHighSqLI : LocallyIntegrable (fun x => |highProd x| ^ 2)
      (volume : Measure (Vec d)) := by
    have hmul := hgSqLI.mul_continuous ((highRemainder_contDiff hf M).continuous.pow 2)
    exact hmul.congr (Filter.Eventually.of_forall fun x => by
      change g x ^ 2 * highRemainder f M x ^ 2 =
        |highRemainder f M x * g x| ^ 2
      rw [sq_abs]
      ring)
  have hLowLI : LocallyIntegrable lowProd (volume : Measure (Vec d)) :=
    by simpa [lowProd, mul_comm] using
      (hg.mul_continuous (lowProjection_contDiff (f := f) M).continuous)
  have hHighLI : LocallyIntegrable highProd (volume : Measure (Vec d)) :=
    by simpa [highProd, mul_comm] using
      (hg.mul_continuous (highRemainder_contDiff hf M).continuous)
  have hLowCellMem := cellMemLp_two_of_localSquare hLowMeas hLowSqLI
  have hHighCellMem := cellMemLp_two_of_localSquare hHighMeas hHighSqLI
  have hSplitL2 := centered_fastProduct_split_l2_bound hd hN hf hper Cf r hCf hr
    hderiv hg2 hfast hNr
  have hLowL2Bound :
      (∫ x in Torus.unitCell d, lowProd x ^ 2) ^ (1 / 2 : ℝ) ≤
        (Fnorm + 32 * K ^ (1 / 2 : ℝ) * Cf *
          Real.exp (-r * (N : ℝ) / 4096)) * Gnorm := by
    simpa only [lowProd, Fnorm, Gnorm, K] using hSplitL2.1
  have hHighL2Bound :
      (∫ x in Torus.unitCell d, highProd x ^ 2) ^ (1 / 2 : ℝ) ≤
        (1024 * ((d : ℝ) + 1) * Cf +
          32 * K ^ (1 / 2 : ℝ) * Cf) *
          Real.exp (-r * (N : ℝ) / 4096) * Gnorm := by
    simpa only [highProd, Fnorm, Gnorm, K] using hSplitL2.2
  have hLowCancellation :=
    centered_lowProjection_fastProduct_mean_gap hN hgapPos (f := f) hg hg2 hfast hgMean
      (M := M)
  have hgapLow : ∀ q : Fin d → ℤ, ‖q‖ < gap →
      UnitAddTorus.mFourierCoeff
        (torusFunction (fun x => (lowProd x : ℂ))) q = 0 := by
    intro q hq
    simpa [lowProd] using hLowCancellation.2 q (by simpa [gap] using hq)
  have hLowComplexCell : MemLp (fun x => (lowProd x : ℂ))
      (ENNReal.ofReal (2 : ℝ))
      ((volume : Measure (Vec d)).restrict (Torus.unitCell d)) := by
    simpa using hLowCellMem.2
  have hLowDual := homogeneousHMinusOneNorm_le_of_torusFourierGap
    hd hLowComplexCell gap hgapPos hgapLow
  have hden : (N : ℝ) ≤ 2 * Real.pi * gap := by
    have hpi : 2 ≤ Real.pi := Real.two_le_pi
    nlinarith [hgapHalf, hNreal]
  have hcoef : (2 * Real.pi * gap)⁻¹ ≤ (N : ℝ)⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 hden
  exact @fast_product_negative_sobolev_bound d N hd hN f Cf r hCf g hK hFnonneg hGnonneg hNreal
      hgapPos hLowLI hHighLI hHighCellMem hLowL2Bound hHighL2Bound hLowDual hcoef
end
end AVenhance.Infra.Ergodic
