/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.CenteredSpectral
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.HMinusOneErgodicFlow

/-! # Centered Spectral Flow

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

namespace AVenhance.Infra.Ergodic
open scoped ContDiff
open MeasureTheory Homogenization AVenhance.Infra.Torus
noncomputable section

theorem homogeneousHMinusOneNorm_le_of_fastPeriodicProduct_flow_without_product_mean
    {d N : ℕ} (hd : 0 < d) (hN : 0 < N)
    (X : PeriodicVolumePreservingDiffeomorphism d)
    {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f) (hper : IsZPeriodic f)
    (Cf r : ℝ) (hCf : 0 ≤ Cf) (hr : 0 < r)
    (hderivComp : HasCoordinateAnalyticL2Bounds
      (fun x => (f (X.toFun x) : ℂ)) Cf r)
    {g : Vec d → ℝ}
    (hg : LocallyIntegrable g (volume : Measure (Vec d)))
    (hg2 : LocallyIntegrable (fun x => |g x| ^ 2)
      (volume : Measure (Vec d)))
    (hfast : IsFastPeriodic N g) (hNr : 2 ≤ r * (N : ℝ))
    (hnear : FlowDerivativeNearIdentity X)
    (hgMean : cellAverage g = 0) :
    homogeneousHMinusOneNorm (fun x => f x * g (X.invFun x)) ≤
      ENNReal.ofReal (
        (3 * (d : ℝ) ^ 2) *
          (((1 + 64 * (ergodicFourierWeight d) ^ (1 / 2 : ℝ) +
            1024 * ((d : ℝ) + 1)) / (N : ℝ)) *
              (cellAverage (fun x => |f x| ^ 2)) ^ (1 / 2 : ℝ) *
              (cellAverage (fun x => |g x| ^ 2)) ^ (1 / 2 : ℝ) +
            (1 + 64 * (ergodicFourierWeight d) ^ (1 / 2 : ℝ) +
              1024 * ((d : ℝ) + 1)) * Cf *
              (cellAverage (fun x => |g x| ^ 2)) ^ (1 / 2 : ℝ) *
              Real.exp (-r * (N : ℝ) / 4096))) := by
  let L : ℝ := 3 * (d : ℝ) ^ 2
  let C : ℝ := 1 + 64 * (ergodicFourierWeight d) ^ (1 / 2 : ℝ) +
    1024 * ((d : ℝ) + 1)
  let Fnorm : ℝ := (cellAverage (fun x => |f x| ^ 2)) ^ (1 / 2 : ℝ)
  let Gnorm : ℝ := (cellAverage (fun x => |g x| ^ 2)) ^ (1 / 2 : ℝ)
  let E : ℝ := Real.exp (-r * (N : ℝ) / 4096)
  have hL : 0 < L := by dsimp [L]; positivity
  let fcomp : Vec d → ℝ := fun x => f (X.toFun x)
  have hcompSmooth : ContDiff ℝ ∞ fcomp := hf.comp X.contDiff_toFun
  have hcompPeriodic : IsZPeriodic fcomp := by
    intro x k
    change f (X.toFun (x + latticeVector k)) = f (X.toFun x)
    rw [X.lattice_equivariant]
    exact hper (X.toFun x) k
  have hfSqPeriodic : IsZPeriodic (fun x => |f x| ^ 2) := by
    intro x k
    simpa [latticeVector] using
      congrArg (fun y : ℝ => y ^ 2) (hper x k)
  have hcompFnorm :
      (cellAverage (fun x => |fcomp x| ^ 2)) ^ (1 / 2 : ℝ) = Fnorm := by
    have havg := cellAverage_comp_flow_eq (fun x => |f x| ^ 2)
      hfSqPeriodic X
    have havg' : cellAverage (fun x => |fcomp x| ^ 2) =
        cellAverage (fun x => |f x| ^ 2) := by
      simpa [fcomp] using havg
    simpa [Fnorm] using congrArg (fun z : ℝ => z ^ (1 / 2 : ℝ)) havg'
  have hgPeriodic := hfast.isZPeriodic hN
  have hbase := homogeneousHMinusOneNorm_le_of_fastPeriodicProduct_without_product_mean
    hd hN hcompSmooth hcompPeriodic Cf r hCf hr hderivComp hg hg2 hfast hNr
    hgMean
  have hmap : ∀ (φ : Vec d → ℝ), ContDiff ℝ ∞ φ →
      IsZPeriodic φ → cellAverage φ = 0 →
      gradientL2SquaredAverage φ ≤ 1 →
      gradientL2SquaredAverage (fun x => L⁻¹ * φ (X.toFun x)) ≤ 1 := by
    intro φ hφ hφper _ hφgrad
    exact gradientTestMap_le_of_nearIdentity hd X hnear φ hφ hφper hφgrad
  have hflow := homogeneousHMinusOneNorm_flow_le_of_testComposition
    hper hgPeriodic X L hL hmap
  have hbase' : homogeneousHMinusOneNorm (fun x => fcomp x * g x) ≤
      ENNReal.ofReal (C / (N : ℝ) * Fnorm * Gnorm +
        C * Cf * Gnorm * E) := by
    simpa only [C, Fnorm, Gnorm, E, hcompFnorm] using hbase
  calc
    _ ≤ ENNReal.ofReal L *
        homogeneousHMinusOneNorm (fun x => fcomp x * g x) := by
      simpa only [fcomp, L] using hflow
    _ ≤ ENNReal.ofReal L *
        ENNReal.ofReal (C / (N : ℝ) * Fnorm * Gnorm +
          C * Cf * Gnorm * E) := by
      gcongr
    _ = ENNReal.ofReal
        (L * (C / (N : ℝ) * Fnorm * Gnorm + C * Cf * Gnorm * E)) := by
      rw [ENNReal.ofReal_mul hL.le]
    _ = _ := by
      simp only [L, C, Fnorm, Gnorm, E]

end

end AVenhance.Infra.Ergodic
