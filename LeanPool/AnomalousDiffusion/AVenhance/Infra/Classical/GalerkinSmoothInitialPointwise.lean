/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinSmoothInitial
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.AveragesL1

/-! The continuous Fourier representative has the prescribed pointwise initial trace. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin

namespace AVenhance.Infra.Classical

local instance classicalInitialPointwiseOneLeTwo : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance classicalInitialPointwiseMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalInitialPointwiseAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalInitialPointwiseProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The real smooth representative agrees pointwise with the datum at time zero. -/
theorem classicalGalerkinRealSmoothLift_initial
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) :
    ∀ x, classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per ⟨0, by norm_num, by norm_num⟩ x = θ₀ x := by
  let t₀ : Icc (0 : ℝ) 1 := ⟨0, by norm_num, by norm_num⟩
  let U := classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per [] t₀
  let L : C(Torus, ℂ) := classicalGalerkinFourierContinuousLimit
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t₀
  let R : C(Torus, ℝ) :=
    ⟨fun y => (L y).re, Complex.reCLM.continuous.comp L.continuous⟩
  let hmem := memLp_periodicToTorus_real hθ₀.continuous hθ₀per
  let U₀ : ScalarTorusL2 := hmem.toLp (AVenhance.Infra.Torus.periodicToTorus θ₀)
  let Z₀ : C(Torus, ℂ) :=
    ⟨AVenhance.Infra.Torus.periodicToTorus (fun x => (θ₀ x : ℂ)),
      AVenhance.Infra.Ergodic.periodicToTorus_continuous_of_periodic
        (Complex.ofRealCLM.continuous.comp hθ₀.continuous)
        (AVenhance.Infra.Torus.isZdPeriodic_iff_frozen _ |>.2 (by
          intro z x
          exact congrArg (fun r : ℝ => (r : ℂ)) (hθ₀per z x)))⟩
  let R₀ : C(Torus, ℝ) :=
    ⟨fun y => (Z₀ y).re, Complex.reCLM.continuous.comp Z₀.continuous⟩
  have hinit := classicalGalerkinWordScalarPathLimit_initial
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per
  have hL2 := classicalGalerkinFourierContinuousLimit_toLp
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t₀
  have hL2' : ContinuousMap.toLp 2 (volume : Measure Torus) ℂ L =
      classicalRealToComplexTorusCLM U₀ := by
    simpa [L, U, U₀, t₀, hinit] using hL2
  have hRlp : (Complex.reCLM.compLpL (2 : ENNReal) (volume : Measure Torus))
      (ContinuousMap.toLp 2 (volume : Measure Torus) ℂ L) =
      ContinuousMap.toLp 2 (volume : Measure Torus) ℝ R := by
    apply Lp.ext
    filter_upwards [Complex.reCLM.coeFn_compLpL
        (ContinuousMap.toLp 2 (volume : Measure Torus) ℂ L),
      ContinuousMap.coeFn_toLp (p := (2 : ENNReal))
        (μ := (volume : Measure Torus)) (𝕜 := ℝ) R,
      ContinuousMap.coeFn_toLp (p := (2 : ENNReal))
        (μ := (volume : Measure Torus)) (𝕜 := ℂ) L] with y hre hR hL
    calc
      _ = Complex.reCLM (ContinuousMap.toLp 2 (volume : Measure Torus) ℂ L y) := hre
      _ = Complex.reCLM (L y) := by rw [hL]
      _ = R y := rfl
      _ = ContinuousMap.toLp 2 (volume : Measure Torus) ℝ R y := hR.symm
  have hrealComplex : (Complex.reCLM.compLpL (2 : ENNReal)
      (volume : Measure Torus)) (classicalRealToComplexTorusCLM U₀) = U₀ := by
    apply Lp.ext
    filter_upwards [Complex.reCLM.coeFn_compLpL
      (classicalRealToComplexTorusCLM U₀),
      Complex.ofRealCLM.coeFn_compLpL U₀] with y hre hreal
    calc
      _ = Complex.reCLM (classicalRealToComplexTorusCLM U₀ y) := hre
      _ = Complex.reCLM (Complex.ofReal (U₀ y)) := by
        change Complex.reCLM
          ((Complex.ofRealCLM.compLpL (2 : ENNReal)
            (volume : Measure Torus)) U₀ y) = _
        rw [hreal]
        simp only [Complex.ofRealCLM_apply, Complex.reCLM_apply, Complex.ofReal_re]
      _ = U₀ y := by
        simp only [Complex.reCLM_apply, Complex.ofReal_re]
  have hR0lp : ContinuousMap.toLp 2 (volume : Measure Torus) ℝ R₀ = U₀ := by
    apply Lp.ext
    filter_upwards [ContinuousMap.coeFn_toLp (p := (2 : ENNReal))
        (μ := (volume : Measure Torus)) (𝕜 := ℝ) R₀,
      hmem.coeFn_toLp] with y hR0 hy
    rw [hR0, hy]
    change (Z₀ y).re = θ₀ (AVenhance.Infra.Torus.unitTorusRepresentative 2 y)
    rfl
  have hRLp : ContinuousMap.toLp 2 (volume : Measure Torus) ℝ R =
      ContinuousMap.toLp 2 (volume : Measure Torus) ℝ R₀ := by
    calc
      _ = (Complex.reCLM.compLpL (2 : ENNReal) (volume : Measure Torus))
          (ContinuousMap.toLp 2 (volume : Measure Torus) ℂ L) := hRlp.symm
      _ = (Complex.reCLM.compLpL (2 : ENNReal) (volume : Measure Torus))
          (classicalRealToComplexTorusCLM U₀) := by rw [hL2']
      _ = U₀ := hrealComplex
      _ = ContinuousMap.toLp 2 (volume : Measure Torus) ℝ R₀ := hR0lp.symm
  have hRfun : R = R₀ := by
    exact (ContinuousMap.toLp_injective (p := (2 : ENNReal))
      (μ := (volume : Measure Torus)) (𝕜 := ℝ)) hRLp
  intro x
  have hx := congrArg (fun f : C(Torus, ℝ) => f
    (AVenhance.Infra.Torus.toUnitTorus 2 x)) hRfun
  change (L (AVenhance.Infra.Torus.toUnitTorus 2 x)).re =
    (Z₀ (AVenhance.Infra.Torus.toUnitTorus 2 x)).re at hx
  have hcandidate := classicalGalerkinSmoothLift_eq_continuousLimit
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t₀ x
  have hdatum := AVenhance.Infra.Torus.fromUnitTorus_periodicToTorus
    (AVenhance.Infra.Torus.isZdPeriodic_iff_frozen θ₀ |>.2 hθ₀per)
  have hdatumx := congrFun hdatum x
  change AVenhance.Infra.Torus.periodicToTorus θ₀
      (AVenhance.Infra.Torus.toUnitTorus 2 x) = θ₀ x at hdatumx
  change (classicalGalerkinSmoothLift φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per t₀ x).re = θ₀ x
  rw [hcandidate]
  rw [hx]
  dsimp [Z₀]
  change (AVenhance.Infra.Torus.periodicToTorus
      (fun y => (θ₀ y : ℂ)) (AVenhance.Infra.Torus.toUnitTorus 2 x)).re = θ₀ x
  have hdatumxC := congrArg (fun r : ℝ => (r : ℂ)) hdatumx
  change AVenhance.Infra.Torus.periodicToTorus
      (fun y : Vec 2 => (θ₀ y : ℂ))
        (AVenhance.Infra.Torus.toUnitTorus 2 x) = (θ₀ x : ℂ) at hdatumxC
  rw [hdatumxC]
  simp

end AVenhance.Infra.Classical

end
