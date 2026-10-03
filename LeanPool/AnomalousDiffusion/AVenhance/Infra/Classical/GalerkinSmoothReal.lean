/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinSmoothTime

/-! The smooth Fourier representative is real-valued, as inherited from the real Galerkin paths. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin

namespace AVenhance.Infra.Classical

local instance classicalSmoothRealOneLeTwo : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance classicalSmoothRealMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalSmoothRealMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalSmoothRealProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The continuous Fourier representative has zero imaginary part: its `L²` class is the
complexification of the real-valued Galerkin limit. -/
theorem classicalGalerkinFourierContinuousLimit_im_eq_zero
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (t : Icc (0 : ℝ) 1) (x : Torus) :
    (classicalGalerkinFourierContinuousLimit φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per t x).im = 0 := by
  let U := classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per [] t
  let L := classicalGalerkinFourierContinuousLimit φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per t
  let Li : C(Torus, ℝ) :=
    ⟨fun y => Complex.im (L y), Complex.imCLM.continuous.comp L.continuous⟩
  have hLp := classicalGalerkinFourierContinuousLimit_toLp
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  have hmap : (Complex.imCLM.compLpL (2 : ENNReal) (volume : Measure Torus))
      ((ContinuousMap.toLp 2 (volume : Measure Torus) ℂ) L) = 0 := by
    rw [show (ContinuousMap.toLp 2 (volume : Measure Torus) ℂ) L =
      classicalRealToComplexTorusCLM U by simpa [L] using hLp]
    change (Complex.imCLM.compLpL (2 : ENNReal) (volume : Measure Torus))
      ((Complex.ofRealCLM.compLpL (2 : ENNReal) (volume : Measure Torus)) U) = 0
    apply Lp.ext
    filter_upwards [Complex.imCLM.coeFn_compLpL
        ((Complex.ofRealCLM.compLpL (2 : ENNReal) (volume : Measure Torus)) U),
      Complex.ofRealCLM.coeFn_compLpL U,
      Lp.coeFn_zero ℝ (2 : ENNReal) (volume : Measure Torus)] with y him hreal hzero
    rw [him, hreal]
    simp
  have hcomp : (ContinuousMap.toLp 2 (volume : Measure Torus) ℝ) Li =
      (Complex.imCLM.compLpL (2 : ENNReal) (volume : Measure Torus))
        ((ContinuousMap.toLp 2 (volume : Measure Torus) ℂ) L) := by
    apply Lp.ext
    filter_upwards [Complex.imCLM.coeFn_compLpL
        ((ContinuousMap.toLp 2 (volume : Measure Torus) ℂ) L),
      ContinuousMap.coeFn_toLp (p := (2 : ENNReal))
        (μ := (volume : Measure Torus)) (𝕜 := ℂ) L,
      ContinuousMap.coeFn_toLp (p := (2 : ENNReal))
        (μ := (volume : Measure Torus)) (𝕜 := ℝ) Li] with y him hL himL
    rw [him, hL, himL]
    rfl
  have hzero : (ContinuousMap.toLp 2 (volume : Measure Torus) ℝ) Li = 0 := by
    rw [hcomp]
    exact hmap
  have hzero' : (ContinuousMap.toLp 2 (volume : Measure Torus) ℝ) Li =
      (ContinuousMap.toLp 2 (volume : Measure Torus) ℝ) 0 := by
    calc
      _ = 0 := hzero
      _ = (ContinuousMap.toLp 2 (volume : Measure Torus) ℝ) 0 :=
        (map_zero (ContinuousMap.toLp 2 (volume : Measure Torus) ℝ)).symm
  have hfun : Li = 0 := by
    exact (ContinuousMap.toLp_injective (p := (2 : ENNReal))
      (μ := (volume : Measure Torus)) (𝕜 := ℝ)) hzero'
  have hx := congrArg (fun f : C(Torus, ℝ) => f x) hfun
  change Li x = 0 at hx
  change Complex.im (L x) = 0
  exact hx

/-- The pointwise smooth Fourier lift is real-valued on every spatial slice. -/
theorem classicalGalerkinSmoothLift_im_eq_zero
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (t : Icc (0 : ℝ) 1) (x : Vec 2) :
    (classicalGalerkinSmoothLift φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per t x).im = 0 := by
  rw [classicalGalerkinSmoothLift_eq_continuousLimit]
  exact classicalGalerkinFourierContinuousLimit_im_eq_zero
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
    (AVenhance.Infra.Torus.toUnitTorus 2 x)

/-- A real-valued version of the smooth Galerkin lift. -/
noncomputable def classicalGalerkinRealSmoothLift
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (t : Icc (0 : ℝ) 1) : Vec 2 → ℝ :=
  fun x => (classicalGalerkinSmoothLift φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per t x).re

theorem classicalGalerkinRealSmoothLift_contDiff
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (t : Icc (0 : ℝ) 1) :
    ContDiff ℝ (⊤ : ℕ∞) (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per t) := by
  unfold classicalGalerkinRealSmoothLift
  exact Complex.reCLM.contDiff.comp
    (classicalGalerkinSmoothLift_contDiff φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per t)

theorem classicalGalerkinRealSmoothLift_periodic
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (t : Icc (0 : ℝ) 1) :
    AVenhance.IsZ2Periodic (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per t) := by
  intro z x
  simp only [classicalGalerkinRealSmoothLift]
  rw [classicalGalerkinSmoothLift_periodic]

end AVenhance.Infra.Classical

end
