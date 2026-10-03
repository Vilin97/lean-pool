/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinSmoothEquation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinSmoothTransportCoefficient

/-! Continuous finite-mode time derivatives for the smooth Galerkin sequence. -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin

namespace AVenhance.Infra.Classical

/-- The ODE right-hand side projected to one Fourier coefficient is continuous through the closed
unit slab. -/
noncomputable def classicalGalerkinFiniteFourierDerivativePath
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ Set.univ))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (N : ℕ) (k : Fin 2 → ℤ) : C(Icc (0 : ℝ) 1, ℂ) := by
  let D := classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N
  let c := classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N
  have hA : ContinuousOn D.weak.coefficient (Icc (0 : ℝ) 1) :=
    classicalForcedGalerkinCoefficient_continuousOn φ hφ κ hκ F hF θ₀ hθ₀ N
  have hA' : Continuous (fun t : Icc (0 : ℝ) 1 => D.weak.coefficient t) :=
    hA.domRestrict
  have hAcurve : Continuous (fun t : Icc (0 : ℝ) 1 =>
      D.weak.coefficient t (c t)) := by
    have hev : Continuous
        (fun p : (Coefficients (RealFourierDimension N) →L[ℝ]
            Coefficients (RealFourierDimension N)) ×
          Coefficients (RealFourierDimension N) => p.1 p.2) := by fun_prop
    exact hev.comp (hA'.prodMk c.continuous)
  have hf : Continuous (fun t : Icc (0 : ℝ) 1 => classicalForcingCoefficients N F t) :=
    (classicalForcingCoefficients_continuous N F hF).comp continuous_subtype_val
  have hsum : Continuous (fun t : Icc (0 : ℝ) 1 =>
      D.weak.coefficient t (c t) + classicalForcingCoefficients N F t) :=
    hAcurve.add hf
  exact ⟨fun t => classicalComplexFourierCoeffCLM k
      (realFourierScalarMap N
        (D.weak.coefficient t (c t) + classicalForcingCoefficients N F t)),
    (classicalComplexFourierCoeffCLM k).continuous.comp
      ((realFourierScalarMap N).continuous.comp hsum)⟩

theorem classicalGalerkinFiniteFourierCoeffPath_hasDerivAt
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Ici (0 : ℝ) ×ˢ Set.univ))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (N : ℕ) (k : Fin 2 → ℤ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun s => classicalComplexFourierCoeffCLM k (realFourierScalarMap N
        (AVenhance.Infra.ODE.extendCurve (by norm_num)
          (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N) s)))
      (classicalGalerkinFiniteFourierDerivativePath φ hφ κ hκ F hF θ₀ hθ₀ N k
        ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩) t := by
  let D := classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N
  let c := classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N
  let ext := AVenhance.Infra.ODE.extendCurve (by norm_num) c
  have htIcc : t ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hext : ext t = c ⟨t, htIcc.1, htIcc.2⟩ :=
    AVenhance.Infra.ODE.extendCurve_eq_of_mem (by norm_num) c htIcc
  have hbase := classicalGalerkinFourierCoefficient_hasDerivAt
    φ hφ κ hκ F hF θ₀ hθ₀ N k ht
  have hclm := hbase.deriv
  have htarget : classicalGalerkinFiniteFourierDerivativePath φ hφ κ hκ F hF
      θ₀ hθ₀ N k ⟨t, htIcc.1, htIcc.2⟩ =
      classicalComplexFourierCoeffCLM k (realFourierScalarMap N
        (D.weak.coefficient t (ext t) + classicalForcingCoefficients N F t)) := by
    simp [classicalGalerkinFiniteFourierDerivativePath, D, c, hext]
  apply hbase.congr_deriv
  simpa [D, c] using htarget.symm

end AVenhance.Infra.Classical

end
