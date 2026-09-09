/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CoefficientJetPressureBounds
public import LeanPool.NavierStokesAndEuler.Euler.CoefficientPathSmooth
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCoefficient
import LeanPool.NavierStokesAndEuler.Euler.CoefficientPathBounds
import LeanPool.NavierStokesAndEuler.Euler.H6PressureConstants

/-! Actual coefficient-orbit bounds control the fixed H5/H6 pressure
constants uniformly over all higher jet truncations. -/

@[expose] public section


noncomputable section

namespace EulerCoefficientPath

open Set Finset ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMeanCoefficients EulerSpatialSobolevInverse EulerJetProductBounds
  EulerParameterWordGevrey EulerGevrey EulerCoefficientJetPressureBounds EulerCylinderSobolev
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]

omit [Fact (0 < P)] in
theorem boundLevel_le_block_zero {s : ℕ} {A : SmoothCoefficient P}
    (J : CoefficientJet P standardDirection s A) (q r : ℕ) (hr : r ≤ q) :
    boundLevel P J r ≤ EulerH6Pressure.coefficientBlock P J q 0 := by
  let S := ∑ k ∈ range (q+1),boundLevel P J k
  have hsum : boundLevel P J r ≤ S := by
    exact single_le_sum (f := fun k => boundLevel P J k)
      (fun k _ => boundLevel_nonneg (n := k) J)
      (show r ∈ range (q+1) from mem_range.mpr (by omega))
  have hnon : 0 ≤ S := sum_nonneg (fun k _ => boundLevel_nonneg J)
  have hpow : (1 : ℝ) ≤ (2 : ℝ)^q := one_le_pow₀ (by norm_num)
  have hh : S ≤ (2 : ℝ)^q*S := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow hnon
  simpa only [EulerH6Pressure.coefficientBlock,Nat.zero_add,S] using hsum.trans hh

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  (A : C(K, Space →ᵇ Space →L[ℝ] Space))
  (hA : ContDiff ℝ ∞ (translateCoefficientPath A))
  (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
  (hb : ∀ n x, ‖iteratedFDeriv ℝ n (translateCoefficientPath A) x‖ ≤ C * majorant Rc 0 n)

include hRc hC hb

theorem coefficientJet_base_bound (s q r : ℕ) (hr : r ≤ q) (t : K) :
    boundLevel P (coefficientJet P A hA s t) r ≤ sobolevCoefficientAmplitude (Fin 4) q Rc C := by
  have hh := (boundLevel_le_block_zero P (coefficientJet P A hA s t) q r hr).trans
    (coefficientJet_block_bound P A hA s q Rc C hRc hC hb 0 t)
  simpa only [majorant,Nat.zero_add,pow_zero,Nat.factorial_zero,Nat.cast_one,one_pow,mul_one] using
      hh

theorem coefficientJet_restrictedPressure_bound (s q b : ℕ) (hq : q ≤ s) (hqb : q ≤ b)
    (c : ℝ) (hc : 0 < c) (t : K) :
    (EulerH6Pressure.CoefficientJet.restrict (coefficientJet P A hA s t) q hq).pressureConstant c ≤
      pressureCost c (sobolevCoefficientAmplitude (Fin 4) b Rc C) q := by
  apply TreeBound.pressureConstant_le _ c hc (sobolevCoefficientAmplitude_nonneg b Rc C hRc hC)
  apply treeBound_of_levels
  intro r hr
  rw [EulerH6Pressure.coefficient_restrict_level P (coefficientJet P A hA s t) hq hr]
  exact coefficientJet_base_bound P A hA Rc C hRc hC hb s b r (hr.trans hqb) t

end EulerCoefficientPath
