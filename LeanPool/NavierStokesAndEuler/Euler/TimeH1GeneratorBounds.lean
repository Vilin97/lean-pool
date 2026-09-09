/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeH1Reconstruction
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeIntegral
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpMultiplier
import LeanPool.NavierStokesAndEuler.Euler.CoerciveEndpointBounds
import LeanPool.NavierStokesAndEuler.Euler.ContinuousPathCalculus
import LeanPool.NavierStokesAndEuler.Euler.TimeLpCoefficientMap
import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointBounds

/-! Uniform-time polynomial bounds from an actual L² value and generator derivative. -/

@[expose] public section


noncomputable section


namespace EulerTimeH1GeneratorBounds

open Set ContinuousLinearMap EulerTimeLp EulerTimeH1Reconstruction
  EulerVolterraConvolution EulerTimeLpCoefficientMap EulerContinuousTimeIntegral
  EulerCoerciveEndpointBounds

variable {U E V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

variable (T : ℝ) (hT : 0 ≤ T)

/-- Reconstruct from the L² value and its prescribed generator derivative. -/
def generatorTrace (B : C(Icc (0 : ℝ) T, U →L[ℝ] U)) :
    TimeLp T U →L[ℝ] C(Icc (0 : ℝ) T, U) :=
  valuePart T hT + (derivativePart T hT).comp (timeMultiplier T hT B)

/-- Trace cost, given by `(1+T) * (T⁻¹ + 2*b)`. -/
def traceCost (T b : ℝ) : ℝ := (1+T) * (T⁻¹ + 2*b)

theorem sqrt_le_one_add (hT : 0 ≤ T) : Real.sqrt T ≤ 1+T := by
  nlinarith only [Real.sq_sqrt hT, Real.sqrt_nonneg T, sq_nonneg (Real.sqrt T-1)]

theorem generatorTrace_norm_le (hTpos : 0 < T)
    (B : C(Icc (0 : ℝ) T, U →L[ℝ] U)) (b : ℝ) (hB : ‖B‖ ≤ b) :
    ‖generatorTrace T hT B‖ ≤ traceCost T b := by
  have hb := (show 0 ≤ ‖B‖ by positivity).trans hB
  have hm := (timeMultiplier_norm T hT B).trans hB
  have hn := (norm_add_le (valuePart (E := U) T hT)
    ((derivativePart T hT).comp (timeMultiplier T hT B))).trans
      (add_le_add (valuePart_norm_le (E := U) T hTpos)
        ((opNorm_comp_le _ _).trans
          (mul_le_mul (derivativePart_norm_le (E := U) T hTpos) hm
            (norm_nonneg _) (by positivity))))
  change ‖generatorTrace T hT B‖ ≤ _ at hn
  apply hn.trans
  calc
    (T⁻¹*Real.sqrt T)+(2*Real.sqrt T)*b = Real.sqrt T * (T⁻¹+2*b) := by ring
    _ ≤ (1+T)*(T⁻¹+2*b) := mul_le_mul_of_nonneg_right (sqrt_le_one_add T hT) (by positivity)

theorem generatorTrace_sub_norm_le (hTpos : 0 < T)
    (B B' : C(Icc (0 : ℝ) T, U →L[ℝ] U)) :
    ‖generatorTrace T hT B - generatorTrace T hT B'‖ ≤ 2*(1+T)*‖B-B'‖ := by
  have he : generatorTrace T hT B - generatorTrace T hT B' =
      (derivativePart T hT).comp (timeMultiplier T hT B-timeMultiplier T hT B') := by
    unfold generatorTrace
    rw [comp_sub]
    abel
  rw [he]
  apply ((opNorm_comp_le _ _).trans (mul_le_mul
    (derivativePart_norm_le (E := U) T hTpos)
    (EulerTransverseEndpointBounds.multiplier_sub_norm_le T hT B B')
    (norm_nonneg _) (by positivity))).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (sqrt_le_one_add T hT) (by norm_num)) (by positivity)

theorem continuousMultiplier_sub_norm_le
    (Q P : C(Icc (0 : ℝ) T, U →L[ℝ] E)) : ‖multiplier Q - multiplier P‖ ≤ ‖Q-P‖ := by
  change ‖EulerContinuousPathCalculus.coefficientMap Q -
    EulerContinuousPathCalculus.coefficientMap P‖ ≤ _
  rw [← map_sub]
  exact multiplier_norm (Q-P)

theorem transportedTrace_norm_le (hTpos : 0 < T)
    (Q : C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (B : C(Icc (0 : ℝ) T, U →L[ℝ] U)) (S : V →L[ℝ] TimeLp T U)
    (q b s : ℝ) (hQ : ‖Q‖ ≤ q) (hB : ‖B‖ ≤ b) (hS : ‖S‖ ≤ s) :
    ‖(multiplier Q).comp ((generatorTrace T hT B).comp S)‖ ≤ q * traceCost T b * s := by
  have hq := (show 0 ≤ ‖Q‖ by positivity).trans hQ
  have htrace := generatorTrace_norm_le T hT hTpos B b hB
  have ht0 := (show 0 ≤ ‖generatorTrace T hT B‖ by positivity).trans htrace
  have hs := (opNorm_comp_le (generatorTrace T hT B) S).trans
    (mul_le_mul htrace hS (norm_nonneg _) ht0)
  exact ((opNorm_comp_le _ _).trans (mul_le_mul ((multiplier_norm Q).trans hQ) hs
    (norm_nonneg _) hq)).trans_eq (by ring)

theorem transportedTrace_sub_norm_le (hTpos : 0 < T)
    (Q P : C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (B B' : C(Icc (0 : ℝ) T, U →L[ℝ] U)) (S S' : V →L[ℝ] TimeLp T U)
    (q b s δq δb δs : ℝ) (hP : ‖P‖ ≤ q) (hB : ‖B‖ ≤ b) (hB' : ‖B'‖ ≤ b)
    (hS : ‖S‖ ≤ s) (hδq : ‖Q - P‖ ≤ δq) (hδb : ‖B - B'‖ ≤ δb) (hδs : ‖S - S'‖ ≤ δs) :
    ‖(multiplier Q).comp ((generatorTrace T hT B).comp S) -
      (multiplier P).comp ((generatorTrace T hT B').comp S')‖ ≤
      δq * traceCost T b * s + q * (2*(1+T)*δb*s + traceCost T b*δs) := by
  have hq := (show 0 ≤ ‖P‖ by positivity).trans hP
  have htrace := generatorTrace_norm_le T hT hTpos B b hB
  have htrace' := generatorTrace_norm_le T hT hTpos B' b hB'
  have ht0 := (show 0 ≤ ‖generatorTrace T hT B‖ by positivity).trans htrace
  have hδt := (generatorTrace_sub_norm_le T hT hTpos B B').trans
    (mul_le_mul_of_nonneg_left hδb (by positivity))
  have hδt0 := (show 0 ≤ ‖generatorTrace T hT B - generatorTrace T hT B'‖ by positivity).trans hδt
  have hs := (opNorm_comp_le (generatorTrace T hT B) S).trans
    (mul_le_mul htrace hS (norm_nonneg _) ht0)
  have hds := (norm_comp_sub_le (generatorTrace T hT B) (generatorTrace T hT B') S S').trans
    (add_le_add (mul_le_mul hδt hS (norm_nonneg _) hδt0)
      (mul_le_mul htrace' hδs (norm_nonneg _) ht0))
  have hδq0 := (show 0 ≤ ‖Q-P‖ by positivity).trans hδq
  apply ((norm_comp_sub_le _ _ _ _).trans
    (add_le_add (mul_le_mul ((continuousMultiplier_sub_norm_le T Q P).trans hδq) hs
      (norm_nonneg _) hδq0)
      (mul_le_mul ((multiplier_norm P).trans hP) hds (norm_nonneg _) hq))).trans_eq
  ring

end EulerTimeH1GeneratorBounds
