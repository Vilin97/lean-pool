/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketIntervalForcing
public import LeanPool.NavierStokesAndEuler.Euler.FixedEvolutionSobolev
import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletPhysicalBounds
import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletTimeBounds
import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPathJets
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear

/-!
# Source bounds for the actual transverse history and its terminal trace

The only quantitative inputs are the literal source coefficient jets and
the forcing's fixed-Sobolev mixed-word bounds. The output is the constructed
history path and its actual terminal coordinate, at the identical radius.
-/

@[expose] public section


noncomputable section

namespace EulerTransversePacketProvider.Data

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerTransverseBoundedFrame EulerGevrey
open scoped ContDiff BoundedContinuousFunction

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] (D : Data U)

theorem frame_spatial_bound (n : ℕ) (C : ℝ)
    (hb : ∀ t x, ‖iteratedFDeriv ℝ n (D.F.field t : Space → Space →L[ℝ] Space) x‖ ≤ C)
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (D.frame.field t : Space → U →L[ℝ] Space) x‖ ≤ C :=
  coefficient_derivative_bound D.m₀ D.R D.F n C hb t x

theorem frameDerivative_spatial_bound (n : ℕ) (C : ℝ)
    (hb : ∀ t x, ‖iteratedFDeriv ℝ n (D.F₁.field t : Space → Space →L[ℝ] Space) x‖ ≤ C)
    (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (D.frameDerivative.field t : Space → U →L[ℝ] Space) x‖ ≤ C :=
  coefficient_derivative_bound D.m₀ D.R D.F₁ n C hb t x

end EulerTransversePacketProvider.Data

namespace EulerLpCylinderTranslation

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerParameterWordGevrey
open scoped ContDiff

theorem trace_block_le (P : ℝ) [Fact (0 < P)]
    {K V ι : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (directions : ι → LiftTangent) (q : ℕ) (p : C(K, CylinderL2 P V))
    (hp : ContDiff ℝ ∞ (fun a => pathTranslate P a p)) (t : K) (n : ℕ) (a : LiftTangent) :
    block directions q (fun b => translate P b (p t)) n a ≤
      block directions q (fun b => pathTranslate P b p) n a := by
  let L : C(K,CylinderL2 P V) →L[ℝ] CylinderL2 P V := ContinuousMap.evalCLM ℝ t
  have hL : ‖L‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro f
    change ‖f t‖ ≤ 1*‖f‖
    simpa only [one_mul] using f.norm_coe_le_norm t
  exact (block_comp_clm_le directions q L _ hp n a).trans
    ((mul_le_mul_of_nonneg_right hL (block_nonneg directions q _ n a)).trans_eq (one_mul _))

end EulerLpCylinderTranslation

namespace EulerTransversePacketProvider.HistoryData

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerPacketProfileRecursion EulerGevrey EulerParameterWordGevrey
  EulerTransverseFixedSobolev EulerFixedEvolutionSobolev
  EulerTimeLpGramSobolev
open scoped ContDiff BoundedContinuousFunction

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (B : HistoryData D) {raw : VectorField} (G : Forcing P D raw)
  {ι : Type*} [Fintype ι] (directions : ι → LiftTangent) (hdir : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (Rc C₀ C₁ CH Cf R : ℝ) (hRc : 0 ≤ Rc) (hC₀ : 0 ≤ C₀)
  (hC₁ : 0 ≤ C₁) (hCH : 0 ≤ CH) (hCf : 0 ≤ Cf)
  (hbF : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F.field t : Space → Space →L[ℝ] Space) x‖ ≤ C₀ * majorant
      Rc
      0 n)
  (hbF₁ : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F₁.field t : Space → Space →L[ℝ] Space) x‖ ≤ C₁ * majorant
      Rc 0 n)
  (hbH : ∀ n t x, ‖iteratedFDeriv ℝ n (B.H.field t : Space → Space →L[ℝ] Space) x‖ ≤ CH * majorant
      Rc
      0 n)
  (hRweak : 2 * blockCost ι q D.T Rc C₀ C₁ CH D.frameLower Cf * (sobolevCoefficientRadius ι Rc + 1)
      ≤ R)
  (hRstrong : 2 * gramBlockCost ι q D.frameLower Rc C₀
    (accelerationBlockAmplitude ι q Rc C₀ C₁ Cf 1) *
 (sobolevCoefficientRadius ι Rc + 1) ≤ R)
  (hT1 : D.T ≤ 1) (d : ℕ)
  (hforce : ∀ n, block directions q (fun a => pathTranslate P a (forcingPath G)) n 0 ≤ Cf * majorant
      R d n)

include hdir hRc hC₀ hC₁ hCH hCf hbF hbF₁ hbH hRweak hRstrong hT1 hforce

/-- True continuous coordinate velocity of the actual zero-endpoint solve. -/
theorem source_coordinate_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a (B.coordinatePath G)) n 0 ≤
      traceCost D.T*majorant R (d+2) n := by
  exact B.coefficients.continuousVelocity_block_bound P directions hdir q
    D.frame.translation_contDiff D.frameDerivative.translation_contDiff B.H.translation_contDiff
    Rc C₀ C₁ CH Cf R hRc hC₀ hC₁ hCH hCf
    (fun j a => D.frame.norm_iteratedFDeriv_translation_le j _
      (mul_nonneg hC₀ (majorant_nonneg Rc hRc 0 j)) (D.frame_spatial_bound j _ (hbF j)) a)
    (fun j a => D.frameDerivative.norm_iteratedFDeriv_translation_le j _
      (mul_nonneg hC₁ (majorant_nonneg Rc hRc 0 j)) (D.frameDerivative_spatial_bound j _ (hbF₁ j))
          a)
    (fun j a => B.H.norm_iteratedFDeriv_translation_le j _
      (mul_nonneg hCH (majorant_nonneg Rc hRc 0 j)) (hbH j) a)
    hRweak hRstrong hT1 (forcingPath G) G.path_orbit d hforce n 0

/-- The actual terminal trace used by the forward solve has the same bound. -/
theorem source_terminal_bound (n : ℕ) :
    block directions q (fun a => translate P a ((B.terminalInitial G).value : CylinderL2 P U)) n 0 ≤
      traceCost D.T*majorant R (d+2) n :=
  (trace_block_le P directions q (B.coordinatePath G) (B.coordinatePath_orbit G)
    ⟨D.T,D.T_pos.le,le_rfl⟩ n 0).trans
      (B.source_coordinate_bound G directions hdir q Rc C₀ C₁ CH Cf R hRc hC₀ hC₁ hCH hCf
        hbF hbF₁ hbH hRweak hRstrong hT1 d hforce n)

/-- Literal history velocity, with the fixed reference-plane contraction already discharged. -/
theorem source_velocity_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a (B.velocityPath G)) n 0 ≤
      (3*sobolevCoefficientAmplitude ι q Rc C₀*traceCost D.T)*majorant R (d+2) n := by
  exact B.coefficients.physicalVelocity_block_bound P directions hdir q
    D.frame.translation_contDiff D.frameDerivative.translation_contDiff B.H.translation_contDiff
    Rc C₀ C₁ CH Cf R hRc hC₀ hC₁ hCH hCf
    (fun j a => D.frame.norm_iteratedFDeriv_translation_le j _
      (mul_nonneg hC₀ (majorant_nonneg Rc hRc 0 j)) (D.frame_spatial_bound j _ (hbF j)) a)
    (fun j a => D.frameDerivative.norm_iteratedFDeriv_translation_le j _
      (mul_nonneg hC₁ (majorant_nonneg Rc hRc 0 j)) (D.frameDerivative_spatial_bound j _ (hbF₁ j))
          a)
    (fun j a => B.H.norm_iteratedFDeriv_translation_le j _
      (mul_nonneg hCH (majorant_nonneg Rc hRc 0 j)) (hbH j) a)
    hRweak hRstrong hT1 (forcingPath G) G.path_orbit d hforce n

/-- The genuine history time derivative, at the identical spatial radius. -/
theorem source_derivative_bound
    (hRuniform : 2 * gramBlockCost ι q D.frameLower Rc C₀
      (accelerationBlockAmplitude ι q Rc C₀ C₁ Cf (traceCost D.T)) *
 (sobolevCoefficientRadius ι
          Rc + 1) ≤ R)
    (n : ℕ) :
    block directions q (fun a => pathTranslate P a (B.derivativePath G)) n 0 ≤
      (3*sobolevCoefficientAmplitude ι q Rc C₁*traceCost D.T +
        3*sobolevCoefficientAmplitude ι q Rc C₀)*majorant R (d+3) n := by
  exact B.coefficients.physicalDerivative_block_bound P directions hdir q
    D.frame.translation_contDiff D.frameDerivative.translation_contDiff B.H.translation_contDiff
    Rc C₀ C₁ CH Cf R hRc hC₀ hC₁ hCH hCf
    (fun j a => D.frame.norm_iteratedFDeriv_translation_le j _
      (mul_nonneg hC₀ (majorant_nonneg Rc hRc 0 j)) (D.frame_spatial_bound j _ (hbF j)) a)
    (fun j a => D.frameDerivative.norm_iteratedFDeriv_translation_le j _
      (mul_nonneg hC₁ (majorant_nonneg Rc hRc 0 j)) (D.frameDerivative_spatial_bound j _ (hbF₁ j))
          a)
    (fun j a => B.H.norm_iteratedFDeriv_translation_le j _
      (mul_nonneg hCH (majorant_nonneg Rc hRc 0 j)) (hbH j) a)
    hRweak hRstrong hT1 hRuniform (forcingPath G) G.path_orbit d hforce n

end EulerTransversePacketProvider.HistoryData
