/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderJetOperations
import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPathJets
import LeanPool.NavierStokesAndEuler.Euler.MeanPacketJets
import LeanPool.NavierStokesAndEuler.Euler.MeanPacketPressureForcing
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderCoefficientBounds
import Mathlib.Algebra.Order.Star.Real
import LeanPool.NavierStokesAndEuler.Euler.MeanPathLpBlocks
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketCylinderFields
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSpatialMeanPath
public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldBounds
import LeanPool.NavierStokesAndEuler.Euler.CylinderActionWords
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevLinear
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevBlocks
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCoefficient
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Comp
import LeanPool.NavierStokesAndEuler.Euler.MeanPacketForcingAlgebra
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevScaling
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketForcing
import LeanPool.NavierStokesAndEuler.Euler.MeanPacketReflection
import LeanPool.NavierStokesAndEuler.Euler.MeanTimeSobolev
public import LeanPool.NavierStokesAndEuler.Euler.MeanSourceFixedInverse
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevAcceleration
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpGramSobolev
public import LeanPool.NavierStokesAndEuler.Euler.MeanContinuousPressure
import LeanPool.NavierStokesAndEuler.Euler.MeanConcreteTranslation
import LeanPool.NavierStokesAndEuler.Euler.MeanSourceSpatialRegularity
import LeanPool.NavierStokesAndEuler.Euler.MeanContinuousPhysical
import LeanPool.NavierStokesAndEuler.Euler.MeanStrongGevrey
import LeanPool.NavierStokesAndEuler.Euler.PacketMajorantShift
public import LeanPool.NavierStokesAndEuler.Euler.MeanContinuousVelocity
public import LeanPool.NavierStokesAndEuler.Euler.MeanContinuousAcceleration
import LeanPool.NavierStokesAndEuler.Euler.TimeLpAccelerationSobolev
import LeanPool.NavierStokesAndEuler.Euler.MeanFixedCoefficientGevrey
import LeanPool.NavierStokesAndEuler.Euler.MeanFixedCoefficientRegularity
public import LeanPool.NavierStokesAndEuler.Euler.MeanGramTranslation
import LeanPool.NavierStokesAndEuler.Euler.MeanAccelerationGevrey
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
public import LeanPool.NavierStokesAndEuler.Euler.MeanStrongEquation
import LeanPool.NavierStokesAndEuler.Euler.MeanTranslatedInverse
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevInverse
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevGevrey
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevProductGevrey
import LeanPool.NavierStokesAndEuler.Euler.TimeLpCoefficientGevrey
import Mathlib.Analysis.Calculus.ContDiff.Operations
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey
public import LeanPool.NavierStokesAndEuler.Euler.MeanFixedTranslation
import LeanPool.NavierStokesAndEuler.Euler.HilbertCoerciveGevrey
public import LeanPool.NavierStokesAndEuler.Euler.MeanScaledCutoff
import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryFrechet
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryMixed
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketUniformScaleSums
import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryDerivative
import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryIterated
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
Source-only budgets for the actual mean solver on the cylinder.  The radius
and inverse guards are fixed before the forcing amplitude, shift, or grade.
The output fields are the genuine velocity, time derivative, and gradient
of the normalized scalar pressure constructed by the source solver.
-/

section

/-!
# Fixed coefficient budgets for the actual mean packet inverse

These data contain only bounds on the prescribed coefficients and their
fixed inverse costs. The external radius is chosen before the forcing grade
or its scalar envelope, which is restored separately by homogeneity.
-/

section

/-! The source boundary operator has uniform Gevrey bounds under physical cutoff rescaling. -/

section

/-! Factorial bounds for actual spatial derivatives of the localized Newtonian operator family. -/

@[expose] public section

noncomputable section

namespace EulerMeanBoundary

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal EulerMeanGradientTest
  EulerMeanCutoffCurl EulerGevrey Finset
open scoped ContDiff

/-- Reuse the additive structure of potential operators in derivative bounds. -/
local instance instPotentialOperatorNormedGroup :
    NormedAddCommGroup (L2 →L[ℝ] homogeneousSpace) := inferInstance

/-- Reuse the additive structure of curl operators in derivative bounds. -/
local instance instCurlOperatorNormedGroup :
    NormedAddCommGroup (homogeneousSpace →L[ℝ] L2) := inferInstance

/-- Reuse the scalar structure of potential operators in derivative bounds. -/
local instance instPotentialOperatorNormedSpace :
    NormedSpace ℝ (L2 →L[ℝ] homogeneousSpace) := inferInstance

/-- Reuse the scalar structure of curl operators in derivative bounds. -/
local instance instCurlOperatorNormedSpace :
    NormedSpace ℝ (homogeneousSpace →L[ℝ] L2) := inferInstance

theorem majorant_four_radius (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    majorant R 0 n ≤ majorant (4*R) 0 n := by
  unfold majorant
  simp only [Nat.add_zero]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hR (by linarith) n) (sq_nonneg _)

/-- One extra derivative costs a fixed factor in the Gevrey radius, not a factorial shift. -/
theorem majorant_next_four_radius (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    majorant R 0 (n+1) ≤ R * majorant (4*R) 0 n := by
  have hs : ((n : ℝ)+1)^2 ≤ (4 : ℝ)^n := by
    calc
      _ ≤ ((2 : ℝ)^n)^2 := pow_le_pow_left₀ (by positivity)
        (EulerPacketUniformScaleSums.stage_count_le_two_pow n) 2
      _ = _ := by rw [← pow_mul, Nat.mul_comm n 2, pow_mul]; norm_num
  have H := mul_le_mul_of_nonneg_left hs
    (mul_nonneg (mul_nonneg hR (pow_nonneg hR n)) (sq_nonneg (n.factorial : ℝ)))
  unfold majorant
  simp only [Nat.add_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    pow_succ, mul_pow]
  nlinarith only [H]

/-- Cutoff gevrey amplitude, constructed using `3`. -/
def cutoffGevreyAmplitude (supportRadius coefficientRadius coefficientSize : ℝ) : ℝ :=
  3 * cutoffCurlConstant * coefficientSize *
    (1 + coefficientRadius *
      (volume (Metric.closedBall (0 : Space) supportRadius)).toReal ^ (1/3 : ℝ))

theorem cutoffGevreyAmplitude_nonneg (R Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) :
    0 ≤ cutoffGevreyAmplitude R Rc C := by
  unfold cutoffGevreyAmplitude
  have h := cutoffCurlConstant_pos.le
  positivity

section LinearCutoffOperation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cutoffOperation_gevrey (L : Cutoff → E)
    (hadd : ∀ χ ψ, L (χ.add ψ) = L χ + L ψ)
    (hsmul : ∀ χ c, L (χ.scale c) = c • L χ)
    (hsub : ∀ χ ψ, L (χ.sub ψ) = L χ - L ψ)
    (hbound : ∀ χ, ‖L χ‖ ≤ cutoffBound χ)
    (χ : Cutoff) (R Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hs : tsupport χ.field ⊆ Metric.closedBall (0 : Space) R)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n χ.field x‖ ≤ C * majorant Rc 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => L (χ.translate b)) a‖ ≤
      cutoffGevreyAmplitude R Rc C * majorant (4*Rc) 0 n := by
  have H := cutoffOperation_iteratedFDeriv_bound L hadd hsmul hsub hbound n χ R
    (C * majorant Rc 0 n) (C * majorant Rc 0 (n+1))
    (mul_nonneg hC (majorant_nonneg Rc hRc _ _))
    (mul_nonneg hC (majorant_nonneg Rc hRc _ _)) hs (hb n) (hb (n+1)) a
  have hV : 0 ≤ (volume (Metric.closedBall (0 : Space) R)).toReal ^ (1/3 : ℝ) := by positivity
  have hinner := add_le_add
    (mul_le_mul_of_nonneg_left (majorant_four_radius Rc hRc n) hC)
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (majorant_next_four_radius Rc hRc n) hC) hV)
  apply H.trans
  calc
    _ ≤ 3 * cutoffCurlConstant *
        (C * majorant (4*Rc) 0 n + C * (Rc * majorant (4*Rc) 0 n) *
          (volume (Metric.closedBall (0 : Space) R)).toReal ^ (1/3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hinner (mul_nonneg (by norm_num) cutoffCurlConstant_pos.le)
    _ = _ := by unfold cutoffGevreyAmplitude; ring

end LinearCutoffOperation

theorem cutoffCurl_gevrey (χ : Cutoff) (R Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hs : tsupport χ.field ⊆ Metric.closedBall (0 : Space) R)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n χ.field x‖ ≤ C * majorant Rc 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => cutoffCurl (χ.translate b)) a‖ ≤
      cutoffGevreyAmplitude R Rc C * majorant (4*Rc) 0 n :=
  cutoffOperation_gevrey cutoffCurl cutoffCurl_add cutoffCurl_scale cutoffCurl_sub
    cutoffCurl_norm_le χ R Rc C hRc hC hs hb n a

theorem weakPotential_gevrey (χ : Cutoff) (R Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hs : tsupport χ.field ⊆ Metric.closedBall (0 : Space) R)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n χ.field x‖ ≤ C * majorant Rc 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => weakPotential (χ.translate b)) a‖ ≤
      cutoffGevreyAmplitude R Rc C * majorant (4*Rc) 0 n :=
  cutoffOperation_gevrey weakPotential weakPotential_add weakPotential_scale weakPotential_sub
    weakPotential_operatorNorm_le χ R Rc C hRc hC hs hb n a

/-- The true derivatives split between the two cutoff positions by the bilinear derivative rule. -/
theorem mixedBoundaryOperator_iteratedFDeriv_le (χ ψ : Cutoff) (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n
      (fun b : Space => mixedBoundaryOperator (χ.translate b) (ψ.translate b)) a‖ ≤
      ∑ k ∈ range (n+1), (n.choose k : ℝ) *
        ‖iteratedFDeriv ℝ k (fun b : Space => cutoffCurl (χ.translate b)) a‖ *
        ‖iteratedFDeriv ℝ (n-k) (fun b : Space => weakPotential (ψ.translate b)) a‖ := by
  have h :=
    (ContinuousLinearMap.compL ℝ L2 homogeneousSpace
        L2).norm_iteratedFDeriv_le_of_bilinear_of_le_one
      (f := fun b : Space => cutoffCurl (χ.translate b))
      (g := fun b : Space => weakPotential (ψ.translate b))
      (cutoffCurl_contDiff χ) (weakPotential_contDiff ψ) a (n := n) (by simp)
      (by
        convert ContinuousLinearMap.norm_compL_le ℝ L2 homogeneousSpace L2 using 1)
  exact h

/-- Factorial estimates follow from the genuine operator family, at every order and parameter. -/
theorem mixedBoundaryOperator_gevrey (χ ψ : Cutoff) (Rχ Rψ Rc Cχ Cψ : ℝ)
    (hRc : 0 ≤ Rc) (hCχ : 0 ≤ Cχ) (hCψ : 0 ≤ Cψ)
    (hsχ : tsupport χ.field ⊆ Metric.closedBall (0 : Space) Rχ)
    (hsψ : tsupport ψ.field ⊆ Metric.closedBall (0 : Space) Rψ)
    (hbχ : ∀ n x, ‖iteratedFDeriv ℝ n χ.field x‖ ≤ Cχ * majorant Rc 0 n)
    (hbψ : ∀ n x, ‖iteratedFDeriv ℝ n ψ.field x‖ ≤ Cψ * majorant Rc 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n
      (fun b : Space => mixedBoundaryOperator (χ.translate b) (ψ.translate b)) a‖ ≤
      3 * cutoffGevreyAmplitude Rχ Rc Cχ * cutoffGevreyAmplitude Rψ Rc Cψ *
        majorant (4*Rc) 0 n := by
  have H := sequence_product_majorant (4*Rc)
    (cutoffGevreyAmplitude Rχ Rc Cχ) (cutoffGevreyAmplitude Rψ Rc Cψ)
    (mul_nonneg (by norm_num) hRc)
    (cutoffGevreyAmplitude_nonneg Rχ Rc Cχ hRc hCχ)
    (cutoffGevreyAmplitude_nonneg Rψ Rc Cψ hRc hCψ) 0 0
    (fun k => ‖iteratedFDeriv ℝ k (fun b : Space => cutoffCurl (χ.translate b)) a‖)
    (fun k => ‖iteratedFDeriv ℝ k (fun b : Space => weakPotential (ψ.translate b)) a‖)
    (fun k => by
      rw [abs_of_nonneg (norm_nonneg _)]
      exact cutoffCurl_gevrey χ Rχ Rc Cχ hRc hCχ hsχ hbχ k a)
    (fun k => by
      rw [abs_of_nonneg (norm_nonneg _)]
      exact weakPotential_gevrey ψ Rψ Rc Cψ hRc hCψ hsψ hbψ k a) n
  exact (mixedBoundaryOperator_iteratedFDeriv_le χ ψ n a).trans ((le_abs_self _).trans H)

end EulerMeanBoundary

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanBoundary

attribute [local instance] instPotentialOperatorNormedGroup instCurlOperatorNormedGroup
  instPotentialOperatorNormedSpace instCurlOperatorNormedSpace

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal EulerMeanGradientTest
  EulerMeanCutoffCurl EulerGevrey
open scoped ContDiff

/-- Cutoff unit ball factor, given by `(Real.pi * 4 / 3) ^ (1/3 : ℝ)`. -/
def cutoffUnitBallFactor : ℝ := (Real.pi * 4 / 3) ^ (1/3 : ℝ)

theorem cutoffUnitBallFactor_nonneg : 0 ≤ cutoffUnitBallFactor := by
  unfold cutoffUnitBallFactor
  positivity

theorem closedBall_volume_oneThird (R : ℝ) (hR : 0 ≤ R) :
    (volume (Metric.closedBall (0 : Space) R)).toReal ^ (1/3 : ℝ) = R * cutoffUnitBallFactor := by
  rw [EuclideanSpace.volume_closedBall_fin_three, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hR, ENNReal.toReal_ofReal (by positivity),
    Real.mul_rpow (pow_nonneg hR 3) (by positivity), ← Real.rpow_natCast_mul hR]
  norm_num [cutoffUnitBallFactor]

/-- Scaled cutoff gevrey size, given by `(9 * (1 + 3 / EulerGevreyCutoff.bumpMass)^2)^3`. -/
def scaledCutoffGevreySize : ℝ := (9 * (1 + 3 / EulerGevreyCutoff.bumpMass)^2)^3

theorem scaledCutoffGevreySize_nonneg : 0 ≤ scaledCutoffGevreySize := by
  unfold scaledCutoffGevreySize
  positivity

/-- The exact scaling factor is retained, so the L³ derivative term will cancel the support radius.
-/
theorem scaledCutoff_scaledRadiusGevrey (ℓ : ℝ) (hℓ : 0 < ℓ) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (scaledCutoff ℓ hℓ).field x‖ ≤
      scaledCutoffGevreySize * majorant (256*ℓ) 0 n := by
  change ‖iteratedFDeriv ℝ n (fun y => EulerSpatialCutoffs.outerCutoff (ℓ • y)) x‖ ≤ _
  rw [iteratedFDeriv_comp_const_smul ℓ
    (EulerSpatialCutoffs.outerCutoff_contDiff.of_le (by simp)), norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hℓ.le n)]
  have H := mul_le_mul_of_nonneg_left (EulerSpatialCutoffs.outerCutoff_gevrey n (ℓ • x))
    (pow_nonneg hℓ.le n)
  apply H.trans_eq
  unfold scaledCutoffGevreySize majorant
  simp only [Nat.add_zero, mul_pow]
  ring

theorem scaledCutoff_support_ball (ℓ : ℝ) (hℓ : 0 < ℓ) :
    tsupport (scaledCutoff ℓ hℓ).field ⊆ Metric.closedBall (0 : Space) (2*ℓ⁻¹) := by
  intro x hx
  have H := scaledCutoff_support ℓ hℓ hx
  change ‖ℓ • x‖ ≤ 2 at H
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ] at H
  have H' := mul_le_mul_of_nonneg_left H (inv_nonneg.mpr hℓ.le)
  simp only [← mul_assoc, inv_mul_cancel₀ hℓ.ne', one_mul] at H'
  simpa only [Metric.mem_closedBall, dist_zero_right, mul_comm] using H'

/-- This is one fixed dimensional constant, independent of the physical scale. -/
def scaledCutoffOperatorAmplitude : ℝ :=
  3 * cutoffCurlConstant * scaledCutoffGevreySize * (1 + 512 * cutoffUnitBallFactor)

theorem scaledCutoffOperatorAmplitude_nonneg : 0 ≤ scaledCutoffOperatorAmplitude := by
  unfold scaledCutoffOperatorAmplitude
  have h₁ := cutoffCurlConstant_pos.le
  have h₂ := scaledCutoffGevreySize_nonneg
  have h₃ := cutoffUnitBallFactor_nonneg
  positivity

theorem scaledCutoff_amplitude (ℓ : ℝ) (hℓ : 0 < ℓ) :
    cutoffGevreyAmplitude (2*ℓ⁻¹) (256*ℓ) scaledCutoffGevreySize =
      scaledCutoffOperatorAmplitude := by
  unfold cutoffGevreyAmplitude scaledCutoffOperatorAmplitude
  rw [closedBall_volume_oneThird (2*ℓ⁻¹) (by positivity)]
  rw [show (256*ℓ) * (2*ℓ⁻¹ * cutoffUnitBallFactor) =
    512 * (ℓ*ℓ⁻¹) * cutoffUnitBallFactor by ring, mul_inv_cancel₀ hℓ.ne', mul_one]

theorem scaled_majorant_le (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1) (n : ℕ) :
    majorant (4*(256*ℓ)) 0 n ≤ majorant 1024 0 n := by
  unfold majorant
  simp only [Nat.add_zero]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact pow_le_pow_left₀ (by positivity) (by linarith) n

theorem scaledCutoffCurl_gevrey (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n
      (fun b : Space => cutoffCurl ((scaledCutoff ℓ hℓ).translate b)) a‖ ≤
      scaledCutoffOperatorAmplitude * majorant 1024 0 n := by
  have H := cutoffCurl_gevrey (scaledCutoff ℓ hℓ) (2*ℓ⁻¹) (256*ℓ) scaledCutoffGevreySize
    (by positivity) scaledCutoffGevreySize_nonneg (scaledCutoff_support_ball ℓ hℓ)
    (scaledCutoff_scaledRadiusGevrey ℓ hℓ) n a
  rw [scaledCutoff_amplitude ℓ hℓ] at H
  exact H.trans (mul_le_mul_of_nonneg_left (scaled_majorant_le ℓ hℓ.le hℓ1 n)
    scaledCutoffOperatorAmplitude_nonneg)

theorem scaledWeakPotential_gevrey (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n
      (fun b : Space => weakPotential ((scaledCutoff ℓ hℓ).translate b)) a‖ ≤
      scaledCutoffOperatorAmplitude * majorant 1024 0 n := by
  have H := weakPotential_gevrey (scaledCutoff ℓ hℓ) (2*ℓ⁻¹) (256*ℓ) scaledCutoffGevreySize
    (by positivity) scaledCutoffGevreySize_nonneg (scaledCutoff_support_ball ℓ hℓ)
    (scaledCutoff_scaledRadiusGevrey ℓ hℓ) n a
  rw [scaledCutoff_amplitude ℓ hℓ] at H
  exact H.trans (mul_le_mul_of_nonneg_left (scaled_majorant_le ℓ hℓ.le hℓ1 n)
    scaledCutoffOperatorAmplitude_nonneg)

/-- Scaled boundary operator amplitude, given by `3 * scaledCutoffOperatorAmplitude^2`. -/
def scaledBoundaryOperatorAmplitude : ℝ := 3 * scaledCutoffOperatorAmplitude^2

theorem scaledBoundaryOperatorAmplitude_nonneg : 0 ≤ scaledBoundaryOperatorAmplitude := by
  unfold scaledBoundaryOperatorAmplitude
  positivity

/-- The source operator is genuinely smooth in the entire spatial translation parameter. -/
theorem scaledBoundaryOperator_contDiff (ℓ : ℝ) (hℓ : 0 < ℓ) :
    ContDiff ℝ ∞ (fun a : Space => boundaryOperator ((scaledCutoff ℓ hℓ).translate a)) :=
  mixedBoundaryOperator_contDiff (scaledCutoff ℓ hℓ) (scaledCutoff ℓ hℓ)

/-- All actual operator derivatives have an unshifted Gevrey-two bound, uniformly for 0 < ℓ ≤ 1. -/
theorem scaledBoundaryOperator_gevrey (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n
      (fun b : Space => boundaryOperator ((scaledCutoff ℓ hℓ).translate b)) a‖ ≤
      scaledBoundaryOperatorAmplitude * majorant 1024 0 n := by
  have H := mixedBoundaryOperator_gevrey (scaledCutoff ℓ hℓ) (scaledCutoff ℓ hℓ)
    (2*ℓ⁻¹) (2*ℓ⁻¹) (256*ℓ) scaledCutoffGevreySize scaledCutoffGevreySize
    (by positivity) scaledCutoffGevreySize_nonneg scaledCutoffGevreySize_nonneg
    (scaledCutoff_support_ball ℓ hℓ) (scaledCutoff_support_ball ℓ hℓ)
    (scaledCutoff_scaledRadiusGevrey ℓ hℓ) (scaledCutoff_scaledRadiusGevrey ℓ hℓ) n a
  rw [scaledCutoff_amplitude ℓ hℓ] at H
  have Hb := H.trans (mul_le_mul_of_nonneg_left (scaled_majorant_le ℓ hℓ.le hℓ1 n)
    (mul_nonneg (mul_nonneg (by norm_num) scaledCutoffOperatorAmplitude_nonneg)
      scaledCutoffOperatorAmplitude_nonneg))
  simpa only [mixedBoundaryOperator_diagonal, scaledBoundaryOperatorAmplitude, pow_two, mul_assoc]
      using Hb

end EulerMeanBoundary

end
end

end

section

/-!
# Genuine all-order spatial estimates for the translated mean inverse

The recurrence is proved for the actual coercive inverse. The translated
solution is identified with the real spatial translation orbit before its
iterated Fréchet derivatives are estimated. Coefficient and forcing amplitudes
enter through explicit polynomials, independently of derivative order.
-/

@[expose] public section

noncomputable section

namespace EulerMeanTranslatedGevrey

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal EulerTimeLp
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanFixedSpaceInverse
  EulerMeanFixedTranslation EulerMeanTranslatedInverse EulerMeanFixedCoefficientRegularity
  EulerMeanFixedCoefficientGevrey EulerHilbertCoerciveGevrey EulerCoerciveProjection
  EulerGevrey EulerOperatorGevreyCalculus EulerTransverseGramInverse
open scoped ContDiff

-- Reuse the nested Hilbert-space instances in the translated inverse estimates.
/-- Cache the standard `NormedAddCommGroup solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanTranslatedGevrey1 : NormedAddCommGroup solenoidalSpace := inferInstance
/-- Cache the standard `InnerProductSpace ℝ solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanTranslatedGevrey2 : InnerProductSpace ℝ solenoidalSpace := inferInstance
/-- Cache the standard `NormedAddCommGroup (TimeLp T L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanTranslatedGevrey3 (T : ℝ) : NormedAddCommGroup (TimeLp T L2) := inferInstance
/-- Cache the standard `InnerProductSpace ℝ (TimeLp T L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanTranslatedGevrey4 (T : ℝ) : InnerProductSpace ℝ (TimeLp T L2) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (TimeLp T solenoidalSpace)` instance to shorten
typeclass synthesis. -/
local instance instMeanTranslatedGevrey5 (T : ℝ) : NormedAddCommGroup (TimeLp T solenoidalSpace) :=
    inferInstance
/-- Cache the standard `InnerProductSpace ℝ (TimeLp T solenoidalSpace)` instance to shorten
typeclass synthesis. -/
local instance instMeanTranslatedGevrey6 (T : ℝ) : InnerProductSpace ℝ (TimeLp T solenoidalSpace)
    := inferInstance

/-- The proved polynomial amplitude for the actual fixed mean operator. -/
def operatorAmplitude (T CF CF₁ CH CM CA L : ℝ) : ℝ :=
  9*(T*CF₁+CF)^2*(1+(T^2/2)*CH+T*(CM+|L| * CA))

/-- The proved polynomial amplitude of the actual forcing pullback. -/
def forcingAmplitude (T CF CF₁ Cf : ℝ) : ℝ := 3*(T*(T*CF₁+CF))*Cf

theorem operatorAmplitude_nonneg (T CF CF₁ CH CM CA L : ℝ)
    (hT : 0 ≤ T) (hCH : 0 ≤ CH) (hCM : 0 ≤ CM) (hCA : 0 ≤ CA) :
    0 ≤ operatorAmplitude T CF CF₁ CH CM CA L := by unfold operatorAmplitude; positivity

theorem forcingAmplitude_nonneg (T CF CF₁ Cf : ℝ)
    (hT : 0 ≤ T) (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCf : 0 ≤ Cf) :
    0 ≤ forcingAmplitude T CF CF₁ Cf := by unfold forcingAmplitude; positivity

variable (T : ℝ) (hT : 0 ≤ T)
  (F F₁ H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (M0 A : L2 →L[ℝ] L2) (L c : ℝ)
  (hc : 0 < c)
  (hcoercive : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪fixedMeanOperator T hT F F₁ H M0 A L v, v⟫_ℝ)

/-- Every actual spatial derivative of the solved mean field satisfies the
factorial bound, with no assumed solution-jet recurrence. -/
theorem solution_translation_gevrey
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
    (hH : ContDiff ℝ ∞ (fun a : Space => translatePath T a H))
    (hM0 : ContDiff ℝ ∞ (fun a : Space => translateOperator a M0))
    (hA : ContDiff ℝ ∞ (fun a : Space => translateOperator a A))
    (f : TimeLp T L2) (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f))
    (Rc R M CF CF₁ CH CM CA Cf : ℝ)
    (hRc : 0 ≤ Rc) (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCH : 0 ≤ CH)
    (hCM : 0 ≤ CM) (hCA : 0 ≤ CA) (hCf : 0 ≤ Cf)
    (hM : 1 ≤ M)
    (hMC : c⁻¹*operatorAmplitude T CF CF₁ CH CM CA L ≤ M)
    (hMD : c⁻¹*forcingAmplitude T CF CF₁ Cf ≤ M)
    (hR : 2*M*(Rc+1) ≤ R)
    (hFb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant Rc 0
        n)
    (hF₁b : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁*majorant Rc
        0 n)
    (hHb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b H) a‖ ≤ CH*majorant Rc 0
        n)
    (hMb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translateOperator b M0) a‖ ≤ CM*majorant Rc
        0 n)
    (hAb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translateOperator b A) a‖ ≤ CA*majorant Rc
        0 n)
    (d : ℕ) (hfb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeTranslation T b f) a‖ ≤
        Cf*majorant R d n)
    (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (fun a : Space => timeSolenoidalTranslation T a
      (coerciveInverse (fixedMeanOperator T hT F F₁ H M0 A L) c hc hcoercive
        (-(fixedMeanPrimitive T hT F F₁).adjoint f))) x‖ ≤ majorant R (d+1) n := by
  have hRcR : Rc ≤ R := (radius_bounds hRc hM hR).2
  have hR0 : 0 ≤ R := hRc.trans hRcR
  have hFbr (k a) : ‖iteratedFDeriv ℝ k (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant R 0
      k :=
    (hFb k a).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc R hRc hRcR 0 k) hCF)
  have hF₁br (k a) : ‖iteratedFDeriv ℝ k (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁*majorant
      R 0 k :=
    (hF₁b k a).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc R hRc hRcR 0 k) hCF₁)
  have hO : ContDiff ℝ ∞ (fun a : Space => translatedMeanOperator T hT a F F₁ H M0 A L) :=
    contDiff_fixedMeanOperator T hT (fun a => translatePath T a F) (fun a => translatePath T a F₁)
      (fun a => translatePath T a H) (fun a => translateOperator a M0) (fun a => translateOperator
          a A)
      L hF hF₁ hH hM0 hA
  have hJ : ContDiff ℝ ∞ (fun a : Space => translatedMeanPrimitive T hT a F F₁) :=
    contDiff_fixedMeanPrimitive T hT (fun a => translatePath T a F) (fun a => translatePath T a F₁)
        hF hF₁
  have hG : ContDiff ℝ ∞ (fun a : Space =>
      -(translatedMeanPrimitive T hT a F F₁).adjoint (timeTranslation T a f)) :=
    (((realAdjoint (U := TimeLp T solenoidalSpace) (E := TimeLp T L2)).contDiff.comp hJ).clm_apply
        hf).neg
  have hOb (j a) : ‖iteratedFDeriv ℝ (j+1)
      (fun b : Space => translatedMeanOperator T hT b F F₁ H M0 A L) a‖ ≤
      operatorAmplitude T CF CF₁ CH CM CA L*(Rc^(j+1)*((j+1).factorial : ℝ)^2) := by
    have h := fixedMeanOperator_bound T hT (fun a => translatePath T a F)
      (fun a => translatePath T a F₁) (fun a => translatePath T a H)
      (fun a => translateOperator a M0) (fun a => translateOperator a A) L hF hF₁ hH hM0 hA
      Rc CF CF₁ CH CM CA hRc hCF hCF₁ hCH hCM hCA hFb hF₁b hHb hMb hAb (j+1) a
    simpa only [translatedMeanOperator, operatorAmplitude, majorant, Nat.add_zero] using h
  have hGb (k a) : ‖iteratedFDeriv ℝ k (fun b : Space =>
      -(translatedMeanPrimitive T hT b F F₁).adjoint (timeTranslation T b f)) a‖ ≤
      forcingAmplitude T CF CF₁ Cf*majorant R d k :=
    fixedMeanForcing_bound T hT (fun a => translatePath T a F) (fun a => translatePath T a F₁)
      (fun a => timeTranslation T a f) hF hF₁ hf R CF CF₁ Cf hR0 hCF hCF₁ hCf d hFbr hF₁br hfb k a
  have hout := coerciveSolution_gevrey_amplitudes
    (fun a : Space => translatedMeanOperator T hT a F F₁ H M0 A L) (fun _ => c) (fun _ => hc)
    (fun a => translatedMeanOperator_coercive T hT a F F₁ H M0 A L c hcoercive)
    (fun a : Space => -(translatedMeanPrimitive T hT a F F₁).adjoint (timeTranslation T a f)) hO hG
    c⁻¹ (operatorAmplitude T CF CF₁ CH CM CA L) (forcingAmplitude T CF CF₁ Cf) M Rc R
    (operatorAmplitude_nonneg T CF CF₁ CH CM CA L hT hCH hCM hCA)
    (forcingAmplitude_nonneg T CF CF₁ Cf hT hCF hCF₁ hCf) hM hMC hMD hRc hR (fun _ => le_rfl)
    hOb d hGb n x
  have heq : (fun a : Space => translatedMeanSolver T hT F F₁ H M0 A L c hc hcoercive a
      (timeTranslation T a f)) =
      (fun a : Space => timeSolenoidalTranslation T a
        (coerciveInverse (fixedMeanOperator T hT F F₁ H M0 A L) c hc hcoercive
          (-(fixedMeanPrimitive T hT F F₁).adjoint f))) :=
    funext (fun a => translatedMeanSolver_covariance T hT F F₁ H M0 A L c hc hcoercive a f)
  exact (congrArg (fun g : Space → TimeLp T solenoidalSpace => ‖iteratedFDeriv ℝ n g x‖)
      heq.symm).trans_le hout

end EulerMeanTranslatedGevrey

end
end

end

section

/-!
# Genuine fixed-Hq bounds for the constructed mean inverse

The input and output use the same ordered spatial words, the same fixed base
Sobolev order, and the same radius. Only the known coefficient estimates are
converted from tensor bounds. Their finite Sobolev cost is paid once, before
applying the actual inverse recurrence.
-/

@[expose] public section

noncomputable section

namespace EulerMeanFixedSobolevGevrey

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal EulerTimeLp
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanFixedSpaceInverse
  EulerMeanFixedTranslation EulerMeanTranslatedInverse EulerMeanFixedCoefficientRegularity
  EulerMeanFixedCoefficientGevrey EulerMeanTranslatedGevrey EulerCoerciveProjection
  EulerGevrey EulerOperatorGevreyCalculus EulerTransverseGramInverse
  EulerParameterWordGevrey EulerTerminalTimePrimitive EulerTimeLpCoefficientGevrey
open scoped ContDiff

-- Reuse the nested Hilbert-space instances in the adjoint and inverse estimates.
/-- Cache the standard `NormedAddCommGroup solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanFixedSobolevGevrey1 : NormedAddCommGroup solenoidalSpace := inferInstance
/-- Cache the standard `InnerProductSpace ℝ solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanFixedSobolevGevrey2 : InnerProductSpace ℝ solenoidalSpace := inferInstance
/-- Cache the standard `NormedAddCommGroup (TimeLp T L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanFixedSobolevGevrey3 (T : ℝ) : NormedAddCommGroup (TimeLp T L2) :=
    inferInstance
/-- Cache the standard `InnerProductSpace ℝ (TimeLp T L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanFixedSobolevGevrey4 (T : ℝ) : InnerProductSpace ℝ (TimeLp T L2) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (TimeLp T solenoidalSpace)` instance to shorten
typeclass synthesis. -/
local instance instMeanFixedSobolevGevrey5 (T : ℝ) : NormedAddCommGroup (TimeLp T solenoidalSpace)
    := inferInstance
/-- Cache the standard `InnerProductSpace ℝ (TimeLp T solenoidalSpace)` instance to shorten
typeclass synthesis. -/
local instance instMeanFixedSobolevGevrey6 (T : ℝ) : InnerProductSpace ℝ (TimeLp T solenoidalSpace)
    := inferInstance

/-- Coefficient-only amplitude of the full mean form in a fixed base order. -/
def operatorBlockAmplitude (ι : Type*) [Fintype ι] (q : ℕ)
    (T Rc CF CF₁ CH CM CA L : ℝ) : ℝ :=
  sobolevCoefficientAmplitude ι q Rc (operatorAmplitude T CF CF₁ CH CM CA L)

/-- Pulling back the right side is a multiplication in the same Sobolev block. -/
def forcingBlockAmplitude (ι : Type*) [Fintype ι] (q : ℕ)
    (T Rc CF CF₁ Cf : ℝ) : ℝ :=
  3*sobolevCoefficientAmplitude ι q Rc (T*(T*CF₁+CF))*Cf

/-- Actual derivatives of the force-pullback operator, before applying it to
any forcing. No forcing derivative is converted to a tensor norm. -/
theorem forcingOperator_bound {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (T : ℝ) (hT : 0 ≤ T)
    (F F₁ : P → C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (hF : ContDiff ℝ ∞ F) (hF₁ : ContDiff ℝ ∞ F₁)
    (Rc CF CF₁ : ℝ) (hRc : 0 ≤ Rc) (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁)
    (hFb : ∀ n x, ‖iteratedFDeriv ℝ n F x‖ ≤ CF * majorant Rc 0 n)
    (hF₁b : ∀ n x, ‖iteratedFDeriv ℝ n F₁ x‖ ≤ CF₁ * majorant Rc 0 n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => -(fixedMeanPrimitive T hT (F y) (F₁ y)).adjoint) x‖ ≤
      (T*(T*CF₁+CF))*majorant Rc 0 n := by
  have hD := contDiff_fixedMeanDerivative T hT F F₁ hF hF₁
  have hJ := contDiff_fixedMeanPrimitive T hT F F₁ hF hF₁
  have hD0 : 0 ≤ T*CF₁+CF := by positivity
  have hJb (k : ℕ) (y : P) :
      ‖iteratedFDeriv ℝ k (fun z => fixedMeanPrimitive T hT (F z) (F₁ z)) y‖ ≤
        (T*(T*CF₁+CF))*majorant Rc 0 k := by
    have hb := clm_comp_const_left_bound (primitiveTimeLp (E := L2) T hT)
      (fun z => fixedMeanDerivative T hT (F z) (F₁ z)) hD Rc (T*CF₁+CF) hRc hD0 0
      (fixedMeanDerivative_bound T hT F F₁ hF hF₁ Rc CF CF₁ hRc hCF hCF₁ 0 hFb hF₁b) k y
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (primitive_norm_le_time (E := L2) T hT) hD0)
      (majorant_nonneg Rc hRc 0 k))
  exact neg_bound (fun y => (fixedMeanPrimitive T hT (F y) (F₁ y)).adjoint)
    Rc (T*(T*CF₁+CF)) 0
    (adjoint_bound (fun y => fixedMeanPrimitive T hT (F y) (F₁ y)) hJ
      Rc (T*(T*CF₁+CF)) hRc (by positivity) 0 hJb) n x

variable {ι : Type*} [Fintype ι]
  (directions : ι → Space) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (T : ℝ) (hT : 0 ≤ T)
  (F F₁ H : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)) (M0 A : L2 →L[ℝ] L2) (L c : ℝ)
  (hc : 0 < c)
  (hcoercive : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪fixedMeanOperator T hT F F₁ H M0 A L v, v⟫_ℝ)

include hd in
/-- A genuine one-shift fixed-Hq estimate for the spatial orbit of the actual
mean solution, at the identical forcing radius and with grade-independent
constants. The fixed-Hq cost is computed from the original L² inverse. -/
theorem solution_translation_block_gevrey
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
    (hH : ContDiff ℝ ∞ (fun a : Space => translatePath T a H))
    (hM0 : ContDiff ℝ ∞ (fun a : Space => translateOperator a M0))
    (hA : ContDiff ℝ ∞ (fun a : Space => translateOperator a A))
    (f : TimeLp T L2) (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f))
    (Rc R M CF CF₁ CH CM CA Cf : ℝ)
    (hRc : 0 ≤ Rc) (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCH : 0 ≤ CH)
    (hCM : 0 ≤ CM) (hCA : 0 ≤ CA) (hCf : 0 ≤ Cf)
    (hM : 1 ≤ M)
    (hMC : sobolevInverseCost c⁻¹ (operatorBlockAmplitude ι q T Rc CF CF₁ CH CM CA L) q *
      operatorBlockAmplitude ι q T Rc CF CF₁ CH CM CA L ≤ M)
    (hMD : sobolevInverseCost c⁻¹ (operatorBlockAmplitude ι q T Rc CF CF₁ CH CM CA L) q *
      forcingBlockAmplitude ι q T Rc CF CF₁ Cf ≤ M)
    (hR : 2*M*(sobolevCoefficientRadius ι Rc+1) ≤ R)
    (hFb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant Rc 0
        n)
    (hF₁b : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁*majorant Rc
        0 n)
    (hHb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b H) a‖ ≤ CH*majorant Rc 0
        n)
    (hMb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translateOperator b M0) a‖ ≤ CM*majorant Rc
        0 n)
    (hAb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translateOperator b A) a‖ ≤ CA*majorant Rc
        0 n)
    (d : ℕ) (hfb : ∀ n a, block directions q (fun b : Space => timeTranslation T b f) n a ≤
        Cf*majorant R d n)
    (n : ℕ) (x : Space) :
    block directions q (fun a : Space => timeSolenoidalTranslation T a
      (coerciveInverse (fixedMeanOperator T hT F F₁ H M0 A L) c hc hcoercive
        (-(fixedMeanPrimitive T hT F F₁).adjoint f))) n x ≤ majorant R (d+1) n := by
  let O := fun a : Space => translatedMeanOperator T hT a F F₁ H M0 A L
  let J := fun a : Space => -(translatedMeanPrimitive T hT a F F₁).adjoint
  let u := fun a : Space => timeSolenoidalTranslation T a
    (coerciveInverse (fixedMeanOperator T hT F F₁ H M0 A L) c hc hcoercive
      (-(fixedMeanPrimitive T hT F F₁).adjoint f))
  let g := fun a : Space => J a (timeTranslation T a f)
  have hO : ContDiff ℝ ∞ O :=
    contDiff_fixedMeanOperator T hT (fun a => translatePath T a F) (fun a => translatePath T a F₁)
      (fun a => translatePath T a H) (fun a => translateOperator a M0) (fun a => translateOperator
          a A)
      L hF hF₁ hH hM0 hA
  have hJ0 : ContDiff ℝ ∞ (fun a : Space => translatedMeanPrimitive T hT a F F₁) :=
    contDiff_fixedMeanPrimitive T hT (fun a => translatePath T a F) (fun a => translatePath T a F₁)
        hF hF₁
  have hJ : ContDiff ℝ ∞ J :=
    ((realAdjoint (U := TimeLp T solenoidalSpace) (E := TimeLp T L2)).contDiff.comp hJ0).neg
  have hu : ContDiff ℝ ∞ u := solution_translation_contDiff T hT F F₁ H M0 A L c hc hcoercive f hO
      hJ0 hf
  have hg : ContDiff ℝ ∞ g := hJ.clm_apply hf
  have heq (a : Space) : O a (u a) = g a := by
    dsimp only [u]
    exact (congrArg (O a)
      (translatedMeanSolver_covariance T hT F F₁ H M0 A L c hc hcoercive a f).symm).trans
        (operator_inverse_apply (O a) c hc
          (translatedMeanOperator_coercive T hT a F F₁ H M0 A L c hcoercive) _)
  have hOb (k a) : ‖iteratedFDeriv ℝ k O a‖ ≤ operatorAmplitude T CF CF₁ CH CM CA L*majorant Rc 0 k
      :=
    fixedMeanOperator_bound T hT (fun a => translatePath T a F)
      (fun a => translatePath T a F₁) (fun a => translatePath T a H)
      (fun a => translateOperator a M0) (fun a => translateOperator a A) L hF hF₁ hH hM0 hA
      Rc CF CF₁ CH CM CA hRc hCF hCF₁ hCH hCM hCA hFb hF₁b hHb hMb hAb k a
  have hJb (k a) : ‖iteratedFDeriv ℝ k J a‖ ≤ (T*(T*CF₁+CF))*majorant Rc 0 k :=
    forcingOperator_bound T hT (fun a => translatePath T a F) (fun a => translatePath T a F₁)
      hF hF₁ Rc CF CF₁ hRc hCF hCF₁ hFb hF₁b k a
  have hO0 := operatorAmplitude_nonneg T CF CF₁ CH CM CA L hT hCH hCM hCA
  have hOA0 : 0 ≤ operatorBlockAmplitude ι q T Rc CF CF₁ CH CM CA L :=
    sobolevCoefficientAmplitude_nonneg q Rc _ hRc hO0
  have hJA0 : 0 ≤ sobolevCoefficientAmplitude ι q Rc (T*(T*CF₁+CF)) :=
    sobolevCoefficientAmplitude_nonneg q Rc _ hRc (by positivity)
  have hD0 : 0 ≤ forcingBlockAmplitude ι q T Rc CF CF₁ Cf := by
    unfold forcingBlockAmplitude
    positivity
  have hr₀ : 0 ≤ sobolevCoefficientRadius ι Rc := sobolevCoefficientRadius_nonneg Rc hRc
  have hrR : sobolevCoefficientRadius ι Rc ≤ R := (radius_bounds hr₀ hM hR).2
  have hbO (k a) := coefficientBlock_of_tensor_bound directions hd q O hO Rc _ hRc hO0 hOb k a
  have hbJ (k a) := coefficientBlock_of_tensor_bound directions hd q J hJ Rc _ hRc
    (show 0 ≤ T*(T*CF₁+CF) by positivity) hJb k a
  have hgb (k a) : block directions q g k a ≤ forcingBlockAmplitude ι q T Rc CF CF₁ Cf*majorant R d
      k :=
    block_clm_apply_gevrey directions q J (fun a => timeTranslation T a f) hJ hf
      (sobolevCoefficientRadius ι Rc) R _ Cf hr₀ hrR hJA0 hCf hbJ d hfb k a
  apply block_inverse_gevrey directions q O u g hO hu hg heq
    (translatedMeanInverse T hT F F₁ H M0 A L c hc hcoercive)
    (fun a v => inverse_operator_apply (O a) c hc
      (translatedMeanOperator_coercive T hT a F F₁ H M0 A L c hcoercive) v)
    c⁻¹ (operatorBlockAmplitude ι q T Rc CF CF₁ CH CM CA L)
    (operatorBlockAmplitude ι q T Rc CF CF₁ CH CM CA L)
    (forcingBlockAmplitude ι q T Rc CF CF₁ Cf) M (sobolevCoefficientRadius ι Rc) R
    hOA0 hD0 hM hMC hMD hr₀ hR
    (translatedMeanInverse_norm T hT F F₁ H M0 A L c hc hcoercive)
    (baseSize_of_tensor_bound directions hd q O hO Rc _ hRc hO0 hOb) _ d hgb n x
  intro j a
  simpa only [majorant, Nat.add_zero, operatorBlockAmplitude] using hbO (j+1) a

end EulerMeanFixedSobolevGevrey

end
end

end

section

/-!
# The actual source mean coordinate inverse has Gevrey spatial bounds

The spatial lower bound, operator smoothness, cutoff derivatives, fixed-space
transport, and inverse recurrence are all supplied by proved constructions.
The remaining quantitative inputs are literal spatial derivatives of the given
matrix coefficients and the actual translation derivatives of the forcing.
-/

@[expose] public section

noncomputable section

namespace EulerMeanSourceGevrey

open MeasureTheory Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanCoefficients EulerMeanBoundary EulerMeanHarmonic EulerMeanSourceInverse
  EulerMeanVariationalInverse EulerMeanFixedSpaceInverse EulerMeanSourceFixedInverse
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanTranslatedGevrey
  EulerTimeLp EulerCoerciveProjection EulerGevrey EulerOperatorGevreyCalculus
open scoped NNReal ContDiff

/-- True spatial coefficient bounds become bounds for the conjugated operator path. -/
theorem translatedPath_bound (T : ℝ)
    (F : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
    (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hbound : ∀ n t x, ‖iteratedFDeriv ℝ n (F.field t : Space → Space →L[ℝ] Space) x‖ ≤ C * majorant
        R 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b (operatorPath T F.field)) a‖ ≤
        C*majorant R 0 n := by
  simpa only [translatePath_operatorPath] using
    norm_iteratedFDeriv_operatorPathTranslation_le T F n (C*majorant R 0 n)
      (mul_nonneg hC (majorant_nonneg R hR 0 n)) (hbound n) a

/-- The initial matrix multiplier has the same literal spatial derivative bounds. -/
theorem translatedMultiplier_bound
    (M0 : BoundedSmoothField (Space →L[ℝ] Space)) (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hbound : ∀ n x, ‖iteratedFDeriv ℝ n (M0.field : Space → Space →L[ℝ] Space) x‖ ≤ C * majorant R
        0
        n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => translateOperator b (multiplier M0.field)) a‖ ≤
        C*majorant R 0 n := by
  simpa only [translateOperator_multiplier] using
    norm_iteratedFDeriv_multiplierTranslation_le M0 n (C*majorant R 0 n)
      (mul_nonneg hC (majorant_nonneg R hR 0 n)) (hbound n) a

variable (T : ℝ) (hT : 0 ≤ T) (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1)
  (F F₁ H : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (M0 : BoundedSmoothField (Space →L[ℝ] Space)) (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  (Be Bc L r : ℝ) (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc)
  (hL : boundaryLocalizationC1 * Bc ≤ L) (hr : 0 ≤ r) (hrquarter : r ≤ 1 / 4)
  (hext : ∀ x, r ≤ ‖ℓ • x‖ → ∀ v : Space, -Be * ‖v‖ ^ 2 ≤ ⟪M0.field x v, v⟫_ℝ)
  (hcore : ∀ x, ‖ℓ • x‖ < r → ∀ v : Space, -Bc * ‖v‖ ^ 2 ≤ ⟪M0.field x v, v⟫_ℝ)
  (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (operatorPath T F.field t x) = x)
  (hF : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (EulerVolterraConvolution.extendPath T hT (operatorPath T F.field))
      (operatorPath T F₁.field t) (Icc (0 : ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K)
  (hF0 : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
  (hH : ∀ t x v, ⟪H.field t x v, v⟫_ℝ ≤ K * ‖v‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) + Be * T + boundaryLocalizationC2 * Bc * r ^ 3 * T ≤ 1 / 2)

include hℓ1 in
/-- The source coordinate solver obeys all-order genuine spatial estimates.
Its coercivity and cutoff assumptions have already been discharged. -/
theorem sourceCoordinateSolver_translation_gevrey
    (f : TimeLp T L2) (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f))
    (Rc R M CF CF₁ CH CM Cf : ℝ) (hRc : 1024 ≤ Rc)
    (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCH : 0 ≤ CH) (hCM : 0 ≤ CM) (hCf : 0 ≤ Cf)
    (hM : 1 ≤ M)
    (hMC : (sourceFixedCoercivity T F F₁ FInv)⁻¹ *
      operatorAmplitude T CF CF₁ CH CM scaledBoundaryOperatorAmplitude L ≤ M)
    (hMD : (sourceFixedCoercivity T F F₁ FInv)⁻¹*forcingAmplitude T CF CF₁ Cf ≤ M)
    (hR : 2*M*(Rc+1) ≤ R)
    (hFb : ∀ n t x, ‖iteratedFDeriv ℝ n (F.field t : Space → Space →L[ℝ] Space) x‖ ≤ CF*majorant Rc
        0 n)
    (hF₁b : ∀ n t x, ‖iteratedFDeriv ℝ n (F₁.field t : Space → Space →L[ℝ] Space) x‖ ≤ CF₁*majorant
        Rc 0 n)
    (hHb : ∀ n t x, ‖iteratedFDeriv ℝ n (H.field t : Space → Space →L[ℝ] Space) x‖ ≤ CH*majorant Rc
        0 n)
    (hMb : ∀ n x, ‖iteratedFDeriv ℝ n (M0.field : Space → Space →L[ℝ] Space) x‖ ≤ CM*majorant Rc 0
        n)
    (d : ℕ) (hfb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeTranslation T b f) a‖ ≤
        Cf*majorant R d n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (fun b : Space => timeSolenoidalTranslation T b
      (sourceCoordinateSolver T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r hBe hBc hL hr hrquarter
        hext hcore hInv hF K hK hF0 hH hsmall f)) a‖ ≤ majorant R (d+1) n := by
  have hRc0 : 0 ≤ Rc := (by norm_num : (0 : ℝ) ≤ 1024).trans hRc
  have hFr : ContDiff ℝ ∞ (fun b : Space => translatePath T b (operatorPath T F.field)) := by
    simpa only [translatePath_operatorPath] using operatorPathTranslation_contDiff T F
  have hF₁r : ContDiff ℝ ∞ (fun b : Space => translatePath T b (operatorPath T F₁.field)) := by
    simpa only [translatePath_operatorPath] using operatorPathTranslation_contDiff T F₁
  have hHr : ContDiff ℝ ∞ (fun b : Space => translatePath T b (operatorPath T H.field)) := by
    simpa only [translatePath_operatorPath] using operatorPathTranslation_contDiff T H
  have hMr : ContDiff ℝ ∞ (fun b : Space => translateOperator b (multiplier M0.field)) := by
    simpa only [translateOperator_multiplier] using multiplierTranslation_contDiff M0
  have hAr : ContDiff ℝ ∞ (fun b : Space => translateOperator b (boundaryOperator (scaledCutoff ℓ
      hℓ))) := by
    simpa only [translateOperator_boundary] using scaledBoundaryOperator_contDiff ℓ hℓ
  have hAb (k b) : ‖iteratedFDeriv ℝ k
      (fun y : Space => translateOperator y (boundaryOperator (scaledCutoff ℓ hℓ))) b‖ ≤
      scaledBoundaryOperatorAmplitude*majorant Rc 0 k := by
    have h := scaledBoundaryOperator_gevrey ℓ hℓ hℓ1 k b
    apply (show ‖iteratedFDeriv ℝ k
      (fun y : Space => translateOperator y (boundaryOperator (scaledCutoff ℓ hℓ))) b‖ ≤
      scaledBoundaryOperatorAmplitude*majorant 1024 0 k by
        simpa only [translateOperator_boundary] using h).trans
    exact mul_le_mul_of_nonneg_left (majorant_radius_mono 1024 Rc (by norm_num) hRc 0 k)
      scaledBoundaryOperatorAmplitude_nonneg
  exact solution_translation_gevrey T hT (operatorPath T F.field) (operatorPath T F₁.field)
    (operatorPath T H.field) (multiplier M0.field) (boundaryOperator (scaledCutoff ℓ hℓ)) L
    (sourceFixedCoercivity T F F₁ FInv) (sourceFixedCoercivity_pos T hT F F₁ FInv)
    (sourceFixedForm_coercive T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r hBe hBc hL hr hrquarter
      hext hcore hInv hF K hK hF0 hH hsmall)
    hFr hF₁r hHr hMr hAr f hf Rc R M CF CF₁ CH CM scaledBoundaryOperatorAmplitude Cf
    hRc0 hCF hCF₁ hCH hCM scaledBoundaryOperatorAmplitude_nonneg hCf hM hMC hMD hR
    (translatedPath_bound T F Rc CF hRc0 hCF hFb)
    (translatedPath_bound T F₁ Rc CF₁ hRc0 hCF₁ hF₁b)
    (translatedPath_bound T H Rc CH hRc0 hCH hHb)
    (translatedMultiplier_bound M0 Rc CM hRc0 hCM hMb) hAb d hfb n a

end EulerMeanSourceGevrey

end
end

end

section

/-!
# Concrete source estimates for the strong mean inverse

The literal source coefficient bounds and actual forcing orbit bounds imply
the successive coordinate and physical-field factorial estimates. Coercivity,
boundary cutoff calculus, Gram inversion, and time reconstruction are all
proved constructions used by this theorem.
-/

section

/-!
# The actual source mean inverse preserves fixed Sobolev word estimates

The input and output are literal ordered spatial derivative blocks of actual
L² translation orbits. Taking q=6 gives the fixed-H6 endpoint without spending
six additional factorial shifts. All constants are independent of the grade.
-/

@[expose] public section

noncomputable section

namespace EulerMeanSourceSobolev

open MeasureTheory Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanCoefficients EulerMeanBoundary EulerMeanHarmonic EulerMeanSourceInverse
  EulerMeanVariationalInverse EulerMeanFixedSpaceInverse EulerMeanSourceFixedInverse
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanTranslatedGevrey
  EulerTimeLp EulerCoerciveProjection EulerGevrey EulerOperatorGevreyCalculus
  EulerParameterWordGevrey EulerMeanSourceGevrey EulerMeanFixedSobolevGevrey
open scoped NNReal ContDiff

variable {ι : Type*} [Fintype ι]
  (directions : ι → Space) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (T : ℝ) (hT : 0 ≤ T) (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1)
  (F F₁ H : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (M0 : BoundedSmoothField (Space →L[ℝ] Space)) (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  (Be Bc L r : ℝ) (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc)
  (hL : boundaryLocalizationC1 * Bc ≤ L) (hr : 0 ≤ r) (hrquarter : r ≤ 1 / 4)
  (hext : ∀ x, r ≤ ‖ℓ • x‖ → ∀ v : Space, -Be * ‖v‖ ^ 2 ≤ ⟪M0.field x v, v⟫_ℝ)
  (hcore : ∀ x, ‖ℓ • x‖ < r → ∀ v : Space, -Bc * ‖v‖ ^ 2 ≤ ⟪M0.field x v, v⟫_ℝ)
  (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (operatorPath T F.field t x) = x)
  (hF : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (EulerVolterraConvolution.extendPath T hT (operatorPath T F.field))
      (operatorPath T F₁.field t) (Icc (0 : ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K)
  (hF0 : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
  (hH : ∀ t x v, ⟪H.field t x v, v⟫_ℝ ≤ K * ‖v‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) + Be * T + boundaryLocalizationC2 * Bc * r ^ 3 * T ≤ 1 / 2)

include hd hℓ1 in
/-- Actual fixed-Hq source estimate, at one unchanged external radius and
with one shift. All form coercivity and cutoff bounds are already proved. -/
theorem sourceCoordinateSolver_translation_block_gevrey
    (f : TimeLp T L2) (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f))
    (Rc R M CF CF₁ CH CM Cf : ℝ) (hRc : 1024 ≤ Rc)
    (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCH : 0 ≤ CH) (hCM : 0 ≤ CM) (hCf : 0 ≤ Cf)
    (hM : 1 ≤ M)
    (hMC : sobolevInverseCost (sourceFixedCoercivity T F F₁ FInv)⁻¹
      (operatorBlockAmplitude ι q T Rc CF CF₁ CH CM scaledBoundaryOperatorAmplitude L) q *
      operatorBlockAmplitude ι q T Rc CF CF₁ CH CM scaledBoundaryOperatorAmplitude L ≤ M)
    (hMD : sobolevInverseCost (sourceFixedCoercivity T F F₁ FInv)⁻¹
      (operatorBlockAmplitude ι q T Rc CF CF₁ CH CM scaledBoundaryOperatorAmplitude L) q *
      forcingBlockAmplitude ι q T Rc CF CF₁ Cf ≤ M)
    (hR : 2*M*(sobolevCoefficientRadius ι Rc+1) ≤ R)
    (hFb : ∀ n t x, ‖iteratedFDeriv ℝ n (F.field t : Space → Space →L[ℝ] Space) x‖ ≤ CF*majorant Rc
        0 n)
    (hF₁b : ∀ n t x, ‖iteratedFDeriv ℝ n (F₁.field t : Space → Space →L[ℝ] Space) x‖ ≤ CF₁*majorant
        Rc 0 n)
    (hHb : ∀ n t x, ‖iteratedFDeriv ℝ n (H.field t : Space → Space →L[ℝ] Space) x‖ ≤ CH*majorant Rc
        0 n)
    (hMb : ∀ n x, ‖iteratedFDeriv ℝ n (M0.field : Space → Space →L[ℝ] Space) x‖ ≤ CM*majorant Rc 0
        n)
    (d : ℕ) (hfb : ∀ n a, block directions q (fun b : Space => timeTranslation T b f) n a ≤
        Cf*majorant R d n)
    (n : ℕ) (a : Space) :
    block directions q (fun b : Space => timeSolenoidalTranslation T b
      (sourceCoordinateSolver T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r hBe hBc hL hr hrquarter
        hext hcore hInv hF K hK hF0 hH hsmall f)) n a ≤ majorant R (d+1) n := by
  have hRc0 : 0 ≤ Rc := (by norm_num : (0 : ℝ) ≤ 1024).trans hRc
  have hFr : ContDiff ℝ ∞ (fun b : Space => translatePath T b (operatorPath T F.field)) := by
    simpa only [translatePath_operatorPath] using operatorPathTranslation_contDiff T F
  have hF₁r : ContDiff ℝ ∞ (fun b : Space => translatePath T b (operatorPath T F₁.field)) := by
    simpa only [translatePath_operatorPath] using operatorPathTranslation_contDiff T F₁
  have hHr : ContDiff ℝ ∞ (fun b : Space => translatePath T b (operatorPath T H.field)) := by
    simpa only [translatePath_operatorPath] using operatorPathTranslation_contDiff T H
  have hMr : ContDiff ℝ ∞ (fun b : Space => translateOperator b (multiplier M0.field)) := by
    simpa only [translateOperator_multiplier] using multiplierTranslation_contDiff M0
  have hAr : ContDiff ℝ ∞ (fun b : Space => translateOperator b (boundaryOperator (scaledCutoff ℓ
      hℓ))) := by
    simpa only [translateOperator_boundary] using scaledBoundaryOperator_contDiff ℓ hℓ
  have hAb (k b) : ‖iteratedFDeriv ℝ k
      (fun y : Space => translateOperator y (boundaryOperator (scaledCutoff ℓ hℓ))) b‖ ≤
      scaledBoundaryOperatorAmplitude*majorant Rc 0 k := by
    have h := scaledBoundaryOperator_gevrey ℓ hℓ hℓ1 k b
    apply (show ‖iteratedFDeriv ℝ k
      (fun y : Space => translateOperator y (boundaryOperator (scaledCutoff ℓ hℓ))) b‖ ≤
      scaledBoundaryOperatorAmplitude*majorant 1024 0 k by
        simpa only [translateOperator_boundary] using h).trans
    exact mul_le_mul_of_nonneg_left (majorant_radius_mono 1024 Rc (by norm_num) hRc 0 k)
      scaledBoundaryOperatorAmplitude_nonneg
  exact solution_translation_block_gevrey directions hd q T hT (operatorPath T F.field)
      (operatorPath T F₁.field)
    (operatorPath T H.field) (multiplier M0.field) (boundaryOperator (scaledCutoff ℓ hℓ)) L
    (sourceFixedCoercivity T F F₁ FInv) (sourceFixedCoercivity_pos T hT F F₁ FInv)
    (sourceFixedForm_coercive T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r hBe hBc hL hr hrquarter
      hext hcore hInv hF K hK hF0 hH hsmall)
    hFr hF₁r hHr hMr hAr f hf Rc R M CF CF₁ CH CM scaledBoundaryOperatorAmplitude Cf
    hRc0 hCF hCF₁ hCH hCM scaledBoundaryOperatorAmplitude_nonneg hCf hM hMC hMD hR
    (translatedPath_bound T F Rc CF hRc0 hCF hFb)
    (translatedPath_bound T F₁ Rc CF₁ hRc0 hCF₁ hF₁b)
    (translatedPath_bound T H Rc CH hRc0 hCH hHb)
    (translatedMultiplier_bound M0 Rc CM hRc0 hCM hMb) hAb d hfb n a

end EulerMeanSourceSobolev

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanSourceStrongSobolev

open MeasureTheory Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanCoefficients EulerMeanBoundary EulerMeanHarmonic EulerMeanSourceInverse
  EulerMeanVariationalInverse EulerMeanSourceFixedInverse
  EulerMeanSourceSpatialRegularity EulerMeanTimeTranslation EulerMeanOperatorTranslation
  EulerMeanTimeContinuousTranslation EulerMeanTranslatedGevrey EulerTimeLp EulerVolterraConvolution
   EulerGevrey EulerParameterWordGevrey
  EulerMeanSourceSobolev EulerMeanFixedSobolevGevrey
open scoped NNReal ContDiff

variable {ι : Type*} [Fintype ι]
  (directions : ι → Space) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (T : ℝ) (hT : 0 ≤ T) (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1)
  (F F₁ H : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (M0 : BoundedSmoothField (Space →L[ℝ] Space)) (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  (Be Bc L r : ℝ) (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc)
  (hL : boundaryLocalizationC1 * Bc ≤ L) (hr : 0 ≤ r) (hrquarter : r ≤ 1 / 4)
  (hext : ∀ x, r ≤ ‖ℓ • x‖ → ∀ v : Space, -Be * ‖v‖ ^ 2 ≤ ⟪M0.field x v, v⟫_ℝ)
  (hcore : ∀ x, ‖ℓ • x‖ < r → ∀ v : Space, -Bc * ‖v‖ ^ 2 ≤ ⟪M0.field x v, v⟫_ℝ)
  (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (operatorPath T F.field t x) = x)
  (hF : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT (operatorPath T F.field))
      (operatorPath T F₁.field t) (Icc (0 : ℝ) T) t)
  (hRight : ∀ (t : Icc (0 : ℝ) T) (x : L2), operatorPath T F.field t (FInv t x) = x)
  (K : ℝ) (hK : 0 ≤ K)
  (hF0 : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
  (hH : ∀ t x v, ⟪H.field t x v, v⟫_ℝ ≤ K * ‖v‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) + Be * T + boundaryLocalizationC2 * Bc * r ^ 3 * T ≤ 1 / 2)
  (f : TimeLp T L2)
  (s : StrongMeanEvolution T hT FInv (operatorPath T F.field) (operatorPath T F₁.field)
    (boundaryOperator (scaledCutoff ℓ hℓ)) L
    (sourceMeanSolver T hT ℓ hℓ M0.field M0.field.continuous.aestronglyMeasurable
      ‖M0.field‖₊ M0.field.norm_coe_le_norm Be Bc L r hBe hBc hL hr hrquarter hext hcore
      FInv (operatorPath T H.field) K hK hF0 (operatorPath_quadratic_upper T H.field K hH) hsmall
          f) f)
  (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f))
  (Rc R M CF CF₁ CH CM Cf : ℝ) (hRc : 1024 ≤ Rc)
  (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCH : 0 ≤ CH) (hCM : 0 ≤ CM) (hCf : 0 ≤ Cf)
  (hM : 1 ≤ M)
  (hMC : sobolevInverseCost (sourceFixedCoercivity T F F₁ FInv)⁻¹
    (operatorBlockAmplitude ι q T Rc CF CF₁ CH CM scaledBoundaryOperatorAmplitude L) q *
    operatorBlockAmplitude ι q T Rc CF CF₁ CH CM scaledBoundaryOperatorAmplitude L ≤ M)
  (hMD : sobolevInverseCost (sourceFixedCoercivity T F F₁ FInv)⁻¹
    (operatorBlockAmplitude ι q T Rc CF CF₁ CH CM scaledBoundaryOperatorAmplitude L) q *
    forcingBlockAmplitude ι q T Rc CF CF₁ Cf ≤ M)
  (hR : 2 * M * (sobolevCoefficientRadius ι Rc + 1) ≤ R)
  (hFb : ∀ n t x, ‖iteratedFDeriv ℝ n (F.field t : Space → Space →L[ℝ] Space) x‖ ≤ CF * majorant Rc
      0
      n)
  (hF₁b : ∀ n t x, ‖iteratedFDeriv ℝ n (F₁.field t : Space → Space →L[ℝ] Space) x‖ ≤ CF₁ * majorant
      Rc 0 n)
  (hHb : ∀ n t x, ‖iteratedFDeriv ℝ n (H.field t : Space → Space →L[ℝ] Space) x‖ ≤ CH * majorant Rc
      0
      n)
  (hMb : ∀ n x, ‖iteratedFDeriv ℝ n (M0.field : Space → Space →L[ℝ] Space) x‖ ≤ CM * majorant Rc 0
      n)
  (d : ℕ)
  (hfb : ∀ n a, block directions q (fun b : Space => timeTranslation T b f) n a ≤ Cf * majorant R d
      n)

include hd hℓ1 hInv hF hRight hf hRc hCF hCF₁ hCH hCM hCf hM hMC hMD hR hFb hF₁b hHb hMb hfb

/-- The actual strong coordinate velocity inherits the bound of the actual source solver. -/
theorem velocity_translation_block_gevrey (n : ℕ) (a : Space) :
    block directions q (fun b : Space => timeSolenoidalTranslation T b s.velocityLp) n a ≤
      majorant R (d+1) n := by
  have heq := velocity_eq_sourceCoordinates T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r
    hBe hBc hL hr hrquarter hext hcore hInv hF hRight K hK hF0 hH hsmall f s
  have horbit := congrArg (fun v : TimeLp T solenoidalSpace =>
    fun b : Space => timeSolenoidalTranslation T b v) heq
  exact (congrArg (fun g : Space → TimeLp T solenoidalSpace => block directions q g n a)
      horbit).trans_le
    (sourceCoordinateSolver_translation_block_gevrey directions hd q T hT ℓ hℓ hℓ1 F F₁ H M0 FInv
        Be Bc L r
      hBe hBc hL hr hrquarter hext hcore hInv hF K hK hF0 hH hsmall f hf
      Rc R M CF CF₁ CH CM Cf hRc hCF hCF₁ hCH hCM hCf hM hMC hMD hR
      hFb hF₁b hHb hMb d hfb n a)

end EulerMeanSourceStrongSobolev

end
end

end

section

/-!
# Uniform-time factorial bounds for the strong mean solution

The proved H¹ reconstruction estimates the continuous coordinate velocity.
The actual continuous Gram inverse then controls acceleration and the
physical time derivative. All bounds concern genuine spatial derivatives.
-/

@[expose] public section

noncomputable section

namespace EulerMeanStrongContinuousGevrey

open EulerGevrey

/-- The fixed H¹ trace cost for unit velocity and acceleration jet amplitudes. -/
def coordinateTraceCost (T : ℝ) : ℝ := T⁻¹*Real.sqrt T+2*Real.sqrt T

theorem coordinateTraceCost_nonneg (T : ℝ) (hT : 0 ≤ T) : 0 ≤ coordinateTraceCost T := by
  unfold coordinateTraceCost
  positivity

end EulerMeanStrongContinuousGevrey

namespace EulerMeanVariationalInverse.StrongMeanEvolution

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanTimeContinuousTranslation
  EulerMeanCoordinatePath EulerMeanContinuousAcceleration EulerMeanStrongGevrey
  EulerMeanStrongContinuousGevrey EulerOperatorGevreyCalculus EulerTimeLpGramGevrey
  EulerTimeLp EulerGevrey
open scoped ContDiff

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)
  (c : ℝ) (hc : 0 < c)
  (hLower : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖solenoidalFrame T F t v‖ ^ 2)
  (fC : C(Icc (0 : ℝ) T, L2))

/-- Actual continuous acceleration and B_t obey uniform-time spatial
factorial bounds, with a fixed H¹ trace cost and one further Gram-inverse shift. -/
theorem continuous_strong_spatial_gevrey (hTpos : 0 < T)
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.velocityLp))
    (ha : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.acceleration))
    (hfC : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a fC))
    (Rc R CF CF₁ Cf : ℝ) (hRc : 0 ≤ Rc) (hR : 1 ≤ R) (hRcR : Rc ≤ R)
    (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCf : 0 ≤ Cf)
    (hFb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant Rc 0
        n)
    (hF₁b : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁*majorant Rc
        0 n)
    (d : ℕ)
    (hvb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeSolenoidalTranslation T b s.velocityLp)
        a‖ ≤ majorant R (d+1) n)
    (hab : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => timeSolenoidalTranslation T b
        s.acceleration) a‖ ≤ majorant R (d+2) n)
    (hfb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => pathTranslation T b fC) a‖ ≤ Cf*majorant R
        d n)
    (hstrong : 2*gramCost c CF (3*CF*(Cf+6*CF₁*coordinateTraceCost T))*(Rc+1) ≤ R) :
    (∀ n a, ‖iteratedFDeriv ℝ n
      (fun b : Space => coordinatePathTranslation T b (s.classicalAcceleration c hc hLower fC)) a‖ ≤
        majorant R (d+3) n) ∧
    (∀ n a, ‖iteratedFDeriv ℝ n
      (fun b : Space => pathTranslation T b (s.classicalPhysicalDerivative c hc hLower fC)) a‖ ≤
        (3*(CF₁*coordinateTraceCost T+CF))*majorant R (d+3) n) := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have htrace := coordinateTraceCost_nonneg T hT
  have hvc := s.coordinateVelocityPath_translation_contDiff hTpos hv ha
  have hvcb (n : ℕ) (a : Space) :
      ‖iteratedFDeriv ℝ n (fun b : Space => coordinatePathTranslation T b s.coordinateVelocityPath)
          a‖ ≤
        coordinateTraceCost T*majorant R (d+2) n := by
    have h := s.coordinateVelocityPath_translation_gevrey hTpos hv ha R 1 1 hR0
      zero_le_one zero_le_one (d+2)
      (fun k x => by
        simpa only [one_mul, Nat.add_assoc] using
          (hvb k x).trans (majorant_shift_mono R hR (d+1) k))
      (fun k x => by simpa only [one_mul] using hab k x) n a
    simpa only [coordinateTraceCost, mul_one] using h
  have hfcb (n : ℕ) (a : Space) :
      ‖iteratedFDeriv ℝ n (fun b : Space => pathTranslation T b fC) a‖ ≤ Cf*majorant R (d+2) n := by
    apply (hfb n a).trans
    apply mul_le_mul_of_nonneg_left _ hCf
    simpa only [Nat.add_assoc] using
      (majorant_shift_mono R hR d n).trans (majorant_shift_mono R hR (d+1) n)
  have hac := s.classicalAcceleration_translation_contDiff c hc hLower fC hF hF₁ hvc hfC
  have hacb (n : ℕ) (a : Space) :
      ‖iteratedFDeriv ℝ n
        (fun b : Space => coordinatePathTranslation T b (s.classicalAcceleration c hc hLower fC))
            a‖ ≤
          majorant R (d+3) n := by
    have h := meanAccelerationPath_translation_gevrey T F F₁ c hc hLower s.coordinateVelocityPath fC
      hF hF₁ hvc hfC Rc R CF CF₁ Cf (coordinateTraceCost T) hRc hR0 hRcR
      hCF hCF₁ hCf htrace hstrong hFb hF₁b (d+2) hfcb hvcb n a
    simpa only [Nat.add_assoc, meanAccelerationPath, classicalAcceleration] using h
  refine ⟨hacb, ?_⟩
  have hFbR (n : ℕ) (a : Space) :
      ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant R 0 n :=
    (hFb n a).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc R hRc hRcR 0 n) hCF)
  have hF₁bR (n : ℕ) (a : Space) :
      ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁*majorant R 0 n :=
    (hF₁b n a).trans (mul_le_mul_of_nonneg_left (majorant_radius_mono Rc R hRc hRcR 0 n) hCF₁)
  intro n a
  have h := s.classicalPhysicalDerivative_translation_gevrey c hc hLower fC hF hF₁ hvc hac
    R CF CF₁ (coordinateTraceCost T) 1 hR0 hCF hCF₁ htrace zero_le_one (d+3) hFbR hF₁bR
    (fun k x => (hvcb k x).trans (mul_le_mul_of_nonneg_left
      (by simpa only [Nat.add_assoc] using majorant_shift_mono R hR (d+2) k) htrace))
    (fun k x => by simpa only [one_mul] using hacb k x) n a
  simpa only [mul_one] using h

end EulerMeanVariationalInverse.StrongMeanEvolution

end
end

end

section

/-! The genuine mean acceleration estimate in fixed-Hq external word blocks. -/

@[expose] public section

noncomputable section

namespace EulerMeanAccelerationSobolev

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerMeanSolenoidal EulerMeanTimeTranslation EulerMeanOperatorTranslation
  EulerMeanVariationalInverse EulerMeanGramTranslation EulerMeanAccelerationGevrey
  EulerTimeLp EulerVolterraConvolution EulerMeanFixedCoefficientRegularity
  EulerMeanFixedCoefficientGevrey EulerTimeLpGramSobolev EulerTimeLpAccelerationSobolev
  EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

/-- Cache the standard `NormedAddCommGroup solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanAccelerationSobolev1 : NormedAddCommGroup solenoidalSpace := inferInstance
/-- Cache the standard `InnerProductSpace ℝ solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanAccelerationSobolev2 : InnerProductSpace ℝ solenoidalSpace := inferInstance
/-- Cache the standard `NormedAddCommGroup (solenoidalSpace →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanAccelerationSobolev3 : NormedAddCommGroup (solenoidalSpace →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (solenoidalSpace →L[ℝ] L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanAccelerationSobolev4 : NormedSpace ℝ (solenoidalSpace →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (L2 →L[ℝ] L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanAccelerationSobolev5 : NormedAddCommGroup (L2 →L[ℝ] L2) := inferInstance
/-- Cache the standard `NormedSpace ℝ (L2 →L[ℝ] L2)` instance to shorten typeclass synthesis. -/
local instance instMeanAccelerationSobolev6 : NormedSpace ℝ (L2 →L[ℝ] L2) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanAccelerationSobolev7 (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T, L2 →L[ℝ]
    L2) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanAccelerationSobolev8 (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)
    := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T, solenoidalSpace →L[ℝ] L2)` instance
to shorten typeclass synthesis. -/
local instance instMeanAccelerationSobolev9 (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T,
    solenoidalSpace →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T, solenoidalSpace →L[ℝ] L2)` instance to
shorten typeclass synthesis. -/
local instance instMeanAccelerationSobolev10 (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,
    solenoidalSpace →L[ℝ] L2) :=
    inferInstance

variable {ι : Type*} [Fintype ι]

/-- The actual acceleration of the constructed mean field spends one shift
relative to its input blocks, at the same fixed Sobolev order and radius. -/
theorem meanAcceleration_translation_block_gevrey
    (directions : ι → Space) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (T : ℝ) (hT : 0 ≤ T) (F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
    (c : ℝ) (hc : 0 < c) (hLower : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖solenoidalFrame T F t v‖ ^ 2)
    (v : TimeLp T solenoidalSpace) (f : TimeLp T L2)
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a v))
    (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f))
    (Rc R CF CF₁ Cf Cv : ℝ) (hRc : 0 ≤ Rc) (hRcR : sobolevCoefficientRadius ι Rc ≤ R)
    (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCf : 0 ≤ Cf) (hCv : 0 ≤ Cv)
    (hstrong : 2*gramBlockCost ι q c Rc CF (accelerationBlockAmplitude ι q Rc CF CF₁ Cf Cv) *
      (sobolevCoefficientRadius ι Rc+1) ≤ R)
    (hFb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant Rc 0
        n)
    (hF₁b : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁*majorant Rc
        0 n)
    (d : ℕ)
    (hfb : ∀ n a, block directions q (fun b : Space => timeTranslation T b f) n a ≤ Cf*majorant R d
        n)
    (hvb : ∀ n a, block directions q (fun b : Space => timeSolenoidalTranslation T b v) n a ≤
        Cv*majorant R d n)
    (n : ℕ) (a : Space) :
    block directions q (fun b : Space =>
      timeSolenoidalTranslation T b (meanAcceleration T hT F F₁ c hc hLower v f)) n a ≤
        majorant R (d+1) n := by
  let Q := fun b : Space => solenoidalFrame T (translatePath T b F)
  let Q₁ := fun b : Space => solenoidalFrame T (translatePath T b F₁)
  have hQ : ContDiff ℝ ∞ Q := contDiff_solenoidalFrame T (fun b => translatePath T b F) hF
  have hQ₁ : ContDiff ℝ ∞ Q₁ := contDiff_solenoidalFrame T (fun b => translatePath T b F₁) hF₁
  have hbQ : ∀ k b, ‖iteratedFDeriv ℝ k Q b‖ ≤ CF*majorant Rc 0 k :=
    solenoidalFrame_bound T (fun b => translatePath T b F) hF Rc CF hRc hCF 0 hFb
  have hbQ₁ : ∀ k b, ‖iteratedFDeriv ℝ k Q₁ b‖ ≤ CF₁*majorant Rc 0 k :=
    solenoidalFrame_bound T (fun b => translatePath T b F₁) hF₁ Rc CF₁ hRc hCF₁ 0 hF₁b
  have hs := solution_block_bound directions hd q T hT Q Q₁ c hc
    (translatedFrame_lower T F c hLower) (fun b => timeTranslation T b f)
    (fun b => timeSolenoidalTranslation T b v) hQ hQ₁ hf hv
    Rc R CF CF₁ Cf Cv hRc hRcR hCF hCF₁ hCf hCv hstrong hbQ hbQ₁ d hfb hvb n a
  exact (congrArg (fun g : Space → TimeLp T solenoidalSpace => block directions q g n a)
    (meanAcceleration_orbit_eq T hT F F₁ c hc hLower v f)).trans_le hs

end EulerMeanAccelerationSobolev

end
end

end

section

/-!
# Actual spatial orbits of continuous mean acceleration

The ordinary solenoidal Gram inverse commutes with simultaneous translation
of its data. This identifies the parameterized continuous solve with the
genuine spatial orbit of the acceleration, including endpoint times.
-/

@[expose] public section

noncomputable section

namespace EulerMeanContinuousSobolev

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanVariationalInverse
  EulerMeanTimeContinuousTranslation EulerMeanCoordinatePath EulerMeanGramTranslation
  EulerMeanFixedCoefficientRegularity EulerMeanFixedCoefficientGevrey
  EulerContinuousGramAcceleration
  EulerTimeLpGramGevrey EulerGevrey EulerMeanContinuousAcceleration
  EulerParameterWordGevrey EulerTimeLpGramSobolev
open scoped ContDiff

/-- Cache the standard `NormedAddCommGroup solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanContinuousSobolev1 : NormedAddCommGroup solenoidalSpace := inferInstance
/-- Cache the standard `InnerProductSpace ℝ solenoidalSpace` instance to shorten typeclass
synthesis. -/
local instance instMeanContinuousSobolev2 : InnerProductSpace ℝ solenoidalSpace := inferInstance
/-- Cache the standard `NormedAddCommGroup (solenoidalSpace →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanContinuousSobolev3 : NormedAddCommGroup (solenoidalSpace →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (solenoidalSpace →L[ℝ] L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanContinuousSobolev4 : NormedSpace ℝ (solenoidalSpace →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (L2 →L[ℝ] L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanContinuousSobolev5 : NormedAddCommGroup (L2 →L[ℝ] L2) := inferInstance
/-- Cache the standard `NormedSpace ℝ (L2 →L[ℝ] L2)` instance to shorten typeclass synthesis. -/
local instance instMeanContinuousSobolev6 : NormedSpace ℝ (L2 →L[ℝ] L2) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,L2 →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanContinuousSobolev7 (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T,L2 →L[ℝ] L2)
    := inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,L2 →L[ℝ] L2)` instance to shorten
typeclass synthesis. -/
local instance instMeanContinuousSobolev8 (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,L2 →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,solenoidalSpace →L[ℝ] L2)` instance
to shorten typeclass synthesis. -/
local instance instMeanContinuousSobolev9 (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ)
    T,solenoidalSpace →L[ℝ] L2) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,solenoidalSpace →L[ℝ] L2)` instance to
shorten typeclass synthesis. -/
local instance instMeanContinuousSobolev10 (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,solenoidalSpace
    →L[ℝ] L2) :=
    inferInstance

variable (T : ℝ) (F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  (c : ℝ) (hc : 0 < c)
  (hLower : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖solenoidalFrame T F t v‖ ^ 2)
  (v : C(Icc (0 : ℝ) T, solenoidalSpace)) (f : C(Icc (0 : ℝ) T, L2))

theorem meanAccelerationPath_translation_block_gevrey
    {ι : Type*} [Fintype ι] (directions : ι → Space) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ ∞ (fun a : Space => coordinatePathTranslation T a v))
    (hf : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a f))
    (Rc R CF CF₁ Cf Cv : ℝ) (hRc : 0 ≤ Rc) (hRcR : sobolevCoefficientRadius ι Rc ≤ R)
    (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCf : 0 ≤ Cf) (hCv : 0 ≤ Cv)
    (hstrong : 2*gramBlockCost ι q c Rc CF (accelerationBlockAmplitude ι q Rc CF CF₁ Cf
        Cv)*(sobolevCoefficientRadius ι Rc+1) ≤ R)
    (hFb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant Rc 0
        n)
    (hF₁b : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁*majorant Rc
        0 n)
    (d : ℕ)
    (hfb : ∀ n a, block directions q (fun b : Space => pathTranslation T b f) n a ≤ Cf*majorant R d
        n)
    (hvb : ∀ n a, block directions q (fun b : Space => coordinatePathTranslation T b v) n a ≤
        Cv*majorant R d n)
    (n : ℕ) (a : Space) :
    block directions q (fun b : Space =>
      coordinatePathTranslation T b (meanAccelerationPath T F F₁ c hc hLower v f)) n a ≤
      majorant R (d+1) n := by
  have hs := EulerContinuousAccelerationSobolev.acceleration_block_bound directions hd q T
    (fun a : Space => solenoidalFrame T (translatePath T a F))
    (fun a : Space => solenoidalFrame T (translatePath T a F₁))
    c hc (translatedFrame_lower T F c hLower)
    (fun a : Space => coordinatePathTranslation T a v) (fun a : Space => pathTranslation T a f)
    (contDiff_solenoidalFrame T (fun a => translatePath T a F) hF)
    (contDiff_solenoidalFrame T (fun a => translatePath T a F₁) hF₁) hv hf
    Rc R CF CF₁ Cf Cv hRc hRcR hCF hCF₁ hCf hCv hstrong
    (solenoidalFrame_bound T (fun b => translatePath T b F) hF Rc CF hRc hCF 0 hFb)
    (solenoidalFrame_bound T (fun b => translatePath T b F₁) hF₁ Rc CF₁ hRc hCF₁ 0 hF₁b)
    d hfb hvb n a
  exact (congrArg (fun g : Space → C(Icc (0 : ℝ) T,solenoidalSpace) => block directions q g n a)
    (meanAccelerationPath_orbit_eq T F F₁ c hc hLower v f)).trans_le hs

end EulerMeanContinuousSobolev

end
end

end

section

/-!
# Concrete source estimates for the strong mean inverse

The literal source coefficient bounds and actual forcing orbit bounds imply
the successive coordinate and physical-field factorial estimates. Coercivity,
boundary cutoff calculus, Gram inversion, and time reconstruction are all
proved constructions used by this theorem.
-/

section

/-!
# Fixed-Hq bounds for the actual classical mean field and its time derivative

Starting with the proved weak inverse's one-shift coordinate bound, this
result gives the actual continuous physical field at shift d+2 and its true
within-time derivative at shift d+3. All use the identical external radius.
-/

@[expose] public section

noncomputable section

namespace EulerMeanVariationalInverse.StrongMeanEvolution

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanTimeContinuousTranslation
  EulerMeanCoordinatePath EulerMeanContinuousAcceleration EulerMeanContinuousSobolev
  EulerMeanTimeSobolev EulerMeanAccelerationSobolev EulerMeanGramTranslation
  EulerMeanStrongGevrey EulerMeanStrongContinuousGevrey EulerTimeLp EulerVolterraConvolution
  EulerTimeLpGramSobolev EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)

/-- The true field and time derivative have same-radius fixed-Sobolev bounds.
The time derivative is proved on [0,T], including within-set endpoints. -/
theorem strong_time_block_bounds {ι : Type*} [Fintype ι]
    (directions : ι → Space) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (hTpos : 0 < T) (c : ℝ) (hc : 0 < c)
    (hLower : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖solenoidalFrame T F t v‖ ^ 2)
    (fC : C(Icc (0 : ℝ) T, L2))
    (hRep : (f : ℝ → L2) =ᵐ[timeMeasure T] extendPath T hT fC)
    (hFTime : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT F) (F₁ t) (Icc (0 : ℝ) T) t)
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.velocityLp))
    (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f))
    (hfC : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a fC))
    (Rc R CF CF₁ Cf : ℝ) (hRc : 0 ≤ Rc) (hR : 1 ≤ R)
    (hRcR : sobolevCoefficientRadius ι Rc ≤ R)
    (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCf : 0 ≤ Cf)
    (hstrong : 2*gramBlockCost ι q c Rc CF (accelerationBlockAmplitude ι q Rc CF CF₁ Cf 1) *
      (sobolevCoefficientRadius ι Rc+1) ≤ R)
    (hstrongC : 2*gramBlockCost ι q c Rc CF
      (accelerationBlockAmplitude ι q Rc CF CF₁ Cf (coordinateTraceCost T)) *
      (sobolevCoefficientRadius ι Rc+1) ≤ R)
    (hFb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant Rc 0
        n)
    (hF₁b : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁*majorant Rc
        0 n)
    (d : ℕ)
    (hfb : ∀ n a, block directions q (fun b : Space => timeTranslation T b f) n a ≤ Cf*majorant R d
        n)
    (hfCb : ∀ n a, block directions q (fun b : Space => pathTranslation T b fC) n a ≤ Cf*majorant R
        d n)
    (hvb : ∀ n a, block directions q (fun b : Space => timeSolenoidalTranslation T b s.velocityLp)
        n a ≤ majorant R (d+1) n) :
    (∀ n a, block directions q (fun b : Space => pathTranslation T b s.continuousVelocity) n a ≤
      (3*sobolevCoefficientAmplitude ι q Rc CF*coordinateTraceCost T)*majorant R (d+2) n) ∧
    (∀ n a, block directions q
      (fun b : Space => pathTranslation T b (s.classicalPhysicalDerivative c hc hLower fC)) n a ≤
      (3*(sobolevCoefficientAmplitude ι q Rc CF₁*coordinateTraceCost T +
        sobolevCoefficientAmplitude ι q Rc CF))*majorant R (d+3) n) ∧
    (∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT s.continuousVelocity)
      (s.classicalPhysicalDerivative c hc hLower fC t) (Icc (0 : ℝ) T) t) := by
  have htrace : 0 ≤ coordinateTraceCost T := coordinateTraceCost_nonneg T hT
  have hf1 (n a) : block directions q (fun b : Space => timeTranslation T b f) n a ≤
      Cf*majorant R (d+1) n :=
    (hfb n a).trans (mul_le_mul_of_nonneg_left (majorant_shift_mono R hR d n) hCf)
  have hv1 (n a) : block directions q (fun b : Space => timeSolenoidalTranslation T b s.velocityLp)
      n a ≤
      1*majorant R (d+1) n := by simpa only [one_mul] using hvb n a
  have hat (n a) : block directions q (fun b : Space => timeSolenoidalTranslation T b
      s.acceleration) n a ≤
      majorant R (d+2) n := by
    refine (congrArg (fun v : TimeLp T solenoidalSpace =>
      block directions q (fun b : Space => timeSolenoidalTranslation T b v) n a)
      (s.acceleration_eq_meanAcceleration c hc hLower)).trans_le ?_
    simpa only [Nat.add_assoc] using meanAcceleration_translation_block_gevrey directions hd q
      T hT F F₁ c hc hLower s.velocityLp f hF hF₁ hv hf Rc R CF CF₁ Cf 1
      hRc hRcR hCF hCF₁ hCf zero_le_one hstrong hFb hF₁b (d+1) hf1 hv1 n a
  have ha := s.acceleration_orbit_contDiff c hc hLower hF hF₁ hv hf
  have hv2 (n a) : block directions q (fun b : Space => timeSolenoidalTranslation T b s.velocityLp)
      n a ≤
      1*majorant R (d+2) n := by
    simpa only [one_mul] using (hvb n a).trans (majorant_shift_mono R hR (d+1) n)
  have hat1 (n a) : block directions q (fun b : Space => timeSolenoidalTranslation T b
      s.acceleration) n a ≤
      1*majorant R (d+2) n := by simpa only [one_mul] using hat n a
  have hvc := s.coordinateVelocityPath_translation_contDiff hTpos hv ha
  have hvcb (n a) : block directions q (fun b : Space => coordinatePathTranslation T b
      s.coordinateVelocityPath) n a ≤
      coordinateTraceCost T*majorant R (d+2) n := by
    simpa only [mul_one, coordinateTraceCost] using
      s.coordinateVelocityPath_translation_block_gevrey directions q hTpos hv ha R 1 1 (d+2) hv2
          hat1 n a
  have hfc2 (n a) : block directions q (fun b : Space => pathTranslation T b fC) n a ≤
      Cf*majorant R (d+2) n :=
    (hfCb n a).trans (mul_le_mul_of_nonneg_left (majorant_mono_shift R hR d (d+2) n (by omega)) hCf)
  have hac (n a) : block directions q
      (fun b : Space => coordinatePathTranslation T b (s.classicalAcceleration c hc hLower fC)) n a
          ≤
        majorant R (d+3) n := by
    simpa only [Nat.add_assoc, meanAccelerationPath, classicalAcceleration] using
        meanAccelerationPath_translation_block_gevrey
      T F F₁ c hc hLower s.coordinateVelocityPath fC directions hd q hF hF₁ hvc hfC
      Rc R CF CF₁ Cf (coordinateTraceCost T) hRc hRcR hCF hCF₁ hCf htrace
      hstrongC hFb hF₁b (d+2) hfc2 hvcb n a
  have hacs := s.classicalAcceleration_translation_contDiff c hc hLower fC hF hF₁ hvc hfC
  have hvc3 (n a) : block directions q (fun b : Space => coordinatePathTranslation T b
      s.coordinateVelocityPath) n a ≤
      coordinateTraceCost T*majorant R (d+3) n :=
    (hvcb n a).trans (mul_le_mul_of_nonneg_left (majorant_shift_mono R hR (d+2) n) htrace)
  have hac1 (n a) : block directions q
      (fun b : Space => coordinatePathTranslation T b (s.classicalAcceleration c hc hLower fC)) n a
          ≤
        1*majorant R (d+3) n := by simpa only [one_mul] using hac n a
  refine ⟨?_, ?_, s.continuousVelocity_hasDerivWithinAt c hc hLower fC hTpos hRep hFTime⟩
  · intro n a
    rw [s.continuousVelocity_eq_frame hTpos hFTime]
    exact framePathApply_translation_block_gevrey directions hd q T F s.coordinateVelocityPath
      hF hvc Rc R CF (coordinateTraceCost T) hRc hRcR hCF htrace (d+2) hFb hvcb n a
  · intro n a
    simpa only [mul_one] using s.classicalPhysicalDerivative_translation_block_gevrey
      directions hd q c hc hLower fC hF hF₁ hvc hacs Rc R CF CF₁ (coordinateTraceCost T) 1
      hRc hRcR hCF hCF₁ htrace zero_le_one (d+3) hFb hF₁b hvc3 hac1 n a

end EulerMeanVariationalInverse.StrongMeanEvolution

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanSourceTimeSobolev

open MeasureTheory Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanCoefficients EulerMeanBoundary EulerMeanHarmonic EulerMeanSourceInverse
  EulerMeanVariationalInverse EulerMeanSourceFixedInverse EulerMeanSourceGevrey
  EulerMeanSourceSpatialRegularity EulerMeanTimeTranslation EulerMeanOperatorTranslation
  EulerMeanTimeContinuousTranslation EulerMeanTranslatedGevrey EulerTimeLp EulerVolterraConvolution
  EulerTimeLpGramGevrey EulerGevrey EulerParameterWordGevrey
   EulerMeanFixedSobolevGevrey EulerMeanSourceStrongSobolev
  EulerMeanStrongContinuousGevrey EulerTimeLpGramSobolev
open scoped NNReal ContDiff

variable {ι : Type*} [Fintype ι]
  (directions : ι → Space) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (T : ℝ) (hT : 0 ≤ T) (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1)
  (F F₁ H : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (M0 : BoundedSmoothField (Space →L[ℝ] Space)) (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  (Be Bc L r : ℝ) (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc)
  (hL : boundaryLocalizationC1 * Bc ≤ L) (hr : 0 ≤ r) (hrquarter : r ≤ 1 / 4)
  (hext : ∀ x, r ≤ ‖ℓ • x‖ → ∀ v : Space, -Be * ‖v‖ ^ 2 ≤ ⟪M0.field x v, v⟫_ℝ)
  (hcore : ∀ x, ‖ℓ • x‖ < r → ∀ v : Space, -Bc * ‖v‖ ^ 2 ≤ ⟪M0.field x v, v⟫_ℝ)
  (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (operatorPath T F.field t x) = x)
  (hF : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT (operatorPath T F.field))
      (operatorPath T F₁.field t) (Icc (0 : ℝ) T) t)
  (hRight : ∀ (t : Icc (0 : ℝ) T) (x : L2), operatorPath T F.field t (FInv t x) = x)
  (K : ℝ) (hK : 0 ≤ K)
  (hF0 : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
  (hH : ∀ t x v, ⟪H.field t x v, v⟫_ℝ ≤ K * ‖v‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) + Be * T + boundaryLocalizationC2 * Bc * r ^ 3 * T ≤ 1 / 2)
  (f : TimeLp T L2)
  (s : StrongMeanEvolution T hT FInv (operatorPath T F.field) (operatorPath T F₁.field)
    (boundaryOperator (scaledCutoff ℓ hℓ)) L
    (sourceMeanSolver T hT ℓ hℓ M0.field M0.field.continuous.aestronglyMeasurable
      ‖M0.field‖₊ M0.field.norm_coe_le_norm Be Bc L r hBe hBc hL hr hrquarter hext hcore
      FInv (operatorPath T H.field) K hK hF0 (operatorPath_quadratic_upper T H.field K hH) hsmall
          f) f)
  (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f))
  (Rc R M CF CF₁ CH CM Cf : ℝ) (hRc : 1024 ≤ Rc)
  (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCH : 0 ≤ CH) (hCM : 0 ≤ CM) (hCf : 0 ≤ Cf)
  (hM : 1 ≤ M)
  (hMC : sobolevInverseCost (sourceFixedCoercivity T F F₁ FInv)⁻¹
    (operatorBlockAmplitude ι q T Rc CF CF₁ CH CM scaledBoundaryOperatorAmplitude L) q *
    operatorBlockAmplitude ι q T Rc CF CF₁ CH CM scaledBoundaryOperatorAmplitude L ≤ M)
  (hMD : sobolevInverseCost (sourceFixedCoercivity T F F₁ FInv)⁻¹
    (operatorBlockAmplitude ι q T Rc CF CF₁ CH CM scaledBoundaryOperatorAmplitude L) q *
    forcingBlockAmplitude ι q T Rc CF CF₁ Cf ≤ M)
  (hR : 2 * M * (sobolevCoefficientRadius ι Rc + 1) ≤ R)
  (hFb : ∀ n t x, ‖iteratedFDeriv ℝ n (F.field t : Space → Space →L[ℝ] Space) x‖ ≤ CF * majorant Rc
      0
      n)
  (hF₁b : ∀ n t x, ‖iteratedFDeriv ℝ n (F₁.field t : Space → Space →L[ℝ] Space) x‖ ≤ CF₁ * majorant
      Rc 0 n)
  (hHb : ∀ n t x, ‖iteratedFDeriv ℝ n (H.field t : Space → Space →L[ℝ] Space) x‖ ≤ CH * majorant Rc
      0
      n)
  (hMb : ∀ n x, ‖iteratedFDeriv ℝ n (M0.field : Space → Space →L[ℝ] Space) x‖ ≤ CM * majorant Rc 0
      n)
  (d : ℕ)
  (hfb : ∀ n a, block directions q (fun b : Space => timeTranslation T b f) n a ≤ Cf * majorant R d
      n)

include hd hℓ1 hInv hF hRight hf hRc hCF hCF₁ hCH hCM hCf hM hMC hMD hR hFb hF₁b hHb hMb hfb

/-- Literal source data and fixed-Hq forcing bounds imply the actual classical
mean field at grade d+2 and its true time derivative at grade d+3, using the
identical external radius throughout. -/
theorem source_strong_time_block_bounds
    (hstrong : 2 * gramBlockCost ι q (meanFrameCoercivity T FInv) Rc CF
      (accelerationBlockAmplitude ι q Rc CF CF₁ Cf 1) *
 (sobolevCoefficientRadius ι Rc + 1) ≤ R)
    (hstrongC : 2 *
 gramBlockCost ι q (meanFrameCoercivity T FInv) Rc CF
      (accelerationBlockAmplitude ι q Rc CF CF₁ Cf (coordinateTraceCost T)) *
      (sobolevCoefficientRadius ι Rc + 1) ≤ R)
    (hTpos : 0 < T) (fC : C(Icc (0 : ℝ) T, L2))
    (hRep : (f : ℝ → L2) =ᵐ[timeMeasure T] extendPath T hT fC)
    (hfC : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a fC))
    (hfCb : ∀ n a, block directions q (fun b : Space => pathTranslation T b fC) n a ≤ Cf*majorant R
        d n) :
    (∀ n a, block directions q (fun b : Space => pathTranslation T b s.continuousVelocity) n a ≤
      (3*sobolevCoefficientAmplitude ι q Rc CF*coordinateTraceCost T)*majorant R (d+2) n) ∧
    (∀ n a, block directions q (fun b : Space => pathTranslation T b
      (s.classicalPhysicalDerivative (meanFrameCoercivity T FInv) (meanFrameCoercivity_pos T FInv)
        (solenoidalFrame_lower T FInv (operatorPath T F.field) hInv) fC)) n a ≤
      (3*(sobolevCoefficientAmplitude ι q Rc CF₁*coordinateTraceCost T +
        sobolevCoefficientAmplitude ι q Rc CF))*majorant R (d+3) n) ∧
    (∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT s.continuousVelocity)
      (s.classicalPhysicalDerivative (meanFrameCoercivity T FInv) (meanFrameCoercivity_pos T FInv)
        (solenoidalFrame_lower T FInv (operatorPath T F.field) hInv) fC t) (Icc (0 : ℝ) T) t) := by
  have hRc0 : 0 ≤ Rc := (by norm_num : (0 : ℝ) ≤ 1024).trans hRc
  have hrc : 0 ≤ sobolevCoefficientRadius ι Rc := sobolevCoefficientRadius_nonneg Rc hRc0
  have hR1 : 1 ≤ R := (radius_bounds hrc hM hR).1
  have hRcR : sobolevCoefficientRadius ι Rc ≤ R := (radius_bounds hrc hM hR).2
  have hFr : ContDiff ℝ ∞ (fun a : Space => translatePath T a (operatorPath T F.field)) := by
    simpa only [translatePath_operatorPath] using operatorPathTranslation_contDiff T F
  have hF₁r : ContDiff ℝ ∞ (fun a : Space => translatePath T a (operatorPath T F₁.field)) := by
    simpa only [translatePath_operatorPath] using operatorPathTranslation_contDiff T F₁
  have hv := EulerMeanSourceSpatialRegularity.velocity_translation_contDiff
    T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r hBe hBc hL hr hrquarter hext hcore
    hInv hF hRight K hK hF0 hH hsmall f s hf
  have hvb := velocity_translation_block_gevrey directions hd q T hT ℓ hℓ hℓ1
    F F₁ H M0 FInv Be Bc L r hBe hBc hL hr hrquarter hext hcore hInv hF hRight
    K hK hF0 hH hsmall f s hf Rc R M CF CF₁ CH CM Cf hRc hCF hCF₁ hCH hCM hCf
    hM hMC hMD hR hFb hF₁b hHb hMb d hfb
  exact s.strong_time_block_bounds directions hd q hTpos
    (meanFrameCoercivity T FInv) (meanFrameCoercivity_pos T FInv)
    (solenoidalFrame_lower T FInv (operatorPath T F.field) hInv) fC hRep hF
    hFr hF₁r hv hf hfC Rc R CF CF₁ Cf hRc0 hR1 hRcR hCF hCF₁ hCf hstrong hstrongC
    (translatedPath_bound T F Rc CF hRc0 hCF hFb)
    (translatedPath_bound T F₁ Rc CF₁ hRc0 hCF₁ hF₁b) d hfb hfCb hvb

end EulerMeanSourceTimeSobolev

end
end

end

section

/-!
# Fixed-Hq bounds for the actual physical mean pressure force

Starting with the proved weak inverse's one-shift coordinate bound, this
result gives the actual continuous physical field at shift d+2 and its true
within-time derivative at shift d+3. All use the identical external radius.
-/

@[expose] public section

noncomputable section

namespace EulerMeanVariationalInverse.StrongMeanEvolution

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanTimeTranslation EulerMeanOperatorTranslation EulerMeanTimeContinuousTranslation
  EulerMeanCoordinatePath EulerMeanContinuousAcceleration EulerMeanContinuousSobolev
  EulerMeanTimeSobolev EulerMeanAccelerationSobolev EulerMeanGramTranslation
  EulerMeanStrongGevrey EulerMeanStrongContinuousGevrey EulerTimeLp EulerVolterraConvolution
  EulerTimeLpGramSobolev EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

variable {T : ℝ} {hT : 0 ≤ T}
  {FInv F F₁ : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2)}
  {A : L2 →L[ℝ] L2} {L : ℝ} {u f : TimeLp T L2}
  (s : StrongMeanEvolution T hT FInv F F₁ A L u f)

/-- The true pressure force retains the same radius and the time-derivative grade d+3. -/
theorem pressure_time_block_bounds {ι : Type*} [Fintype ι]
    (directions : ι → Space) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (hTpos : 0 < T) (c : ℝ) (hc : 0 < c)
    (hLower : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖solenoidalFrame T F t v‖ ^ 2)
    (fC : C(Icc (0 : ℝ) T, L2))
    (hF : ContDiff ℝ ∞ (fun a : Space => translatePath T a F))
    (hF₁ : ContDiff ℝ ∞ (fun a : Space => translatePath T a F₁))
    (hv : ContDiff ℝ ∞ (fun a : Space => timeSolenoidalTranslation T a s.velocityLp))
    (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f))
    (hfC : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a fC))
    (Rc R CF CF₁ Cf : ℝ) (hRc : 0 ≤ Rc) (hR : 1 ≤ R)
    (hRcR : sobolevCoefficientRadius ι Rc ≤ R)
    (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCf : 0 ≤ Cf)
    (hstrong : 2*gramBlockCost ι q c Rc CF (accelerationBlockAmplitude ι q Rc CF CF₁ Cf 1) *
      (sobolevCoefficientRadius ι Rc+1) ≤ R)
    (hstrongC : 2*gramBlockCost ι q c Rc CF
      (accelerationBlockAmplitude ι q Rc CF CF₁ Cf (coordinateTraceCost T)) *
      (sobolevCoefficientRadius ι Rc+1) ≤ R)
    (hFb : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F) a‖ ≤ CF*majorant Rc 0
        n)
    (hF₁b : ∀ n a, ‖iteratedFDeriv ℝ n (fun b : Space => translatePath T b F₁) a‖ ≤ CF₁*majorant Rc
        0 n)
    (d : ℕ)
    (hfb : ∀ n a, block directions q (fun b : Space => timeTranslation T b f) n a ≤ Cf*majorant R d
        n)
    (hfCb : ∀ n a, block directions q (fun b : Space => pathTranslation T b fC) n a ≤ Cf*majorant R
        d n)
    (hvb : ∀ n a, block directions q (fun b : Space => timeSolenoidalTranslation T b s.velocityLp)
        n a ≤ majorant R (d+1) n) :
    (ContDiff ℝ ∞ (fun a : Space => pathTranslation T a (s.pressurePath c hc hLower fC))) ∧
    (∀ n a, block directions q
      (fun b : Space => pathTranslation T b (s.pressurePath c hc hLower fC)) n a ≤
      (Cf+3*sobolevCoefficientAmplitude ι q Rc CF +
        6*sobolevCoefficientAmplitude ι q Rc CF₁*coordinateTraceCost T)*majorant R (d+3) n) := by
  have htrace : 0 ≤ coordinateTraceCost T := coordinateTraceCost_nonneg T hT
  have hf1 (n a) : block directions q (fun b : Space => timeTranslation T b f) n a ≤
      Cf*majorant R (d+1) n :=
    (hfb n a).trans (mul_le_mul_of_nonneg_left (majorant_shift_mono R hR d n) hCf)
  have hv1 (n a) : block directions q (fun b : Space => timeSolenoidalTranslation T b s.velocityLp)
      n a ≤
      1*majorant R (d+1) n := by simpa only [one_mul] using hvb n a
  have hat (n a) : block directions q (fun b : Space => timeSolenoidalTranslation T b
      s.acceleration) n a ≤
      majorant R (d+2) n := by
    refine (congrArg (fun v : TimeLp T solenoidalSpace =>
      block directions q (fun b : Space => timeSolenoidalTranslation T b v) n a)
      (s.acceleration_eq_meanAcceleration c hc hLower)).trans_le ?_
    simpa only [Nat.add_assoc] using meanAcceleration_translation_block_gevrey directions hd q
      T hT F F₁ c hc hLower s.velocityLp f hF hF₁ hv hf Rc R CF CF₁ Cf 1
      hRc hRcR hCF hCF₁ hCf zero_le_one hstrong hFb hF₁b (d+1) hf1 hv1 n a
  have ha := s.acceleration_orbit_contDiff c hc hLower hF hF₁ hv hf
  have hv2 (n a) : block directions q (fun b : Space => timeSolenoidalTranslation T b s.velocityLp)
      n a ≤
      1*majorant R (d+2) n := by
    simpa only [one_mul] using (hvb n a).trans (majorant_shift_mono R hR (d+1) n)
  have hat1 (n a) : block directions q (fun b : Space => timeSolenoidalTranslation T b
      s.acceleration) n a ≤
      1*majorant R (d+2) n := by simpa only [one_mul] using hat n a
  have hvc := s.coordinateVelocityPath_translation_contDiff hTpos hv ha
  have hvcb (n a) : block directions q (fun b : Space => coordinatePathTranslation T b
      s.coordinateVelocityPath) n a ≤
      coordinateTraceCost T*majorant R (d+2) n := by
    simpa only [mul_one, coordinateTraceCost] using
      s.coordinateVelocityPath_translation_block_gevrey directions q hTpos hv ha R 1 1 (d+2) hv2
          hat1 n a
  have hfc2 (n a) : block directions q (fun b : Space => pathTranslation T b fC) n a ≤
      Cf*majorant R (d+2) n :=
    (hfCb n a).trans (mul_le_mul_of_nonneg_left (majorant_mono_shift R hR d (d+2) n (by omega)) hCf)
  have hac (n a) : block directions q
      (fun b : Space => coordinatePathTranslation T b (s.classicalAcceleration c hc hLower fC)) n a
          ≤
        majorant R (d+3) n := by
    simpa only [Nat.add_assoc, meanAccelerationPath, classicalAcceleration] using
        meanAccelerationPath_translation_block_gevrey
      T F F₁ c hc hLower s.coordinateVelocityPath fC directions hd q hF hF₁ hvc hfC
      Rc R CF CF₁ Cf (coordinateTraceCost T) hRc hRcR hCF hCF₁ hCf htrace
      hstrongC hFb hF₁b (d+2) hfc2 hvcb n a
  have hacs := s.classicalAcceleration_translation_contDiff c hc hLower fC hF hF₁ hvc hfC
  have hvc3 (n a) : block directions q (fun b : Space => coordinatePathTranslation T b
      s.coordinateVelocityPath) n a ≤
      coordinateTraceCost T*majorant R (d+3) n :=
    (hvcb n a).trans (mul_le_mul_of_nonneg_left (majorant_shift_mono R hR (d+2) n) htrace)
  have hac1 (n a) : block directions q
      (fun b : Space => coordinatePathTranslation T b (s.classicalAcceleration c hc hLower fC)) n a
          ≤
        1*majorant R (d+3) n := by simpa only [one_mul] using hac n a
  have hfc3 (n a) : block directions q (fun b : Space => pathTranslation T b fC) n a ≤
      Cf*majorant R (d+3) n :=
    (hfCb n a).trans (mul_le_mul_of_nonneg_left (majorant_mono_shift R hR d (d+3) n (by omega)) hCf)
  refine ⟨s.pressurePath_translation_contDiff c hc hLower fC hF hF₁ hvc hacs hfC, ?_⟩
  intro n a
  simpa only [mul_one] using s.pressurePath_translation_block_gevrey c hc hLower fC
    directions hd q hF hF₁ hvc hacs hfC Rc R CF CF₁ Cf (coordinateTraceCost T) 1
    hRc hRcR hCF hCF₁ htrace zero_le_one (d+3) hFb hF₁b hfc3 hvc3 hac1 n a

end EulerMeanVariationalInverse.StrongMeanEvolution

end
end

end

section

/-!
# Concrete source estimates for the strong mean inverse

The literal source coefficient bounds and actual forcing orbit bounds imply
the successive coordinate and physical-field factorial estimates. Coercivity,
boundary cutoff calculus, Gram inversion, and time reconstruction are all
proved constructions used by this theorem.
-/

@[expose] public section

noncomputable section

namespace EulerMeanSourcePressureSobolev

open MeasureTheory Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanCoefficients EulerMeanBoundary EulerMeanHarmonic EulerMeanSourceInverse
  EulerMeanVariationalInverse EulerMeanSourceFixedInverse EulerMeanSourceGevrey
  EulerMeanSourceSpatialRegularity EulerMeanTimeTranslation EulerMeanOperatorTranslation
  EulerMeanTimeContinuousTranslation EulerMeanTranslatedGevrey EulerTimeLp EulerVolterraConvolution
  EulerTimeLpGramGevrey EulerGevrey EulerParameterWordGevrey
   EulerMeanFixedSobolevGevrey EulerMeanSourceStrongSobolev
  EulerMeanStrongContinuousGevrey EulerTimeLpGramSobolev
open scoped NNReal ContDiff

variable {ι : Type*} [Fintype ι]
  (directions : ι → Space) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (T : ℝ) (hT : 0 ≤ T) (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1)
  (F F₁ H : SmoothCoefficientPath (Icc (0 : ℝ) T) (Space →L[ℝ] Space))
  (M0 : BoundedSmoothField (Space →L[ℝ] Space)) (FInv : C(Icc (0 : ℝ) T, L2 →L[ℝ] L2))
  (Be Bc L r : ℝ) (hBe : 0 ≤ Be) (hBc : 0 ≤ Bc)
  (hL : boundaryLocalizationC1 * Bc ≤ L) (hr : 0 ≤ r) (hrquarter : r ≤ 1 / 4)
  (hext : ∀ x, r ≤ ‖ℓ • x‖ → ∀ v : Space, -Be * ‖v‖ ^ 2 ≤ ⟪M0.field x v, v⟫_ℝ)
  (hcore : ∀ x, ‖ℓ • x‖ < r → ∀ v : Space, -Bc * ‖v‖ ^ 2 ≤ ⟪M0.field x v, v⟫_ℝ)
  (hInv : ∀ (t : Icc (0 : ℝ) T) (x : L2), FInv t (operatorPath T F.field t x) = x)
  (hF : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT (operatorPath T F.field))
      (operatorPath T F₁.field t) (Icc (0 : ℝ) T) t)
  (hRight : ∀ (t : Icc (0 : ℝ) T) (x : L2), operatorPath T F.field t (FInv t x) = x)
  (K : ℝ) (hK : 0 ≤ K)
  (hF0 : FInv ⟨0, le_rfl, hT⟩ = ContinuousLinearMap.id ℝ L2)
  (hH : ∀ t x v, ⟪H.field t x v, v⟫_ℝ ≤ K * ‖v‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) + Be * T + boundaryLocalizationC2 * Bc * r ^ 3 * T ≤ 1 / 2)
  (f : TimeLp T L2)
  (s : StrongMeanEvolution T hT FInv (operatorPath T F.field) (operatorPath T F₁.field)
    (boundaryOperator (scaledCutoff ℓ hℓ)) L
    (sourceMeanSolver T hT ℓ hℓ M0.field M0.field.continuous.aestronglyMeasurable
      ‖M0.field‖₊ M0.field.norm_coe_le_norm Be Bc L r hBe hBc hL hr hrquarter hext hcore
      FInv (operatorPath T H.field) K hK hF0 (operatorPath_quadratic_upper T H.field K hH) hsmall
          f) f)
  (hf : ContDiff ℝ ∞ (fun a : Space => timeTranslation T a f))
  (Rc R M CF CF₁ CH CM Cf : ℝ) (hRc : 1024 ≤ Rc)
  (hCF : 0 ≤ CF) (hCF₁ : 0 ≤ CF₁) (hCH : 0 ≤ CH) (hCM : 0 ≤ CM) (hCf : 0 ≤ Cf)
  (hM : 1 ≤ M)
  (hMC : sobolevInverseCost (sourceFixedCoercivity T F F₁ FInv)⁻¹
    (operatorBlockAmplitude ι q T Rc CF CF₁ CH CM scaledBoundaryOperatorAmplitude L) q *
    operatorBlockAmplitude ι q T Rc CF CF₁ CH CM scaledBoundaryOperatorAmplitude L ≤ M)
  (hMD : sobolevInverseCost (sourceFixedCoercivity T F F₁ FInv)⁻¹
    (operatorBlockAmplitude ι q T Rc CF CF₁ CH CM scaledBoundaryOperatorAmplitude L) q *
    forcingBlockAmplitude ι q T Rc CF CF₁ Cf ≤ M)
  (hR : 2 * M * (sobolevCoefficientRadius ι Rc + 1) ≤ R)
  (hFb : ∀ n t x, ‖iteratedFDeriv ℝ n (F.field t : Space → Space →L[ℝ] Space) x‖ ≤ CF * majorant Rc
      0
      n)
  (hF₁b : ∀ n t x, ‖iteratedFDeriv ℝ n (F₁.field t : Space → Space →L[ℝ] Space) x‖ ≤ CF₁ * majorant
      Rc 0 n)
  (hHb : ∀ n t x, ‖iteratedFDeriv ℝ n (H.field t : Space → Space →L[ℝ] Space) x‖ ≤ CH * majorant Rc
      0
      n)
  (hMb : ∀ n x, ‖iteratedFDeriv ℝ n (M0.field : Space → Space →L[ℝ] Space) x‖ ≤ CM * majorant Rc 0
      n)
  (d : ℕ)
  (hfb : ∀ n a, block directions q (fun b : Space => timeTranslation T b f) n a ≤ Cf * majorant R d
      n)

include hd hℓ1 hInv hF hRight hf hRc hCF hCF₁ hCH hCM hCf hM hMC hMD hR hFb hF₁b hHb hMb hfb

/-- The literal source pressure force is smooth and has the same fixed-Hq grade as B_t. -/
theorem source_pressure_block_bounds
    (hstrong : 2 * gramBlockCost ι q (meanFrameCoercivity T FInv) Rc CF
      (accelerationBlockAmplitude ι q Rc CF CF₁ Cf 1) *
 (sobolevCoefficientRadius ι Rc + 1) ≤ R)
    (hstrongC : 2 *
 gramBlockCost ι q (meanFrameCoercivity T FInv) Rc CF
      (accelerationBlockAmplitude ι q Rc CF CF₁ Cf (coordinateTraceCost T)) *
      (sobolevCoefficientRadius ι Rc + 1) ≤ R)
    (hTpos : 0 < T) (fC : C(Icc (0 : ℝ) T, L2))
    (hfC : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a fC))
    (hfCb : ∀ n a, block directions q (fun b : Space => pathTranslation T b fC) n a ≤ Cf*majorant R
        d n) :
    (ContDiff ℝ ∞ (fun a : Space => pathTranslation T a
      (s.pressurePath (meanFrameCoercivity T FInv) (meanFrameCoercivity_pos T FInv)
        (solenoidalFrame_lower T FInv (operatorPath T F.field) hInv) fC))) ∧
    (∀ n a, block directions q (fun b : Space => pathTranslation T b
      (s.pressurePath (meanFrameCoercivity T FInv) (meanFrameCoercivity_pos T FInv)
        (solenoidalFrame_lower T FInv (operatorPath T F.field) hInv) fC)) n a ≤
      (Cf+3*sobolevCoefficientAmplitude ι q Rc CF +
        6*sobolevCoefficientAmplitude ι q Rc CF₁*coordinateTraceCost T)*majorant R (d+3) n) := by
  have hRc0 : 0 ≤ Rc := (by norm_num : (0 : ℝ) ≤ 1024).trans hRc
  have hrc : 0 ≤ sobolevCoefficientRadius ι Rc := sobolevCoefficientRadius_nonneg Rc hRc0
  have hR1 : 1 ≤ R := (radius_bounds hrc hM hR).1
  have hRcR : sobolevCoefficientRadius ι Rc ≤ R := (radius_bounds hrc hM hR).2
  have hFr : ContDiff ℝ ∞ (fun a : Space => translatePath T a (operatorPath T F.field)) := by
    simpa only [translatePath_operatorPath] using operatorPathTranslation_contDiff T F
  have hF₁r : ContDiff ℝ ∞ (fun a : Space => translatePath T a (operatorPath T F₁.field)) := by
    simpa only [translatePath_operatorPath] using operatorPathTranslation_contDiff T F₁
  have hv := EulerMeanSourceSpatialRegularity.velocity_translation_contDiff
    T hT ℓ hℓ F F₁ H M0 FInv Be Bc L r hBe hBc hL hr hrquarter hext hcore
    hInv hF hRight K hK hF0 hH hsmall f s hf
  have hvb := velocity_translation_block_gevrey directions hd q T hT ℓ hℓ hℓ1
    F F₁ H M0 FInv Be Bc L r hBe hBc hL hr hrquarter hext hcore hInv hF hRight
    K hK hF0 hH hsmall f s hf Rc R M CF CF₁ CH CM Cf hRc hCF hCF₁ hCH hCM hCf
    hM hMC hMD hR hFb hF₁b hHb hMb d hfb
  exact s.pressure_time_block_bounds directions hd q hTpos
    (meanFrameCoercivity T FInv) (meanFrameCoercivity_pos T FInv)
    (solenoidalFrame_lower T FInv (operatorPath T F.field) hInv) fC
    hFr hF₁r hv hf hfC Rc R CF CF₁ Cf hRc0 hR1 hRcR hCF hCF₁ hCf hstrong hstrongC
    (translatedPath_bound T F Rc CF hRc0 hCF hFb)
    (translatedPath_bound T F₁ Rc CF₁ hRc0 hCF₁ hF₁b) d hfb hfCb hvb

end EulerMeanSourcePressureSobolev

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanPacketProvider

open Set EulerSmoothLimit EulerMeanSolenoidal EulerMeanBoundary
  EulerMeanSourceFixedInverse EulerMeanFixedSobolevGevrey EulerParameterWordGevrey
  EulerTimeLpGramSobolev EulerMeanStrongContinuousGevrey EulerMeanTimeTranslation
  EulerMeanTimeContinuousTranslation EulerGevrey
open scoped ContDiff

/-- Fixed coefficient and inverse budgets, with no conclusion about a solution. -/
structure SobolevData (D : Data) (ι : Type*) [Fintype ι] (q : ℕ) (R : ℝ) where
  /-- Rc of `SobolevData`, of type `ℝ`. -/
  Rc : ℝ
  /-- M of `SobolevData`, of type `ℝ`. -/
  M : ℝ
  /-- CF of `SobolevData`, of type `ℝ`. -/
  CF : ℝ
  /-- CF₁ of `SobolevData`, of type `ℝ`. -/
  CF₁ : ℝ
  /-- CH of `SobolevData`, of type `ℝ`. -/
  CH : ℝ
  /-- CM of `SobolevData`, of type `ℝ`. -/
  CM : ℝ
  /-- Cf of `SobolevData`, of type `ℝ`. -/
  Cf : ℝ
  radius_lower : 1024 ≤ Rc
  inverse_cost_lower : 1 ≤ M
  CF_nonneg : 0 ≤ CF
  CF₁_nonneg : 0 ≤ CF₁
  CH_nonneg : 0 ≤ CH
  CM_nonneg : 0 ≤ CM
  Cf_nonneg : 0 ≤ Cf
  operator_budget :
    sobolevInverseCost (sourceFixedCoercivity D.T D.F D.F₁ D.opInv)⁻¹
      (operatorBlockAmplitude ι q D.T Rc CF CF₁ CH CM scaledBoundaryOperatorAmplitude D.L) q *
      operatorBlockAmplitude ι q D.T Rc CF CF₁ CH CM scaledBoundaryOperatorAmplitude D.L ≤ M
  forcing_budget :
    sobolevInverseCost (sourceFixedCoercivity D.T D.F D.F₁ D.opInv)⁻¹
      (operatorBlockAmplitude ι q D.T Rc CF CF₁ CH CM scaledBoundaryOperatorAmplitude D.L) q *
      forcingBlockAmplitude ι q D.T Rc CF CF₁ Cf ≤ M
  radius_budget : 2*M*(sobolevCoefficientRadius ι Rc+1) ≤ R
  acceleration_budget :
    2*gramBlockCost ι q D.frameLower Rc CF
      (accelerationBlockAmplitude ι q Rc CF CF₁ Cf 1)*(sobolevCoefficientRadius ι Rc+1) ≤ R
  continuous_acceleration_budget :
    2*gramBlockCost ι q D.frameLower Rc CF
      (accelerationBlockAmplitude ι q Rc CF CF₁ Cf (coordinateTraceCost D.T)) *
      (sobolevCoefficientRadius ι Rc+1) ≤ R
  frame_bound : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.F.field t : Space → Space →L[ℝ] Space) x‖ ≤ CF*majorant Rc 0 n
  frame_derivative_bound : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.F₁.field t : Space → Space →L[ℝ] Space) x‖ ≤ CF₁*majorant Rc 0 n
  curvature_bound : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.H.field t : Space → Space →L[ℝ] Space) x‖ ≤ CH*majorant Rc 0 n
  initial_strain_bound : ∀ n x,
    ‖iteratedFDeriv ℝ n (D.M0.field : Space → Space →L[ℝ] Space) x‖ ≤ CM*majorant Rc 0 n

namespace SobolevData

variable {D : Data} {ι : Type*} [Fintype ι] {q : ℕ} {R : ℝ}
  (E : SobolevData D ι q R)

/-- Velocity amplitude, given by `3*sobolevCoefficientAmplitude ι q E.Rc
E.CF*coordinateTraceCost D.T`. -/
def velocityAmplitude : ℝ :=
  3*sobolevCoefficientAmplitude ι q E.Rc E.CF*coordinateTraceCost D.T

/-- Derivative amplitude, given by `3*(sobolevCoefficientAmplitude ι q E.Rc
E.CF₁*coordinateTraceCost D.T + sobolevCoefficientAmplitude ι q E.Rc E.CF)`. -/
def derivativeAmplitude : ℝ :=
  3*(sobolevCoefficientAmplitude ι q E.Rc E.CF₁*coordinateTraceCost D.T +
    sobolevCoefficientAmplitude ι q E.Rc E.CF)

/-- Pressure amplitude, given by `E.Cf+3*sobolevCoefficientAmplitude ι q E.Rc E.CF +
6*sobolevCoefficientAmplitude ι q E.Rc E.CF₁*coordinateTraceCost D.T`. -/
def pressureAmplitude : ℝ :=
  E.Cf+3*sobolevCoefficientAmplitude ι q E.Rc E.CF +
    6*sobolevCoefficientAmplitude ι q E.Rc E.CF₁*coordinateTraceCost D.T

/-- The concrete source estimates at the fixed budgets above. -/
theorem normalized_bounds (directions : ι → Space) (hd : ∀ i, ‖directions i‖ ≤ 1)
    {raw : EulerPacketProfileRecursion.VectorField} (G : Forcing D raw) (d : ℕ)
    (hfb : ∀ n a, block directions q (fun b : Space => timeTranslation D.T b G.lp) n a ≤
      E.Cf*majorant R d n)
    (hfCb : ∀ n a, block directions q (fun b : Space => pathTranslation D.T b G.path) n a ≤
      E.Cf*majorant R d n) :
    (∀ n a, block directions q (fun b : Space => pathTranslation D.T b G.velocityPath) n a ≤
      E.velocityAmplitude*majorant R (d+2) n) ∧
    (∀ n a, block directions q (fun b : Space => pathTranslation D.T b G.derivativePath) n a ≤
      E.derivativeAmplitude*majorant R (d+3) n) ∧
    (∀ n a, block directions q (fun b : Space => pathTranslation D.T b G.pressureForcePath) n a ≤
      E.pressureAmplitude*majorant R (d+3) n) := by
  have ht := EulerMeanSourceTimeSobolev.source_strong_time_block_bounds directions hd q
    D.T D.T_pos.le D.ℓ D.ℓ_pos D.ℓ_le_one D.F D.F₁ D.H D.M0 D.opInv
    D.Be D.Bc D.L D.r D.Be_nonneg D.Bc_nonneg D.L_lower D.r_nonneg D.r_le_quarter
    D.exterior_lower D.core_lower D.opInv_left D.opF_time D.opInv_right
    D.K D.K_nonneg D.opInv_initial D.curvature_upper D.small G.lp G.solution G.lp_orbit
    E.Rc R E.M E.CF E.CF₁ E.CH E.CM E.Cf E.radius_lower E.CF_nonneg E.CF₁_nonneg
    E.CH_nonneg E.CM_nonneg E.Cf_nonneg E.inverse_cost_lower E.operator_budget E.forcing_budget
    E.radius_budget E.frame_bound E.frame_derivative_bound E.curvature_bound E.initial_strain_bound
    d hfb E.acceleration_budget E.continuous_acceleration_budget D.T_pos
    G.path G.lp_rep G.path_orbit hfCb
  have hp := EulerMeanSourcePressureSobolev.source_pressure_block_bounds directions hd q
    D.T D.T_pos.le D.ℓ D.ℓ_pos D.ℓ_le_one D.F D.F₁ D.H D.M0 D.opInv
    D.Be D.Bc D.L D.r D.Be_nonneg D.Bc_nonneg D.L_lower D.r_nonneg D.r_le_quarter
    D.exterior_lower D.core_lower D.opInv_left D.opF_time D.opInv_right
    D.K D.K_nonneg D.opInv_initial D.curvature_upper D.small G.lp G.solution G.lp_orbit
    E.Rc R E.M E.CF E.CF₁ E.CH E.CM E.Cf E.radius_lower E.CF_nonneg E.CF₁_nonneg
    E.CH_nonneg E.CM_nonneg E.Cf_nonneg E.inverse_cost_lower E.operator_budget E.forcing_budget
    E.radius_budget E.frame_bound E.frame_derivative_bound E.curvature_bound E.initial_strain_bound
    d hfb E.acceleration_budget E.continuous_acceleration_budget D.T_pos
    G.path G.path_orbit hfCb
  exact ⟨ht.1, ht.2.1, hp.2⟩

end SobolevData
end EulerMeanPacketProvider

end
end

end

section

/-!
# Mean inverse estimates with an external forcing envelope

The scalar amplitude is normalized before the actual solve and restored by
proved homogeneity. Every radius condition depends only on the fixed source
data and the fixed normalized forcing scale, never on the recursive grade
or its forcing envelope. Zero envelope is treated by actual zero forcing.
-/

section

/-!
# Homogeneity of the genuine mean packet solution

The selected strong representatives inherit the linearity of the actual
coercive inverse. Consequently scalar forcing envelopes remain outside the
velocity, time-derivative, and physical-pressure estimates.
-/

@[expose] public section

noncomputable section

namespace EulerMeanPacketProvider.Forcing

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanVariationalInverse  EulerTimeLp EulerVolterraConvolution
  EulerMeanTimeContinuousTranslation EulerPacketPointJets EulerPacketProfileRecursion
open scoped ContDiff

variable {D : Data} {raw raw' : VectorField}

theorem path_ae_raw (G : Forcing D raw) (t : Icc (0 : ℝ) D.T) (θ : ℝ) :
    (G.path t : Space → Space) =ᵐ[volume] fun x => raw (t,(x,θ)) := by
  rw [G.path_eq]
  exact (G.slices t).toLp_ae.trans (Filter.Eventually.of_forall fun x => (G.raw_eq t x θ).symm)

section Scaling

variable (G : Forcing D raw) (H : Forcing D raw') (a : ℝ)
  (hraw : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw' (t, (x, θ)) = a • raw (t, (x, θ)))

include hraw

theorem path_smul : H.path = a • G.path := by
  apply ContinuousMap.ext
  intro t
  apply Lp.ext
  filter_upwards [G.path_ae_raw t 0, H.path_ae_raw t 0, Lp.coeFn_smul a (G.path t)] with x hG hH ha
  change H.path t x = (a • G.path t) x
  rw [hH, ha, Pi.smul_apply, hG, hraw t x 0]

theorem lp_smul : H.lp = a • G.lp := by
  exact (congrArg (pathLp (E := L2) D.T D.T_pos.le) (path_smul G H a hraw)).trans
    (pathLp_smul D.T D.T_pos.le a G.path)

theorem velocityLp_smul : H.solution.velocityLp = a • G.solution.velocityLp := by
  exact H.velocityLp_eq_coordinateSolver.trans
    ((congrArg D.coordinateSolver (lp_smul G H a hraw)).trans
      ((D.coordinateSolver.map_smul a G.lp).trans
        (congrArg (fun v : TimeLp D.T solenoidalSpace => a • v)
          G.velocityLp_eq_coordinateSolver).symm))

/-- Linearity of the L² solve fixes the continuous coordinate representative at every time. -/
theorem coordinate_velocity_smul (t : Icc (0 : ℝ) D.T) :
    H.solution.velocity t = a • G.solution.velocity t := by
  have hae : (fun r => H.solution.velocity r) =ᵐ[timeMeasure D.T]
      fun r => a • G.solution.velocity r := by
    filter_upwards [H.solution.velocity_ae, G.solution.velocity_ae,
      Lp.coeFn_smul a G.solution.velocityLp] with r hH hG ha
    have he := congrArg (fun z : TimeLp D.T solenoidalSpace => z r) (velocityLp_smul G H a hraw)
    exact hH.symm.trans (he.trans (ha.trans (congrArg (fun v : solenoidalSpace => a • v) hG)))
  have hcG : ContinuousOn G.solution.velocity (Icc (0 : ℝ) D.T) := by
    simpa only [uIcc_of_le D.T_pos.le] using G.solution.velocity_ac.continuousOn
  have hcH : ContinuousOn H.solution.velocity (Icc (0 : ℝ) D.T) := by
    simpa only [uIcc_of_le D.T_pos.le] using H.solution.velocity_ac.continuousOn
  exact Measure.eqOn_Icc_of_ae_eq volume D.T_pos.ne hae hcH (hcG.const_smul a) t.property

theorem coordinateVelocityPath_smul :
    H.solution.coordinateVelocityPath = a • G.solution.coordinateVelocityPath := by
  apply ContinuousMap.ext
  intro t
  exact coordinate_velocity_smul G H a hraw t

theorem velocityPath_smul : H.velocityPath = a • G.velocityPath := by
  let J := EulerContinuousTimeIntegral.multiplier (solenoidalFrame D.T D.opF)
  exact (H.solution.continuousVelocity_eq_frame D.T_pos D.opF_time).trans
    ((congrArg J (coordinateVelocityPath_smul G H a hraw)).trans
      ((J.map_smul a G.solution.coordinateVelocityPath).trans
        (congrArg (fun p : C(Icc (0 : ℝ) D.T,L2) => a • p)
          (G.solution.continuousVelocity_eq_frame D.T_pos D.opF_time)).symm))

/-- The true within-time derivatives scale by uniqueness of the derivative. -/
theorem derivativePath_smul : H.derivativePath = a • G.derivativePath := by
  apply ContinuousMap.ext
  intro t
  have h₁ := H.velocityPath_time t
  have h₂ := (G.velocityPath_time t).const_smul a
  have he : extendPath D.T D.T_pos.le H.velocityPath =
      fun r => a • extendPath D.T D.T_pos.le G.velocityPath r := by
    funext r
    exact congrArg (fun p : C(Icc (0 : ℝ) D.T,L2) => p (projIcc 0 D.T D.T_pos.le r))
      (velocityPath_smul G H a hraw)
  rw [he] at h₁
  exact (h₁.derivWithin ((uniqueDiffOn_Icc D.T_pos) t t.property)).symm.trans
    (h₂.derivWithin ((uniqueDiffOn_Icc D.T_pos) t t.property))

/-- The actual physical pressure residual scales, including at the time endpoints. -/
theorem pressureForcePath_smul : H.pressureForcePath = a • G.pressureForcePath := by
  apply ContinuousMap.ext
  intro t
  have hG := G.solution.pressurePath_equation D.frameLower D.frameLower_pos D.frame_lower
    G.path D.T_pos D.opF_time D.opM D.opStrain_eq t
  have hH := H.solution.pressurePath_equation D.frameLower D.frameLower_pos D.frame_lower
    H.path D.T_pos D.opF_time D.opM D.opStrain_eq t
  have hv : H.velocityPath t = a • G.velocityPath t :=
    congrArg (fun p : C(Icc (0 : ℝ) D.T,L2) => p t) (velocityPath_smul G H a hraw)
  have hd : H.derivativePath t = a • G.derivativePath t :=
    congrArg (fun p : C(Icc (0 : ℝ) D.T,L2) => p t) (derivativePath_smul G H a hraw)
  have hf : H.path t = a • G.path t :=
    congrArg (fun p : C(Icc (0 : ℝ) D.T,L2) => p t) (path_smul G H a hraw)
  change H.derivativePath t+D.opM t (H.velocityPath t)+H.pressureForcePath t=H.path t at hH
  change G.derivativePath t+D.opM t (G.velocityPath t)+G.pressureForcePath t=G.path t at hG
  rw [hd, hv, hf, map_smul] at hH
  have he := congrArg (fun z : L2 => a • z) hG
  simp only [smul_add] at he
  exact add_left_cancel (hH.trans he.symm)

end Scaling

end EulerMeanPacketProvider.Forcing

end
end

end

section

/-! Zero forcing produces the actual zero velocity, derivative, and pressure force. -/

@[expose] public section

noncomputable section

namespace EulerMeanPacketProvider.Forcing

open Set MeasureTheory EulerSmoothLimit EulerMeanSolenoidal EulerPacketProfileRecursion

variable {D : Data} {raw : VectorField} (G : Forcing D raw)

theorem raw_zero_of_path_zero (hp : G.path = 0) (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    raw (t,(x,θ)) = 0 := by
  have hpt : G.path t = 0 := congrArg (fun p : C(Icc (0 : ℝ) D.T,L2) => p t) hp
  have hz : (G.path t : Space → Space) =ᵐ[volume] (fun _ => (0 : Space)) := by
    rw [hpt]
    exact Lp.coeFn_zero Space 2 volume
  have hc : Continuous (fun y => raw (t,(y,θ))) := by
    have he : (fun y => raw (t,(y,θ))) = (G.slices t).field := funext (fun y => G.raw_eq t y θ)
    rw [he]
    exact (G.slices t).smooth.continuous
  exact congrFun (Measure.eq_of_ae_eq ((G.path_ae_raw t θ).symm.trans hz) hc continuous_const) x

theorem paths_zero_of_raw_zero
    (hz : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw (t, (x, θ)) = 0) :
    G.velocityPath = 0 ∧ G.derivativePath = 0 ∧ G.pressureForcePath = 0 := by
  have hs : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw (t,(x,θ)) = (0 : ℝ) • raw (t,(x,θ)) := by
    intro t x θ
    rw [hz t x θ, zero_smul]
  exact ⟨by simpa only [zero_smul] using velocityPath_smul G G 0 hs,
    by simpa only [zero_smul] using derivativePath_smul G G 0 hs,
    by simpa only [zero_smul] using pressureForcePath_smul G G 0 hs⟩

theorem paths_zero_of_path_zero (hp : G.path = 0) :
    G.velocityPath = 0 ∧ G.derivativePath = 0 ∧ G.pressureForcePath = 0 :=
  paths_zero_of_raw_zero G (raw_zero_of_path_zero G hp)

end EulerMeanPacketProvider.Forcing

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanPacketProvider.SobolevData

open Set EulerSmoothLimit EulerMeanSolenoidal EulerMeanTimeTranslation
  EulerMeanTimeContinuousTranslation EulerParameterWordGevrey EulerGevrey
  EulerPacketProfileRecursion
open scoped ContDiff

variable {D : Data} {ι : Type*} [Fintype ι] {q : ℕ} {R : ℝ}

/-- The fixed-Hq mean inverse preserves one external radius for arbitrary
nonnegative scalar forcing envelopes. -/
theorem envelope_bounds (E : SobolevData D ι q R)
    (directions : ι → Space) (hd : ∀ i, ‖directions i‖ ≤ 1)
    {raw : VectorField} (G : Forcing D raw) (d : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hfb : ∀ n a, block directions q (fun b : Space => timeTranslation D.T b G.lp) n a ≤
      A*(E.Cf*majorant R d n))
    (hfCb : ∀ n a, block directions q (fun b : Space => pathTranslation D.T b G.path) n a ≤
      A*(E.Cf*majorant R d n)) :
    (∀ n a, block directions q (fun b : Space => pathTranslation D.T b G.velocityPath) n a ≤
      A*(E.velocityAmplitude*majorant R (d+2) n)) ∧
    (∀ n a, block directions q (fun b : Space => pathTranslation D.T b G.derivativePath) n a ≤
      A*(E.derivativeAmplitude*majorant R (d+3) n)) ∧
    (∀ n a, block directions q (fun b : Space => pathTranslation D.T b G.pressureForcePath) n a ≤
      A*(E.pressureAmplitude*majorant R (d+3) n)) := by
  rcases eq_or_lt_of_le hA with hzero | hpos
  · subst A
    have hv := value_zero_of_block_zero_bound directions q
      (fun b : Space => pathTranslation D.T b G.path) 0 (by simpa only [zero_mul] using hfCb 0 0)
    have he : pathTranslation D.T 0 G.path = G.path := by
      apply ContinuousMap.ext
      intro t
      exact translation_zero (G.path t)
    have hp : G.path = 0 := he.symm.trans hv
    have hzero := G.paths_zero_of_path_zero hp
    simp only [hzero.1, hzero.2.1, hzero.2.2, map_zero, block_zero_function, zero_mul,
      le_refl, implies_true, and_self]
  · let H : Forcing D (A⁻¹ • raw) := G.smul A⁻¹
    have hscale : ∀ (t : Icc (0 : ℝ) D.T) x θ,
        (A⁻¹ • raw) (t,(x,θ)) = A⁻¹ • raw (t,(x,θ)) := fun _ _ _ => rfl
    have hLp : (fun b : Space => timeTranslation D.T b H.lp) =
        fun b : Space => A⁻¹ • timeTranslation D.T b G.lp := by
      funext b
      exact (congrArg (timeTranslation D.T b) (Forcing.lp_smul G H A⁻¹ hscale)).trans
        ((timeTranslation D.T b).map_smul A⁻¹ G.lp)
    have hPath : (fun b : Space => pathTranslation D.T b H.path) =
        fun b : Space => A⁻¹ • pathTranslation D.T b G.path := by
      funext b
      exact (congrArg (pathTranslation D.T b) (Forcing.path_smul G H A⁻¹ hscale)).trans
        ((pathTranslation D.T b).map_smul A⁻¹ G.path)
    have hn : ∀ n a, block directions q (fun b : Space => timeTranslation D.T b H.lp) n a ≤
        E.Cf*majorant R d n := by
      intro n a
      refine (congrArg (fun g : Space → EulerTimeLp.TimeLp D.T L2 =>
        block directions q g n a) hLp).trans_le ?_
      exact block_normalize_bound directions q _ G.lp_orbit A hpos R E.Cf d n a (hfb n a)
    have hnC : ∀ n a, block directions q (fun b : Space => pathTranslation D.T b H.path) n a ≤
        E.Cf*majorant R d n := by
      intro n a
      refine (congrArg (fun g : Space → C(Icc (0 : ℝ) D.T,L2) =>
        block directions q g n a) hPath).trans_le ?_
      exact block_normalize_bound directions q _ G.path_orbit A hpos R E.Cf d n a (hfCb n a)
    have hbounds := E.normalized_bounds directions hd H d hn hnC
    have hback : ∀ (t : Icc (0 : ℝ) D.T) x θ,
        raw (t,(x,θ)) = A • (A⁻¹ • raw) (t,(x,θ)) := by
      intro t x θ
      simp only [Pi.smul_apply, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    have hVB := Forcing.velocityPath_smul H G A hback
    have hVD := Forcing.derivativePath_smul H G A hback
    have hVP := Forcing.pressureForcePath_smul H G A hback
    refine ⟨?_, ?_, ?_⟩
    · intro n a
      apply block_restore_bound directions q _ _ H.velocityPath_orbit A hpos.le
        (fun b => (congrArg (pathTranslation D.T b) hVB).trans
          ((pathTranslation D.T b).map_smul A H.velocityPath)) R E.velocityAmplitude (d+2) n a
              (hbounds.1 n a)
    · intro n a
      apply block_restore_bound directions q _ _ H.derivativePath_orbit A hpos.le
        (fun b => (congrArg (pathTranslation D.T b) hVD).trans
          ((pathTranslation D.T b).map_smul A H.derivativePath)) R E.derivativeAmplitude (d+3) n a
              (hbounds.2.1 n a)
    · intro n a
      apply block_restore_bound directions q _ _ H.pressureForcePath_orbit A hpos.le
        (fun b => (congrArg (pathTranslation D.T b) hVP).trans
          ((pathTranslation D.T b).map_smul A H.pressureForcePath)) R E.pressureAmplitude (d+3) n a
              (hbounds.2.2 n a)

end EulerMeanPacketProvider.SobolevData

end
end

end

section

/-!
Exact parameter restriction transfers the ordinary mean estimates to the
four-letter cylinder word alphabet.  The zero angular direction is retained,
so neither the external radius nor the fixed Sobolev order changes.
-/

section

/-! Exact parameter restriction and injective subalphabet bounds for genuine derivative words. -/

@[expose] public section

noncomputable section

namespace EulerParameterWordGevrey

open ContinuousLinearMap Finset
open scoped ContDiff

variable {P Q E ι κ : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] [Fintype κ]

/-- Restricting an alphabet only discards nonnegative summands. -/
theorem wordSum_subalphabet_le (directions : κ → P) (e : ι → κ) (he : Function.Injective e)
    (f : P → E) (n : ℕ) (x : P) :
    wordSum (directions ∘ e) f n x ≤ wordSum directions f n x := by
  classical
  have hinj : Function.Injective (fun w : Fin n → ι => e ∘ w) := by
    intro u v h
    exact funext (fun j => he (congrFun h j))
  calc
    _ = ∑ w ∈ univ.image (fun w : Fin n → ι => e ∘ w), ‖wordDerivative directions f w x‖ := by
      rw [sum_image hinj.injOn]
      rfl
    _ ≤ ∑ w : Fin n → κ, ‖wordDerivative directions f w x‖ :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => norm_nonneg _)

/-- The same literal subalphabet restriction is contractive on every fixed Sobolev block. -/
theorem block_subalphabet_le (directions : κ → P) (e : ι → κ) (he : Function.Injective e)
    (q : ℕ) (f : P → E) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : P) :
    block (directions ∘ e) q f n x ≤ block directions q f n x := by
  rw [block_eq_sum_levels _ q f hf,block_eq_sum_levels _ q f hf]
  exact sum_le_sum (fun k _ => wordSum_subalphabet_le directions e he f (n+k) x)

omit [Fintype ι] in
/-- A linear parameter map transports the actual directions exactly. -/
theorem wordDerivative_comp_right (directions : ι → P) (A : P →L[ℝ] Q)
    (f : Q → E) (hf : ContDiff ℝ ∞ f) {n : ℕ} (w : Fin n → ι) (x : P) :
    wordDerivative directions (f ∘ A) w x = wordDerivative (A ∘ directions) f w (A x) := by
  have h := congrArg (fun D : P[×n]→L[ℝ] E => D (fun j => directions (w j)))
    (A.iteratedFDeriv_comp_right hf x (i := n) (by simp))
  exact h

theorem wordSum_comp_right (directions : ι → P) (A : P →L[ℝ] Q)
    (f : Q → E) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : P) :
    wordSum directions (f ∘ A) n x = wordSum (A ∘ directions) f n (A x) := by
  unfold wordSum
  exact sum_congr rfl (fun w _ => congrArg norm (wordDerivative_comp_right directions A f hf w x))

/-- Restricting parameters does not change a fixed block when the directions are transported. -/
theorem block_comp_right (directions : ι → P) (A : P →L[ℝ] Q)
    (q : ℕ) (f : Q → E) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : P) :
    block directions q (f ∘ A) n x = block (A ∘ directions) q f n (A x) := by
  rw [block_eq_sum_levels _ q _ (hf.comp A.contDiff),block_eq_sum_levels _ q _ hf]
  exact sum_congr rfl (fun k _ => wordSum_comp_right directions A f hf (n+k) x)

end EulerParameterWordGevrey

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanPacketProvider

open Set Real MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerCylinderSpatialEmbedding
  EulerCylinderSpatialMean EulerMeanTimeContinuousTranslation EulerCylinderSobolev
  EulerParameterWordGevrey EulerGevrey EulerPacketCylinderField EulerPacketProfileRecursion
open scoped ContDiff

/-- Spatial direction, given by `(standardDirection i).1`. -/
def spatialDirection (i : Fin 4) : Space := (standardDirection i).1

theorem spatialDirection_norm (i : Fin 4) : ‖spatialDirection i‖ ≤ 1 := by
  cases i using Fin.cases <;> simp [spatialDirection]

variable (P T : ℝ) [Fact (0 < P)]

/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanCylinderWordBounds1 : NormedAddCommGroup C(Icc (0 : ℝ) T,L2) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanCylinderWordBounds2 : NormedSpace ℝ C(Icc (0 : ℝ) T,L2) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,LiftL2 P)` instance to shorten
typeclass synthesis. -/
local instance instMeanCylinderWordBounds3 : NormedAddCommGroup C(Icc (0 : ℝ) T,LiftL2 P) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,LiftL2 P)` instance to shorten typeclass
synthesis. -/
local instance instMeanCylinderWordBounds4 : NormedSpace ℝ C(Icc (0 : ℝ) T,LiftL2 P) :=
    inferInstance

theorem spatialEmbeddingPath_norm : ‖spatialEmbeddingPath P T‖ ≤ sqrt P := by
  apply opNorm_le_bound _ (sqrt_nonneg P)
  intro p
  apply (ContinuousMap.norm_le _ (mul_nonneg (sqrt_nonneg P) (norm_nonneg p))).mpr
  intro t
  exact ((embedding (V := Space) P).le_of_opNorm_le (embedding_norm P) (p t)).trans
    (mul_le_mul_of_nonneg_left (p.norm_coe_le_norm t) (sqrt_nonneg P))

theorem pathMean_spatialEmbeddingPath (p : C(Icc (0 : ℝ) T, L2)) :
    pathMean P (spatialEmbeddingPath P T p) = p := by
  apply ContinuousMap.ext
  intro t
  exact mean_embedding P (p t)

theorem spatialEmbeddingPath_block_le (p : C(Icc (0 : ℝ) T, L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p))
    (q n : ℕ) (a : LiftTangent) :
    block standardDirection q
      (fun b : LiftTangent => pathTranslate P b (spatialEmbeddingPath P T p)) n a ≤
      sqrt P*block spatialDirection q (fun b : Space => pathTranslation T b p) n a.1 := by
  let f := fun b : Space => pathTranslation T b p
  let fstMap : LiftTangent →L[ℝ] Space := fst ℝ Space ℝ
  have he : (fun b : LiftTangent => pathTranslate P b (spatialEmbeddingPath P T p)) =
      (spatialEmbeddingPath P T) ∘ (f ∘ fstMap) :=
    funext (fun b => spatialEmbeddingPath_translation P T p b)
  refine (congrArg (fun g : LiftTangent → C(Icc (0 : ℝ) T,LiftL2 P) =>
    block standardDirection q g n a) he).trans_le ?_
  have hh := block_comp_clm_le standardDirection q (spatialEmbeddingPath P T)
    (f ∘ fstMap) (hp.comp fstMap.contDiff) n a
  have hh := hh.trans_eq (congrArg (fun r : ℝ => ‖spatialEmbeddingPath P T‖*r)
    (block_comp_right standardDirection fstMap q f hp n a))
  exact hh.trans (mul_le_mul_of_nonneg_right (spatialEmbeddingPath_norm P T)
    (block_nonneg spatialDirection q f n a.1))

theorem ordinaryPath_block_le (p : C(Icc (0 : ℝ) T, L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p))
    (q n : ℕ) (a : Space) :
    block spatialDirection q (fun b : Space => pathTranslation T b p) n a ≤
      (P⁻¹*sqrt P)*block standardDirection q
        (fun b : LiftTangent => pathTranslate P b (spatialEmbeddingPath P T p)) n (a,0) := by
  let f := fun b : Space => pathTranslation T b p
  let fstMap : LiftTangent →L[ℝ] Space := fst ℝ Space ℝ
  let g := fun b : LiftTangent => pathTranslate P b (spatialEmbeddingPath P T p)
  have he : (fun b : LiftTangent => pathMean P (g b)) = f ∘ fstMap := by
    funext b
    change pathMean P (pathTranslate P b (spatialEmbeddingPath P T p)) = f (fstMap b)
    rw [spatialEmbeddingPath_translation, pathMean_spatialEmbeddingPath]
    rfl
  have hh := pathMean_block_bound P standardDirection q g (spatialEmbeddingPath_orbit P T p hp) n
      (a,0)
  rw [he, block_comp_right standardDirection fstMap q f hp] at hh
  exact hh

theorem ordinaryPath_majorant (p : C(Icc (0 : ℝ) T, L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p))
    (q : ℕ) (R A : ℝ) (d : ℕ)
    (hb : ∀ n, block standardDirection q
      (fun b : LiftTangent => pathTranslate P b (spatialEmbeddingPath P T p)) n 0 ≤ A*majorant R d
          n)
    (n : ℕ) (a : Space) :
    block spatialDirection q (fun b : Space => pathTranslation T b p) n a ≤
      ((P⁻¹*sqrt P)*A)*majorant R d n := by
  have hh := ordinaryPath_block_le P T p hp q n a
  rw [path_block_constant P standardDirection q (spatialEmbeddingPath P T p)
    (spatialEmbeddingPath_orbit P T p hp)] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left (hb n)
    (mul_nonneg (inv_nonneg.mpr (le_of_lt (Fact.out : 0 < P))) (sqrt_nonneg P))).trans_eq (by ring))

theorem spatialEmbeddingPath_majorant (p : C(Icc (0 : ℝ) T, L2))
    (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p))
    (q : ℕ) (R A : ℝ) (d : ℕ)
    (hb : ∀ n a, block spatialDirection q (fun b : Space => pathTranslation T b p) n a ≤
      A*majorant R d n) (n : ℕ) :
    block standardDirection q
      (fun b : LiftTangent => pathTranslate P b (spatialEmbeddingPath P T p)) n 0 ≤
      (sqrt P*A)*majorant R d n := by
  exact (spatialEmbeddingPath_block_le P T p hp q n 0).trans
    ((mul_le_mul_of_nonneg_left (hb n 0) (sqrt_nonneg P)).trans_eq (by ring))

theorem embedding_mean_norm_product : sqrt P*(P⁻¹*sqrt P) = 1 := by
  have hP := (Fact.out : 0 < P)
  calc
    _ = P⁻¹*(sqrt P)^2 := by ring
    _ = 1 := by rw [sq_sqrt hP.le, inv_mul_cancel₀ hP.ne']

namespace Forcing

variable {T} {D : Data} {raw : VectorField} (G : Forcing D raw)

theorem ordinary_word_bound {q : ℕ} {R A : ℝ} {d : ℕ}
    (hb : (G.toCylinderField P).WordBound q R A d) (n : ℕ) (a : Space) :
    block spatialDirection q (fun b : Space => pathTranslation D.T b G.path) n a ≤
      ((P⁻¹*sqrt P)*A)*majorant R d n :=
  ordinaryPath_majorant P D.T G.path G.path_orbit q R A d hb n a

theorem toCylinderField_word_bound {q : ℕ} {R A : ℝ} {d : ℕ}
    (hb : ∀ n a, block spatialDirection q (fun b : Space => pathTranslation D.T b G.path) n a ≤
      A*majorant R d n) : (G.toCylinderField P).WordBound q R (sqrt P*A) d :=
  spatialEmbeddingPath_majorant P D.T G.path G.path_orbit q R A d hb

end Forcing
end EulerMeanPacketProvider

end
end

end

section

/-! A single uniform-time forcing bound suffices for the normalized mean estimates. -/

@[expose] public section

noncomputable section

namespace EulerMeanPacketProvider.SobolevData

open EulerSmoothLimit EulerMeanTimeTranslation EulerMeanTimeContinuousTranslation
  EulerParameterWordGevrey EulerGevrey EulerPacketProfileRecursion
open scoped ContDiff

variable {D : Data} {ι : Type*} [Fintype ι] {q : ℕ} {R : ℝ}

theorem radius_nonneg (E : SobolevData D ι q R) : 0 ≤ R := by
  have hr : 0 ≤ E.Rc := (by norm_num : (0 : ℝ) ≤ 1024).trans E.radius_lower
  have hrc := sobolevCoefficientRadius_nonneg (ι := ι) E.Rc hr
  have hm : 0 ≤ E.M := (by norm_num : (0 : ℝ) ≤ 1).trans E.inverse_cost_lower
  exact (mul_nonneg (mul_nonneg (by norm_num) hm) (by linarith)).trans E.radius_budget

/-- The fixed normalized time factor may be chosen as max(1,sqrt(T)); it
does not depend on the forcing grade or scalar envelope. -/
theorem path_envelope_bounds (E : SobolevData D ι q R)
    (hCf1 : 1 ≤ E.Cf) (hCfT : Real.sqrt D.T ≤ E.Cf)
    (directions : ι → Space) (hd : ∀ i, ‖directions i‖ ≤ 1)
    {raw : VectorField} (G : Forcing D raw) (d : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ n a, block directions q (fun b : Space => pathTranslation D.T b G.path) n a ≤
      A*majorant R d n) :
    (∀ n a, block directions q (fun b : Space => pathTranslation D.T b G.velocityPath) n a ≤
      A*(E.velocityAmplitude*majorant R (d+2) n)) ∧
    (∀ n a, block directions q (fun b : Space => pathTranslation D.T b G.derivativePath) n a ≤
      A*(E.derivativeAmplitude*majorant R (d+3) n)) ∧
    (∀ n a, block directions q (fun b : Space => pathTranslation D.T b G.pressureForcePath) n a ≤
      A*(E.pressureAmplitude*majorant R (d+3) n)) := by
  apply E.envelope_bounds directions hd G d A hA
  · intro n a
    have h := (pathLp_block_le directions q D.T D.T_pos.le G.path G.path_orbit n a).trans
      (mul_le_mul_of_nonneg_left (hb n a) (Real.sqrt_nonneg D.T))
    have hm := mul_nonneg hA (majorant_nonneg R E.radius_nonneg d n)
    have hc := mul_le_mul_of_nonneg_right hCfT hm
    exact h.trans (by nlinarith)
  · intro n a
    have hm := mul_nonneg hA (majorant_nonneg R E.radius_nonneg d n)
    have hc := mul_le_mul_of_nonneg_right hCf1 hm
    exact (hb n a).trans (by nlinarith)

end EulerMeanPacketProvider.SobolevData

end
end

end

@[expose] public section

noncomputable section

namespace EulerMeanPacketProvider

open Set Real ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanCoefficients EulerMeanTimeContinuousTranslation EulerParameterWordGevrey EulerGevrey
  EulerMeanStrongContinuousGevrey EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerPacketPointJets EulerPacketProfileRecursion EulerPacketCylinderField
open scoped ContDiff BoundedContinuousFunction

/-- All quantitative inputs concern the source coefficients and their inverse.
The fixed normalized forcing factor only accounts for time-L² inclusion. -/
structure Budget (D : Data) (q : ℕ) (R : ℝ) extends SobolevData D (Fin 4) q R where
  forcing_one : 1 ≤ Cf
  forcing_time : sqrt D.T ≤ Cf

/-- Frame coefficient, bundling `path`, `orbit`, `raw_eq`. -/
def Data.frameCoefficient (D : Data) : MatrixCoefficient D.T
    (fun z => D.F.field (D.clamp z.1) z.2.1) where
  path := D.F.field
  orbit := D.F.translation_contDiff
  raw_eq t x θ := by rw [Data.clamp_coe]

namespace Forcing

variable {D : Data} {raw : VectorField} (G : Forcing D raw)
  (P : ℝ) [Fact (0 < P)]

/-- Pressure force cylinder field, given by `G.pressureForceForcing.toCylinderField P`. -/
def pressureForceCylinderField : EulerPacketCylinderField.Field P D.T G.pressureForce :=
  G.pressureForceForcing.toCylinderField P

/-- This witness represents the literal spatial gradient encoded by the
packet pressure jet, not merely the projected physical pressure force. -/
def pressureGradientCylinderField : EulerPacketCylinderField.Field P D.T (pressureGradient
    G.scalar) :=
  (D.frameCoefficient.adjoint.multiply (G.pressureForceCylinderField P)).congr (by
    intro t x θ
    change pressureGradient G.scalar (t,(x,θ)) =
      (D.F.field (D.clamp t) x).adjoint (G.pressureForce (t,(x,θ)))
    rw [Data.clamp_coe]
    change (toDual ℝ Space).symm ((pressureJet G.scalar (t,(x,θ))).2.comp spatialInjection) = _
    rw [pressureJet_spatial_derivative G.scalar t x θ
      ((G.scalar_spatial_smooth t).differentiable (by simp) (x,θ))]
    exact G.scalarGradient_eq t x θ)

theorem restore_cylinder_word_bound {q d : ℕ} {R A C : ℝ}
    (hb : ∀ n a, block spatialDirection q (fun b : Space => pathTranslation D.T b G.path) n a ≤
      ((P⁻¹*sqrt P)*A)*(C*majorant R d n)) :
    (G.toCylinderField P).WordBound q R (A*C) d := by
  have hh := G.toCylinderField_word_bound P (A := ((P⁻¹*sqrt P)*A)*C) (fun n a =>
    (hb n a).trans_eq (by ring))
  have hC : sqrt P*(((P⁻¹*sqrt P)*A)*C) = A*C := by
    calc
      _ = (sqrt P*(P⁻¹*sqrt P))*(A*C) := by ring
      _ = _ := by rw [embedding_mean_norm_product, one_mul]
  simpa only [hC] using hh

end Forcing

namespace Budget

variable {D : Data} {q : ℕ} {R : ℝ} (B : Budget D q R)

/-- Velocity cost, given by `B.toSobolevData.velocityAmplitude`. -/
def velocityCost : ℝ := B.toSobolevData.velocityAmplitude
/-- Derivative cost, given by `B.toSobolevData.derivativeAmplitude`. -/
def derivativeCost : ℝ := B.toSobolevData.derivativeAmplitude
/-- Pressure force cost, given by `B.toSobolevData.pressureAmplitude`. -/
def pressureForceCost : ℝ := B.toSobolevData.pressureAmplitude
/-- Pressure gradient cost, given by `3*sobolevCoefficientAmplitude (Fin 4) q B.Rc
B.CF*B.pressureForceCost`. -/
def pressureGradientCost : ℝ := 3*sobolevCoefficientAmplitude (Fin 4) q B.Rc
    B.CF*B.pressureForceCost

theorem coefficient_radius_nonneg : 0 ≤ B.Rc :=
  (by norm_num : (0:ℝ) ≤ 1024).trans B.radius_lower

theorem radius_bounds : 1 ≤ R ∧ sobolevCoefficientRadius (Fin 4) B.Rc ≤ R := by
  have hr := sobolevCoefficientRadius_nonneg (ι := Fin 4) B.Rc B.coefficient_radius_nonneg
  have hm := B.inverse_cost_lower
  have h := B.radius_budget
  constructor <;> nlinarith only [hr, hm, h]

theorem costs_nonneg : 0 ≤ B.velocityCost ∧ 0 ≤ B.derivativeCost ∧
    0 ≤ B.pressureForceCost ∧ 0 ≤ B.pressureGradientCost := by
  have hF := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q B.Rc B.CF
    B.coefficient_radius_nonneg B.CF_nonneg
  have hF₁ := sobolevCoefficientAmplitude_nonneg (ι := Fin 4) q B.Rc B.CF₁
    B.coefficient_radius_nonneg B.CF₁_nonneg
  have hT := coordinateTraceCost_nonneg D.T D.T_pos.le
  have hf := B.Cf_nonneg
  unfold velocityCost derivativeCost pressureGradientCost pressureForceCost
    SobolevData.velocityAmplitude SobolevData.derivativeAmplitude SobolevData.pressureAmplitude
  constructor
  · positivity
  constructor
  · positivity
  constructor <;> positivity

theorem frameCoefficient_bound (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath D.frameCoefficient.path) a‖ ≤
      B.CF*majorant B.Rc 0 n :=
  D.F.norm_iteratedFDeriv_translation_le n (B.CF*majorant B.Rc 0 n)
    (mul_nonneg B.CF_nonneg (majorant_nonneg B.Rc B.coefficient_radius_nonneg 0 n))
    (B.frame_bound n) a

/-- Same-radius bounds on the three actual physical output paths. The
period factors from averaging and constant extension cancel exactly. -/
theorem physical_word_bounds (P : ℝ) [Fact (0 < P)] {raw : VectorField}
    (G : Forcing D raw) (d : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hG : (G.toCylinderField P).WordBound q R A d) :
    (G.vectorCylinderField P).WordBound q R (A*B.velocityCost) (d+2) ∧
    (G.vectorDerivativeCylinderField P).WordBound q R (A*B.derivativeCost) (d+3) ∧
    (G.pressureForceCylinderField P).WordBound q R (A*B.pressureForceCost) (d+3) := by
  have hA' : 0 ≤ (P⁻¹*sqrt P)*A := by
    have hp := (Fact.out : 0 < P)
    positivity
  obtain ⟨hv, hd, hp⟩ := B.toSobolevData.path_envelope_bounds B.forcing_one B.forcing_time
    spatialDirection spatialDirection_norm G d ((P⁻¹*sqrt P)*A) hA'
    (G.ordinary_word_bound P hG)
  exact ⟨G.vectorForcing.restore_cylinder_word_bound P hv,
    G.vectorDerivativeForcing.restore_cylinder_word_bound P hd,
    G.pressureForceForcing.restore_cylinder_word_bound P hp⟩

/-- The mean solver consumes at most three shifts, with a linear forcing
amplitude and the identical radius. The third output is d(bar q). -/
theorem word_bounds (P : ℝ) [Fact (0 < P)] {raw : VectorField}
    (G : Forcing D raw) (d : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hG : (G.toCylinderField P).WordBound q R A d) :
    (G.vectorCylinderField P).WordBound q R (A*B.velocityCost) (d+2) ∧
    (G.vectorDerivativeCylinderField P).WordBound q R (A*B.derivativeCost) (d+3) ∧
    (G.pressureGradientCylinderField P).WordBound q R (A*B.pressureGradientCost) (d+3) := by
  obtain ⟨hv, hd, hp⟩ := B.physical_word_bounds P G d A hA hG
  have hprod := hp.multiply D.frameCoefficient.adjoint B.Rc B.CF
    B.coefficient_radius_nonneg B.CF_nonneg (mul_nonneg hA B.costs_nonneg.2.2.1) B.radius_bounds.2
    (D.frameCoefficient.adjoint_bound B.Rc B.CF B.frameCoefficient_bound)
  refine ⟨hv, hd, ?_⟩
  change (D.frameCoefficient.adjoint.multiply (G.pressureForceCylinderField P)).WordBound q R
    (A*B.pressureGradientCost) (d+3)
  convert! hprod using 1
  unfold pressureGradientCost
  ring

/-- Any actual cylinder witness of the input raw forcing can supply the
bound; the provider's canonical choice is immaterial. -/
theorem word_bounds_of_field (P : ℝ) [Fact (0 < P)] {raw : VectorField}
    (G : Forcing D raw) (F : EulerPacketCylinderField.Field P D.T raw)
    (d : ℕ) (A : ℝ) (hA : 0 ≤ A) (hF : F.WordBound q R A d) :
    (G.vectorCylinderField P).WordBound q R (A*B.velocityCost) (d+2) ∧
    (G.vectorDerivativeCylinderField P).WordBound q R (A*B.derivativeCost) (d+3) ∧
    (G.pressureGradientCylinderField P).WordBound q R (A*B.pressureGradientCost) (d+3) :=
  B.word_bounds P G d A hA (hF.transfer (G.toCylinderField P))

/-- A common three-shift budget also covers the velocity, and is therefore
within the source allowance of ten shifts. -/
theorem three_shift_bounds (P : ℝ) [Fact (0 < P)] {raw : VectorField}
    (G : Forcing D raw) (F : EulerPacketCylinderField.Field P D.T raw)
    (d : ℕ) (A : ℝ) (hA : 0 ≤ A) (hF : F.WordBound q R A d) :
    (G.vectorCylinderField P).WordBound q R (A*B.velocityCost) (d+3) ∧
    (G.vectorDerivativeCylinderField P).WordBound q R (A*B.derivativeCost) (d+3) ∧
    (G.pressureGradientCylinderField P).WordBound q R (A*B.pressureGradientCost) (d+3) := by
  obtain ⟨hv, hd, hp⟩ := B.word_bounds_of_field P G F d A hA hF
  exact ⟨hv.mono_shift B.radius_bounds.1 (mul_nonneg hA B.costs_nonneg.1) (by omega), hd, hp⟩

/-- The mean profile H₀^(2p−2) is a constant scalar envelope. The same
fixed source budget applies at every grade and every derivative shift. -/
theorem grade_profile_bounds (P : ℝ) [Fact (0 < P)] {raw : VectorField}
    (G : Forcing D raw) (F : EulerPacketCylinderField.Field P D.T raw)
    (p d : ℕ) (A H₀ : ℝ) (hA : 0 ≤ A) (hH₀ : 0 ≤ H₀)
    (hF : F.WordBound q R (A * H₀ ^ (2 * p - 2)) d) :
    (G.vectorCylinderField P).WordBound q R ((A*B.velocityCost)*H₀^(2*p-2)) (d+3) ∧
    (G.vectorDerivativeCylinderField P).WordBound q R ((A*B.derivativeCost)*H₀^(2*p-2)) (d+3) ∧
    (G.pressureGradientCylinderField P).WordBound q R ((A*B.pressureGradientCost)*H₀^(2*p-2)) (d+3)
        := by
  have hh := B.three_shift_bounds P G F d (A*H₀^(2*p-2)) (mul_nonneg hA (pow_nonneg hH₀ _)) hF
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hh

end Budget
end EulerMeanPacketProvider
