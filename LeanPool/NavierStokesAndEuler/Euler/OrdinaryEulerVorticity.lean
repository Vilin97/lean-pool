/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerGradientControl
public import LeanPool.NavierStokesAndEuler.Euler.PacketPotentialRegularity

/-! Genuine ordinary vorticity fields, their continuous supremum norms,
and actual time integrals. These are literal curls of the velocity. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerVectorCalculus
  EulerMeanSobolevBoundedField EulerMeanBoundary EulerMeanCutoffCurl EulerPacketPiola
  EulerVolterraConvolution EulerContinuousTimeIntegral
open scoped ContDiff Topology

/-- Vorticity field, given by `mapField curlOperator A.derivative`. -/
def vorticityField (A : SmoothL2Field Space) : SmoothL2Field Space :=
  mapField curlOperator A.derivative

theorem vorticityField_apply (A : SmoothL2Field Space) (x : Space) :
    (vorticityField A).field x=vectorCurl A.field x :=
  (vectorCurl_eq_matrix A.field x (A.smooth.differentiable (by simp) x)).symm

theorem vorticityField_continuous {K : Type*} [TopologicalSpace K]
    (A : K → SmoothL2Field Space) (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) (n : ℕ) :
    Continuous (fun t => (vorticityField (A t)).jetLp n) :=
  continuous_jetLp_mapField curlOperator (fun t => (A t).derivative)
    (continuous_jetLp_derivative A hA) n

/-- Vorticity norm, given by `‖finiteField (vorticityField A)‖`. -/
def vorticityNorm (A : SmoothL2Field Space) : ℝ := ‖finiteField (vorticityField A)‖

theorem vorticityNorm_nonneg (A : SmoothL2Field Space) : 0 ≤ vorticityNorm A := norm_nonneg _

theorem vorticityNorm_le_iff (A : SmoothL2Field Space) (K : ℝ) :
    vorticityNorm A ≤ K ↔ ∀ x, ‖vectorCurl A.field x‖ ≤ K := by
  unfold vorticityNorm
  rw [BoundedContinuousFunction.norm_le_of_nonempty]
  simp only [finiteField_apply,vorticityField_apply]

theorem vorticityNorm_continuous {K : Type*} [TopologicalSpace K]
    (A : K → SmoothL2Field Space) (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) :
    Continuous (fun t => vorticityNorm (A t)) :=
  (continuous_finiteField (fun t => vorticityField (A t)) (vorticityField_continuous A hA)).norm

namespace Evolution

variable {T : ℝ} {hT : 0 ≤ T} (U : Evolution T hT)

/-- Vorticity norm path, given by `⟨fun t => vorticityNorm (U.velocity
t),vorticityNorm_continuous U.velocity U.velocity_continuous⟩`. -/
def vorticityNormPath : C(Icc (0 : ℝ) T,ℝ) :=
  ⟨fun t => vorticityNorm (U.velocity t),vorticityNorm_continuous U.velocity U.velocity_continuous⟩

theorem vorticityNormPath_nonneg (t : Icc (0 : ℝ) T) : 0 ≤ U.vorticityNormPath t :=
  vorticityNorm_nonneg _

theorem vorticityNormPath_le_iff (t : Icc (0 : ℝ) T) (K : ℝ) :
    U.vorticityNormPath t ≤ K ↔ ∀ x, ‖vectorCurl (U.velocity t).field x‖ ≤ K :=
  vorticityNorm_le_iff _ K

theorem pointwise_vorticity_le (t : Icc (0 : ℝ) T) (x : Space) :
    ‖vectorCurl (U.velocity t).field x‖ ≤ U.vorticityNormPath t :=
  (U.vorticityNormPath_le_iff t _).mp le_rfl x

/-- Vorticity integral, given by `realIntegral T hT U.vorticityNormPath t`. -/
def vorticityIntegral (t : Icc (0 : ℝ) T) : ℝ := realIntegral T hT U.vorticityNormPath t

theorem vorticityIntegral_nonneg (t : Icc (0 : ℝ) T) : 0 ≤ U.vorticityIntegral t :=
  intervalIntegral.integral_nonneg_of_forall t.property.1
    (fun r => U.vorticityNormPath_nonneg (projIcc 0 T hT r))

theorem vorticityIntegral_initial : U.vorticityIntegral ⟨0,le_rfl,hT⟩=0 :=
  intervalIntegral.integral_same

theorem vorticityIntegral_continuous : Continuous U.vorticityIntegral :=
  (show Continuous (realIntegral T hT U.vorticityNormPath) from
    (show Differentiable ℝ (realIntegral T hT U.vorticityNormPath) from
      fun t => (realIntegral_hasDerivAt T hT U.vorticityNormPath
          t).differentiableAt).continuous).comp
        continuous_subtype_val

theorem vorticityIntegral_mono (s t : Icc (0 : ℝ) T) (hst : (s : ℝ) ≤ t) :
    U.vorticityIntegral s ≤ U.vorticityIntegral t :=
  intervalIntegral.integral_mono_interval le_rfl s.property.1 hst
    (Eventually.of_forall (fun r => U.vorticityNormPath_nonneg (projIcc 0 T hT r)))
    ((extendPath_continuous T hT U.vorticityNormPath).intervalIntegrable 0 t)

theorem vorticityIntegral_le_const (K : ℝ)
    (hK : ∀ t x, ‖vectorCurl (U.velocity t).field x‖ ≤ K) (t : Icc (0 : ℝ) T) :
    U.vorticityIntegral t ≤ K*(t : ℝ) := by
  have hc := extendPath_continuous T hT U.vorticityNormPath
  calc
    _ ≤ ∫ _r in (0 : ℝ)..(t : ℝ), K :=
      intervalIntegral.integral_mono_on t.property.1 (hc.intervalIntegrable 0 t)
        (continuous_const.intervalIntegrable 0 t) (fun r _ =>
          (U.vorticityNormPath_le_iff (projIcc 0 T hT r) K).mpr (hK _))
    _ = _ := by simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]; ring

theorem vorticityNormPath_le_gradient (t : Icc (0 : ℝ) T) :
    U.vorticityNormPath t ≤ ‖curlOperator‖*U.gradientNormPath t := by
  apply (U.vorticityNormPath_le_iff t _).mpr
  intro x
  rw [← vorticityField_apply]
  exact (curlOperator.le_opNorm (fderiv ℝ (U.velocity t).field x)).trans
    (mul_le_mul_of_nonneg_left (U.pointwise_gradient_le t x) (norm_nonneg _))

end Evolution
end EulerOrdinarySobolev
