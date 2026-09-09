/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryGradientEnergy
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryVariableGronwall
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerHigherEnergy

@[expose] public section

/-! Actual gradient-supremum control of Euler Sobolev norms.  The
gradient norm is a constructed continuous path, its time integral
controls H³, and the checked H³-tame estimate then propagates every
higher order on the same time interval. -/

noncomputable section

namespace EulerOrdinarySobolev.Evolution

open Set MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerMeanClassical
  EulerMeanSobolevBoundedField EulerVolterraConvolution EulerContinuousTimeIntegral

variable {T : ℝ} {hT : 0 ≤ T}

def gradientNormPath (U : Evolution T hT) : C(Icc (0 : ℝ) T,ℝ) :=
  ⟨fun t => ‖finiteField (U.velocity t).derivative‖,
    (continuous_finiteField (fun t => (U.velocity t).derivative)
      (continuous_jetLp_derivative U.velocity U.velocity_continuous)).norm⟩

theorem gradientNormPath_nonneg (U : Evolution T hT) (t : Icc (0 : ℝ) T) :
    0 ≤ U.gradientNormPath t := by
  change 0 ≤ ‖finiteField (U.velocity t).derivative‖
  exact norm_nonneg _

theorem gradientNormPath_le_iff (U : Evolution T hT) (t : Icc (0 : ℝ) T) (K : ℝ) :
    U.gradientNormPath t ≤ K ↔ ∀ x, ‖fderiv ℝ (U.velocity t).field x‖ ≤ K := by
  change ‖finiteField (U.velocity t).derivative‖ ≤ K ↔ _
  rw [BoundedContinuousFunction.norm_le_of_nonempty]
  simp only [finiteField_apply]
  rfl

theorem pointwise_gradient_le (U : Evolution T hT) (t : Icc (0 : ℝ) T) (x : Space) :
    ‖fderiv ℝ (U.velocity t).field x‖ ≤ U.gradientNormPath t :=
  (U.gradientNormPath_le_iff t _).mp le_rfl x

def gradientIntegral (U : Evolution T hT) (t : Icc (0 : ℝ) T) : ℝ :=
  realIntegral T hT U.gradientNormPath t

theorem gradientIntegral_nonneg (U : Evolution T hT) (t : Icc (0 : ℝ) T) :
    0 ≤ U.gradientIntegral t :=
  intervalIntegral.integral_nonneg_of_forall t.property.1
    (fun r => U.gradientNormPath_nonneg (projIcc 0 T hT r))

theorem gradientIntegral_le_const (U : Evolution T hT) (K : ℝ)
    (hK : ∀ t x, ‖fderiv ℝ (U.velocity t).field x‖ ≤ K) (t : Icc (0 : ℝ) T) :
    U.gradientIntegral t ≤ K*(t : ℝ) := by
  have hc := extendPath_continuous T hT U.gradientNormPath
  calc
    _ ≤ ∫ _r in (0 : ℝ)..(t : ℝ), K :=
      intervalIntegral.integral_mono_on t.property.1 (hc.intervalIntegrable 0 t)
        (continuous_const.intervalIntegrable 0 t) (fun r _ =>
          (U.gradientNormPath_le_iff (projIcc 0 T hT r) K).mpr (hK _))
    _ = _ := by simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]; ring

theorem integerEnergyDerivative_gradient (U : Evolution T hT) (K : ℝ)
    (t : Icc (0 : ℝ) T) (hK : ∀ x, ‖fderiv ℝ (U.velocity t).field x‖ ≤ K) :
    U.integerEnergyDerivative 3 t ≤ gradientEnergyConstant*K*U.integerEnergyPath 3 t := by
  rw [integerEnergyDerivative,derivative_eq_eulerRhs]
  apply h3_energy_gradient _ _ K hK _ (U.solenoidal t) (U.gradient t)
  exact solenoidal_representative_divergence _ (U.solenoidal t) _ (U.velocity t).smooth
    (U.velocity t).toLp_ae

theorem h3_energy_gradientIntegral (U : Evolution T hT) (t : Icc (0 : ℝ) T) :
    wordEnergy 3 (U.velocity t) ≤ wordEnergy 3 (U.velocity ⟨0,le_rfl,hT⟩)*
      Real.exp (gradientEnergyConstant*U.gradientIntegral t) := by
  have hd (r : ℝ) (hr : r ∈ Ico 0 T) :
      HasDerivWithinAt (extendPath T hT (U.integerEnergyPath 3))
        (U.integerEnergyDerivative 3 (projIcc 0 T hT r)) (Icc 0 T) r := by
    have h := U.integerEnergy_hasDerivWithinAt 3 ⟨r,hr.1,hr.2.le⟩
    simpa only [projIcc_of_mem hT (show r ∈ Icc 0 T from ⟨hr.1,hr.2.le⟩)] using h
  have hb (r : ℝ) (_hr : r ∈ Ico 0 T) :
      U.integerEnergyDerivative 3 (projIcc 0 T hT r) ≤
        gradientEnergyConstant*extendPath T hT U.gradientNormPath r*
          extendPath T hT (U.integerEnergyPath 3) r :=
    U.integerEnergyDerivative_gradient _ _ (U.pointwise_gradient_le _)
  have h := variable_linear_stability T hT
    (extendPath T hT (U.integerEnergyPath 3))
    (fun r => U.integerEnergyDerivative 3 (projIcc 0 T hT r))
    gradientEnergyConstant U.gradientNormPath
    ((U.integerEnergyPath 3).continuous.comp continuous_projIcc).continuousOn hd hb t
  simpa only [extendPath,projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩),
    integerEnergyPath,ContinuousMap.coe_mk,gradientIntegral] using h

theorem h3_energy_gradient_bound (U : Evolution T hT) (K : ℝ)
    (hK : ∀ t x, ‖fderiv ℝ (U.velocity t).field x‖ ≤ K) (t : Icc (0 : ℝ) T) :
    wordEnergy 3 (U.velocity t) ≤ wordEnergy 3 (U.velocity ⟨0,le_rfl,hT⟩)*
      Real.exp (gradientEnergyConstant*K*(t : ℝ)) := by
  apply (U.h3_energy_gradientIntegral t).trans
  apply mul_le_mul_of_nonneg_left _ (wordEnergy_nonneg _ _)
  apply Real.exp_le_exp.mpr
  exact (mul_le_mul_of_nonneg_left (U.gradientIntegral_le_const K hK t)
    gradientEnergyConstant_nonneg).trans_eq (by ring)

def gradientH3Bound (U : Evolution T hT) (G : ℝ) : ℝ :=
  Real.sqrt (wordEnergy 3 (U.velocity ⟨0,le_rfl,hT⟩)*Real.exp (gradientEnergyConstant*G))

theorem wordBound_of_gradientIntegral (U : Evolution T hT) (G : ℝ)
    (hG : ∀ t, U.gradientIntegral t ≤ G) (t : Icc (0 : ℝ) T) :
    WordBound 3 (U.gradientH3Bound G) (U.velocity t) := by
  intro n hn w
  apply (wordBound_sqrt_energy 3 (U.velocity t) n hn w).trans
  apply Real.sqrt_le_sqrt
  exact (U.h3_energy_gradientIntegral t).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (hG t) gradientEnergyConstant_nonneg))
      (wordEnergy_nonneg _ _))

theorem h3_tensorNorm_of_gradientIntegral (U : Evolution T hT) (G : ℝ)
    (hG : ∀ t, U.gradientIntegral t ≤ G) (t : Icc (0 : ℝ) T) :
    tensorNorm 3 (U.velocity t) ≤ wordCount 3*U.gradientH3Bound G :=
  tensorNorm_le_wordCount _ 3 _ (U.wordBound_of_gradientIntegral G hG t)

theorem higher_energy_of_gradientIntegral (U : Evolution T hT) (m : ℕ) (hm : 3 ≤ m)
    (G : ℝ) (hG : ∀ t, U.gradientIntegral t ≤ G) (t : Icc (0 : ℝ) T) :
    wordEnergy m (U.velocity t) ≤ wordEnergy m (U.velocity ⟨0,le_rfl,hT⟩)*
      Real.exp (tameEnergyConstant m*U.gradientH3Bound G*T) :=
  U.integer_energy_uniform m hm _ (U.wordBound_of_gradientIntegral G hG) t

theorem higher_tensorNorm_of_gradientIntegral (U : Evolution T hT) (m : ℕ) (hm : 3 ≤ m)
    (G : ℝ) (hG : ∀ t, U.gradientIntegral t ≤ G) (t : Icc (0 : ℝ) T) :
    tensorNorm m (U.velocity t) ≤ wordCount m*
      Real.sqrt (wordEnergy m (U.velocity ⟨0,le_rfl,hT⟩)*
        Real.exp (tameEnergyConstant m*U.gradientH3Bound G*T)) :=
  U.tensorNorm_uniform m hm _ (U.wordBound_of_gradientIntegral G hG) t

theorem higher_tensorNorm_of_gradientBound (U : Evolution T hT) (m : ℕ) (hm : 3 ≤ m)
    (K : ℝ) (hK : ∀ t x, ‖fderiv ℝ (U.velocity t).field x‖ ≤ K)
    (t : Icc (0 : ℝ) T) :
    tensorNorm m (U.velocity t) ≤ wordCount m*
      Real.sqrt (wordEnergy m (U.velocity ⟨0,le_rfl,hT⟩)*
        Real.exp (tameEnergyConstant m*U.gradientH3Bound (K*T)*T)) := by
  have hK0 : 0 ≤ K := (norm_nonneg (fderiv ℝ (U.velocity t).field 0)).trans (hK t 0)
  exact U.higher_tensorNorm_of_gradientIntegral m hm (K*T)
    (fun s => (U.gradientIntegral_le_const K hK s).trans
      (mul_le_mul_of_nonneg_left s.property.2 hK0)) t

end EulerOrdinarySobolev.Evolution
