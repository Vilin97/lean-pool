/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanFixedSobolevGevrey
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketForcing
public import LeanPool.NavierStokesAndEuler.Euler.MeanScaledBoundaryGevrey
public import LeanPool.NavierStokesAndEuler.Euler.MeanSourceFixedInverse
public import LeanPool.NavierStokesAndEuler.Euler.MeanStrongContinuousGevrey
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevAcceleration
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpGramSobolev
import LeanPool.NavierStokesAndEuler.Euler.MeanSourcePressureSobolev
import LeanPool.NavierStokesAndEuler.Euler.MeanSourceTimeSobolev

/-!
# Fixed coefficient budgets for the actual mean packet inverse

These data contain only bounds on the prescribed coefficients and their
fixed inverse costs. The external radius is chosen before the forcing grade
or its scalar envelope, which is restored separately by homogeneity.
-/

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
