/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointData
public import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletEquation

@[expose] public section

/-!
The literal homogeneous physical equation for the constructed nonzero-
terminal cylinder history. Pointwise tangency and the normal residual are
deduced from the actual frame range; there is no single L² normal vector.
-/

noncomputable section

namespace EulerCylinderDirichlet.Coefficients

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderRectangular
  EulerTransverseGramInverse EulerTransverseNormalResidual EulerBoundedFieldCalculus
open scoped BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E) (Y : CylinderL2 P U)

theorem endpoint_coordinate_equation_ae (t : Icc (0 : ℝ) T) :
    ∀ᵐ x ∂liftMeasure P,
      gram (D.Q t x.1) (D.endpointAcceleration P Y t x) =
        (D.Q t x.1).adjoint ((-2 : ℝ) • D.Q₁ t x.1 (D.endpointCoordinate P Y t x)) := by
  let v := D.endpointCoordinate P Y t
  let a := D.endpointAcceleration P Y t
  let r := (-2 : ℝ) • fullOperatorMap P (D.Q₁ t) v
  have he : (fullOperatorMap P (D.Q t)).adjoint (fullOperatorMap P (D.Q t) a) =
      (fullOperatorMap P (D.Q t)).adjoint r := D.endpoint_projected_equation P Y t
  rw [fullOperatorMap_adjoint] at he
  filter_upwards [
    EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (adjointMap (D.Q t)))
      (fullOperatorMap P (D.Q t) a),
    EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (D.Q t)) a,
    EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (adjointMap (D.Q t))) r,
    Lp.coeFn_smul (-2 : ℝ) (fullOperatorMap P (D.Q₁ t) v),
    EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (D.Q₁ t)) v]
    with x hl hq hr hs hq₁
  have hp := congrArg (fun w : CylinderL2 P U => w x) he
  change fullOperatorMap P (adjointMap (D.Q t)) (fullOperatorMap P (D.Q t) a) x =
    fullOperatorMap P (adjointMap (D.Q t)) r x at hp
  change fullOperatorMap P (adjointMap (D.Q t)) (fullOperatorMap P (D.Q t) a) x =
    (D.Q t x.1).adjoint (fullOperatorMap P (D.Q t) a x) at hl
  change fullOperatorMap P (D.Q t) a x = D.Q t x.1 (a x) at hq
  change fullOperatorMap P (adjointMap (D.Q t)) r x = (D.Q t x.1).adjoint (r x) at hr
  change r x = (-2 : ℝ) • (fullOperatorMap P (D.Q₁ t) v x) at hs
  change fullOperatorMap P (D.Q₁ t) v x = D.Q₁ t x.1 (v x) at hq₁
  rw [hl,hq,hr,hs,hq₁] at hp
  exact hp

theorem endpointVelocity_ae (t : Icc (0 : ℝ) T) :
    D.endpointVelocity P Y t =ᵐ[liftMeasure P] fun x =>
      D.Q t x.1 (D.endpointCoordinate P Y t x) :=
  EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (D.Q t)) _

theorem endpointDerivative_ae (t : Icc (0 : ℝ) T) :
    D.endpointDerivative P Y t =ᵐ[liftMeasure P] fun x =>
      D.Q₁ t x.1 (D.endpointCoordinate P Y t x)+D.Q t x.1 (D.endpointAcceleration P Y t x) := by
  let v := D.endpointCoordinate P Y t
  let a := D.endpointAcceleration P Y t
  filter_upwards [
    EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (D.Q₁ t)) v,
    EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (D.Q t)) a,
    Lp.coeFn_add (fullOperatorMap P (D.Q₁ t) v) (fullOperatorMap P (D.Q t) a)] with x h₁ h₂ hs
  exact hs.trans (congrArg₂ (·+·) h₁ h₂)

theorem endpoint_physical_balance_ae
    (M : Icc (0 : ℝ) T → Space → E →L[ℝ] E) (m : Icc (0 : ℝ) T → Space → E)
    (hm : ∀ t x, m t x ≠ 0)
    (hTangent : ∀ t x v, ⟪m t x,D.Q t x v⟫_ℝ = 0)
    (hRange : ∀ t x η, ⟪m t x,η⟫_ℝ = 0 → ∃ v, D.Q t x v = η)
    (hFlow : ∀ t x, D.Q₁ t x = (M t x).comp (D.Q t x))
    (t : Icc (0 : ℝ) T) :
    ∀ᵐ x ∂liftMeasure P,
      D.endpointDerivative P Y t x+M t x.1 (D.endpointVelocity P Y t x)+
        (-(2*⟪m t x.1,M t x.1 (D.endpointVelocity P Y t x)⟫_ℝ)/‖m t x.1‖^2) • m t x.1 = 0 := by
  filter_upwards [D.endpoint_coordinate_equation_ae P Y t,D.endpointVelocity_ae P Y t,
    D.endpointDerivative_ae P Y t] with x he hv hd
  rw [hv,hd]
  have h := physical_velocity_balance (D.Q t x.1) (D.Q₁ t x.1) (M t x.1) (m t x.1)
    (hm t x.1) (hTangent t x.1) (hRange t x.1) (hFlow t x.1)
    (D.endpointCoordinate P Y t x) (D.endpointAcceleration P Y t x) (0 : E)
    (by simpa only [zero_sub,neg_smul] using he)
  simpa only [inner_zero_right,zero_sub] using h

end EulerCylinderDirichlet.Coefficients
