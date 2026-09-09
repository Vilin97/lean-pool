/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletMean
public import LeanPool.NavierStokesAndEuler.Euler.TransverseNormalResidual

@[expose] public section

/-!
# The literal spatial equation of the actual cylinder history

The Hilbert-space projected equation is an equality of genuine L² fields.
The adjoint multiplier identity turns it into the pointwise matrix equation
almost everywhere. Its normal residual is exactly the scalar source in (11).
-/

noncomputable section

namespace EulerCylinderDirichlet.Coefficients

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderRectangular
  EulerTimeLp EulerTransverseGramInverse EulerTransverseNormalResidual EulerBoundedFieldCalculus
open scoped BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E)
  (f : C(Icc (0 : ℝ) T,CylinderL2 P E))

/-- The exact source equation (10) for the actual cylinder representatives. -/
theorem coordinate_equation_ae (t : Icc (0 : ℝ) T) :
    ∀ᵐ x ∂liftMeasure P,
      gram (D.Q t x.1) (D.accelerationPath P f t x) =
        (D.Q t x.1).adjoint (f t x-(2 : ℝ) •
          D.Q₁ t x.1 (D.velocityPath P (pathLp T D.time_pos.le f) t x)) := by
  let v := D.velocityPath P (pathLp T D.time_pos.le f) t
  let a := D.accelerationPath P f t
  let r := f t-(2 : ℝ) • fullOperatorMap P (D.Q₁ t) v
  have he : (fullOperatorMap P (D.Q t)).adjoint (fullOperatorMap P (D.Q t) a) =
      (fullOperatorMap P (D.Q t)).adjoint r := D.projected_equation P f t
  rw [fullOperatorMap_adjoint] at he
  filter_upwards [
    EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (adjointMap (D.Q t)))
      (fullOperatorMap P (D.Q t) a),
    EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (D.Q t)) a,
    EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (adjointMap (D.Q t))) r,
    Lp.coeFn_sub (f t) ((2 : ℝ) • fullOperatorMap P (D.Q₁ t) v),
    Lp.coeFn_smul (2 : ℝ) (fullOperatorMap P (D.Q₁ t) v),
    EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (D.Q₁ t)) v]
    with x hl hq hr hsub hsmul hq₁
  have hp := congrArg (fun w : CylinderL2 P U => w x) he
  change fullOperatorMap P (adjointMap (D.Q t)) (fullOperatorMap P (D.Q t) a) x =
    fullOperatorMap P (adjointMap (D.Q t)) r x at hp
  change fullOperatorMap P (adjointMap (D.Q t)) (fullOperatorMap P (D.Q t) a) x =
    (D.Q t x.1).adjoint (fullOperatorMap P (D.Q t) a x) at hl
  change fullOperatorMap P (D.Q t) a x = D.Q t x.1 (a x) at hq
  change fullOperatorMap P (adjointMap (D.Q t)) r x = (D.Q t x.1).adjoint (r x) at hr
  change fullOperatorMap P (D.Q₁ t) v x = D.Q₁ t x.1 (v x) at hq₁
  rw [hl,hq,hr] at hp
  change r x = f t x-((2 : ℝ) • fullOperatorMap P (D.Q₁ t) v) x at hsub
  change ((2 : ℝ) • fullOperatorMap P (D.Q₁ t) v) x =
    (2 : ℝ) • (fullOperatorMap P (D.Q₁ t) v x) at hsmul
  rw [hsub,hsmul,hq₁] at hp
  exact hp

theorem physicalVelocity_ae (t : Icc (0 : ℝ) T) :
    D.physicalVelocity P f t =ᵐ[liftMeasure P] fun x =>
      D.Q t x.1 (D.velocityPath P (pathLp T D.time_pos.le f) t x) :=
  EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (D.Q t)) _

theorem physicalDerivative_ae (t : Icc (0 : ℝ) T) :
    D.physicalDerivative P f t =ᵐ[liftMeasure P] fun x =>
      D.Q₁ t x.1 (D.velocityPath P (pathLp T D.time_pos.le f) t x)+
        D.Q t x.1 (D.accelerationPath P f t x) := by
  let v := D.velocityPath P (pathLp T D.time_pos.le f) t
  let a := D.accelerationPath P f t
  filter_upwards [
    EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (D.Q₁ t)) v,
    EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (D.Q t)) a,
    Lp.coeFn_add (fullOperatorMap P (D.Q₁ t) v) (fullOperatorMap P (D.Q t) a)]
    with x h₁ h₂ hs
  exact hs.trans (congrArg₂ (·+·) h₁ h₂)

/-- The scalar normal source in (11), derived from the actual inverse. -/
theorem physical_balance_ae
    (M : Icc (0 : ℝ) T → Space → E →L[ℝ] E) (m : Icc (0 : ℝ) T → Space → E)
    (hm : ∀ t x, m t x ≠ 0)
    (hTangent : ∀ t x v, ⟪m t x,D.Q t x v⟫_ℝ = 0)
    (hRange : ∀ t x η, ⟪m t x,η⟫_ℝ = 0 → ∃ v, D.Q t x v = η)
    (hFlow : ∀ t x, D.Q₁ t x = (M t x).comp (D.Q t x))
    (t : Icc (0 : ℝ) T) :
    ∀ᵐ x ∂liftMeasure P,
      D.physicalDerivative P f t x+M t x.1 (D.physicalVelocity P f t x)+
        ((⟪m t x.1,f t x⟫_ℝ-2*⟪m t x.1,M t x.1 (D.physicalVelocity P f t x)⟫_ℝ)/
          ‖m t x.1‖^2) • m t x.1 = f t x := by
  filter_upwards [D.coordinate_equation_ae P f t,D.physicalVelocity_ae P f t,
    D.physicalDerivative_ae P f t] with x he hv hd
  rw [hv,hd]
  exact physical_velocity_balance (D.Q t x.1) (D.Q₁ t x.1) (M t x.1) (m t x.1)
    (hm t x.1) (hTangent t x.1) (hRange t x.1) (hFlow t x.1) _ _ _ he

end EulerCylinderDirichlet.Coefficients
