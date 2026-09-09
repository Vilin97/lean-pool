/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointForcing
public import LeanPool.NavierStokesAndEuler.Euler.CylinderFieldReflection
import LeanPool.NavierStokesAndEuler.Euler.CylinderDirichletParity

/-! Actual odd terminal data give odd endpoint histories under even coefficients. -/

@[expose] public section


noncomputable section

namespace EulerCylinderDirichlet.Coefficients

open Set ContinuousLinearMap EulerLpCylinderTranslation EulerLpCylinderRectangular
  EulerCylinderFieldReflection

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (D : Coefficients T U E)
  (hQ : ∀ t x, D.Q t (-x) = D.Q t x)
  (hQ₁ : ∀ t x, D.Q₁ t (-x) = D.Q₁ t x)
  (hH : ∀ t x, D.H t (-x) = D.H t x)
  (Y : CylinderL2 P U) (hY : reflection P Y = -Y)

include hQ₁ hY in
omit [CompleteSpace U] [CompleteSpace E] in
theorem endpointForcing_odd (t : Icc (0 : ℝ) T) :
    reflection P (D.endpointForcing P Y t) = -D.endpointForcing P Y t := by
  change reflection P ((2 : ℝ) • fullOperatorMap P (D.Q₁ t) (T⁻¹ • Y)) =
    -((2 : ℝ) • fullOperatorMap P (D.Q₁ t) (T⁻¹ • Y))
  rw [map_smul,reflection_fullOperator P (D.Q₁ t) (hQ₁ t),map_smul,hY,smul_neg,map_neg,smul_neg]

include hQ hQ₁ hH hY

theorem endpointCoordinate_odd (t : Icc (0 : ℝ) T) :
    reflection P (D.endpointCoordinate P Y t) = -D.endpointCoordinate P Y t := by
  rw [D.endpointCoordinate_eq_const_sub P Y t,map_sub,map_smul,hY,smul_neg,
    D.velocityPath_odd P hQ hQ₁ hH (D.endpointForcing P Y) (D.endpointForcing_odd P hQ₁ Y hY) t]
  module

theorem endpointAcceleration_odd (t : Icc (0 : ℝ) T) :
    reflection P (D.endpointAcceleration P Y t) = -D.endpointAcceleration P Y t := by
  rw [D.endpointAcceleration_eq_forced P Y,ContinuousMap.neg_apply,map_neg,
    D.accelerationPath_odd P hQ hQ₁ hH (D.endpointForcing P Y) (D.endpointForcing_odd P hQ₁ Y hY) t]

theorem endpointVelocity_odd (t : Icc (0 : ℝ) T) :
    reflection P (D.endpointVelocity P Y t) = -D.endpointVelocity P Y t := by
  change reflection P (fullOperatorMap P (D.Q t) (D.endpointCoordinate P Y t)) = _
  rw [reflection_fullOperator P (D.Q t) (hQ t),D.endpointCoordinate_odd P hQ hQ₁ hH Y hY t,map_neg]
  rfl

theorem endpointDerivative_odd (t : Icc (0 : ℝ) T) :
    reflection P (D.endpointDerivative P Y t) = -D.endpointDerivative P Y t := by
  change reflection P (fullOperatorMap P (D.Q₁ t) (D.endpointCoordinate P Y t) +
    fullOperatorMap P (D.Q t) (D.endpointAcceleration P Y t)) = _
  rw [map_add,reflection_fullOperator P (D.Q₁ t) (hQ₁ t),reflection_fullOperator P (D.Q t) (hQ t),
    D.endpointCoordinate_odd P hQ hQ₁ hH Y hY t,D.endpointAcceleration_odd P hQ hQ₁ hH Y hY t,
    map_neg,map_neg]
  exact (neg_add _ _).symm

end EulerCylinderDirichlet.Coefficients
