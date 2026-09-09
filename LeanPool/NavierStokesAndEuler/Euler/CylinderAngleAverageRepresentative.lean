/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverage
public import LeanPool.NavierStokesAndEuler.Euler.CylinderAnglePrimitive
public import LeanPool.NavierStokesAndEuler.Euler.SobolevPointEvaluation
import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleRepresentative

/-! The actual L² angular average equals the literal mean of every continuous H³ representative. -/

@[expose] public section


noncomputable section

namespace EulerCylinderAngleAverage

open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerSobolevPointEvaluation EulerSpatialSobolevInverse EulerPressureSpatialRegularity
  EulerLpCylinderTranslation

variable (P : ℝ) [Fact (0 < P)]

theorem average_full_translation (a : LiftDomain P) (u : LiftL2 P) :
    average P (translation P a u) = translation P a (average P u) := by
  apply average_intertwines P (translation P a).toContinuousLinearMap
  intro s v
  exact translations_commute P a (coveringMap P (0,s)) v

/-- Sobolev average, given by `liftOperator P q (average P) (average_full_translation P)`. -/
def sobolevAverage (q : ℕ) : SobolevSpace P q →L[ℝ] SobolevSpace P q :=
  liftOperator P q (average P) (average_full_translation P)

theorem sobolevAverage_norm (q : ℕ) : ‖sobolevAverage P q‖ ≤ 1 :=
  (norm_liftOperator_le P q (average P) (average_full_translation P)).trans (average_norm P)

theorem sobolevAngleCurve_continuous {q : ℕ} (u : SobolevSpace P q) :
    Continuous (fun s : ℝ => sobolevTranslation P q (EulerCylinderAnglePrimitive.angleShift P s) u)
        :=
  (sobolevTranslation_continuous P u).comp (EulerCylinderAnglePrimitive.angleShift_continuous P)

theorem sobolevAverage_eq_integral {q : ℕ} (u : SobolevSpace P q) :
    sobolevAverage P q u = P⁻¹ • (∫ s in (0 : ℝ)..P,
      sobolevTranslation P q (EulerCylinderAnglePrimitive.angleShift P s) u) := by
  apply value_injective P
  change average P (value P u) = (valueOperator P q)
    (P⁻¹ • (∫ s in (0 : ℝ)..P,
      sobolevTranslation P q (EulerCylinderAnglePrimitive.angleShift P s) u))
  rw [map_smul, ← (valueOperator P q).intervalIntegral_comp_comm
    ((sobolevAngleCurve_continuous P u).intervalIntegrable 0 P)]
  rfl

theorem pointEvaluation_average_kernel (u : SobolevSpace P 3) (x : LiftDomain P) :
    pointEvaluation P x (sobolevAverage P 3 u) = P⁻¹ • (∫ s in (0 : ℝ)..P,
      representative P u (x+EulerCylinderAnglePrimitive.angleShift P s)) := by
  rw [sobolevAverage_eq_integral, map_smul,
    ← (pointEvaluation P x).intervalIntegral_comp_comm
      ((sobolevAngleCurve_continuous P u).intervalIntegrable 0 P)]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  exact EulerCylinderAnglePrimitive.pointEvaluation_translation P u _ x

/-- Pointwise identification with the actual normalized angular integral, at every angle. -/
theorem pointEvaluation_average_mean (u : SobolevSpace P 3)
    (f : LiftDomain P → Vector3) (hf : Continuous f)
    (hrep : (value P u : LiftDomain P → Vector3) =ᵐ[liftMeasure P] f)
    (y : Vector3) (θ : ℝ) :
    pointEvaluation P (y,(θ : AddCircle P)) (sobolevAverage P 3 u) =
      P⁻¹ • (∫ s in (0 : ℝ)..P, f (y,(s : AddCircle P))) := by
  rw [pointEvaluation_average_kernel, representative_eq P u f hf hrep]
  congr 1
  simp only [EulerCylinderAnglePrimitive.angleShift, Prod.mk_add_mk, add_zero, ← AddCircle.coe_add]
  rw [intervalIntegral.integral_comp_add_left (fun s : ℝ => f (y,(s : AddCircle P))) θ]
  have hp : Function.Periodic (fun s : ℝ => f (y,(s : AddCircle P))) P := by
    intro s
    change f (y,((s+P : ℝ) : AddCircle P)) = f (y,(s : AddCircle P))
    rw [AddCircle.coe_add_period]
  simpa only [add_zero, zero_add] using hp.intervalIntegral_add_eq θ 0

/-- The operator's zero kernel is precisely the classical zero-mean condition. -/
theorem average_eq_zero_iff (u : SobolevSpace P 3)
    (f : LiftDomain P → Vector3) (hf : Continuous f)
    (hrep : (value P u : LiftDomain P → Vector3) =ᵐ[liftMeasure P] f) :
    average P (value P u) = 0 ↔ ∀ y, (∫ s in (0 : ℝ)..P, f (y,(s : AddCircle P))) = 0 := by
  constructor
  · intro h y
    have hz : sobolevAverage P 3 u = 0 := by
      apply value_injective P
      change average P (value P u) = (valueOperator P 3) 0
      simpa only [map_zero] using h
    have he := pointEvaluation_average_mean P u f hf hrep y 0
    rw [hz, map_zero] at he
    exact (smul_eq_zero.mp he.symm).resolve_left (inv_ne_zero (ne_of_gt (Fact.out : 0 < P)))
  · intro h
    have he (x : LiftDomain P) : representative P (sobolevAverage P 3 u) x = 0 := by
      obtain ⟨θ,hθ⟩ := QuotientAddGroup.mk_surjective x.2
      have hx : x=(x.1,(θ : AddCircle P)) := by
        apply Prod.ext
        · rfl
        · exact hθ.symm
      rw [hx]
      change pointEvaluation P (x.1,(θ : AddCircle P)) (sobolevAverage P 3 u) = 0
      rw [pointEvaluation_average_mean P u f hf hrep, h, smul_zero]
    apply Lp.ext
    filter_upwards [representative_ae P (sobolevAverage P 3 u),
      Lp.coeFn_zero Vector3 2 (liftMeasure P)] with x hx hzero
    exact hx.trans ((he x).trans hzero.symm)

end EulerCylinderAngleAverage
