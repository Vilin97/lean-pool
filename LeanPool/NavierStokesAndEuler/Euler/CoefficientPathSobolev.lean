/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CoefficientPathSmooth
public import LeanPool.NavierStokesAndEuler.Euler.SobolevOperatorCoordinates

@[expose] public section

/-! The constructed coefficient jets act continuously in operator norm
on every finite cylinder Sobolev space. -/

noncomputable section

namespace EulerCoefficientPath

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMeanCoefficients EulerSpatialSobolevInverse EulerCylinderSobolev
  EulerCylinderSobolevSpace EulerSobolevCoefficientPressure

open scoped ContDiff BoundedContinuousFunction

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

private local instance : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) := inferInstance

variable (P : ℝ) [Fact (0 < P)]
  (A : C(K, Space →ᵇ Space →L[ℝ] Space))
  (hA : ContDiff ℝ ∞ (translateCoefficientPath A))

def sobolevOperator (q : ℕ) (t : K) : SobolevSpace P q →L[ℝ] SobolevSpace P q :=
  coefficientSobolevOperator P (coefficientJet P A hA q t)

@[simp] theorem sobolevOperator_value (q : ℕ) (t : K) (u : SobolevSpace P q) :
    value P (sobolevOperator P A hA q t u) =
      (smoothCoefficient P A hA t).operator (value P u) :=
  coefficientSobolevOperator_value P (coefficientJet P A hA q t) u

theorem sobolevOperator_value_comp (q : ℕ) (t : K) :
    (valueOperator P q).comp (sobolevOperator P A hA q t) =
      (smoothCoefficient P A hA t).operator.comp (valueOperator P q) := by
  apply ContinuousLinearMap.ext
  intro u
  exact sobolevOperator_value P A hA q t u

theorem sobolevOperator_derivative (q : ℕ) (t : K) (i : Fin 4)
    (u : SobolevSpace P (q+1)) :
    derivativeOperator P q i (sobolevOperator P A hA (q+1) t u) =
      sobolevOperator P A hA q t (derivativeOperator P q i u) +
      sobolevOperator P (orbitDerivativePath A (standardDirection i).1)
        (orbitDerivativePath_orbit A hA (standardDirection i).1) q t (truncateOperator P q u) := by
  apply value_injective P
  have h₁ := derivativeOperator_hasDerivAt P i (sobolevOperator P A hA (q+1) t u)
  rw [sobolevOperator_value] at h₁
  have h₂ := (smoothCoefficient P A hA t).product_hasDerivAt
    (smoothCoefficient P (orbitDerivativePath A (standardDirection i).1)
      (orbitDerivativePath_orbit A hA (standardDirection i).1) t)
    (standardDirection i) (fun x => (cylinder_fieldDerivative P A hA t (standardDirection i)
      x).symm)
    (value P u) (value P (derivativeOperator P q i u)) (derivativeOperator_hasDerivAt P i u)
  change value P (derivativeOperator P q i (sobolevOperator P A hA (q+1) t u)) =
    value P (sobolevOperator P A hA q t (derivativeOperator P q i u)) +
    value P (sobolevOperator P (orbitDerivativePath A (standardDirection i).1)
      (orbitDerivativePath_orbit A hA (standardDirection i).1) q t (truncateOperator P q u))
  simp only [sobolevOperator_value,value_truncateOperator]
  exact h₁.unique h₂

theorem sobolevOperator_derivative_comp (q : ℕ) (t : K) (i : Fin 4) :
    (derivativeOperator P q i).comp (sobolevOperator P A hA (q+1) t) =
      (sobolevOperator P A hA q t).comp (derivativeOperator P q i) +
      (sobolevOperator P (orbitDerivativePath A (standardDirection i).1)
        (orbitDerivativePath_orbit A hA (standardDirection i).1) q t).comp (truncateOperator P q)
          := by
  apply ContinuousLinearMap.ext
  intro u
  exact sobolevOperator_derivative P A hA q t i u

private theorem sobolevOperator_continuous_aux (q : ℕ) :
    ∀ (A : C(K, Space →ᵇ Space →L[ℝ] Space))
      (hA : ContDiff ℝ ∞ (translateCoefficientPath A)),
      Continuous (fun t => sobolevOperator P A hA q t) := by
  induction q with
  | zero =>
    intro A hA
    apply continuous_of_valueComposition P
    simp_rw [sobolevOperator_value_comp]
    exact (smoothCoefficient_operator_continuous P A hA).clm_comp_const (valueOperator P 0)
  | succ q ih =>
    intro A hA
    apply continuous_of_value_and_derivatives P q
    · simp_rw [sobolevOperator_value_comp]
      exact (smoothCoefficient_operator_continuous P A hA).clm_comp_const (valueOperator P (q+1))
    · intro i
      simp_rw [sobolevOperator_derivative_comp]
      exact ((ih A hA).clm_comp_const (derivativeOperator P q i)).add
        ((ih (orbitDerivativePath A (standardDirection i).1)
          (orbitDerivativePath_orbit A hA (standardDirection i).1)).clm_comp_const
            (truncateOperator P q))

theorem sobolevOperator_continuous (q : ℕ) :
    Continuous (fun t => sobolevOperator P A hA q t) :=
  sobolevOperator_continuous_aux P q A hA

end EulerCoefficientPath
