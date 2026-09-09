/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldProducts
public import LeanPool.NavierStokesAndEuler.Euler.BoundedFieldCalculus

@[expose] public section

/-! Actual bounded coefficient paths identified with the raw packet coefficients. -/

noncomputable section

namespace EulerPacketCylinderField

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerBoundedFieldCalculus
  EulerPacketPointJets EulerPacketProfileRecursion
open scoped ContDiff BoundedContinuousFunction

private local instance : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) := inferInstance

structure MatrixCoefficient (T : ℝ) (raw : Domain → Space →L[ℝ] Space) where
  path : C(Icc (0 : ℝ) T,Space →ᵇ Space →L[ℝ] Space)
  orbit : ContDiff ℝ ∞ (translateCoefficientPath path)
  raw_eq : ∀ (t : Icc (0 : ℝ) T) x θ, raw (t,(x,θ)) = path t x

structure VectorCoefficient (T : ℝ) (raw : VectorField) where
  path : C(Icc (0 : ℝ) T,Space →ᵇ Space)
  orbit : ContDiff ℝ ∞ (translateCoefficientPath path)
  raw_eq : ∀ (t : Icc (0 : ℝ) T) x θ, raw (t,(x,θ)) = path t x

namespace MatrixCoefficient

variable {P T : ℝ} [Fact (0 < P)] {coef : Domain → Space →L[ℝ] Space} {raw : VectorField}

def multiply (A : MatrixCoefficient T coef) (G : Field P T raw) :
    Field P T (fun z => coef z (raw z)) :=
  G.multiply A.path A.orbit coef A.raw_eq

def adjoint (A : MatrixCoefficient T coef) :
    MatrixCoefficient T (fun z => (coef z).adjoint) where
  path := pathAdjointMap A.path
  orbit := by
    have he : translateCoefficientPath (pathAdjointMap A.path) =
        (pathAdjointMap (α := Space) (K := Icc (0 : ℝ) T) (U := Space) (E := Space)) ∘
          translateCoefficientPath A.path := by
      funext a
      apply ContinuousMap.ext
      intro t
      apply BoundedContinuousFunction.ext
      intro x
      rfl
    rw [he]
    exact (pathAdjointMap (α := Space) (K := Icc (0 : ℝ) T) (U := Space) (E :=
      Space)).contDiff.comp A.orbit
  raw_eq t x θ := by rw [A.raw_eq]; rfl

end MatrixCoefficient

/-- This data is only regularity and literal identification of the three source coefficients. -/
structure CoefficientData (P T : ℝ) (O : Operators) where
  period_eq : O.period = P
  interval_eq : O.interval = Icc (0 : ℝ) T
  inverse : MatrixCoefficient T O.inverseFrame
  strain : MatrixCoefficient T O.strain
  normal : VectorCoefficient T O.normal

end EulerPacketCylinderField
