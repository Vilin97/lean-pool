/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeField

@[expose] public section

/-! The ordinary three-dimensional coefficient interface is a literal
restriction of the generic smooth time-field interface. -/

noncomputable section

namespace SmoothTimeField

open EulerSmoothLimit EulerMeanCoefficients

variable {K V : Type} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def toSmoothCoefficientPath (A : SmoothTimeField K Space V) : SmoothCoefficientPath K V :=
  ⟨A.field,A.smooth,A.jet,A.jet_eq⟩

@[simp] theorem toSmoothCoefficientPath_field (A : SmoothTimeField K Space V) :
    A.toSmoothCoefficientPath.field = A.field := rfl

@[simp] theorem toSmoothCoefficientPath_jet (A : SmoothTimeField K Space V) (n : ℕ) :
    A.toSmoothCoefficientPath.jet n = A.jet n := rfl

end SmoothTimeField
