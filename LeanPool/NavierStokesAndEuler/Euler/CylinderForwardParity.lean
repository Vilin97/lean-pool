/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderFieldReflection
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderCoefficients
import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelNaturality
import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelSymmetry
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderCoefficientTime

/-! Actual supported forward evolution preserves joint odd parity for even coefficients. -/

@[expose] public section


noncomputable section

namespace EulerCylinderForwardParity

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
  EulerLpCylinderRectangular EulerLpCylinderCoefficients EulerCylinderFieldReflection
      EulerLinearDuhamel
open scoped BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (S : Set Space) (hS : MeasurableSet S) (hSym : ∀ x, -x ∈ S ↔ x ∈ S)
  (T : ℝ) (hT : 0 ≤ T) (B : C(Icc (0 : ℝ) T, Space →ᵇ V →L[ℝ] V))
  (hB : ∀ t x, B t (-x) = B t x)
  (U : Evolution T hT (liftedOperatorPath P S hS T B))

include hB in
theorem solution_reflection (f : C(Icc (0 : ℝ) T, Supported P V S hS)) (a₀ : Supported P V S hS) :
    supportedPathReflection P S hS hSym (U.solution f a₀) =
      U.solution (supportedPathReflection P S hS hSym f) (supportedReflection P S hS hSym a₀) := by
  apply (U.solution_map U (supportedReflection P S hS hSym) _ f a₀).symm
  intro t u
  change liftedOperator P S hS (B t) (supportedReflection P S hS hSym u) =
    supportedReflection P S hS hSym (liftedOperator P S hS (B t) u)
  rw [← supportedOperator_eq_square]
  exact (supportedReflection_operator P S hS hSym (B t) (hB t) u).symm

include hB in
theorem solution_reflection_neg (f : C(Icc (0 : ℝ) T, Supported P V S hS))
    (a₀ : Supported P V S hS)
    (hf : ∀ t, supportedReflection P S hS hSym (f t) = -f t)
    (ha₀ : supportedReflection P S hS hSym a₀ = -a₀) (t : Icc (0 : ℝ) T) :
    supportedReflection P S hS hSym (U.solution f a₀ t) = -U.solution f a₀ t := by
  have hfp : supportedPathReflection P S hS hSym f = -f := by
    apply ContinuousMap.ext
    exact hf
  have he := solution_reflection P S hS hSym T hT B hB U f a₀
  rw [hfp,ha₀,U.solution_neg] at he
  exact congrArg (fun p : C(Icc (0 : ℝ) T,Supported P V S hS) => p t) he

include hB hSym in
theorem solution_full_reflection_neg (f : C(Icc (0 : ℝ) T, Supported P V S hS))
    (a₀ : Supported P V S hS)
    (hf : ∀ t, reflection P (f t : CylinderL2 P V) = -(f t : CylinderL2 P V))
    (ha₀ : reflection P (a₀ : CylinderL2 P V) = -(a₀ : CylinderL2 P V)) (t : Icc (0 : ℝ) T) :
    reflection P (U.solution f a₀ t : CylinderL2 P V) = -(U.solution f a₀ t : CylinderL2 P V) := by
  have h := solution_reflection_neg P S hS hSym T hT B hB U f a₀
    (fun r => Subtype.ext (hf r)) (Subtype.ext ha₀) t
  exact congrArg (fun u : Supported P V S hS => (u : CylinderL2 P V)) h

end EulerCylinderForwardParity
