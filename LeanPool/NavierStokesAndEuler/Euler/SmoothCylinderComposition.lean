/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderDescentJets
public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowTimeGevrey
import LeanPool.NavierStokesAndEuler.Euler.GevreyJetCompositionLp
import LeanPool.NavierStokesAndEuler.Euler.SmoothCylinderFlow
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

/-! Actual L² composition of any smooth periodic field with the
constructed cylinder flow. The outer amplitude is retained. -/

@[expose] public section


noncomputable section

namespace EulerSmoothCylinderFlow

open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderCoverDescent
  EulerSmoothBanachFlow EulerSmoothFlowGevrey
open scoped ContDiff BoundedContinuousFunction

/-- Cache the standard `NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] LiftTangent))`
instance to shorten typeclass synthesis. -/
local instance instSmoothCylinderComposition1 (n : ℕ) : NormedAddCommGroup (LiftTangent →ᵇ
    (LiftTangent [×n]→L[ℝ]
    LiftTangent)) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] LiftTangent))`
instance to shorten typeclass synthesis. -/
local instance instSmoothCylinderComposition2 (n : ℕ) : NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent
    [×n]→L[ℝ] LiftTangent))
    := inferInstance
/-- The `MeasurableSpace (LiftTangent [×n]→L[ℝ] LiftTangent)` structure used in smooth cylinder
composition. -/
local instance instSmoothCylinderComposition3 (n : ℕ) : MeasurableSpace (LiftTangent [×n]→L[ℝ]
    LiftTangent) := borel _
local instance instSmoothCylinderComposition4 (n : ℕ) : BorelSpace (LiftTangent [×n]→L[ℝ]
    LiftTangent) := ⟨rfl⟩
local instance instSmoothCylinderComposition5 (n : ℕ) : FiniteDimensional ℝ (LiftTangent [×n]→L[ℝ]
    LiftTangent) := by
  let J : (LiftTangent [×n]→L[ℝ] LiftTangent) →ₗ[ℝ]
      MultilinearMap ℝ (fun _ : Fin n => LiftTangent) LiftTangent :=
    ContinuousMultilinearMap.toMultilinearMapLinear
  exact FiniteDimensional.of_injective J ContinuousMultilinearMap.toMultilinearMap_injective

variable (P T : ℝ) [Fact (0 < P)] (hT : 0 ≤ T)
  (A : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent)
  (hA : ∀ (c : AddSubgroup.zmultiples P) (t : Icc (0 : ℝ) T) z,
    A.field t (z.1, (c : ℝ) + z.2) = A.field t z)
  (hdiv : ∀ t x,
    LinearMap.trace ℝ LiftTangent (fderiv ℝ (A.field t : LiftTangent → LiftTangent)
        x).toLinearMap = 0)

include hA hdiv in
theorem composeJet_memLp_and_bound
    (f : LiftTangent → LiftTangent) (hf : ContDiff ℝ ∞ f)
    (hperiod : ∀ (c : AddSubgroup.zmultiples P) z, f (z.1, (c : ℝ) + z.2) = f z)
    (B R C S : ℝ) (hB : 0 ≤ B) (hR : 0 < R) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hsmall : B * R * T ≤ 1 / 8)
    (hb : ∀ n, ‖A.jet n‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)
    (n : ℕ)
    (hLp : ∀ j ≤ n, MemLp (fun q => jetSeries P f q j) 2 (liftMeasure P))
    (hNorm : ∀ j ≤ n,
      (eLpNorm (fun q => jetSeries P f q j) 2 (liftMeasure P)).toReal ≤ C * S ^ j * (j.factorial :
          ℝ)
          ^
          2)
    (t : Icc (0 : ℝ) T) :
    MemLp (fun q => jetSeries P (f ∘ (flowData T hT A).forward t) q n) 2 (liftMeasure P) ∧
      (eLpNorm (fun q => jetSeries P (f ∘ (flowData T hT A).forward t) q n)
        2 (liftMeasure P)).toReal ≤ C*(flowRadius B R T S)^n*(n.factorial : ℝ)^2 := by
  have he : (fun q => jetSeries P (f ∘ (flowData T hT A).forward t) q n) =
      fun q => (jetSeries P f (forward P T hT A t q)).taylorComp
        (jetSeries P ((flowData T hT A).forward t) q) n :=
    funext (fun q => jetSeries_comp P f hperiod ((flowData T hT A).forward t)
      hf (forward_contDiff T hT A t) q n)
  have hm : AEStronglyMeasurable
      (fun q => jetSeries P (f ∘ (flowData T hT A).forward t) q n) (liftMeasure P) :=
    (((hf.comp (forward_contDiff T hT A t)).continuous_iteratedFDeriv
      (m := n) (by simp)).measurable.comp (sectionPoint_measurable P)).aestronglyMeasurable
  rw [he] at hm ⊢
  apply EulerGevreyJetCompositionLp.composition_memLp_and_bound (liftMeasure P)
    (forward P T hT A t) (forward_measurePreserving P T hT A hA hdiv t)
    (jetSeries P ((flowData T hT A).forward t)) (jetSeries P f) n hm
    C (1+B*T) (4*R+1) S hC (by positivity) (by positivity) hS hLp hNorm
  intro j hj _ q
  exact forward_positive_bound T hT A B R hB hR hsmall hb j hj t (sectionPoint P q)

end EulerSmoothCylinderFlow
