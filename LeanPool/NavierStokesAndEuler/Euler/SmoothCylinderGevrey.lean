/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothCylinderJets
public import LeanPool.NavierStokesAndEuler.Euler.SmoothFlowTimeGevrey
public import LeanPool.NavierStokesAndEuler.Euler.GevreyFlowLpIntegration
public import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

@[expose] public section

/-! The actual periodic flow displacement has simultaneous uniform and
L² Gevrey bounds. The L² estimate uses the cylinder's own Haar measure
and the differentiated equation of the constructed flow. -/

noncomputable section

namespace EulerSmoothCylinderFlow

open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderCoverDescent
  EulerSmoothBanachFlow EulerSmoothFlowGevrey
open scoped ContDiff Interval BoundedContinuousFunction

private local instance (n : ℕ) : NormedAddCommGroup (LiftTangent [×n]→L[ℝ] LiftTangent) :=
  inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (LiftTangent [×n]→L[ℝ] LiftTangent) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ]
  LiftTangent)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (LiftTangent →ᵇ (LiftTangent [×n]→L[ℝ] LiftTangent))
  := inferInstance
private local instance (n : ℕ) : MeasurableSpace (LiftTangent [×n]→L[ℝ] LiftTangent) := borel _
private local instance (n : ℕ) : BorelSpace (LiftTangent [×n]→L[ℝ] LiftTangent) := ⟨rfl⟩
private local instance (n : ℕ) : FiniteDimensional ℝ (LiftTangent [×n]→L[ℝ] LiftTangent) := by
  let J : (LiftTangent [×n]→L[ℝ] LiftTangent) →ₗ[ℝ]
      MultilinearMap ℝ (fun _ : Fin n => LiftTangent) LiftTangent :=
    ContinuousMultilinearMap.toMultilinearMapLinear
  exact FiniteDimensional.of_injective J ContinuousMultilinearMap.toMultilinearMap_injective

variable (P T : ℝ) [Fact (0 < P)] (hT : 0 ≤ T)
  (A : SmoothTimeField (Icc (0 : ℝ) T) LiftTangent LiftTangent)
  (hA : ∀ (c : AddSubgroup.zmultiples P) (t : Icc (0 : ℝ) T) z,
    A.field t (z.1,(c : ℝ)+z.2)=A.field t z)

theorem displacementJet_bound (B R : ℝ)
    (hB : 0 ≤ B) (hR : 0 < R) (hsmall : B*R*T ≤ 1/8)
    (hb : ∀ n, ‖A.jet n‖ ≤ B*R^n*(n.factorial : ℝ)^2)
    (n : ℕ) (t : Icc (0 : ℝ) T) (q : LiftDomain P) :
    ‖displacementJet P T hT A t q n‖ ≤ B*(t : ℝ)*(4*R)^n*(n.factorial : ℝ)^2 :=
  EulerSmoothFlowGevrey.displacement_bound T hT A B R hB hR hsmall hb
    n t t.property (sectionPoint P q)

variable (hdiv : ∀ t x,
  LinearMap.trace ℝ LiftTangent (fderiv ℝ (A.field t : LiftTangent → LiftTangent) x).toLinearMap=0)

include hA hdiv in
theorem compositionJet_memLp_and_bound (B R C S : ℝ)
    (hB : 0 ≤ B) (hR : 0 < R) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hsmall : B*R*T ≤ 1/8)
    (hb : ∀ n, ‖A.jet n‖ ≤ B*R^n*(n.factorial : ℝ)^2)
    (n : ℕ)
    (hLp : ∀ t : Icc (0 : ℝ) T, ∀ j ≤ n,
      MemLp (fun q => jetSeries P (A.field t : LiftTangent → LiftTangent) q j) 2 (liftMeasure P))
    (hNorm : ∀ t : Icc (0 : ℝ) T, ∀ j ≤ n,
      (eLpNorm (fun q => jetSeries P (A.field t : LiftTangent → LiftTangent) q j)
        2 (liftMeasure P)).toReal ≤ C*S^j*(j.factorial : ℝ)^2)
    (t : ℝ) :
    MemLp (fun q => compositionJet P T hT A t q n) 2 (liftMeasure P) ∧
      (eLpNorm (fun q => compositionJet P T hT A t q n) 2 (liftMeasure P)).toReal ≤
        C*(flowRadius B R T S)^n*(n.factorial : ℝ)^2 := by
  apply EulerGevreyJetCompositionLp.composition_memLp_and_bound (liftMeasure P)
    (forward P T hT A (projIcc 0 T hT t))
    (forward_measurePreserving P T hT A hA hdiv (projIcc 0 T hT t))
    (jetSeries P (forwardCover T hT A t)) (jetSeries P (velocityCover T hT A t)) n
    ((compositionJet_joint_measurable P T hT A hA n).comp (measurable_const.prodMk
      measurable_id)).aestronglyMeasurable
    C (1+B*T) (4*R+1) S hC (by positivity) (by positivity) hS
  · exact hLp (projIcc 0 T hT t)
  · exact hNorm (projIcc 0 T hT t)
  · intro j hj _ q
    exact forward_positive_bound T hT A B R hB hR hsmall hb j hj
      (projIcc 0 T hT t) (sectionPoint P q)

include hA hdiv in
theorem displacementJet_memLp_and_bound (B R C S : ℝ)
    (hB : 0 ≤ B) (hR : 0 < R) (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hsmall : B*R*T ≤ 1/8)
    (hb : ∀ n, ‖A.jet n‖ ≤ B*R^n*(n.factorial : ℝ)^2)
    (n : ℕ)
    (hLp : ∀ t : Icc (0 : ℝ) T, ∀ j ≤ n,
      MemLp (fun q => jetSeries P (A.field t : LiftTangent → LiftTangent) q j) 2 (liftMeasure P))
    (hNorm : ∀ t : Icc (0 : ℝ) T, ∀ j ≤ n,
      (eLpNorm (fun q => jetSeries P (A.field t : LiftTangent → LiftTangent) q j)
        2 (liftMeasure P)).toReal ≤ C*S^j*(j.factorial : ℝ)^2)
    (t : Icc (0 : ℝ) T) :
    MemLp (fun q => displacementJet P T hT A t q n) 2 (liftMeasure P) ∧
      (eLpNorm (fun q => displacementJet P T hT A t q n) 2 (liftMeasure P)).toReal ≤
        (t : ℝ)*C*(flowRadius B R T S)^n*(n.factorial : ℝ)^2 := by
  have hm := (compositionJet_joint_measurable P T hT A hA n).aestronglyMeasurable
    (μ := (volume.restrict (Icc 0 (t : ℝ))).prod (liftMeasure P))
  have hi := EulerGevreyFlowLpIntegration.integrated_composition_bound (t : ℝ) t.property.1
    (liftMeasure P) (fun s => forward P T hT A (projIcc 0 T hT s))
    (fun s _ => forward_measurePreserving P T hT A hA hdiv (projIcc 0 T hT s))
    (fun s => jetSeries P (forwardCover T hT A s))
    (fun s => jetSeries P (velocityCover T hT A s)) n hm
    C (1+B*T) (4*R+1) S hC (by positivity) (by positivity) hS
    (fun s _ => hLp (projIcc 0 T hT s)) (fun s _ => hNorm (projIcc 0 T hT s))
    (fun s _ j hj _ q => forward_positive_bound T hT A B R hB hR hsmall hb j hj
      (projIcc 0 T hT s) (sectionPoint P q))
  have he : (fun q => ∫ s in (0 : ℝ)..(t : ℝ), compositionJet P T hT A s q n) =
      fun q => displacementJet P T hT A t q n :=
    funext (fun q => (displacementJet_integral P T hT A hA t q n).symm)
  change MemLp (fun q => ∫ s in (0 : ℝ)..(t : ℝ), compositionJet P T hT A s q n)
      2 (liftMeasure P) ∧
    (eLpNorm (fun q => ∫ s in (0 : ℝ)..(t : ℝ), compositionJet P T hT A s q n)
      2 (liftMeasure P)).toReal ≤ (t : ℝ)*C*(flowRadius B R T S)^n*(n.factorial : ℝ)^2 at hi
  rwa [he] at hi

end EulerSmoothCylinderFlow
