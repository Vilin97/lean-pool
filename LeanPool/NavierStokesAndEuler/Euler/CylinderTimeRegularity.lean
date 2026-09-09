/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderOrbitSobolev
public import LeanPool.NavierStokesAndEuler.Euler.InjectivePathDerivativeWithin

@[expose] public section

/-!
# Actual smooth cylinder fields from continuous mixed-orbit paths

Uniform-time mixed L² regularity constructs a jointly continuous genuine
representative, smooth in all spatial/angular variables. A continuous L² time
right-hand side lifts through the injective Sobolev inclusion and yields the
actual pointwise within-time derivative, including both interval endpoints.
-/

noncomputable section

namespace EulerCylinderSmoothOrbit

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerCylinderSobolevSpace EulerMetricTransport
  EulerVolterraConvolution EulerInjectivePathDerivative
open scoped ContDiff

variable (period : ℝ) [Fact (0 < period)]
  {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- The genuine representative obtained by bounded H3 point evaluation. -/
def pointField (p : C(K,LiftL2 period))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a p))
    (t : K) (x : LiftDomain period) : Space :=
  EulerSobolevPointEvaluation.pointEvaluation period x (sobolevPath period 3 p hp t)

/-- The reconstructed field is jointly continuous in time and cylinder position. -/
theorem pointField_joint_continuous (p : C(K,LiftL2 period))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a p)) :
    Continuous (fun z : K × LiftDomain period => pointField period p hp z.1 z.2) :=
  EulerSobolevJointEvaluation.path_representative_joint_continuous period (sobolevPath period 3 p
    hp)

/-- The bounded point evaluation is exactly the smooth representative of each actual L² slice. -/
theorem pointField_eq_representative (p : C(K,LiftL2 period))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a p)) (t : K) :
    pointField period p hp t = representative period (p t) (path_evaluation_smooth period p hp t)
      := by
  funext x
  apply EulerSobolevPointEvaluation.pointEvaluation_eq
  · exact smoothField_continuous period _ (representative_smooth period _ _)
  · simpa only [sobolevPath_value] using representative_ae period (p t) (path_evaluation_smooth
    period p hp t)

/-- Every time slice is genuinely smooth in all three spatial and the angular variable. -/
theorem pointField_smooth (p : C(K,LiftL2 period))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a p))
    (t : K) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (pointField period p hp t) x) := by
  rw [pointField_eq_representative]
  exact representative_smooth period _ _ x

/-- The reconstructed field represents the original, rather than a separate chosen solution. -/
theorem pointField_ae (p : C(K,LiftL2 period))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a p)) (t : K) :
    (p t : LiftDomain period → Space) =ᵐ[liftMeasure period] pointField period p hp t := by
  rw [pointField_eq_representative]
  exact representative_ae period _ _

section Derivative

variable (T : ℝ) (hT : 0 ≤ T) (p f : C(Icc (0 : ℝ) T,LiftL2 period))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a p))
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a f))
  (hd : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT p) (f t) (Icc (0 : ℝ) T) t)

include hd in
/-- The time equation is actual in each complete Sobolev space, by injectivity of its L² inclusion. -/
theorem sobolevPath_hasDerivWithinAt (q : ℕ) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (sobolevPath period q p hp))
      (sobolevPath period q f hf t) (Icc (0 : ℝ) T) t := by
  apply hasDerivWithinAt_of_injective_map (valueOperator period q) (value_injective period)
    T hT (sobolevPath period q p hp) (sobolevPath period q f hf)
  intro r hr
  have hdr := (hd ⟨r,hr.1.le,hr.2.le⟩).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
  convert hdr using 1
  · funext s
    exact sobolevPath_value period q p hp (projIcc 0 T hT s)
  · change value period (sobolevPath period q f hf (projIcc 0 T hT r)) = f ⟨r,hr.1.le,hr.2.le⟩
    rw [sobolevPath_value,projIcc_of_mem hT ⟨hr.1.le,hr.2.le⟩]

include hd in
/-- The pointwise PDE time derivative holds within the closed interval at every cylinder point. -/
theorem pointField_hasDerivWithinAt (t : Icc (0 : ℝ) T) (x : LiftDomain period) :
    HasDerivWithinAt (fun s => pointField period p hp (projIcc 0 T hT s) x)
      (pointField period f hf t x) (Icc (0 : ℝ) T) t := by
  have h := (EulerSobolevPointEvaluation.pointEvaluation period x).hasFDerivAt.comp_hasDerivWithinAt
    (t : ℝ) (sobolevPath_hasDerivWithinAt period T hT p f hp hf hd 3 t)
  exact h

end Derivative

end EulerCylinderSmoothOrbit
