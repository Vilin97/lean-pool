/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSlowCurl
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPotentialPath
public import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverageTime

@[expose] public section

/-! The actual potential and slow curl preserve the zero angular mean required by the packet
  recursion. -/

noncomputable section

namespace EulerCylinderCorrectorMeanZero

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerCylinderSmoothOrbit
  EulerLpCylinderTranslation EulerLpCylinderRectangular EulerCylinderAngleAverage
  EulerCylinderAnglePrimitive EulerCylinderPotential EulerCylinderSlowCurl
  EulerParameterWordGevrey EulerCylinderSobolev
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]

theorem average_primitive (u : LiftL2 P) :
    average P (primitive P u) = primitive P (average P u) :=
  average_intertwines P (primitive P) (fun s v => primitive_mixed_translation P (0,s) v) u

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

private local instance : NormedAddCommGroup (LiftL2 P) := inferInstance
private local instance : NormedSpace ℝ (LiftL2 P) := inferInstance
private local instance : NormedAddCommGroup C(K,LiftL2 P) := inferInstance
private local instance : NormedSpace ℝ C(K,LiftL2 P) := inferInstance

omit [CompactSpace K] in
theorem pathAverage_primitive (p : C(K,LiftL2 P)) :
    pathAverage P (pathPrimitive P p) = pathPrimitive P (pathAverage P p) := by
  apply ContinuousMap.ext
  intro t
  exact average_primitive P (p t)

theorem derivativePath_zero (i : Fin 4) : derivativePath P (0 : C(K,LiftL2 P)) i = 0 := by
  simp only [derivativePath, wordPath, map_zero, wordDerivative, iteratedFDeriv_one_apply,
    fderiv_const_apply, zero_apply]

variable (p : C(K,LiftL2 P)) (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))

include hp in
theorem pathAverage_derivativePath (i : Fin 4) :
    pathAverage P (derivativePath P p i) = derivativePath P (pathAverage P p) i := by
  have he : (fun a : LiftTangent => pathTranslate P a (pathAverage P p)) =
      pathAverage P ∘ (fun a : LiftTangent => pathTranslate P a p) :=
    funext (fun a => (pathAverage_translation P a p).symm)
  have hw := wordDerivative_comp_clm
    (P := LiftTangent) (E := C(K,LiftL2 P)) (F := C(K,LiftL2 P))
    standardDirection (pathAverage (K := K) (V := Space) P)
    (fun a : LiftTangent => pathTranslate P a p) hp (fun _ : Fin 1 => i) 0
  simpa only [derivativePath, wordPath, he] using hw.symm

theorem pathAverage_potentialPath (B : C(K,Space →ᵇ Space →L[ℝ] Space)) :
    pathAverage P (potentialPath P B p) = potentialPath P B (pathAverage P p) := by
  unfold potentialPath
  rw [pathAverage_fullMultiplier, pathAverage_primitive]

theorem potentialPath_mean_zero (B : C(K,Space →ᵇ Space →L[ℝ] Space))
    (hz : pathAverage P p = 0) : pathAverage P (potentialPath P B p) = 0 := by
  rw [pathAverage_potentialPath, hz]
  simp only [potentialPath, map_zero]

include hp in
theorem pathAverage_slowCurl (G : C(K,Space →ᵇ Space →L[ℝ] Space)) :
    pathAverage P (path P G p) = path P G (pathAverage P p) := by
  unfold path
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold term
  rw [pathAverage_fullMultiplier, pathAverage_derivativePath P p hp]

include hp in
theorem slowCurl_mean_zero (G : C(K,Space →ᵇ Space →L[ℝ] Space))
    (hz : pathAverage P p = 0) : pathAverage P (path P G p) = 0 := by
  rw [pathAverage_slowCurl P p hp G, hz]
  simp only [path, term, derivativePath_zero, map_zero, Finset.sum_const_zero]

end EulerCylinderCorrectorMeanZero
