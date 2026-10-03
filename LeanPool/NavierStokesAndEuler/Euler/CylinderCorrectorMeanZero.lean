/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSlowCurl
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPotentialPath
public import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleAverage

/-! The actual potential and slow curl preserve the zero angular mean required by the packet
recursion. -/

@[expose] public section


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

/-- Cache the standard `NormedAddCommGroup (LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderCorrectorMeanZero1 : NormedAddCommGroup (LiftL2 P) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderCorrectorMeanZero2 : NormedSpace ℝ (LiftL2 P) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,LiftL2 P)` instance to shorten typeclass
synthesis. -/
local instance instCylinderCorrectorMeanZero3 : NormedAddCommGroup C(K,LiftL2 P) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderCorrectorMeanZero4 : NormedSpace ℝ C(K,LiftL2 P) := inferInstance

omit [CompactSpace K] in
theorem pathAverage_primitive (p : C(K, LiftL2 P)) :
    pathAverage (K := K) (V := Vector3) P (pathPrimitive (K := K) P p) =
      pathPrimitive (K := K) P (pathAverage (K := K) (V := Vector3) P p) := by
  apply ContinuousMap.ext
  intro t
  exact average_primitive P (p t)

theorem derivativePath_zero (i : Fin 4) : derivativePath P (0 : C(K,LiftL2 P)) i = 0 := by
  simp only [derivativePath, wordPath, map_zero, wordDerivative, iteratedFDeriv_one_apply,
    fderiv_const_apply, zero_apply]

variable (p : C(K, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate (K := K) (V := Vector3) P a p))

include hp in
theorem pathAverage_derivativePath (i : Fin 4) :
    pathAverage (K := K) (V := Vector3) P (derivativePath P p i) =
      derivativePath P (pathAverage (K := K) (V := Vector3) P p) i := by
  have he : (fun a : LiftTangent => pathTranslate (K := K) (V := Vector3) P a
        (pathAverage (K := K) (V := Vector3) P p)) =
      pathAverage (K := K) (V := Vector3) P ∘
        (fun a : LiftTangent => pathTranslate (K := K) (V := Vector3) P a p) :=
    funext (fun a => (pathAverage_translation P a p).symm)
  have hw := wordDerivative_comp_clm
    (P := LiftTangent) (E := C(K,LiftL2 P)) (F := C(K,LiftL2 P))
    standardDirection (pathAverage (K := K) (V := Space) P)
    (fun a : LiftTangent => pathTranslate (K := K) (V := Vector3) P a p) hp (fun _ : Fin 1 => i) 0
  simpa only [derivativePath, wordPath, he] using hw.symm

theorem pathAverage_potentialPath (B : C(K, Space →ᵇ Space →L[ℝ] Space)) :
    pathAverage (K := K) (V := Vector3) P (potentialPath P B p) =
      potentialPath P B (pathAverage (K := K) (V := Vector3) P p) := by
  unfold potentialPath
  exact (pathAverage_fullMultiplier P _ _).trans (congrArg _ (pathAverage_primitive P _))

theorem potentialPath_mean_zero (B : C(K, Space →ᵇ Space →L[ℝ] Space))
    (hz : pathAverage (K := K) (V := Vector3) P p = 0) :
    pathAverage (K := K) (V := Vector3) P (potentialPath P B p) = 0 := by
  rw [pathAverage_potentialPath, hz]
  simp only [potentialPath, map_zero]

include hp in
theorem pathAverage_slowCurl (G : C(K, Space →ᵇ Space →L[ℝ] Space)) :
    pathAverage (K := K) (V := Vector3) P (path P G p) =
      path P G (pathAverage (K := K) (V := Vector3) P p) := by
  unfold path
  refine (map_sum (pathAverage (K := K) (V := Vector3) P) _ _).trans
    (Finset.sum_congr rfl fun i _ => ?_)
  unfold term
  exact (pathAverage_fullMultiplier P _ _).trans
    (congrArg _ (pathAverage_derivativePath P p hp _))

include hp in
theorem slowCurl_mean_zero (G : C(K, Space →ᵇ Space →L[ℝ] Space))
    (hz : pathAverage (K := K) (V := Vector3) P p = 0) :
    pathAverage (K := K) (V := Vector3) P (path P G p) = 0 := by
  rw [pathAverage_slowCurl P p hp G, hz]
  simp only [path, term, derivativePath_zero, map_zero, Finset.sum_const_zero]

end EulerCylinderCorrectorMeanZero
