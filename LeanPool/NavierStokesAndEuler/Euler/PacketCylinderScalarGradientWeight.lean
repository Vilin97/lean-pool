/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderScalarGradientBounds
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPotentialWeight

@[expose] public section

/-! Pressure-gradient bounds after literal time-profile division, with no profile extrema or time
  derivative. -/

noncomputable section

namespace EulerPacketCylinderField

open Set ContinuousLinearMap Finset EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpCylinderRectangular EulerCylinderConstantMap
  EulerCylinderScalarPrimitive EulerCylinderSmoothOrbit EulerCylinderPotential
  EulerCylinderSobolev EulerParameterWordGevrey EulerGevrey EulerContinuousTimeWeight
  EulerPacketProfileRecursion
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {K : Type*} [TopologicalSpace K] [CompactSpace K]

private theorem pathMap_timeWeight
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (g : C(K,ℝ)) (p : C(K,CylinderL2 P E)) :
    pathMap P L (weight g p) = weight g (pathMap P L p) := by
  apply ContinuousMap.ext
  intro t
  exact (map P L).map_smul (g t) (p t)

variable (p : C(K,CylinderL2 P ℝ))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))

include hp in
theorem scalarWeightedOrbit (g : C(K,ℝ)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (weight g p)) := by
  have he : (fun a : LiftTangent => pathTranslate P a (weight g p)) =
      weight g ∘ (fun a : LiftTangent => pathTranslate P a p) :=
    funext (fun a => translate_weight P g a p)
  rw [he]
  exact (weight g).contDiff.comp hp

include hp in
theorem scalarGradientPath_weight (g : C(K,ℝ)) :
    scalarGradientPath (weight g p) = weight g (scalarGradientPath p) := by
  unfold scalarGradientPath
  rw [map_sum]
  apply sum_congr rfl
  intro i _
  rw [pathMap_timeWeight,derivativePath_weight P g (pathMap P scalarEmbed p)
    (pathMap_orbit_contDiff P scalarEmbed p hp) i.succ,pathMap_timeWeight]

include hp in
theorem scalarGradientPath_normalize (g : C(K,ℝ)) (hg : ∀ t, 0 < g t) :
    scalarGradientPath (normalize g hg p) = normalize g hg (scalarGradientPath p) :=
  scalarGradientPath_weight p hp (reciprocal g hg)

include hp in
theorem scalarGradientPath_normalized_majorant (g : C(K,ℝ)) (hg : ∀ t, 0 < g t)
    (q : ℕ) (R A : ℝ) (d : ℕ)
    (hb : ∀ n, block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg p)) n 0 ≤ A*majorant R d n)
    (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (scalarGradientPath p))) n 0 ≤
        (3*A)*majorant R (d+1) n := by
  rw [← scalarGradientPath_normalize p hp g hg]
  exact scalarGradientPath_majorant (normalize g hg p)
    (scalarWeightedOrbit p hp (reciprocal g hg)) q R A d hb n

end EulerPacketCylinderField
