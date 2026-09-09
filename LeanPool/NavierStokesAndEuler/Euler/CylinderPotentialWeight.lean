/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderPotentialPath
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPathWords
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderTimeWeight

@[expose] public section

/-! Exact profile normalization of spatial derivative paths and the vector potential. -/

noncomputable section

namespace EulerCylinderPotential

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerCylinderSmoothOrbit
  EulerLpCylinderTranslation EulerLpCylinderRectangular EulerCylinderAnglePrimitive
  EulerContinuousTimeWeight EulerParameterWordGevrey EulerMeanCoefficients EulerGevrey
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]
  {K : Type*} [TopologicalSpace K] [CompactSpace K]

private local instance : NormedAddCommGroup (LiftL2 P) := inferInstance
private local instance : NormedSpace ℝ (LiftL2 P) := inferInstance
private local instance : NormedAddCommGroup C(K,LiftL2 P) := inferInstance
private local instance : NormedSpace ℝ C(K,LiftL2 P) := inferInstance

variable (g : C(K,ℝ)) (p : C(K,LiftL2 P))

theorem weighted_orbit (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (weight g p)) := by
  have he : (fun a : LiftTangent => pathTranslate P a (weight g p)) =
      fun a => weight g (pathTranslate P a p) := funext (fun a => translate_weight P g a p)
  rw [he]
  exact (weight g).contDiff.comp hp

/-- The entire spatial/angular word commutes with a time-only scalar factor. -/
theorem wordPath_weight (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
    {n : ℕ} (w : Fin n → Fin 4) :
    wordPath P (weight g p) w = weight g (wordPath P p w) := by
  have he : (fun a : LiftTangent => pathTranslate P a (weight g p)) =
      weight g ∘ (fun a : LiftTangent => pathTranslate P a p) :=
    funext (fun a => translate_weight P g a p)
  unfold wordPath
  rw [he]
  exact wordDerivative_comp_clm EulerCylinderSobolev.standardDirection (weight g)
    (fun a : LiftTangent => pathTranslate P a p) hp w 0

theorem derivativePath_weight (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
    (i : Fin 4) : derivativePath P (weight g p) i = weight g (derivativePath P p i) :=
  wordPath_weight P g p hp (fun _ : Fin 1 => i)

theorem pathPrimitive_weight : pathPrimitive P (weight g p) = weight g (pathPrimitive P p) := by
  apply ContinuousMap.ext
  intro t
  exact (EulerCylinderAnglePrimitive.primitive P).map_smul (g t) (p t)

variable (B : C(K,Space →ᵇ Space →L[ℝ] Space))

theorem fullMultiplier_weight : fullMultiplierMap P B (weight g p) =
    weight g (fullMultiplierMap P B p) := by
  apply ContinuousMap.ext
  intro t
  exact (fullOperatorMap P (B t)).map_smul (g t) (p t)

theorem potentialPath_weight : potentialPath P B (weight g p) = weight g (potentialPath P B p) := by
  unfold potentialPath
  rw [pathPrimitive_weight, fullMultiplier_weight]

theorem potentialPath_normalize (hg : ∀ t, 0 < g t) :
    potentialPath P B (normalize g hg p) = normalize g hg (potentialPath P B p) :=
  potentialPath_weight P (reciprocal g hg) p B

/-- The bound applies to the literal quotient Q/g, without any extrema or derivative of g. -/
theorem normalized_potentialPath_block_bound (hg : ∀ t, 0 < g t)
    (hB : ContDiff ℝ ∞ (translateCoefficientPath B))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (normalize g hg p)))
    {ι : Type*} [Fintype ι] (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1)
    (q : ℕ) (Rc C R D : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hR : sobolevCoefficientRadius ι Rc ≤ R)
    (hbB : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath B) a‖ ≤ C*majorant Rc 0 n)
    (d : ℕ) (hbp : ∀ n, block directions q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg p)) n 0 ≤ D*majorant R d n)
    (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate P a (normalize g hg (potentialPath P B
      p))) n 0 ≤
      (3*sobolevCoefficientAmplitude ι q Rc C*(P*D))*majorant R d n := by
  rw [← potentialPath_normalize P g p B hg]
  exact potentialPath_block_bound P B hB (normalize g hg p) hp directions hd q Rc C R D
    hRc hC hD hR hbB d hbp n

end EulerCylinderPotential
