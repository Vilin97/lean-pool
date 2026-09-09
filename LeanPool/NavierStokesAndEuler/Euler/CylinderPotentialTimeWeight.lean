/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderPotentialTime
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeWeight
import LeanPool.NavierStokesAndEuler.Euler.CylinderPotentialWeight

/-! Same-radius bounds and literal profile normalization for the constructed potential time
derivative. -/

@[expose] public section


noncomputable section

namespace EulerCylinderPotential

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerMeanCoefficients
  EulerParameterWordGevrey EulerGevrey EulerContinuousTimeWeight
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] (T : ℝ)
  (B B₁ : C(Icc (0 : ℝ) T, Space →ᵇ Space →L[ℝ] Space))
  (hB : ContDiff ℝ ∞ (translateCoefficientPath B))
  (hB₁ : ContDiff ℝ ∞ (translateCoefficientPath B₁))
  (p f : C(Icc (0 : ℝ) T, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a f))

/-- Cache the standard `NormedAddCommGroup (LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderPotentialTimeWeight1 : NormedAddCommGroup (LiftL2 P) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderPotentialTimeWeight2 : NormedSpace ℝ (LiftL2 P) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,LiftL2 P)` instance to shorten
typeclass synthesis. -/
local instance instCylinderPotentialTimeWeight3 : NormedAddCommGroup C(Icc (0 : ℝ) T,LiftL2 P) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,LiftL2 P)` instance to shorten typeclass
synthesis. -/
local instance instCylinderPotentialTimeWeight4 : NormedSpace ℝ C(Icc (0 : ℝ) T,LiftL2 P) :=
    inferInstance

include hB hB₁ hp hf in
theorem potentialDerivative_block_bound {ι : Type*} [Fintype ι]
    (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (Rc C R D : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hR : sobolevCoefficientRadius ι Rc ≤ R)
    (hbB : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath B) a‖ ≤ C * majorant Rc 0 n)
    (hbB₁ : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath B₁) a‖ ≤ C * majorant Rc 0 n)
    (d : ℕ)
    (hbp : ∀ n, block directions q (fun a : LiftTangent => pathTranslate P a p) n 0 ≤ D*majorant R
        d n)
    (hbf : ∀ n, block directions q (fun a : LiftTangent => pathTranslate P a f) n 0 ≤ D*majorant R
        d n)
    (n : ℕ) :
    block directions q (fun a : LiftTangent =>
      pathTranslate P a (potentialDerivative P T B B₁ p f)) n 0 ≤
      (6*sobolevCoefficientAmplitude ι q Rc C*(P*D))*majorant R d n := by
  have he : (fun a : LiftTangent => pathTranslate P a (potentialDerivative P T B B₁ p f)) =
      (fun a : LiftTangent => pathTranslate P a (potentialPath P B₁ p)) +
        (fun a : LiftTangent => pathTranslate P a (potentialPath P B f)) := by
    funext a
    exact map_add (pathTranslate P a) _ _
  rw [he]
  have hs := block_add_le directions q _ _
    (potentialPath_orbit P B₁ hB₁ p hp) (potentialPath_orbit P B hB f hf) n (0 : LiftTangent)
  have h₁ := potentialPath_block_bound P B₁ hB₁ p hp directions hd q
    Rc C R D hRc hC hD hR hbB₁ d hbp n
  have h₂ := potentialPath_block_bound P B hB f hf directions hd q
    Rc C R D hRc hC hD hR hbB d hbf n
  exact (hs.trans (add_le_add h₁ h₂)).trans_eq (by ring)

theorem potentialDerivative_normalize (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t) :
    normalize g hg (potentialDerivative P T B B₁ p f) =
      potentialDerivative P T B B₁ (normalize g hg p) (normalize g hg f) := by
  unfold potentialDerivative EulerContinuousTimeWeight.normalize
  rw [map_add, potentialPath_weight P (reciprocal g hg) p B₁,
    potentialPath_weight P (reciprocal g hg) f B]

include hB hB₁ hp hf in
/-- Estimate Q_t/g from A/g and A_t/g, without differentiating the profile g. -/
theorem normalized_potentialDerivative_block_bound
    (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
    {ι : Type*} [Fintype ι] (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (Rc C R D : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hR : sobolevCoefficientRadius ι Rc ≤ R)
    (hbB : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath B) a‖ ≤ C * majorant Rc 0 n)
    (hbB₁ : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath B₁) a‖ ≤ C * majorant Rc 0 n)
    (d : ℕ)
    (hbp : ∀ n, block directions q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg p)) n 0 ≤ D*majorant R d n)
    (hbf : ∀ n, block directions q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg f)) n 0 ≤ D*majorant R d n)
    (n : ℕ) :
    block directions q (fun a : LiftTangent =>
      pathTranslate P a (normalize g hg (potentialDerivative P T B B₁ p f))) n 0 ≤
      (6*sobolevCoefficientAmplitude ι q Rc C*(P*D))*majorant R d n := by
  rw [potentialDerivative_normalize]
  exact potentialDerivative_block_bound P T B B₁ hB hB₁
    (normalize g hg p) (normalize g hg f)
    (weighted_orbit P (reciprocal g hg) p hp) (weighted_orbit P (reciprocal g hg) f hf)
    directions hd q Rc C R D hRc hC hD hR hbB hbB₁ d hbp hbf n

end EulerCylinderPotential
