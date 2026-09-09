/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSlowCurlBounds
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderFullTime

@[expose] public section

/-! Actual within-time differentiation and bounds for the constructed slow-curl path. -/

noncomputable section

namespace EulerCylinderSlowCurl

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerLpCylinderRectangular
  EulerMeanCoefficients EulerPacketPiola EulerParameterWordGevrey EulerGevrey
  EulerVolterraConvolution EulerCylinderSobolev
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)] (T : ℝ) (hT : 0 ≤ T)
  (G G₁ : C(Icc (0 : ℝ) T,Space →ᵇ Space →L[ℝ] Space))
  (hG : ContDiff ℝ ∞ (translateCoefficientPath G))
  (hG₁ : ContDiff ℝ ∞ (translateCoefficientPath G₁))
  (p f : C(Icc (0 : ℝ) T,LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a f))

def derivative : C(Icc (0 : ℝ) T,LiftL2 P) := path P G₁ p + path P G f

include hG hG₁ hp hf in
theorem derivative_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (derivative P T G G₁ p f)) := by
  simp only [derivative, map_add]
  exact (path_orbit P G₁ hG₁ p hp).add (path_orbit P G hG f hf)

private local instance : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) := inferInstance

variable
  (hGt : ∀ t ∈ Icc (0 : ℝ) T, ∀ y : Space,
    HasDerivWithinAt (fun r => extendPath T hT G r y)
      (extendPath T hT G₁ t y) (Icc (0 : ℝ) T) t)
  (hd : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT p) (f t) (Icc (0 : ℝ) T) t)

include hp hf hGt hd in
theorem path_hasDerivWithinAt (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (path P G p))
      (derivative P T G G₁ p f t) (Icc (0 : ℝ) T) t := by
  have hcoeff (i : Fin 3) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) T) (y : Space) :
      HasDerivWithinAt (fun s => extendPath T hT (curlCoefficientPath i G) s y)
        (extendPath T hT (curlCoefficientPath i G₁) r y) (Icc (0 : ℝ) T) r :=
    (curlCoefficient i).hasFDerivAt.comp_hasDerivWithinAt r (hGt r hr y)
  have hterm (i : Fin 3) : HasDerivWithinAt (extendPath T hT (term P G p i))
      (term P G₁ p i t + term P G f i t) (Icc (0 : ℝ) T) t :=
    fullProduct_hasDerivWithinAt P T hT (curlCoefficientPath i G) (curlCoefficientPath i G₁)
      (hcoeff i) (derivativePath P p i.succ) (derivativePath P f i.succ)
      (wordPath_hasDerivWithinAt P T hT p f hp hf hd (fun _ : Fin 1 => i.succ)) t
  have h := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ => hterm i)
  convert h using 1 <;> try rfl
  simp [derivative, path, Finset.sum_add_distrib]

include hGt hd in
/-- The reconstructed classical curl has the derivative of the actual L² construction. -/
theorem field_hasDerivWithinAt (t : Icc (0 : ℝ) T) (x : LiftDomain P) :
    HasDerivWithinAt (fun r => field P G hG p hp (projIcc 0 T hT r) x)
      (pointField P (derivative P T G G₁ p f)
        (derivative_orbit P T G G₁ hG hG₁ p f hp hf) t x) (Icc (0 : ℝ) T) t :=
  pointField_hasDerivWithinAt P T hT (path P G p) (derivative P T G G₁ p f)
    (path_orbit P G hG p hp) (derivative_orbit P T G G₁ hG hG₁ p f hp hf)
    (path_hasDerivWithinAt P T hT G G₁ p f hp hf hGt hd) t x

include hG hG₁ hp hf in
/-- The true curl time derivative retains the same radius and one spatial shift. -/
theorem derivative_block_bound (q : ℕ) (Rc C R D : ℝ)
    (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hR : sobolevCoefficientRadius (Fin 4) Rc ≤ R)
    (hbG : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath G) a‖ ≤ C*majorant Rc 0 n)
    (hbG₁ : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath G₁) a‖ ≤ C*majorant Rc 0 n)
    (d : ℕ)
    (hbp : ∀ n, block standardDirection q (fun a : LiftTangent => pathTranslate P a p) n 0 ≤
      D*majorant R d n)
    (hbf : ∀ n, block standardDirection q (fun a : LiftTangent => pathTranslate P a f) n 0 ≤
      D*majorant R d n) (n : ℕ) :
    block standardDirection q (fun a : LiftTangent => pathTranslate P a (derivative P T G G₁ p f))
      n 0 ≤
      (18*sobolevCoefficientAmplitude (Fin 4) q Rc C*D)*majorant R (d+1) n := by
  have he : (fun a : LiftTangent => pathTranslate P a (derivative P T G G₁ p f)) =
      (fun a : LiftTangent => pathTranslate P a (path P G₁ p)) +
        (fun a : LiftTangent => pathTranslate P a (path P G f)) := by
    funext a
    exact map_add (pathTranslate P a) _ _
  rw [he]
  calc
    _ ≤ block standardDirection q (fun a : LiftTangent => pathTranslate P a (path P G₁ p)) n 0 +
        block standardDirection q (fun a : LiftTangent => pathTranslate P a (path P G f)) n 0 :=
      block_add_le standardDirection q _ _ (path_orbit P G₁ hG₁ p hp) (path_orbit P G hG f hf) n 0
    _ ≤ (9*sobolevCoefficientAmplitude (Fin 4) q Rc C*D)*majorant R (d+1) n +
        (9*sobolevCoefficientAmplitude (Fin 4) q Rc C*D)*majorant R (d+1) n :=
      add_le_add (path_block_bound P G₁ hG₁ p hp q Rc C R D hRc hC hD hR hbG₁ d hbp n)
        (path_block_bound P G hG f hf q Rc C R D hRc hC hD hR hbG d hbf n)
    _ = _ := by ring

end EulerCylinderSlowCurl
