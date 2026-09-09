/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSlowCurlTime
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeWeight
import LeanPool.NavierStokesAndEuler.Euler.CylinderPotentialWeight
import LeanPool.NavierStokesAndEuler.Euler.CylinderSlowCurlBounds

/-! Exact time-profile normalization of the actual slow curl and its time derivative. -/

@[expose] public section


noncomputable section

namespace EulerCylinderSlowCurl

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerCylinderSobolev EulerLpCylinderTranslation
  EulerLpCylinderRectangular EulerMeanCoefficients EulerPacketPiola
  EulerParameterWordGevrey EulerGevrey EulerContinuousTimeWeight EulerCylinderPotential
open scoped ContDiff BoundedContinuousFunction

section General

variable (P : ℝ) [Fact (0 < P)]
  {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Cache the standard `NormedAddCommGroup (LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderSlowCurlWeight1 : NormedAddCommGroup (LiftL2 P) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderSlowCurlWeight2 : NormedSpace ℝ (LiftL2 P) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,LiftL2 P)` instance to shorten typeclass
synthesis. -/
local instance instCylinderSlowCurlWeight3 : NormedAddCommGroup C(K,LiftL2 P) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderSlowCurlWeight4 : NormedSpace ℝ C(K,LiftL2 P) := inferInstance

variable (g : C(K, ℝ)) (G : C(K, Space →ᵇ Space →L[ℝ] Space))
  (p : C(K, LiftL2 P)) (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))

include hp in
theorem term_weight (i : Fin 3) : term P G (weight g p) i = weight g (term P G p i) := by
  unfold term
  rw [derivativePath_weight P g p hp i.succ, fullMultiplier_weight]

include hp in
theorem path_weight : path P G (weight g p) = weight g (path P G p) := by
  unfold path
  simp_rw [term_weight P g G p hp]
  exact (map_sum (weight g) _ _).symm

include hp in
theorem path_normalize (hg : ∀ t, 0 < g t) :
    path P G (normalize g hg p) = normalize g hg (path P G p) :=
  path_weight P (reciprocal g hg) G p hp

include hp in
/-- The literal normalized curl has the same radius, with one spatial derivative. -/
theorem normalized_path_block_bound (hg : ∀ t, 0 < g t)
    (hG : ContDiff ℝ ∞ (translateCoefficientPath G))
    (q : ℕ) (Rc C R D : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hR : sobolevCoefficientRadius (Fin 4) Rc ≤ R)
    (hbG : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath G) a‖ ≤ C * majorant Rc 0 n)
    (d : ℕ) (hbp : ∀ n, block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg p)) n 0 ≤ D*majorant R d n)
    (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (path P G p))) n 0 ≤
      (9*sobolevCoefficientAmplitude (Fin 4) q Rc C*D)*majorant R (d+1) n := by
  rw [← path_normalize P g G p hp hg]
  exact path_block_bound P G hG (normalize g hg p)
    (weighted_orbit P (reciprocal g hg) p hp) q Rc C R D hRc hC hD hR hbG d hbp n

end General

section Time

variable (P : ℝ) [Fact (0 < P)] (T : ℝ)
  (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
  (G G₁ : C(Icc (0 : ℝ) T, Space →ᵇ Space →L[ℝ] Space))
  (p f : C(Icc (0 : ℝ) T, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a f))

include hp hf in
/-- This is C_t/g, so no derivative or extremum of the profile is needed. -/
theorem derivative_normalize :
    normalize g hg (derivative P T G G₁ p f) =
      derivative P T G G₁ (normalize g hg p) (normalize g hg f) := by
  unfold derivative EulerContinuousTimeWeight.normalize
  rw [map_add, path_weight P (reciprocal g hg) G₁ p hp,
    path_weight P (reciprocal g hg) G f hf]

include hp hf in
theorem normalized_derivative_block_bound
    (hG : ContDiff ℝ ∞ (translateCoefficientPath G))
    (hG₁ : ContDiff ℝ ∞ (translateCoefficientPath G₁))
    (q : ℕ) (Rc C R D : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hR : sobolevCoefficientRadius (Fin 4) Rc ≤ R)
    (hbG : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath G) a‖ ≤ C * majorant Rc 0 n)
    (hbG₁ : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath G₁) a‖ ≤ C * majorant Rc 0 n)
    (d : ℕ)
    (hbp : ∀ n, block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg p)) n 0 ≤ D*majorant R d n)
    (hbf : ∀ n, block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg f)) n 0 ≤ D*majorant R d n)
    (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (derivative P T G G₁ p f))) n 0 ≤
      (18*sobolevCoefficientAmplitude (Fin 4) q Rc C*D)*majorant R (d+1) n := by
  rw [derivative_normalize P T g hg G G₁ p f hp hf]
  exact derivative_block_bound P T G G₁ hG hG₁ (normalize g hg p) (normalize g hg f)
    (weighted_orbit P (reciprocal g hg) p hp) (weighted_orbit P (reciprocal g hg) f hf)
    q Rc C R D hRc hC hD hR hbG hbG₁ d hbp hbf n

end Time

end EulerCylinderSlowCurl
