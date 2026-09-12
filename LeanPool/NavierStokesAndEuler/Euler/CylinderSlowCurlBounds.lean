/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSlowCurl
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCoefficient
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangularRegularity

/-! The literal slow curl as a continuous cylinder L² path with same-radius bounds. -/

@[expose] public section


noncomputable section

namespace EulerCylinderSlowCurl

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMetricTransport EulerLiftedWeakDerivative EulerCylinderSmoothOrbit EulerCylinderSobolev
  EulerLpCylinderTranslation EulerLpCylinderRectangular EulerMeanCoefficients
  EulerPacketPiola EulerMeanBoundary EulerParameterWordGevrey EulerGevrey
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]
  {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instCylinderSlowCurlBounds1 : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instCylinderSlowCurlBounds2 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedAddCommGroup (LiftTangent →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCylinderSlowCurlBounds3 : NormedAddCommGroup (LiftTangent →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instCylinderSlowCurlBounds4 : NormedSpace ℝ (LiftTangent →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCylinderSlowCurlBounds5 : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCylinderSlowCurlBounds6 : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCylinderSlowCurlBounds7 : NormedAddCommGroup C(K,Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCylinderSlowCurlBounds8 : NormedSpace ℝ C(K,Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderSlowCurlBounds9 : NormedAddCommGroup (LiftL2 P) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderSlowCurlBounds10 : NormedSpace ℝ (LiftL2 P) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,LiftL2 P)` instance to shorten typeclass
synthesis. -/
local instance instCylinderSlowCurlBounds11 : NormedAddCommGroup C(K,LiftL2 P) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderSlowCurlBounds12 : NormedSpace ℝ C(K,LiftL2 P) := inferInstance

variable
  (G : C(K, Space →ᵇ Space →L[ℝ] Space))
  (hG : ContDiff ℝ ∞ (translateCoefficientPath G))
  (p : C(K, LiftL2 P)) (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))


include hG hp in
/-- One spatial derivative consumes one shift; the external radius is unchanged. -/
theorem path_block_bound (q : ℕ) (Rc C R D : ℝ)
    (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hR : sobolevCoefficientRadius (Fin 4) Rc ≤ R)
    (hbG : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath G) a‖ ≤ C * majorant Rc 0 n)
    (d : ℕ) (hbp : ∀ n, block standardDirection q
      (fun a : LiftTangent => pathTranslate P a p) n 0 ≤ D*majorant R d n) (n : ℕ) :
    block standardDirection q (fun a : LiftTangent => pathTranslate P a (path P G p)) n 0 ≤
      (9*sobolevCoefficientAmplitude (Fin 4) q Rc C*D)*majorant R (d+1) n := by
  have hdirections (i : Fin 4) : ‖standardDirection i‖ ≤ 1 := by
    cases i using Fin.cases <;> simp [Prod.norm_def]
  have ht (i : Fin 3) :
      block standardDirection q (fun a : LiftTangent => pathTranslate P a (term P G p i)) n 0 ≤
        (3*sobolevCoefficientAmplitude (Fin 4) q Rc C*D)*majorant R (d+1) n := by
    have h := product_orbit_block_bound P (curlCoefficientPath i G) (curlCoefficientPath_orbit i G
        hG)
      standardDirection hdirections q (derivativePath P p i.succ) (derivativePath_orbit P p hp
          i.succ)
      Rc C R D hRc hC hD hR
      (fun j a => curlCoefficientPath_bound i G hG j (C*majorant Rc 0 j) (hbG j) a)
      (d+1) (derivativePath_majorant P p hp i.succ q R D d hbp) n
    exact h
  let f := fun i : Fin 3 => fun a : LiftTangent => pathTranslate P a (term P G p i)
  have he : (fun a : LiftTangent => pathTranslate P a (path P G p)) = f 0+(f 1+f 2) := by
    funext a
    simp [path, Fin.sum_univ_succ, f]
  rw [he]
  have h₀ := term_orbit P G hG p hp 0
  have h₁ := term_orbit P G hG p hp 1
  have h₂ := term_orbit P G hG p hp 2
  have hs₀ := block_add_le (E := C(K,LiftL2 P)) standardDirection q
    (f 0) (f 1+f 2) h₀ (h₁.add h₂) n (0 : LiftTangent)
  have hs₁ := block_add_le (E := C(K,LiftL2 P)) standardDirection q
    (f 1) (f 2) h₁ h₂ n (0 : LiftTangent)
  have hsum := hs₀.trans (add_le_add (ht 0) (hs₁.trans (add_le_add (ht 1) (ht 2))))
  exact hsum.trans_eq (by ring)


end EulerCylinderSlowCurl
