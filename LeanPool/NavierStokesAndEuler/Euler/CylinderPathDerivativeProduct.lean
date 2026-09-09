/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderPathProductBounds

@[expose] public section

/-! A literal product with one mixed cylinder derivative consumes exactly one shift. -/

noncomputable section

namespace EulerCylinderPathProduct

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerCylinderSobolev
  EulerParameterWordGevrey EulerGevrey EulerMetricTransport EulerLiftedWeakDerivative
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] {K : Type*} [TopologicalSpace K] [CompactSpace K]
  (L : Space →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (p q : C(K,LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hq : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a q))
  (i : Fin 4)

/-- The continuous L² path for one factor times an actual spatial or angular derivative. -/
def scalarDerivativeProductPath : C(K,LiftL2 P) :=
  scalarProductPath P L hL p (derivativePath P q i) hp (derivativePath_orbit P q hq i)

theorem scalarDerivativeProductPath_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent =>
      pathTranslate P a (scalarDerivativeProductPath P L hL p q hp hq i)) :=
  scalarProductPath_orbit P L hL p (derivativePath P q i) hp (derivativePath_orbit P q hq i)

theorem pointField_scalarDerivativeProductPath (t : K) (x : LiftDomain P) :
    pointField P (scalarDerivativeProductPath P L hL p q hp hq i)
      (scalarDerivativeProductPath_orbit P L hL p q hp hq i) t x =
      L (pointField P p hp t x) •
        fieldFDeriv P (pointField P q hq t) x (standardDirection i) := by
  have h := pointField_scalarProductPath P L hL p (derivativePath P q i)
    hp (derivativePath_orbit P q hq i) t x
  rw [pointField_derivativePath P q hq] at h
  exact h

/-- Fixed-H6 external word bounds preserve the same radius, with one derivative shift. -/
theorem scalarDerivativeProductPath_majorant (R A C : ℝ)
    (hR : 0 ≤ R) (hA : 0 ≤ A) (hC : 0 ≤ C) (d e : ℕ) (a : LiftTangent)
    (hb : ∀ n, block standardDirection 6 (fun b : LiftTangent => pathTranslate P b p) n a ≤
      A*majorant R d n)
    (hc : ∀ n, block standardDirection 6 (fun b : LiftTangent => pathTranslate P b q) n a ≤
      C*majorant R e n) (n : ℕ) :
    block standardDirection 6 (fun b : LiftTangent =>
      pathTranslate P b (scalarDerivativeProductPath P L hL p q hp hq i)) n a ≤
      (3*productBlockConstant P*A*C)*majorant R (d+e+1) n := by
  have hd (j : ℕ) : block standardDirection 6
      (fun b : LiftTangent => pathTranslate P b (derivativePath P q i)) j a ≤
        C*majorant R (e+1) j := by
    have h := (derivativePath_block_bound P q hq i 6 j a).trans (hc (j+1))
    simpa only [majorant, show j+1+e=j+(e+1) by omega] using h
  simpa only [scalarDerivativeProductPath, Nat.add_assoc] using
    scalarProductPath_majorant P L hL p (derivativePath P q i)
      hp (derivativePath_orbit P q hq i) R A C hR hA hC d (e+1) a hb hd n

end EulerCylinderPathProduct
