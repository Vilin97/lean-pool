/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevL2Product
public import LeanPool.NavierStokesAndEuler.Euler.SobolevRestriction
import LeanPool.NavierStokesAndEuler.Euler.SobolevTranslationDifferentiation

/-! Actual strong product jets from the genuine Sobolev-to-L² bilinear multiplication. -/

@[expose] public section


noncomputable section

namespace EulerSobolevL2Product

open MeasureTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity EulerCylinderSobolev
  EulerCylinderSobolevSpace EulerSpatialSobolevInverse
open scoped Topology ENNReal

variable (period : ℝ) [Fact (0 < period)]

/-- Genuine L² differentiation of a pointwise product, with one Sobolev derivative on its
coefficient. -/
theorem scalarProduct_hasDerivAt (L : Vector3 →L[ℝ] ℝ) (i : Fin 4)
    (u : SobolevSpace period 4) (v v' : LiftL2 period)
    (hv : HasDerivAt (fun t => translation period (translationPath period (standardDirection i) t)
        v) v' 0) :
    HasDerivAt (fun t => translation period (translationPath period (standardDirection i) t)
      (scalarProduct period (le_refl 3) L (truncateOperator period 3 u) v))
      (scalarProduct period (le_refl 3) L (truncateOperator period 3 u) v' +
        scalarProduct period (le_refl 3) L (derivativeOperator period 3 i u) v) 0 := by
  let B := scalarProductBilinear period (le_refl 3) L
  have hU := sobolevTranslation_hasDerivAt period i u
  have h := B.hasDerivAt_of_bilinear (fun _ => hU) (fun _ => hv)
  have hzero : sobolevTranslation period 3 (translationPath period (standardDirection i) 0)
      (truncateOperator period 3 u) = truncateOperator period 3 u := by
    apply value_injective period
    change translation period (translationPath period (standardDirection i) 0) (value period u) =
        value period u
    rw [translationPath_zero, translation_zero]
  have he : (fun t => B (sobolevTranslation period 3 (translationPath period (standardDirection i)
      t)
      (truncateOperator period 3 u)) (translation period (translationPath period (standardDirection
          i) t) v)) =
      fun t => translation period (translationPath period (standardDirection i) t)
        (scalarProduct period (le_refl 3) L (truncateOperator period 3 u) v) := by
    funext t
    exact scalarProduct_translation period (le_refl 3) L _ _ _
  change HasDerivAt (fun t => B (sobolevTranslation period 3 (translationPath period
      (standardDirection i) t)
      (truncateOperator period 3 u)) (translation period (translationPath period (standardDirection
          i) t) v))
      (B (sobolevTranslation period 3 (translationPath period (standardDirection i) 0)
          (truncateOperator period 3 u)) v' +
        B (derivativeOperator period 3 i u) (translation period (translationPath period
            (standardDirection i) 0) v)) 0 at h
  rw [he, hzero, translationPath_zero, translation_zero] at h
  exact h

/-- Pointwise multiplication with q+3 coefficient derivatives produces a genuine q-jet. -/
def productJet (L : Vector3 →L[ℝ] ℝ) {q : ℕ} (u : SobolevSpace period (q + 3))
    {v : LiftL2 period} (J : SpatialJet period standardDirection q v) :
    SpatialJet period standardDirection q
      (scalarProduct period (le_refl 3) L (restrictOperator period (by omega : 3 ≤ q+3) u) v) := by
  induction q generalizing v with
  | zero => exact .zero _
  | succ q ih =>
    cases J with
    | succ dv lower hd =>
      let u0 : SobolevSpace period (q+3) := truncateOperator period (q+3) u
      let du : Fin 4 → SobolevSpace period (q+3) := fun i => derivativeOperator period (q+3) i u
      let u3 : SobolevSpace period 3 := restrictOperator period (by omega : 3 ≤ q+1+3) u
      let d : Fin 4 → LiftL2 period := fun i =>
        scalarProduct period (le_refl 3) L (restrictOperator period (by
            omega : 3 ≤ q+3) u0) (dv i) +
        scalarProduct period (le_refl 3) L (restrictOperator period (by omega : 3 ≤ q+3) (du i)) v
      have hbase : restrictOperator period (by omega : 3 ≤ q+3) u0 = u3 := by
        apply value_injective period
        rfl
      have hlower (i : Fin 4) : SpatialJet period standardDirection q (d i) :=
        (ih u0 (lower i)).add (ih (du i) (SpatialJet.succ dv lower hd).truncate)
      refine .succ d hlower ?_
      intro i
      let u4 : SobolevSpace period 4 := restrictOperator period (by omega : 4 ≤ q+1+3) u
      have h0 : truncateOperator period 3 u4 = u3 := by
        apply value_injective period
        rfl
      have h1 : derivativeOperator period 3 i u4 =
          restrictOperator period (by omega : 3 ≤ q+3) (du i) := by
        apply value_injective period
        rfl
      have h := scalarProduct_hasDerivAt period L i u4 v (dv i) (hd i)
      rw [h0, h1, ← hbase] at h
      exact h

/-- The output Sobolev array of an actual pointwise scalar-vector product. -/
def productHighLow (L : Vector3 →L[ℝ] ℝ) {q : ℕ}
    (u : SobolevSpace period (q + 3)) (v : SobolevSpace period q) : SobolevSpace period q :=
  ofJet period (productJet period L u (toJet period v))

@[simp] theorem productHighLow_value (L : Vector3 →L[ℝ] ℝ) {q : ℕ}
    (u : SobolevSpace period (q + 3)) (v : SobolevSpace period q) :
    value period (productHighLow period L u v) =
      scalarProduct period (le_refl 3) L (restrictOperator period (by
          omega : 3 ≤ q+3) u) (value period v) :=
  value_ofJet period _

end EulerSobolevL2Product
