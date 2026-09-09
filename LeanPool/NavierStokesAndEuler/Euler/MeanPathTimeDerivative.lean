/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeIntegral
public import LeanPool.NavierStokesAndEuler.Euler.MeanOrbitSobolev
public import LeanPool.NavierStokesAndEuler.Euler.MeanTimeContinuousTranslation
import LeanPool.NavierStokesAndEuler.Euler.MeanPathSpatialRepresentative
import LeanPool.NavierStokesAndEuler.Euler.MeanSpatialEvaluation
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder

/-!
# Commuting actual spatial derivatives with the time derivative

The time integral is a fixed bounded linear map on continuous L² paths.
Differentiating its exact identity in the translation parameter therefore
commutes every spatial jet with the time integral. The resulting finite
Sobolev arrays transfer the actual time derivative to the smooth spatial
representatives.
-/

@[expose] public section


noncomputable section

namespace EulerMeanPathTimeDerivative

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerMeanTimeContinuousTranslation EulerContinuousTimeIntegral EulerVolterraConvolution
  EulerMeanSmoothRepresentative EulerMeanOrdinaryLift EulerCylinderSobolevSpace
  EulerSobolevPointEvaluation
open scoped ContDiff

/-- Cache the standard `NormedAddCommGroup L2` instance to shorten typeclass synthesis. -/
local instance instMeanPathTimeDerivative1 : NormedAddCommGroup L2 := inferInstance
/-- Cache the standard `NormedSpace ℝ L2` instance to shorten typeclass synthesis. -/
local instance instMeanPathTimeDerivative2 : NormedSpace ℝ L2 := inferInstance
/-- Cache the standard `AddCommGroup L2` instance to shorten typeclass synthesis. -/
local instance instMeanPathTimeDerivative3 : AddCommGroup L2 := (inferInstance : NormedAddCommGroup
    L2).toAddCommGroup
/-- Cache the standard `Module ℝ L2` instance to shorten typeclass synthesis. -/
local instance instMeanPathTimeDerivative4 : Module ℝ L2 := (inferInstance : NormedSpace ℝ
    L2).toModule
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanPathTimeDerivative5 (T : ℝ) : NormedAddCommGroup C(Icc (0 : ℝ) T,L2) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,L2)` instance to shorten typeclass
synthesis. -/
local instance instMeanPathTimeDerivative6 (T : ℝ) : NormedSpace ℝ C(Icc (0 : ℝ) T,L2) :=
    inferInstance

/-- The constant path with the same initial value, as an actual bounded linear map. -/
def initialValueMap (T : ℝ) (hT : 0 ≤ T) :
    C(Icc (0 : ℝ) T,L2) →L[ℝ] C(Icc (0 : ℝ) T,L2) :=
  (ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T)).comp
    (ContinuousMap.evalCLM ℝ (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T))

variable (T : ℝ) (hT : 0 ≤ T) (p q : C(Icc (0 : ℝ) T, L2))
  (hder : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT p) (q t) (Icc (0 : ℝ) T) t)

include hder in
/-- The exact time-integral identity holds after every actual spatial translation. -/
theorem path_integral_identity (a : Space) :
    pathTranslation T a p = initialValueMap T hT (pathTranslation T a p) +
      integral T hT (pathTranslation T a q) := by
  have hd (t : Icc (0 : ℝ) T) :
      HasDerivWithinAt (extendPath T hT (pathTranslation T a p))
        (pathTranslation T a q t) (Icc (0 : ℝ) T) t :=
    (translation a).toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt (t : ℝ) (hder t)
  apply ContinuousMap.ext
  intro t
  have h := eq_initial_add_integral T hT (pathTranslation T a q)
    (extendPath T hT (pathTranslation T a p)) hd t
  change pathTranslation T a p t = pathTranslation T a p ⟨0, le_rfl, hT⟩ +
    integral T hT (pathTranslation T a q) t
  simpa only [extendPath, projIcc_of_mem hT t.property,
    projIcc_of_mem hT ⟨le_rfl, hT⟩] using h

variable (hp : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a p))
  (hq : ContDiff ℝ ∞ (fun a : Space => pathTranslation T a q))

include hder hp hq in
/-- Every genuine spatial jet satisfies the same exact bounded time-integral identity. -/
theorem spatialJetPath_integral_identity (n : ℕ) (v : Fin n → Space) :
    iteratedFDeriv ℝ n (fun a : Space => pathTranslation T a p) 0 v =
      initialValueMap T hT (iteratedFDeriv ℝ n (fun a : Space => pathTranslation T a p) 0 v) +
      integral T hT (iteratedFDeriv ℝ n (fun a : Space => pathTranslation T a q) 0 v) := by
  let P := fun a : Space => pathTranslation T a p
  let Q := fun a : Space => pathTranslation T a q
  let K := initialValueMap T hT
  let J := integral (E := L2) T hT
  have hKP : ContDiff ℝ ∞ (K ∘ P) := K.contDiff.comp hp
  have hJQ : ContDiff ℝ ∞ (J ∘ Q) := J.contDiff.comp hq
  have hfun : P = (K ∘ P)+(J ∘ Q) :=
    funext (fun a => path_integral_identity T hT p q hder a)
  have hD := congrArg (fun g : Space → C(Icc (0 : ℝ) T,L2) => iteratedFDeriv ℝ n g 0 v) hfun
  have hs := congrArg (fun D : Space [×n]→L[ℝ] C(Icc (0 : ℝ) T,L2) => D v)
    (iteratedFDeriv_add_apply (x := (0 : Space))
      (hKP.contDiffAt.of_le (by simp)) (hJQ.contDiffAt.of_le (by simp)))
  have hK := congrArg (fun D : Space [×n]→L[ℝ] C(Icc (0 : ℝ) T,L2) => D v)
    (K.iteratedFDeriv_comp_left (x := (0 : Space)) hp.contDiffAt (by simp))
  have hJ := congrArg (fun D : Space [×n]→L[ℝ] C(Icc (0 : ℝ) T,L2) => D v)
    (J.iteratedFDeriv_comp_left (x := (0 : Space)) hq.contDiffAt (by simp))
  exact hD.trans (hs.trans (congrArg₂ (fun x y : C(Icc (0 : ℝ) T,L2) => x+y) hK hJ))

include hder hp hq in
/-- Every actual spatial jet has the time derivative obtained by differentiating q. -/
theorem spatialJetPath_hasDerivWithinAt (n : ℕ) (v : Fin n → Space) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt
      (extendPath T hT (iteratedFDeriv ℝ n (fun a : Space => pathTranslation T a p) 0 v))
      (iteratedFDeriv ℝ n (fun a : Space => pathTranslation T a q) 0 v t) (Icc (0 : ℝ) T) t := by
  let P := iteratedFDeriv ℝ n (fun a : Space => pathTranslation T a p) 0 v
  let Q := iteratedFDeriv ℝ n (fun a : Space => pathTranslation T a q) 0 v
  have heq : P = initialValueMap T hT P + integral T hT Q :=
    spatialJetPath_integral_identity T hT p q hder hp hq n v
  have hd := (integral_hasDerivWithinAt T hT Q t).const_add (P ⟨0, le_rfl, hT⟩)
  have hfun : extendPath T hT P =
      fun r => P ⟨0, le_rfl, hT⟩+extendPath T hT (integral T hT Q) r := by
    funext r
    exact congrArg (fun f : C(Icc (0 : ℝ) T,L2) => f (projIcc 0 T hT r)) heq
  rw [hfun]
  exact hd

private theorem hasDerivWithinAt_submodule_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Submodule ℝ E) (f : ℝ → S) (v : S) (U : Set ℝ) (t : ℝ) :
    HasDerivWithinAt f v U t ↔ HasDerivWithinAt (fun s => (f s : E)) (v : E) U t := by
  rw [hasDerivWithinAt_iff_tendsto, hasDerivWithinAt_iff_tendsto]
  rfl

local instance instMeanPathTimeDerivative7 : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

include hder hp hq in
/-- The complete finite Sobolev array has the actual time derivative; no
separate mixed-jet assumption is needed. -/
theorem ordinarySobolev_hasDerivWithinAt (k : ℕ) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt
      (fun r => ordinarySobolev k (extendPath T hT p r)
        (pathTranslation_evaluation_contDiff T p hp (projIcc 0 T hT r)))
      (ordinarySobolev k (q t) (pathTranslation_evaluation_contDiff T q hq t))
      (Icc (0 : ℝ) T) t := by
  apply (hasDerivWithinAt_submodule_iff (sobolevSubspace 1 k).toSubmodule _ _ _ _).mpr
  apply hasDerivWithinAt_pi.mpr
  intro w
  have hd := ordinaryLift.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt (t : ℝ)
    (spatialJetPath_hasDerivWithinAt T hT p q hder hp hq w.1.val (coordinateTuple w.2) t)
  simpa only [ordinarySobolev_coordinate, extendPath,
    path_orbit_tensor_evaluation T p hp, path_orbit_tensor_evaluation T q hq,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, ContinuousMap.evalCLM_apply,
    Function.comp_def, LinearIsometry.coe_toContinuousLinearMap] using hd

include hder hp hq in
/-- The smooth ordinary-space representative has the actual classical time
derivative represented by q, including within-interval endpoint derivatives. -/
theorem representative_hasDerivWithinAt (t : Icc (0 : ℝ) T) (x : Space) :
    HasDerivWithinAt
      (fun r => representative (extendPath T hT p r)
        (pathTranslation_evaluation_contDiff T p hp (projIcc 0 T hT r)) x)
      (representative (q t) (pathTranslation_evaluation_contDiff T q hq t) x)
      (Icc (0 : ℝ) T) t := by
  have hd := (pointEvaluation 1 (x, 0)).hasFDerivAt.comp_hasDerivWithinAt (t : ℝ)
    (ordinarySobolev_hasDerivWithinAt T hT p q hder hp hq 3 t)
  convert hd using 1 <;> try rfl
  · funext r
    exact (pointEvaluation_ordinary _ _ _).symm
  · exact (pointEvaluation_ordinary _ _ _).symm

end EulerMeanPathTimeDerivative
