/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.HilbertProductSubspaceRetraction
public import LeanPool.NavierStokesAndEuler.Euler.CylinderOrbitSobolev
public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevOperators
import LeanPool.NavierStokesAndEuler.Euler.CylinderPathWords
import LeanPool.NavierStokesAndEuler.Euler.ParameterWordHigher

/-!
# Smoothness of the actual translated continuous Sobolev path

The finite Sobolev array consists of genuine derivative words of the given
L² orbit. A bounded retraction of the closed compatible-array space proves
its smoothness in the complete Hq path norm. It is used qualitatively only.
-/

@[expose] public section


noncomputable section

namespace EulerCylinderSmoothOrbit

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSobolevSpace EulerLpCylinderTranslation EulerParameterWordGevrey
  EulerHilbertProductSubspace EulerCylinderSobolev
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)] {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Sobolev path translate, given by `(sobolevTranslation P q (coveringMap P
a)).compLeftContinuous ℝ K`. -/
def sobolevPathTranslate (q : ℕ) (a : LiftTangent) :
    C(K,SobolevSpace P q) →L[ℝ] C(K,SobolevSpace P q) :=
  (sobolevTranslation P q (coveringMap P a)).compLeftContinuous ℝ K

/-- Sobolev orbit, given by `sobolevPathTranslate P q a (sobolevPath P q p hp)`. -/
def sobolevOrbit (q : ℕ) (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) (a : LiftTangent) :
    C(K,SobolevSpace P q) := sobolevPathTranslate P q a (sobolevPath P q p hp)

@[simp] theorem sobolevOrbit_value (q : ℕ) (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
    (a : LiftTangent) (t : K) : value P (sobolevOrbit P q p hp a t) = pathTranslate P a p t := by
  change translation P (coveringMap P a) (value P (sobolevPath P q p hp t)) = _
  rw [sobolevPath_value]
  rfl

theorem sobolevOrbit_coordinate (q : ℕ) (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
    (a : LiftTangent) (t : K) (w : SobolevWord q) :
    (sobolevOrbit P q p hp a t).val w =
      wordDerivative standardDirection (fun b : LiftTangent => pathTranslate P b p) w.2 a t := by
  have hc : (sobolevPath P q p hp t).val w = wordPath P p w.2 t := by
    exact (sobolev_coordinate P q (p t) (path_evaluation_smooth P p hp t) w).trans
      (path_word_evaluation P p hp w.2 t)
  change translate P a ((sobolevPath P q p hp t).val w) = _
  rw [hc]
  exact congrArg (fun z : C(K,LiftL2 P) => z t) (wordPath_translation P p hp w.2 a)

/-- Assemble sobolev path, given by `((retraction (sobolevSubspace P q)).compLeftContinuous ℝ
K).comp packPaths`. -/
def assembleSobolevPath (q : ℕ) :
    (SobolevWord q → C(K,LiftL2 P)) →L[ℝ] C(K,SobolevSpace P q) :=
  ((retraction (sobolevSubspace P q)).compLeftContinuous ℝ K).comp packPaths

theorem sobolevOrbit_eq_assemble (q : ℕ) (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) (a : LiftTangent) :
    sobolevOrbit P q p hp a = assembleSobolevPath P q
      (fun w => wordDerivative standardDirection (fun b : LiftTangent => pathTranslate P b p) w.2
          a) := by
  apply ContinuousMap.ext
  intro t
  have he : packPaths (fun w : SobolevWord q =>
        wordDerivative standardDirection (fun b : LiftTangent => pathTranslate P b p) w.2 a) t =
      (sobolevOrbit P q p hp a t).val := by
    funext w
    rw [packPaths_apply]
    exact (sobolevOrbit_coordinate P q p hp a t w).symm
  change sobolevOrbit P q p hp a t = retraction (sobolevSubspace P q) _
  exact ((congrArg (retraction (sobolevSubspace P q)) he).trans
    (retraction_subtype (sobolevSubspace P q) (sobolevOrbit P q p hp a t))).symm

/-- Actual L² orbit smoothness promotes to every fixed complete Sobolev path space. -/
theorem sobolevOrbit_contDiff (q : ℕ) (p : C(K, LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p)) :
    ContDiff ℝ ∞ (sobolevOrbit P q p hp) := by
  have he : sobolevOrbit P q p hp = fun a => assembleSobolevPath P q
      (fun w => wordDerivative standardDirection (fun b : LiftTangent => pathTranslate P b p) w.2
          a) :=
    funext (sobolevOrbit_eq_assemble P q p hp)
  rw [he]
  apply (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := SobolevWord q → C(K,LiftL2 P)) (F := C(K,SobolevSpace P q)) (assembleSobolevPath P
        q)).comp
  apply contDiff_pi.mpr
  intro w
  exact wordDerivative_contDiff standardDirection (fun b : LiftTangent => pathTranslate P b p) hp
      w.2

end EulerCylinderSmoothOrbit
