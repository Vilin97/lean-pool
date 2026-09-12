/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderClassicalWordBounds
public import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeRegularity
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedWeakDerivative
public import LeanPool.NavierStokesAndEuler.Euler.SobolevWordBlocks
import LeanPool.NavierStokesAndEuler.Euler.ClassicalPressureCurl
import LeanPool.NavierStokesAndEuler.Euler.ParameterWordHigher
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder

/-! Actual continuous L² paths for every ordered cylinder derivative. -/

@[expose] public section


noncomputable section

namespace EulerCylinderSmoothOrbit

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMetricTransport EulerLiftedWeakDerivative EulerTransportDerivatives
  EulerCylinderSobolevSpace EulerCylinderSobolev EulerSobolevWordBlocks
  EulerLpCylinderTranslation EulerVolterraConvolution EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]
  {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- The actual uniform-time derivative word, evaluated at the untranslated path. -/
def wordPath (p : C(K, LiftL2 P)) {n : ℕ} (w : Fin n → Fin 4) : C(K,LiftL2 P) :=
  wordDerivative standardDirection (fun a : LiftTangent => pathTranslate P a p) w 0

variable (p : C(K, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))

include hp in
theorem wordPath_apply {n : ℕ} (w : Fin n → Fin 4) (t : K) :
    wordPath P p w t = strongWord P (p t) w :=
  (path_word_evaluation P p hp w t).symm

include hp in
theorem wordPath_translation {n : ℕ} (w : Fin n → Fin 4) (a : LiftTangent) :
    pathTranslate P a (wordPath P p w) =
      wordDerivative standardDirection (fun b : LiftTangent => pathTranslate P b p) w a := by
  apply ContinuousMap.ext
  intro t
  rw [pathTranslate_apply, wordPath_apply P p hp,
    strongWord_translation P (p t) (path_evaluation_smooth P p hp t)]
  exact congrArg (fun D => D (fun j => standardDirection (w j)))
    ((ContinuousMap.evalCLM ℝ t : C(K,LiftL2 P) →L[ℝ] LiftL2 P).iteratedFDeriv_comp_left
      (hp.contDiffAt (x := a)) (i := n) (by simp))

include hp in
theorem wordPath_orbit {n : ℕ} (w : Fin n → Fin 4) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (wordPath P p w)) := by
  simpa only [wordPath_translation P p hp] using
    wordDerivative_contDiff standardDirection (fun a : LiftTangent => pathTranslate P a p) hp w

theorem wordPath_ae {n : ℕ} (w : Fin n → Fin 4) (t : K) :
    (wordPath P p w t : LiftDomain P → Space) =ᵐ[liftMeasure P]
      iteratedFieldDerivative P w (pointField P p hp t) := by
  rw [wordPath_apply P p hp, pointField_eq_representative]
  exact strongWord_ae P (p t) (path_evaluation_smooth P p hp t) w

/-- The new path represents the literal derivative of the old classical field. -/
theorem pointField_wordPath {n : ℕ} (w : Fin n → Fin 4) (t : K) :
    pointField P (wordPath P p w) (wordPath_orbit P p hp w) t =
      iteratedFieldDerivative P w (pointField P p hp t) := by
  apply Measure.eq_of_ae_eq
    ((pointField_ae P (wordPath P p w) (wordPath_orbit P p hp w) t).symm.trans
      (wordPath_ae P p hp w t))
  · exact smoothField_continuous P _ (pointField_smooth P _ _ t)
  · exact smoothField_continuous P _
      (iteratedFieldDerivative_smooth P w _ (pointField_smooth P p hp t))

theorem wordPath_eq_sobolev (q : ℕ) {n : ℕ} (w : Fin n → Fin 4) (t : K) :
    value P (wordBlock P q n w (sobolevPath P (q+n) p hp t)) = wordPath P p w t := by
  rw [wordBlock_value, wordPath_apply P p hp]
  exact sobolev_coordinate P (q+n) (p t) (path_evaluation_smooth P p hp t)
    ⟨⟨n,by omega⟩,w⟩

/-- A single spatial or angular derivative retains an actual continuous-time L² path. -/
def derivativePath (i : Fin 4) : C(K,LiftL2 P) := wordPath P p (fun _ : Fin 1 => i)

include hp in
theorem derivativePath_translation (i : Fin 4) (a : LiftTangent) :
    pathTranslate P a (derivativePath P p i) =
      directional standardDirection (fun b : LiftTangent => pathTranslate P b p) i a := by
  rw [derivativePath, wordPath_translation P p hp]
  change iteratedFDeriv ℝ 1 (fun b : LiftTangent => pathTranslate P b p) a
    (fun _ : Fin 1 => standardDirection i) = _
  rw [iteratedFDeriv_one_apply]
  rfl

include hp in
theorem derivativePath_orbit (i : Fin 4) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (derivativePath P p i)) :=
  wordPath_orbit P p hp (fun _ : Fin 1 => i)

theorem pointField_derivativePath (i : Fin 4) (t : K) (x : LiftDomain P) :
    pointField P (derivativePath P p i) (derivativePath_orbit P p hp i) t x =
      fieldFDeriv P (pointField P p hp t) x (standardDirection i) :=
  congrFun (pointField_wordPath P p hp (fun _ : Fin 1 => i) t) x

include hp in
/-- Differentiation uses one external word, with no dimension-dependent radius loss. -/
theorem derivativePath_block_bound (i : Fin 4) (q n : ℕ) (a : LiftTangent) :
    block standardDirection q (fun b : LiftTangent => pathTranslate P b (derivativePath P p i)) n a
        ≤
      block standardDirection q (fun b : LiftTangent => pathTranslate P b p) (n+1) a := by
  have he : (fun b : LiftTangent => pathTranslate P b (derivativePath P p i)) =
      directional standardDirection (fun b : LiftTangent => pathTranslate P b p) i :=
    funext (derivativePath_translation P p hp i)
  rw [he, block_succ standardDirection q (fun b : LiftTangent => pathTranslate P b p) hp]
  exact Finset.single_le_sum
    (f := fun j : Fin 4 => block standardDirection q
      (directional standardDirection (fun b : LiftTangent => pathTranslate P b p) j) n a)
    (fun j _ => block_nonneg standardDirection q
      (directional standardDirection (fun b : LiftTangent => pathTranslate P b p) j) n a)
    (Finset.mem_univ i)

include hp in
theorem derivativePath_majorant (i : Fin 4) (q : ℕ) (R D : ℝ) (d : ℕ)
    (hb : ∀ n, block standardDirection q (fun a : LiftTangent => pathTranslate P a p) n 0 ≤
      D*majorant R d n) (n : ℕ) :
    block standardDirection q (fun a : LiftTangent => pathTranslate P a (derivativePath P p i)) n 0
        ≤
      D*majorant R (d+1) n := by
  have h := (derivativePath_block_bound P p hp i q n 0).trans (hb (n+1))
  simpa only [majorant, show n+1+d=n+(d+1) by omega] using h

variable (T : ℝ) (hT : 0 ≤ T) (u f : C(Icc (0 : ℝ) T, LiftL2 P))
  (hu : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a u))
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a f))
  (hd : ∀ t : Icc (0 : ℝ) T, HasDerivWithinAt (extendPath T hT u) (f t) (Icc (0 : ℝ) T) t)

include hu hf hd in
/-- Every constructed derivative path has the derivative of the actual time equation. -/
theorem wordPath_hasDerivWithinAt {n : ℕ} (w : Fin n → Fin 4) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (wordPath P u w))
      (wordPath P f w t) (Icc (0 : ℝ) T) t := by
  let L := (valueOperator P 0).comp (wordBlock P 0 n w)
  have h := L.hasFDerivAt.comp_hasDerivWithinAt (t : ℝ)
    (sobolevPath_hasDerivWithinAt P T hT u f hu hf hd (0+n) t)
  change HasDerivWithinAt
    (fun r => value P (wordBlock P 0 n w (sobolevPath P (0+n) u hu (projIcc 0 T hT r))))
    (value P (wordBlock P 0 n w (sobolevPath P (0+n) f hf t))) (Icc (0 : ℝ) T) t at h
  change HasDerivWithinAt (fun r => wordPath P u w (projIcc 0 T hT r))
    (wordPath P f w t) (Icc (0 : ℝ) T) t
  simpa only [wordPath_eq_sobolev] using h

end EulerCylinderSmoothOrbit
