/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderPathWords
public import LeanPool.NavierStokesAndEuler.Euler.PacketCurlCoordinates
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangular
public import LeanPool.NavierStokesAndEuler.Euler.PacketPiolaPair
import LeanPool.NavierStokesAndEuler.Euler.ClassicalPressureCurl
import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeGradient
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangularRegularity
import LeanPool.NavierStokesAndEuler.Euler.PacketPotentialRegularity

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
local instance instCylinderSlowCurl1 : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instCylinderSlowCurl2 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedAddCommGroup (LiftTangent →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCylinderSlowCurl3 : NormedAddCommGroup (LiftTangent →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftTangent →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instCylinderSlowCurl4 : NormedSpace ℝ (LiftTangent →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCylinderSlowCurl5 : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCylinderSlowCurl6 : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCylinderSlowCurl7 : NormedAddCommGroup C(K,Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instCylinderSlowCurl8 : NormedSpace ℝ C(K,Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderSlowCurl9 : NormedAddCommGroup (LiftL2 P) := inferInstance
/-- Cache the standard `NormedSpace ℝ (LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderSlowCurl10 : NormedSpace ℝ (LiftL2 P) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,LiftL2 P)` instance to shorten typeclass
synthesis. -/
local instance instCylinderSlowCurl11 : NormedAddCommGroup C(K,LiftL2 P) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderSlowCurl12 : NormedSpace ℝ C(K,LiftL2 P) := inferInstance

variable
  (G : C(K, Space →ᵇ Space →L[ℝ] Space))
  (hG : ContDiff ℝ ∞ (translateCoefficientPath G))
  (p : C(K, LiftL2 P)) (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))

/-- Term, given by `fullMultiplierMap P (curlCoefficientPath i G) (derivativePath P p i.succ)`. -/
def term (i : Fin 3) : C(K,LiftL2 P) :=
  fullMultiplierMap P (curlCoefficientPath i G) (derivativePath P p i.succ)

include hG hp in
theorem term_orbit (i : Fin 3) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (term P G p i)) :=
  product_orbit_contDiff P (curlCoefficientPath i G) (curlCoefficientPath_orbit i G hG)
    (derivativePath P p i.succ) (derivativePath_orbit P p hp i.succ)

/-- Path, given by `∑ i : Fin 3, term P G p i`. -/
def path : C(K,LiftL2 P) := ∑ i : Fin 3, term P G p i

include hG hp in
theorem path_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (path P G p)) := by
  simp only [path, map_sum]
  exact ContDiff.sum (fun i _ => term_orbit P G hG p hp i)

theorem term_ae (i : Fin 3) (t : K) :
    (term P G p i t : LiftDomain P → Space) =ᵐ[liftMeasure P]
      fun x => curlCoefficient i (G t x.1)
        (fieldFDeriv P (pointField P p hp t) x (standardDirection i.succ)) := by
  filter_upwards [EulerLpOperatorField.full_ae (liftMeasure P)
      (fieldLift P (curlCoefficientPath i G t)) (derivativePath P p i.succ t),
    pointField_ae P (derivativePath P p i.succ) (derivativePath_orbit P p hp i.succ) t]
    with x hc hd
  change term P G p i t x = curlCoefficient i (G t x.1) (derivativePath P p i.succ t x) at hc
  rw [hc, hd, pointField_derivativePath P p hp]

theorem path_ae (t : K) :
    (path P G p t : LiftDomain P → Space) =ᵐ[liftMeasure P]
      fun x => curlMatrix ((fieldFDeriv P (pointField P p hp t) x).comp
        ((ContinuousLinearMap.inl ℝ Space ℝ).comp (G t x.1))) := by
  have ht : ∀ᶠ x in ae (liftMeasure P), ∀ i : Fin 3,
      term P G p i t x = curlCoefficient i (G t x.1)
        (fieldFDeriv P (pointField P p hp t) x (standardDirection i.succ)) :=
    Filter.eventually_all.mpr (fun i => term_ae P G p hp i t)
  have hs := Lp.coeFn_fun_finsetSum (Finset.univ : Finset (Fin 3)) (fun i => term P G p i t)
  filter_upwards [hs, ht] with x hs ht
  change (∑ i : Fin 3, term P G p i t) x = _
  rw [hs, curlMatrix_coordinates]
  exact Finset.sum_congr rfl (fun i _ => ht i)

/-- Field, given by `pointField P (path P G p) (path_orbit P G hG p hp) t`. -/
def field (t : K) : LiftDomain P → Space :=
  pointField P (path P G p) (path_orbit P G hG p hp) t

/-- The reconstructed L² path is exactly the classical curl used in the packet. -/
theorem field_formula (t : K) (x : LiftDomain P) :
    field P G hG p hp t x =
      curlMatrix ((fieldFDeriv P (pointField P p hp t) x).comp
        ((ContinuousLinearMap.inl ℝ Space ℝ).comp (G t x.1))) := by
  have he : field P G hG p hp t = fun x =>
      curlMatrix ((fieldFDeriv P (pointField P p hp t) x).comp
        ((ContinuousLinearMap.inl ℝ Space ℝ).comp (G t x.1))) := by
    apply Measure.eq_of_ae_eq
      ((pointField_ae P (path P G p) (path_orbit P G hG p hp) t).symm.trans
        (path_ae P G p hp t))
    · exact smoothField_continuous P _ (pointField_smooth P _ _ t)
    · have hD := (pointField_fderiv_joint_continuous (K := K) P p hp).comp
          ((continuous_const : Continuous (fun _ : LiftDomain P => t)).prodMk continuous_id)
      exact curlOperator.continuous.comp
        (hD.clm_comp (continuous_const.clm_comp ((G t).continuous.comp continuous_fst)))
  exact congrFun he x

theorem field_eq_liftedSlowCurl (F : K → Space → Space ≃L[ℝ] Space)
    (hF : ∀ t y, G t y = (F t y).symm.toContinuousLinearMap) (t : K) :
    field P G hG p hp t = liftedSlowCurl P (F t) (pointField P p hp t) := by
  funext x
  rw [field_formula, hF]
  rfl


end EulerCylinderSlowCurl
