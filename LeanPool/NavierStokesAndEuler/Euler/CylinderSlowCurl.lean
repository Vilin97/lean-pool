/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderPathWords
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangular
public import LeanPool.NavierStokesAndEuler.Euler.PacketPiolaPair
import LeanPool.NavierStokesAndEuler.Euler.ClassicalPressureCurl
import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeGradient
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangularRegularity
import LeanPool.NavierStokesAndEuler.Euler.PacketPotentialRegularity
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderSobolev
public import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryOperator
public import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPath
public import LeanPool.NavierStokesAndEuler.Euler.PacketPotentialMultiplier
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! The literal slow curl as a continuous cylinder L² path with same-radius bounds. -/

section

/-! Coordinate realization of the actual slow curl and its bounded coefficients. -/

@[expose] public section

noncomputable section

namespace EulerPacketPiola

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerLiftedGradientSpace
  EulerMeanBoundary EulerPacketCrossProduct EulerCylinderSobolev EulerMeanCoefficients
open scoped BoundedContinuousFunction ContDiff

/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketCurlCoordinates1 : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketCurlCoordinates2 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance

/-- The coefficient of one genuine spatial derivative in the slow curl. -/
def curlCoefficient (i : Fin 3) : (Space →L[ℝ] Space) →L[ℝ] (Space →L[ℝ] Space) :=
  crossOperator.comp ((ContinuousLinearMap.apply (E := EuclideanSpace ℝ (Fin 3)) ℝ Space
      (EuclideanSpace.single i 1)).comp
    (ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
      : (Space →L[ℝ] Space) →L[ℝ] (Space →L[ℝ] Space)))

@[simp] theorem curlCoefficient_apply (i : Fin 3) (G : Space →L[ℝ] Space) :
    curlCoefficient i G =
      crossLeft (adjoint (𝕜 := ℝ) (E := Space) (F := Space) G (EuclideanSpace.single i 1)) := rfl

theorem curlCoefficient_norm (i : Fin 3) : ‖curlCoefficient i‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro G
  rw [curlCoefficient_apply, one_mul]
  calc
    ‖crossLeft (adjoint (𝕜 := ℝ) (E := Space) (F := Space) G (EuclideanSpace.single i 1))‖ ≤
        ‖adjoint (𝕜 := ℝ) (E := Space) (F := Space) G (EuclideanSpace.single i 1)‖ :=
      crossLeft_norm_le _
    _ ≤ ‖adjoint (𝕜 := ℝ) (E := Space) (F := Space) G‖*‖EuclideanSpace.single i (1 : ℝ)‖ :=
      (adjoint (𝕜 := ℝ) (E := Space) (F := Space) G).le_opNorm _
    _ = ‖G‖ := by simp only [PiLp.norm_single, norm_one, mul_one, LinearIsometryEquiv.norm_map]

theorem slowDerivative_coordinates (D : LiftTangent →L[ℝ] Space) (G : Space →L[ℝ] Space) :
    D.comp ((ContinuousLinearMap.inl ℝ Space ℝ).comp G) =
      ∑ i : Fin 3, rankOne ℝ (E := Space) (F := Space) (D (standardDirection i.succ))
        (adjoint (𝕜 := ℝ) (E := Space) (F := Space) G (EuclideanSpace.single i 1)) := by
  have he (v : Space) :
      (∑ i : Fin 3,
        ⟪adjoint (𝕜 := ℝ) (E := Space) (F := Space) G (EuclideanSpace.single i 1),v⟫_ℝ •
          standardDirection i.succ) = (G v,0) := by
    simp_rw [G.adjoint_inner_left, standardDirection_succ]
    apply Prod.ext
    · change (∑ i : Fin 3, ⟪EuclideanSpace.single i 1,G v⟫_ℝ • EuclideanSpace.single i 1) = G v
      ext j
      simp only [EuclideanSpace.inner_single_left, conj_trivial, one_mul, WithLp.ofLp_sum,
          WithLp.ofLp_smul, PiLp.ofLp_single, Finset.sum_apply, Pi.smul_apply, Pi.single_apply,
          smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    · simp only [Prod.smul_mk, smul_eq_mul, mul_zero, Fin.sum_univ_succ, Fin.isValue,
        Fin.succ_zero_eq_one, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
        Fin.succ_one_eq_two, Prod.mk_add_mk, add_zero]
  apply ContinuousLinearMap.ext
  intro v
  change D (G v,0) = ∑ i : Fin 3,
    ⟪adjoint (𝕜 := ℝ) (E := Space) (F := Space) G (EuclideanSpace.single i 1),v⟫_ℝ •
      D (standardDirection i.succ)
  rw [← he v, map_sum]
  simp only [map_smul]

/-- The literal slow curl is a sum of three rectangular coefficient products. -/
theorem curlMatrix_coordinates (D : LiftTangent →L[ℝ] Space) (G : Space →L[ℝ] Space) :
    curlMatrix (D.comp ((ContinuousLinearMap.inl ℝ Space ℝ).comp G)) =
      ∑ i : Fin 3, curlCoefficient i G (D (standardDirection i.succ)) := by
  rw [slowDerivative_coordinates]
  change curlOperator (∑ i : Fin 3, rankOne ℝ (E := Space) (F := Space)
    (D (standardDirection i.succ))
    (adjoint (𝕜 := ℝ) (E := Space) (F := Space) G (EuclideanSpace.single i 1))) = _
  rw [map_sum]
  simp only [curlOperator_apply, curlMatrix_rankOne, curlCoefficient_apply, crossLeft_apply]

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Cache the standard `NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketCurlCoordinates3 : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space)` instance to shorten
typeclass synthesis. -/
local instance instPacketCurlCoordinates4 : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) :=
    inferInstance

/-- Curl coefficient path, given by `((curlCoefficient i).compLeftContinuousBounded
Space).compLeftContinuous ℝ K`. -/
def curlCoefficientPath (i : Fin 3) :
    C(K,Space →ᵇ Space →L[ℝ] Space) →L[ℝ] C(K,Space →ᵇ Space →L[ℝ] Space) :=
  ((curlCoefficient i).compLeftContinuousBounded Space).compLeftContinuous ℝ K

omit [CompactSpace K] in
@[simp] theorem curlCoefficientPath_apply (i : Fin 3)
    (G : C(K, Space →ᵇ Space →L[ℝ] Space)) (t : K) (y : Space) :
    curlCoefficientPath (K := K) i G t y = curlCoefficient i (G t y) := rfl

theorem curlCoefficientPath_norm (i : Fin 3) : ‖curlCoefficientPath (K := K) i‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun G => le_of_le_of_eq ?_ (one_mul ‖G‖).symm
  apply (ContinuousMap.norm_le _ (norm_nonneg G)).mpr
  intro t
  apply (BoundedContinuousFunction.norm_le (norm_nonneg G)).mpr
  intro y
  change ‖curlCoefficient i (G t y)‖ ≤ ‖G‖
  exact ((curlCoefficient i).le_of_opNorm_le (curlCoefficient_norm i) (G t y)).trans
    (by simpa only [one_mul] using ((G t).norm_coe_le_norm y).trans (G.norm_coe_le_norm t))

omit [CompactSpace K] in
theorem curlCoefficientPath_translation (i : Fin 3)
    (G : C(K, Space →ᵇ Space →L[ℝ] Space)) (a : Space) :
    translateCoefficientPath (K := K) (V := Space →L[ℝ] Space)
        (curlCoefficientPath (K := K) i G) a =
      curlCoefficientPath (K := K) i
        (translateCoefficientPath (K := K) (V := Space →L[ℝ] Space) G a) := by
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro y
  rfl

theorem curlCoefficientPath_orbit (i : Fin 3) (G : C(K, Space →ᵇ Space →L[ℝ] Space))
    (hG : ContDiff ℝ ∞ (translateCoefficientPath (K := K) (V := Space →L[ℝ] Space) G)) :
    ContDiff ℝ ∞ (translateCoefficientPath (K := K) (V := Space →L[ℝ] Space)
      (curlCoefficientPath (K := K) i G)) := by
  have he := funext (curlCoefficientPath_translation (K := K) i G)
  rw [he]
  exact (curlCoefficientPath (K := K) i).contDiff.comp hG

theorem curlCoefficientPath_bound (i : Fin 3) (G : C(K, Space →ᵇ Space →L[ℝ] Space))
    (hG : ContDiff ℝ ∞ (translateCoefficientPath (K := K) (V := Space →L[ℝ] Space) G))
    (n : ℕ) (C : ℝ)
    (hb : ∀ a, ‖iteratedFDeriv ℝ n
      (translateCoefficientPath (K := K) (V := Space →L[ℝ] Space) G) a‖ ≤ C) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (K := K) (V := Space →L[ℝ] Space)
      (curlCoefficientPath (K := K) i G)) a‖ ≤ C := by
  have he := funext (curlCoefficientPath_translation (K := K) i G)
  rw [he]
  have h := (curlCoefficientPath (K := K) i).norm_iteratedFDeriv_comp_left
    (hG.contDiffAt (x := a)) (n := n) (by simp only [WithTop.le_coe_top, ne_eq,
        WithTop.natCast_ne_top, not_false_eq_true])
  exact h.trans ((mul_le_mul_of_nonneg_right (curlCoefficientPath_norm (K := K) i)
      (norm_nonneg _)).trans ((one_mul _).trans_le (hb a)))

end EulerPacketPiola

end
end

end

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
  (hG : ContDiff ℝ ∞ (translateCoefficientPath (K := K) (V := Space →L[ℝ] Space) G))
  (p : C(K, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate (K := K) (V := Vector3) P a p))

/-- Term, given by `fullMultiplierMap P (curlCoefficientPath i G) (derivativePath P p i.succ)`. -/
def term (i : Fin 3) : C(K,LiftL2 P) :=
  fullMultiplierMap (K := K) (E := Space) (F := Space) P (curlCoefficientPath (K := K) i G)
    (derivativePath P p i.succ)

include hG hp in
theorem term_orbit (i : Fin 3) :
    ContDiff ℝ ∞ (fun a : LiftTangent =>
      pathTranslate (K := K) (V := Vector3) P a (term P G p i)) :=
  product_orbit_contDiff P (curlCoefficientPath (K := K) i G) (curlCoefficientPath_orbit i G hG)
    (derivativePath P p i.succ) (derivativePath_orbit P p hp i.succ)

/-- Path, given by `∑ i : Fin 3, term P G p i`. -/
def path : C(K,LiftL2 P) := ∑ i : Fin 3, term P G p i

include hG hp in
theorem path_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent =>
      pathTranslate (K := K) (V := Vector3) P a (path P G p)) := by
  simp only [path, map_sum]
  exact ContDiff.sum (fun i _ => term_orbit P G hG p hp i)

theorem term_ae (i : Fin 3) (t : K) :
    (term P G p i t : LiftDomain P → Space) =ᵐ[liftMeasure P]
      fun x => curlCoefficient i (G t x.1)
        (fieldFDeriv P (pointField P p hp t) x (standardDirection i.succ)) := by
  filter_upwards [EulerLpOperatorField.full_ae (liftMeasure P)
      (fieldLift (W := Space →L[ℝ] Space) P (curlCoefficientPath (K := K) i G t))
      (derivativePath P p i.succ t),
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
