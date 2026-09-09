/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.GraphPullback
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedCurl
public import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryOperator

/-!
Curl in the constant lifted directions `(κ eᵢ, m₀ᵢ)` on the actual periodic
cylinder.  Mixed covering derivatives commute, so its lifted divergence
vanishes.  Compact smooth potentials also produce members of the existing
closed divergence-free Bochner L² space.
-/

@[expose] public section


noncomputable section


namespace EulerPacketPiola

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanBoundary
  EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
  EulerLiftedWeakDerivative EulerLiftedCurl
open scoped ContDiff

variable (period : ℝ)

theorem liftedDirection_coordinate (κ : ℝ) (m : Vector3) (i : Fin 3) :
    EulerGraphPullback.liftedDirection κ m (EuclideanSpace.single i 1) =
      coordinateDirection κ m i := by
  rw [EulerGraphPullback.liftedDirection_apply]
  simp only [coordinateDirection, EuclideanSpace.inner_single_right, conj_trivial, one_mul]

/-- Lifted curl, given by `curlMatrix ((fieldFDeriv period Q x).comp
(EulerGraphPullback.liftedDirection κ m))`. -/
def liftedCurl (κ : ℝ) (m : Vector3) (Q : LiftDomain period → Vector3)
    (x : LiftDomain period) : Vector3 :=
  curlMatrix ((fieldFDeriv period Q x).comp (EulerGraphPullback.liftedDirection κ m))

theorem liftedCurl_component (κ : ℝ) (m : Vector3) (Q : LiftDomain period → Vector3)
    (x : LiftDomain period) (i : Fin 3) :
    liftedCurl period κ m Q x i =
      (fieldDerivative period (coordinateDirection κ m (i + 1)) Q x) (i + 2) -
      (fieldDerivative period (coordinateDirection κ m (i + 2)) Q x) (i + 1) := by
  simp only [liftedCurl, curlMatrix, ContinuousLinearMap.comp_apply, liftedDirection_coordinate]
  rfl

theorem component_smooth (Q : LiftDomain period → Vector3)
    (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) (i : Fin 3) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (fun y => Q y i) x) :=
  (EuclideanSpace.proj i : Vector3 →L[ℝ] ℝ).contDiff.comp (hQ x)

theorem liftedCurl_component_scalar (κ : ℝ) (m : Vector3) (Q : LiftDomain period → Vector3)
    (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) (x : LiftDomain period) (i : Fin 3) :
    liftedCurl period κ m Q x i =
      fieldDerivative period (coordinateDirection κ m (i + 1)) (fun y => Q y (i + 2)) x -
      fieldDerivative period (coordinateDirection κ m (i + 2)) (fun y => Q y (i + 1)) x := by
  rw [liftedCurl_component]
  congr 1
  · exact (fieldDerivative_linear period (EuclideanSpace.proj (i + 2)) Q hQ _ x).symm
  · exact (fieldDerivative_linear period (EuclideanSpace.proj (i + 1)) Q hQ _ x).symm

/-- The full lifted curl is a finite sum of the existing antisymmetric scalar curl tests. -/
theorem liftedCurl_eq_tests (κ : ℝ) (m : Vector3) (Q : LiftDomain period → Vector3)
    (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) :
    liftedCurl period κ m Q = fun x =>
      curlTest period κ m 0 1 (fun y => Q y 2) x +
      curlTest period κ m 1 2 (fun y => Q y 0) x +
      curlTest period κ m 2 0 (fun y => Q y 1) x := by
  funext x
  ext i
  rw [liftedCurl_component_scalar period κ m Q hQ]
  fin_cases i <;>
    norm_num [curlTest, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      EuclideanSpace.single, Pi.single_apply, Fin.add_def, Fin.ext_iff]
  · rfl
  · change
      fieldDerivative period (coordinateDirection κ m 2) (fun y => Q y 0) x -
        fieldDerivative period (coordinateDirection κ m 0) (fun y => Q y 2) x =
      -fieldDerivative period (coordinateDirection κ m 0) (fun y => Q y 2) x +
        fieldDerivative period (coordinateDirection κ m 2) (fun y => Q y 0) x
    ring
  · change
      fieldDerivative period (coordinateDirection κ m 0) (fun y => Q y 1) x -
        fieldDerivative period (coordinateDirection κ m 1) (fun y => Q y 0) x =
      -fieldDerivative period (coordinateDirection κ m 1) (fun y => Q y 0) x +
        fieldDerivative period (coordinateDirection κ m 0) (fun y => Q y 1) x
    ring

theorem liftedCurl_smooth (κ : ℝ) (m : Vector3) (Q : LiftDomain period → Vector3)
    (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (liftedCurl period κ m Q) x) := by
  rw [liftedCurl_eq_tests period κ m Q hQ]
  exact ((curlTest_smooth period κ m 0 1 _ (component_smooth period Q hQ 2) x).add
    (curlTest_smooth period κ m 1 2 _ (component_smooth period Q hQ 0) x)).add
    (curlTest_smooth period κ m 2 0 _ (component_smooth period Q hQ 1) x)

theorem scalar_fieldDerivative_sub (a : LiftTangent) (f g : LiftDomain period → ℝ)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) (x : LiftDomain period) :
    fieldDerivative period a (fun y => f y - g y) x =
      fieldDerivative period a f x - fieldDerivative period a g x := by
  change (fderiv ℝ (fun z => localFieldLift period f x z - localFieldLift period g x z) 0) a = _
  rw [fderiv_fun_sub (((hf x).differentiable (by simp)) 0)
    (((hg x).differentiable (by simp)) 0)]
  rfl

theorem fieldDerivative_liftedCurl_component (κ : ℝ) (m : Vector3)
    (Q : LiftDomain period → Vector3) (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x))
    (a : LiftTangent) (x : LiftDomain period) (i : Fin 3) :
    (fieldDerivative period a (liftedCurl period κ m Q) x) i =
      fieldDerivative period a
        (fieldDerivative period (coordinateDirection κ m (i + 1)) (fun y => Q y (i + 2))) x -
      fieldDerivative period a
        (fieldDerivative period (coordinateDirection κ m (i + 2)) (fun y => Q y (i + 1))) x := by
  change (EuclideanSpace.proj i) (fieldDerivative period a (liftedCurl period κ m Q) x) = _
  rw [← fieldDerivative_linear period (EuclideanSpace.proj i) (liftedCurl period κ m Q)
    (liftedCurl_smooth period κ m Q hQ) a x]
  have he : (fun y => (EuclideanSpace.proj i) (liftedCurl period κ m Q y)) =
      fun y => fieldDerivative period (coordinateDirection κ m (i + 1)) (fun z => Q z (i + 2)) y -
        fieldDerivative period (coordinateDirection κ m (i + 2)) (fun z => Q z (i + 1)) y :=
    funext fun y => liftedCurl_component_scalar period κ m Q hQ y i
  rw [he]
  exact scalar_fieldDerivative_sub period a _ _
    (fieldDerivative_smooth period _ _ (component_smooth period Q hQ (i + 2)))
    (fieldDerivative_smooth period _ _ (component_smooth period Q hQ (i + 1))) x

/-- The constant lifted divergence of an actual lifted curl vanishes pointwise. -/
theorem lifted_divergence_curl (κ : ℝ) (m : Vector3) (Q : LiftDomain period → Vector3)
    (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) (x : LiftDomain period) :
    (∑ i : Fin 3, (fieldDerivative period (coordinateDirection κ m i)
      (liftedCurl period κ m Q) x) i) = 0 := by
  simp only [fieldDerivative_liftedCurl_component period κ m Q hQ, Fin.sum_univ_three]
  have h01 := fieldDerivatives_commute period (coordinateDirection κ m 0)
    (coordinateDirection κ m 1) (fun y => Q y 2) (component_smooth period Q hQ 2) x
  have h02 := fieldDerivatives_commute period (coordinateDirection κ m 0)
    (coordinateDirection κ m 2) (fun y => Q y 1) (component_smooth period Q hQ 1) x
  have h12 := fieldDerivatives_commute period (coordinateDirection κ m 1)
    (coordinateDirection κ m 2) (fun y => Q y 0) (component_smooth period Q hQ 0) x
  change
    (fieldDerivative period (coordinateDirection κ m 0)
      (fieldDerivative period (coordinateDirection κ m 1) (fun y => Q y 2)) x -
     fieldDerivative period (coordinateDirection κ m 0)
      (fieldDerivative period (coordinateDirection κ m 2) (fun y => Q y 1)) x) +
    (fieldDerivative period (coordinateDirection κ m 1)
      (fieldDerivative period (coordinateDirection κ m 2) (fun y => Q y 0)) x -
     fieldDerivative period (coordinateDirection κ m 1)
      (fieldDerivative period (coordinateDirection κ m 0) (fun y => Q y 2)) x) +
    (fieldDerivative period (coordinateDirection κ m 2)
      (fieldDerivative period (coordinateDirection κ m 0) (fun y => Q y 1)) x -
     fieldDerivative period (coordinateDirection κ m 2)
      (fieldDerivative period (coordinateDirection κ m 1) (fun y => Q y 0)) x) = 0
  rw [h01, h02, h12]
  ring

theorem component_compact (Q : LiftDomain period → Vector3) (hQ : HasCompactSupport Q)
    (i : Fin 3) : HasCompactSupport (fun x => Q x i) :=
  hQ.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_comp_subset (g := fun v : Vector3 => v i) rfl Q)

variable [Fact (0 < period)]

/-- Lifted curl Lᵖ, constructed using `curlTestLp`. -/
def liftedCurlLp (κ : ℝ) (m : Vector3) (Q : LiftDomain period → Vector3)
    (hc : HasCompactSupport Q) (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) :
    LiftL2 period :=
  curlTestLp period κ m 0 1 (fun y => Q y 2) (component_compact period Q hc 2) (component_smooth
      period Q hQ 2) +
  curlTestLp period κ m 1 2 (fun y => Q y 0) (component_compact period Q hc 0) (component_smooth
      period Q hQ 0) +
  curlTestLp period κ m 2 0 (fun y => Q y 1) (component_compact period Q hc 1) (component_smooth
      period Q hQ 1)

theorem liftedCurlLp_ae (κ : ℝ) (m : Vector3) (Q : LiftDomain period → Vector3)
    (hc : HasCompactSupport Q) (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) :
    (liftedCurlLp period κ m Q hc hQ : LiftDomain period → Vector3) =ᵐ[liftMeasure period]
      liftedCurl period κ m Q := by
  let a := curlTestLp period κ m 0 1 (fun y => Q y 2) (component_compact period Q hc 2)
      (component_smooth period Q hQ 2)
  let b := curlTestLp period κ m 1 2 (fun y => Q y 0) (component_compact period Q hc 0)
      (component_smooth period Q hQ 0)
  let c := curlTestLp period κ m 2 0 (fun y => Q y 1) (component_compact period Q hc 1)
      (component_smooth period Q hQ 1)
  filter_upwards [Lp.coeFn_add (a + b) c, Lp.coeFn_add a b,
    curlTestLp_ae period κ m 0 1 (fun y => Q y 2) (component_compact period Q hc 2)
        (component_smooth period Q hQ 2),
    curlTestLp_ae period κ m 1 2 (fun y => Q y 0) (component_compact period Q hc 0)
        (component_smooth period Q hQ 0),
    curlTestLp_ae period κ m 2 0 (fun y => Q y 1) (component_compact period Q hc 1)
        (component_smooth period Q hQ 1)]
    with x habc hab ha hb hc'
  change (a + b + c) x = _
  change (a + b + c) x = (a + b) x + c x at habc
  change (a + b) x = a x + b x at hab
  rw [habc, hab, ha, hb, hc', liftedCurl_eq_tests period κ m Q hQ]

/-- Compact lifted curls belong to the actual closed constraint space used by the correction. -/
theorem liftedCurlLp_mem (κ : ℝ) (m : Vector3) (Q : LiftDomain period → Vector3)
    (hc : HasCompactSupport Q) (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) :
    liftedCurlLp period κ m Q hc hQ ∈ divergenceFreeSpace period κ m := by
  intro p hp
  simp only [liftedCurlLp, inner_add_right]
  rw [gradient_curl_pairing period κ m 0 1 _ _ _ hp,
    gradient_curl_pairing period κ m 1 2 _ _ _ hp,
    gradient_curl_pairing period κ m 2 0 _ _ _ hp]
  ring

end EulerPacketPiola
