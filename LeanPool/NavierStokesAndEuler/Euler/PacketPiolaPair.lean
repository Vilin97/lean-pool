/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketAngularPotential
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
public import LeanPool.NavierStokesAndEuler.Euler.PacketPiolaAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.TransverseGramInverse
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.GraphPullback
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedCurl
public import LeanPool.NavierStokesAndEuler.Euler.MeanBoundaryOperator

/-!
The exact fast/slow splitting of the packet curl.  The angular term is the
ordinary cross product with `F⁻ᵀ m₀`; the angular primitive then produces the
literal pair `A + κ C`.  Its weighted pullback is realized in the actual
lifted divergence-free L² space.
-/

section

/-!
The curl Piola identity on the actual periodic cylinder.  The Jacobian acts
only on the three label variables.  Its derivative cancels in the lifted
curl by symmetry of the genuine second derivative; the angular component
passes through unchanged.  This supplies an actual element of the closed
lifted divergence-free L² space from a compact smooth packet potential.
-/

section

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

end
end

end

section

/-!
The actual curl Piola identity for a determinant-one coordinate map.
The derivative of the Jacobian cancels by symmetry of the genuine second
Fréchet derivative.  No curl identity or commutation relation is assumed.
-/

@[expose] public section

noncomputable section

namespace EulerPacketPiola

open EulerSmoothLimit EulerMeanBoundary EulerMeanCutoffCurl EulerVectorCalculus
  InnerProductSpace ContinuousLinearMap EulerTransverseGramInverse
open scoped ContDiff

/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketPiola1 : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketPiola2 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance

theorem adjoint_apply_coordinate (A : Space →L[ℝ] Space) (q : Space) (i : Fin 3) :
    (A.adjoint q) i = ⟪A (EuclideanSpace.single i 1), q⟫_ℝ := by
  simpa only [EuclideanSpace.inner_single_left, conj_trivial, one_mul] using
    A.adjoint_inner_right (EuclideanSpace.single i 1) q

/-- Pull back a Euclidean covector field by the actual derivative of the coordinate map. -/
def pullbackCovector (Ξ Q : Space → Space) (x : Space) : Space :=
  (fderiv ℝ Ξ x).adjoint (Q x)

/-- Symmetric second derivatives remove the entire derivative-of-Jacobian term from curl. -/
theorem curl_pullbackCovector (Ξ Q : Space → Space) (hΞ : ContDiff ℝ 2 Ξ)
    (x : Space) (hQ : DifferentiableAt ℝ Q x) :
    vectorCurl (pullbackCovector Ξ Q) x =
      curlMatrix ((fderiv ℝ Ξ x).adjoint.comp (fderiv ℝ Q x)) := by
  have hD : DifferentiableAt ℝ (fderiv ℝ Ξ) x :=
    ((hΞ.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero).differentiableAt
  have hA : HasFDerivAt (fun y => (fderiv ℝ Ξ y).adjoint)
      ((realAdjoint (U := Space) (E := Space)).comp (fderiv ℝ (fderiv ℝ Ξ) x)) x :=
    (realAdjoint (U := Space) (E := Space)).hasFDerivAt.comp x hD.hasFDerivAt
  have hp := hA.clm_apply hQ.hasFDerivAt
  have hzero : curlMatrix
      (((realAdjoint (U := Space) (E := Space)).comp
        (fderiv ℝ (fderiv ℝ Ξ) x)).flip (Q x)) = 0 := by
    ext i
    change ((fderiv ℝ (fderiv ℝ Ξ) x (EuclideanSpace.single (i + 1) 1)).adjoint (Q x)) (i + 2) -
      ((fderiv ℝ (fderiv ℝ Ξ) x (EuclideanSpace.single (i + 2) 1)).adjoint (Q x)) (i + 1) = 0
    rw [adjoint_apply_coordinate, adjoint_apply_coordinate]
    have hs := ((hΞ.contDiffAt (x := x)).isSymmSndFDerivAt (n := 2) (by simp)).eq
      (EuclideanSpace.single (i + 1) 1) (EuclideanSpace.single (i + 2) 1)
    rw [hs, sub_self]
  change vectorCurl (fun y => (fderiv ℝ Ξ y).adjoint (Q y)) x = _
  rw [vectorCurl_eq_matrix _ x hp.differentiableAt, hp.fderiv, curlMatrix_add, hzero, add_zero]

/-- The source's slow transformed curl `d × Q`, with `d=F⁻ᵀ ∇`. -/
def transformedCurl (F : Space → Space ≃L[ℝ] Space) (Q : Space → Space) (x : Space) : Space :=
  curlMatrix ((fderiv ℝ Q x).comp (F x).symm.toContinuousLinearMap)

/-- For the actual Jacobian and unit determinant, `F⁻¹(d×Q)=curl(FᵀQ)`. -/
theorem piola_curl (Ξ Q : Space → Space) (hΞ : ContDiff ℝ 2 Ξ)
    (F : Space ≃L[ℝ] Space) (x : Space)
    (hF : fderiv ℝ Ξ x = F.toContinuousLinearMap)
    (hdet : (operatorMatrix F.toContinuousLinearMap).det = 1)
    (hQ : DifferentiableAt ℝ Q x) :
    F.symm (curlMatrix ((fderiv ℝ Q x).comp F.symm.toContinuousLinearMap)) =
      vectorCurl (pullbackCovector Ξ Q) x := by
  rw [curl_pullbackCovector Ξ Q hΞ x hQ, hF]
  exact (curlMatrix_piola F hdet (fderiv ℝ Q x)).symm

theorem pullbackCovector_smooth (Ξ Q : Space → Space)
    (hΞ : ContDiff ℝ ∞ Ξ) (hQ : ContDiff ℝ ∞ Q) :
    ContDiff ℝ ∞ (pullbackCovector Ξ Q) :=
  ((realAdjoint (U := Space) (E := Space)).contDiff.comp
    (hΞ.fderiv_right (m := ∞) (by simp))).clm_apply hQ

/-- The transformed curl produces an actually divergence-free label velocity. -/
theorem divergence_piola_curl (Ξ Q : Space → Space)
    (hΞ : ContDiff ℝ ∞ Ξ) (hQ : ContDiff ℝ ∞ Q)
    (F : Space → Space ≃L[ℝ] Space)
    (hF : ∀ x, fderiv ℝ Ξ x = (F x).toContinuousLinearMap)
    (hdet : ∀ x, (operatorMatrix (F x).toContinuousLinearMap).det = 1) (x : Space) :
    divergence (fun y => (F y).symm (transformedCurl F Q y)) x = 0 := by
  have he : (fun y => (F y).symm (transformedCurl F Q y)) =
      vectorCurl (pullbackCovector Ξ Q) := by
    funext y
    exact piola_curl Ξ Q (hΞ.of_le (by simp)) (F y) y (hF y) (hdet y)
      ((hQ.differentiable (by simp)).differentiableAt)
  rw [he]
  exact divergence_curl (fun i y => pullbackCovector Ξ Q y i)
    ((contDiff_piLp 2).mp (pullbackCovector_smooth Ξ Q hΞ hQ)) x

end EulerPacketPiola

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketPiola

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanBoundary
  EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
  EulerLiftedWeakDerivative EulerTransverseGramInverse
open scoped ContDiff

/-- Cache the standard `NormedAddCommGroup (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketLiftedPiola1 : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
/-- Cache the standard `NormedSpace ℝ (Space →L[ℝ] Space)` instance to shorten typeclass
synthesis. -/
local instance instPacketLiftedPiola2 : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance

theorem realAdjoint_apply (A : Space →L[ℝ] Space) :
    realAdjoint A = A.adjoint := rfl

/-- Covering curl, given by `curlMatrix ((fderiv ℝ q z).comp (EulerGraphPullback.liftedDirection
κ m))`. -/
def coveringCurl (κ : ℝ) (m : Space) (q : LiftTangent → Space)
    (z : LiftTangent) : Space :=
  curlMatrix ((fderiv ℝ q z).comp (EulerGraphPullback.liftedDirection κ m))

/-- Covering pullback covector, given by `(fderiv ℝ Ξ z.1).adjoint (q z)`. -/
def coveringPullbackCovector (Ξ : Space → Space) (q : LiftTangent → Space)
    (z : LiftTangent) : Space :=
  (fderiv ℝ Ξ z.1).adjoint (q z)

/-- Cancellation of the actual Hessian in all constant lifted directions. -/
theorem coveringCurl_pullback (κ : ℝ) (m : Space) (Ξ : Space → Space)
    (q : LiftTangent → Space) (hΞ : ContDiff ℝ 2 Ξ) (z : LiftTangent)
    (hq : DifferentiableAt ℝ q z) :
    coveringCurl κ m (coveringPullbackCovector Ξ q) z =
      curlMatrix ((fderiv ℝ Ξ z.1).adjoint.comp
        ((fderiv ℝ q z).comp (EulerGraphPullback.liftedDirection κ m))) := by
  have hD : DifferentiableAt ℝ (fderiv ℝ Ξ) z.1 :=
    ((hΞ.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero).differentiableAt
  have hX : HasFDerivAt (fun w : LiftTangent => fderiv ℝ Ξ w.1)
      ((fderiv ℝ (fderiv ℝ Ξ) z.1).comp (ContinuousLinearMap.fst ℝ Space ℝ)) z :=
    hD.hasFDerivAt.comp z hasFDerivAt_fst
  have hA : HasFDerivAt (fun w : LiftTangent => (fderiv ℝ Ξ w.1).adjoint)
      ((realAdjoint (U := Space) (E := Space)).comp
        ((fderiv ℝ (fderiv ℝ Ξ) z.1).comp (ContinuousLinearMap.fst ℝ Space ℝ))) z :=
    (realAdjoint (U := Space) (E := Space)).hasFDerivAt.comp z hX
  have hp := hA.clm_apply hq.hasFDerivAt
  have hzero : curlMatrix
      ((((realAdjoint (U := Space) (E := Space)).comp
        ((fderiv ℝ (fderiv ℝ Ξ) z.1).comp (ContinuousLinearMap.fst ℝ Space ℝ))).flip (q z)).comp
          (EulerGraphPullback.liftedDirection κ m)) = 0 := by
    ext i
    simp only [curlMatrix, WithLp.ofLp_toLp, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, EulerGraphPullback.liftedDirection_apply,
      ContinuousLinearMap.coe_fst', realAdjoint_apply, PiLp.zero_apply]
    change
      ((fderiv ℝ (fderiv ℝ Ξ) z.1 (κ • EuclideanSpace.single (i + 1) 1)).adjoint (q z)) (i + 2) -
      ((fderiv ℝ (fderiv ℝ Ξ) z.1 (κ • EuclideanSpace.single (i + 2) 1)).adjoint (q z)) (i + 1) = 0
    rw [adjoint_apply_coordinate, adjoint_apply_coordinate]
    simp only [map_smul, smul_apply, real_inner_smul_left]
    have hs := ((hΞ.contDiffAt (x := z.1)).isSymmSndFDerivAt (n := 2) (by simp)).eq
      (EuclideanSpace.single (i + 1) 1) (EuclideanSpace.single (i + 2) 1)
    rw [hs, sub_self]
  change curlMatrix ((fderiv ℝ (fun w : LiftTangent => (fderiv ℝ Ξ w.1).adjoint (q w)) z).comp
      (EulerGraphPullback.liftedDirection κ m)) = _
  rw [hp.fderiv, ContinuousLinearMap.add_comp, curlMatrix_add, hzero, add_zero]
  rfl

/-- Unit determinant transforms the full slow-plus-angular curl by the inverse Jacobian. -/
theorem covering_piola_curl (κ : ℝ) (m : Space) (Ξ : Space → Space)
    (q : LiftTangent → Space) (hΞ : ContDiff ℝ 2 Ξ) (z : LiftTangent)
    (F : Space ≃L[ℝ] Space) (hF : fderiv ℝ Ξ z.1 = F.toContinuousLinearMap)
    (hdet : (operatorMatrix F.toContinuousLinearMap).det = 1)
    (hq : DifferentiableAt ℝ q z) :
    F.symm (curlMatrix ((fderiv ℝ q z).comp
      ((EulerGraphPullback.liftedDirection κ m).comp F.symm.toContinuousLinearMap))) =
      coveringCurl κ m (coveringPullbackCovector Ξ q) z := by
  rw [coveringCurl_pullback κ m Ξ q hΞ z hq, hF]
  exact (curlMatrix_piola F hdet
    ((fderiv ℝ q z).comp (EulerGraphPullback.liftedDirection κ m))).symm

variable (period : ℝ)

/-- Lifted pullback covector, given by `(fderiv ℝ Ξ x.1).adjoint (Q x)`. -/
def liftedPullbackCovector (Ξ : Space → Space) (Q : LiftDomain period → Space)
    (x : LiftDomain period) : Space :=
  (fderiv ℝ Ξ x.1).adjoint (Q x)

/-- Transformed lifted curl, given by `curlMatrix ((fieldFDeriv period Q x).comp
((EulerGraphPullback.liftedDirection κ m).comp (F x.1).symm.toContinuousLinearMap))`. -/
def transformedLiftedCurl (κ : ℝ) (m : Space)
    (F : Space → Space ≃L[ℝ] Space) (Q : LiftDomain period → Space)
    (x : LiftDomain period) : Space :=
  curlMatrix ((fieldFDeriv period Q x).comp
    ((EulerGraphPullback.liftedDirection κ m).comp (F x.1).symm.toContinuousLinearMap))

/-- The actual local chart of the pulled-back potential. -/
theorem localFieldLift_pullbackCovector (Ξ : Space → Space)
    (Q : LiftDomain period → Space) (x : LiftDomain period) :
    localFieldLift period (liftedPullbackCovector period Ξ Q) x =
      coveringPullbackCovector (fun y => Ξ (x.1 + y)) (localFieldLift period Q x) := by
  funext z
  simp only [localFieldLift, liftedPullbackCovector, coveringPullbackCovector,
    fderiv_comp_add_left]

/-- The Piola curl identity for the periodic packet, with the actual scaled lifted directions. -/
theorem lifted_piola_curl (κ : ℝ) (m : Space) (Ξ : Space → Space)
    (Q : LiftDomain period → Space) (hΞ : ContDiff ℝ 2 Ξ)
    (F : Space → Space ≃L[ℝ] Space)
    (hF : ∀ y, fderiv ℝ Ξ y = (F y).toContinuousLinearMap)
    (hdet : ∀ y, (operatorMatrix (F y).toContinuousLinearMap).det = 1)
    (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) (x : LiftDomain period) :
    (F x.1).symm (transformedLiftedCurl period κ m F Q x) =
      liftedCurl period κ m (liftedPullbackCovector period Ξ Q) x := by
  have hshift : ContDiff ℝ 2 (fun y => Ξ (x.1 + y)) :=
    hΞ.comp (contDiff_const.add contDiff_id)
  have hF0 : fderiv ℝ (fun y => Ξ (x.1 + y)) (0 : LiftTangent).1 =
      (F x.1).toContinuousLinearMap := by
    simpa only [fderiv_comp_add_left, Prod.fst_zero, add_zero] using hF x.1
  have he := covering_piola_curl κ m (fun y => Ξ (x.1 + y))
    (localFieldLift period Q x) hshift 0 (F x.1) hF0 (hdet x.1)
    (((hQ x).differentiable (by simp)).differentiableAt)
  simpa only [transformedLiftedCurl, liftedCurl, fieldFDeriv, coveringCurl,
    ← localFieldLift_pullbackCovector period Ξ Q x] using he

theorem liftedPullbackCovector_smooth (Ξ : Space → Space)
    (Q : LiftDomain period → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (liftedPullbackCovector period Ξ Q) x) := by
  change ContDiff ℝ ∞ (fun z : LiftTangent =>
    (fderiv ℝ Ξ (x.1 + z.1)).adjoint (localFieldLift period Q x z))
  exact ((realAdjoint (U := Space) (E := Space)).contDiff.comp
    ((hΞ.fderiv_right (m := ∞) (by simp)).comp
      (contDiff_const.add contDiff_fst))).clm_apply (hQ x)

theorem liftedPullbackCovector_compact (Ξ : Space → Space)
    (Q : LiftDomain period → Space) (hc : HasCompactSupport Q) :
    HasCompactSupport (liftedPullbackCovector period Ξ Q) := by
  apply hc.mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  simp only [liftedPullbackCovector, hx, map_zero]

/-- Actual pointwise lifted divergence vanishes for the transformed packet curl. -/
theorem lifted_divergence_piola_curl (κ : ℝ) (m : Space) (Ξ : Space → Space)
    (Q : LiftDomain period → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (F : Space → Space ≃L[ℝ] Space)
    (hF : ∀ y, fderiv ℝ Ξ y = (F y).toContinuousLinearMap)
    (hdet : ∀ y, (operatorMatrix (F y).toContinuousLinearMap).det = 1)
    (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) (x : LiftDomain period) :
    (∑ i : Fin 3, (fieldDerivative period (coordinateDirection κ m i)
      (fun y => (F y.1).symm (transformedLiftedCurl period κ m F Q y)) x) i) = 0 := by
  have he : (fun y => (F y.1).symm (transformedLiftedCurl period κ m F Q y)) =
      liftedCurl period κ m (liftedPullbackCovector period Ξ Q) :=
    funext fun y => lifted_piola_curl period κ m Ξ Q (hΞ.of_le (by simp)) F hF hdet hQ y
  rw [he]
  exact lifted_divergence_curl period κ m _ (liftedPullbackCovector_smooth period Ξ Q hΞ hQ) x

variable [Fact (0 < period)]

/-- A genuine Bochner L² realization of the pulled-back packet curl. -/
def piolaLiftedCurlLp (κ : ℝ) (m : Space) (Ξ : Space → Space)
    (Q : LiftDomain period → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (hc : HasCompactSupport Q) (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) :
    LiftL2 period :=
  liftedCurlLp period κ m (liftedPullbackCovector period Ξ Q)
    (liftedPullbackCovector_compact period Ξ Q hc)
    (liftedPullbackCovector_smooth period Ξ Q hΞ hQ)

theorem piolaLiftedCurlLp_ae (κ : ℝ) (m : Space) (Ξ : Space → Space)
    (Q : LiftDomain period → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (hc : HasCompactSupport Q) (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x))
    (F : Space → Space ≃L[ℝ] Space)
    (hF : ∀ y, fderiv ℝ Ξ y = (F y).toContinuousLinearMap)
    (hdet : ∀ y, (operatorMatrix (F y).toContinuousLinearMap).det = 1) :
    (piolaLiftedCurlLp period κ m Ξ Q hΞ hc hQ : LiftDomain period → Space) =ᵐ[liftMeasure period]
      (fun x => (F x.1).symm (transformedLiftedCurl period κ m F Q x)) := by
  filter_upwards [liftedCurlLp_ae period κ m (liftedPullbackCovector period Ξ Q)
    (liftedPullbackCovector_compact period Ξ Q hc)
    (liftedPullbackCovector_smooth period Ξ Q hΞ hQ)] with x hx
  exact hx.trans (lifted_piola_curl period κ m Ξ Q (hΞ.of_le (by simp)) F hF hdet hQ x).symm

/-- The pulled-back packet satisfies the exact closed constraint used by correction assembly. -/
theorem piolaLiftedCurlLp_mem (κ : ℝ) (m : Space) (Ξ : Space → Space)
    (Q : LiftDomain period → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (hc : HasCompactSupport Q) (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) :
    piolaLiftedCurlLp period κ m Ξ Q hΞ hc hQ ∈ divergenceFreeSpace period κ m :=
  liftedCurlLp_mem period κ m (liftedPullbackCovector period Ξ Q)
    (liftedPullbackCovector_compact period Ξ Q hc)
    (liftedPullbackCovector_smooth period Ξ Q hΞ hQ)

end EulerPacketPiola

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketPiola

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerMeanBoundary
  EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
  EulerLiftedWeakDerivative EulerPacketCrossProduct EulerPacketAngularPotential
open scoped ContDiff

theorem curlMatrix_rankOne (a b : Space) :
    curlMatrix (rankOne ℝ a b) = cross b a := by
  ext i
  fin_cases i <;>
    simp [curlMatrix, rankOne_apply, EuclideanSpace.inner_single_right,
      cross, cross_apply]

/-- The actual four-dimensional derivative splits into its slow and angular parts. -/
theorem curl_lifted_split (κ : ℝ) (m : Space) (L : LiftTangent →L[ℝ] Space)
    (G : Space →L[ℝ] Space) :
    curlMatrix (L.comp ((EulerGraphPullback.liftedDirection κ m).comp G)) =
      κ • curlMatrix (L.comp ((ContinuousLinearMap.inl ℝ Space ℝ).comp G)) +
        cross (G.adjoint m) (L (0, 1)) := by
  have he : L.comp ((EulerGraphPullback.liftedDirection κ m).comp G) =
      κ • (L.comp ((ContinuousLinearMap.inl ℝ Space ℝ).comp G)) +
        rankOne ℝ (L (0, 1)) (G.adjoint m) := by
    apply ContinuousLinearMap.ext
    intro v
    change L (κ • G v, ⟪m, G v⟫_ℝ) =
      κ • L (G v, 0) + ⟪G.adjoint m, v⟫_ℝ • L (0, 1)
    rw [G.adjoint_inner_left]
    have hv : (κ • G v, ⟪m, G v⟫_ℝ) =
        κ • (G v, (0 : ℝ)) + ⟪m, G v⟫_ℝ • ((0 : Space), (1 : ℝ)) := by
      ext <;> simp
    rw [hv, map_add, map_smul, map_smul]
  rw [he, curlMatrix_add, curlMatrix_smul, curlMatrix_rankOne]

/-- Covering slow curl, given by `curlMatrix ((fderiv ℝ q z).comp ((ContinuousLinearMap.inl ℝ
Space ℝ).comp G))`. -/
def coveringSlowCurl (G : Space →L[ℝ] Space) (q : LiftTangent → Space)
    (z : LiftTangent) : Space :=
  curlMatrix ((fderiv ℝ q z).comp ((ContinuousLinearMap.inl ℝ Space ℝ).comp G))

/-- The same angular primitive as in the source, at each ordinary label. -/
def coveringPotential (P : ℝ) (m : Space → Space) (A : LiftTangent → Space)
    (z : LiftTangent) : Space :=
  potential P (m z.1) (fun θ => A (z.1, θ)) z.2

/-- The derivative in the angle direction is proved from the actual primitive. -/
theorem coveringPotential_angle_derivative (P : ℝ) (m : Space → Space)
    (A : LiftTangent → Space) (z : LiftTangent)
    (hA : Continuous (fun θ => A (z.1, θ)))
    (hq : DifferentiableAt ℝ (coveringPotential P m A) z) :
    fderiv ℝ (coveringPotential P m A) z (0, 1) =
      potentialMultiplier (m z.1) (A z) := by
  have hline : HasDerivAt (fun θ => coveringPotential P m A (z.1, θ))
      (fderiv ℝ (coveringPotential P m A) z (0, 1)) z.2 :=
    by
      have hh : HasFDerivAt (coveringPotential P m A)
          (fderiv ℝ (coveringPotential P m A) z) (z.1, z.2) := hq.hasFDerivAt
      simpa only [Function.comp_def, id_eq] using hh.comp_hasDerivAt z.2
        ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))
  exact hline.unique (potential_hasDerivAt P (m z.1) (fun θ => A (z.1, θ)) hA z.2)

/-- A literal source pair is a Piola curl for the actual constructed angular primitive. -/
theorem coveringPotential_pair_piola (P κ : ℝ) (m₀ : Space) (Ξ : Space → Space)
    (A : LiftTangent → Space) (hΞ : ContDiff ℝ 2 Ξ)
    (F : Space → Space ≃L[ℝ] Space) (z : LiftTangent)
    (hF : fderiv ℝ Ξ z.1 = (F z.1).toContinuousLinearMap)
    (hdet : (operatorMatrix (F z.1).toContinuousLinearMap).det = 1)
    (hm : (F z.1).symm.toContinuousLinearMap.adjoint m₀ ≠ 0)
    (htan : ⟪(F z.1).symm.toContinuousLinearMap.adjoint m₀, A z⟫_ℝ = 0)
    (hA : Continuous (fun θ => A (z.1, θ)))
    (hq : DifferentiableAt ℝ
      (coveringPotential P (fun y => (F y).symm.toContinuousLinearMap.adjoint m₀) A) z) :
    (F z.1).symm (A z + κ • coveringSlowCurl (F z.1).symm.toContinuousLinearMap
      (coveringPotential P (fun y => (F y).symm.toContinuousLinearMap.adjoint m₀) A) z) =
      coveringCurl κ m₀ (coveringPullbackCovector Ξ
        (coveringPotential P (fun y => (F y).symm.toContinuousLinearMap.adjoint m₀) A)) z := by
  have hp := covering_piola_curl κ m₀ Ξ _ hΞ z (F z.1) hF hdet hq
  rw [curl_lifted_split, coveringPotential_angle_derivative P _ A z hA hq,
    cross_potentialMultiplier _ _ hm htan] at hp
  simpa only [coveringSlowCurl, add_comm] using hp

variable (period : ℝ)

/-- Lifted slow curl, given by `curlMatrix ((fieldFDeriv period Q x).comp
((ContinuousLinearMap.inl ℝ Space ℝ).comp (F x.1).symm.toContinuousLinearMap))`. -/
def liftedSlowCurl (F : Space → Space ≃L[ℝ] Space) (Q : LiftDomain period → Space)
    (x : LiftDomain period) : Space :=
  curlMatrix ((fieldFDeriv period Q x).comp
    ((ContinuousLinearMap.inl ℝ Space ℝ).comp (F x.1).symm.toContinuousLinearMap))

theorem transformedLiftedCurl_split (κ : ℝ) (m₀ : Space)
    (F : Space → Space ≃L[ℝ] Space) (Q : LiftDomain period → Space)
    (x : LiftDomain period) :
    transformedLiftedCurl period κ m₀ F Q x =
      κ • liftedSlowCurl period F Q x +
        cross ((F x.1).symm.toContinuousLinearMap.adjoint m₀)
          (fieldDerivative period (0, 1) Q x) :=
  curl_lifted_split κ m₀ (fieldFDeriv period Q x) (F x.1).symm.toContinuousLinearMap

/-- Only the actual angular derivative formula for Q is needed to identify the source pair. -/
theorem lifted_pair_piola (κ : ℝ) (m₀ : Space) (Ξ : Space → Space)
    (A Q : LiftDomain period → Space) (hΞ : ContDiff ℝ 2 Ξ)
    (F : Space → Space ≃L[ℝ] Space)
    (hF : ∀ y, fderiv ℝ Ξ y = (F y).toContinuousLinearMap)
    (hdet : ∀ y, (operatorMatrix (F y).toContinuousLinearMap).det = 1)
    (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) (x : LiftDomain period)
    (hm : (F x.1).symm.toContinuousLinearMap.adjoint m₀ ≠ 0)
    (htan : ⟪(F x.1).symm.toContinuousLinearMap.adjoint m₀, A x⟫_ℝ = 0)
    (hangle : fieldDerivative period (0, 1) Q x =
      potentialMultiplier ((F x.1).symm.toContinuousLinearMap.adjoint m₀) (A x)) :
    (F x.1).symm (A x + κ • liftedSlowCurl period F Q x) =
      liftedCurl period κ m₀ (liftedPullbackCovector period Ξ Q) x := by
  have hp := lifted_piola_curl period κ m₀ Ξ Q hΞ F hF hdet hQ x
  rw [transformedLiftedCurl_split, hangle, cross_potentialMultiplier _ _ hm htan] at hp
  simpa only [add_comm] using hp

/-- The exact powers in source (13), without discarding the terminal corrector. -/
theorem weighted_lifted_pair_piola (κ : ℝ) (m₀ : Space) (Ξ : Space → Space)
    (A Q : LiftDomain period → Space) (hΞ : ContDiff ℝ 2 Ξ)
    (F : Space → Space ≃L[ℝ] Space)
    (hF : ∀ y, fderiv ℝ Ξ y = (F y).toContinuousLinearMap)
    (hdet : ∀ y, (operatorMatrix (F y).toContinuousLinearMap).det = 1)
    (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) (x : LiftDomain period)
    (hm : (F x.1).symm.toContinuousLinearMap.adjoint m₀ ≠ 0)
    (htan : ⟪(F x.1).symm.toContinuousLinearMap.adjoint m₀, A x⟫_ℝ = 0)
    (hangle : fieldDerivative period (0, 1) Q x =
      potentialMultiplier ((F x.1).symm.toContinuousLinearMap.adjoint m₀) (A x)) (p : ℕ) :
    (F x.1).symm (κ ^ p • A x + κ ^ (p + 1) • liftedSlowCurl period F Q x) =
      κ ^ p • liftedCurl period κ m₀ (liftedPullbackCovector period Ξ Q) x := by
  have he : κ ^ p • A x + κ ^ (p + 1) • liftedSlowCurl period F Q x =
      κ ^ p • (A x + κ • liftedSlowCurl period F Q x) := by
    rw [smul_add, smul_smul, pow_succ]
  rw [he, map_smul, lifted_pair_piola period κ m₀ Ξ A Q hΞ F hF hdet hQ x hm htan hangle]

variable [Fact (0 < period)]

/-- Piola pair Lᵖ, given by `κ ^ p • piolaLiftedCurlLp period κ m₀ Ξ Q hΞ hc hQ`. -/
def piolaPairLp (κ : ℝ) (m₀ : Space) (Ξ : Space → Space)
    (Q : LiftDomain period → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (hc : HasCompactSupport Q) (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) (p : ℕ) :
    LiftL2 period := κ ^ p • piolaLiftedCurlLp period κ m₀ Ξ Q hΞ hc hQ

theorem piolaPairLp_mem (κ : ℝ) (m₀ : Space) (Ξ : Space → Space)
    (Q : LiftDomain period → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (hc : HasCompactSupport Q) (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x)) (p : ℕ) :
    piolaPairLp period κ m₀ Ξ Q hΞ hc hQ p ∈ divergenceFreeSpace period κ m₀ :=
  (divergenceFreeSpace period κ m₀).smul_mem (κ ^ p)
    (piolaLiftedCurlLp_mem period κ m₀ Ξ Q hΞ hc hQ)

theorem piolaPairLp_ae (κ : ℝ) (m₀ : Space) (Ξ : Space → Space)
    (A Q : LiftDomain period → Space) (hΞ : ContDiff ℝ ∞ Ξ)
    (hc : HasCompactSupport Q) (hQ : ∀ x, ContDiff ℝ ∞ (localFieldLift period Q x))
    (F : Space → Space ≃L[ℝ] Space)
    (hF : ∀ y, fderiv ℝ Ξ y = (F y).toContinuousLinearMap)
    (hdet : ∀ y, (operatorMatrix (F y).toContinuousLinearMap).det = 1)
    (hm : ∀ x, (F x).symm.toContinuousLinearMap.adjoint m₀ ≠ 0)
    (htan : ∀ x, ⟪(F x.1).symm.toContinuousLinearMap.adjoint m₀, A x⟫_ℝ = 0)
    (hangle : ∀ x, fieldDerivative period (0, 1) Q x =
      potentialMultiplier ((F x.1).symm.toContinuousLinearMap.adjoint m₀) (A x)) (p : ℕ) :
    (piolaPairLp period κ m₀ Ξ Q hΞ hc hQ p : LiftDomain period → Space) =ᵐ[liftMeasure period]
      fun x => (F x.1).symm (κ ^ p • A x + κ ^ (p + 1) • liftedSlowCurl period F Q x) := by
  filter_upwards [Lp.coeFn_smul (κ ^ p) (piolaLiftedCurlLp period κ m₀ Ξ Q hΞ hc hQ),
    liftedCurlLp_ae period κ m₀ (liftedPullbackCovector period Ξ Q)
      (liftedPullbackCovector_compact period Ξ Q hc)
      (liftedPullbackCovector_smooth period Ξ Q hΞ hQ)] with x hs hx
  calc
    piolaPairLp period κ m₀ Ξ Q hΞ hc hQ p x =
        κ ^ p • piolaLiftedCurlLp period κ m₀ Ξ Q hΞ hc hQ x := hs
    _ = κ ^ p • liftedCurl period κ m₀ (liftedPullbackCovector period Ξ Q) x :=
      congrArg (fun v : Space => κ ^ p • v) hx
    _ = (F x.1).symm (κ ^ p • A x + κ ^ (p + 1) • liftedSlowCurl period F Q x) :=
      (weighted_lifted_pair_piola period κ m₀ Ξ A Q (hΞ.of_le (by simp)) F hF hdet hQ x
        (hm x.1) (htan x) (hangle x) p).symm

end EulerPacketPiola
