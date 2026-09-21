/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanDuhamelFrechet

/-!
# Frechet spatial derivatives of the Euclidean heat semigroup

The coordinate heat-kernel derivative formulas are assembled here into the
genuine first and second Frechet derivatives of the Euclidean heat semigroup.
The Hessian contains all mixed entries, not only its diagonal trace.
-/

@[expose] public noncomputable section
open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-- One coordinate of the spatial gradient of the Euclidean heat semigroup. -/
def heatSemigroupGradientCoordND {n : ℕ} (t : ℝ)
    (f : (Fin n → ℝ) → ℝ) (k : Fin n) (x : Fin n → ℝ) : ℝ :=
  ∫ y : Fin n → ℝ,
    (heatKernelND t (x - y) * (-(x - y) k / (2 * t))) * f y

/-- The spatial gradient of the Euclidean heat semigroup as a continuous
linear functional. -/
def heatSemigroupGradientCLM {n : ℕ} (t : ℝ)
    (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  coordinateLinearFunctional (fun k => heatSemigroupGradientCoordND t f k x)

@[simp] theorem heatSemigroupGradientCLM_apply {n : ℕ} (t : ℝ)
    (f : (Fin n → ℝ) → ℝ) (x v : Fin n → ℝ) :
    heatSemigroupGradientCLM t f x v =
      ∑ k : Fin n, heatSemigroupGradientCoordND t f k x * v k := by
  simp [heatSemigroupGradientCLM]

section HessianPackaging

local instance heatCoordinateDualNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance heatCoordinateBilinearNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance heatCoordinateBilinearContinuousAdd {n : ℕ} :
    ContinuousAdd ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :=
  IsTopologicalAddGroup.toContinuousAdd

/-- The full spatial Hessian of the Euclidean heat semigroup, including mixed
entries, as a curried continuous bilinear form. -/
def heatSemigroupHessianCLM {n : ℕ} (t : ℝ)
    (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ) :=
  coordinateHessianCLM (fun j k =>
    heatHessianEntryConvolutionND t f j k x)

@[simp] theorem heatSemigroupHessianCLM_apply {n : ℕ} (t : ℝ)
    (f : (Fin n → ℝ) → ℝ) (x v w : Fin n → ℝ) :
    heatSemigroupHessianCLM t f x v w =
      ∑ j : Fin n, ∑ k : Fin n,
        heatHessianEntryConvolutionND t f j k x * (v j * w k) := by
  simp [heatSemigroupHessianCLM]

/-- The operator-valued heat-semigroup Hessian is continuous in space for
bounded continuous data. -/
theorem continuous_heatSemigroupHessianCLM {n : ℕ} {t : ℝ} (ht : 0 < t)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    Continuous (heatSemigroupHessianCLM t f) := by
  unfold heatSemigroupHessianCLM coordinateHessianCLM
  apply continuous_finsetSum
  intro j _
  apply continuous_finsetSum
  intro k _
  exact (continuous_heatHessianEntryConvolutionND ht f.continuous
    (fun y => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm y) j k).smul
      continuous_const

end HessianPackaging

/-- A fixed gradient coordinate has the corresponding full Hessian column as
its genuine Frechet derivative. -/
theorem hasFDerivAt_heatSemigroupGradientCoordND
    {n : ℕ} {t : ℝ} (ht : 0 < t)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (k : Fin n) (x : Fin n → ℝ) :
    HasFDerivAt (heatSemigroupGradientCoordND t f k)
      (coordinateLinearFunctional (fun j =>
        heatHessianEntryConvolutionND t f j k x)) x := by
  classical
  refine hasFDerivAt_of_continuous_coordinate_derivatives
    (heatSemigroupGradientCoordND t f k)
    (fun z => coordinateLinearFunctional (fun j =>
      heatHessianEntryConvolutionND t f j k z)) ?_ ?_ x
  · unfold coordinateLinearFunctional
    apply continuous_finsetSum
    intro j _
    exact (continuous_heatHessianEntryConvolutionND ht f.continuous
      (fun y => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm y) j k).smul
        continuous_const
  · intro z j
    have hderiv : HasDerivAt
        (fun a => heatSemigroupGradientCoordND t f k (Function.update z j a))
        (heatHessianEntryConvolutionND t f j k z) (z j) := by
      simpa only [heatSemigroupGradientCoordND,
        heatHessianEntryConvolutionND] using
        hasDerivAt_heatSemigroupND_coordGradient_entry ht z j k
          f.continuous.aestronglyMeasurable
          (fun y => f.norm_coe_le_norm y)
    have hval : coordinateLinearFunctional (fun i =>
        heatHessianEntryConvolutionND t f i k z) (Pi.single j 1) =
        heatHessianEntryConvolutionND t f j k z :=
      coordinateLinearFunctional_single _ j
    rw [hval]
    exact hderiv.hasFDerivAt

/-- The operator-valued heat-semigroup gradient is continuous in space. -/
theorem continuous_heatSemigroupGradientCLM
    {n : ℕ} {t : ℝ} (ht : 0 < t)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    Continuous (heatSemigroupGradientCLM t f) := by
  unfold heatSemigroupGradientCLM coordinateLinearFunctional
  apply continuous_finsetSum
  intro k _
  exact (continuous_iff_continuousAt.mpr fun x =>
    (hasFDerivAt_heatSemigroupGradientCoordND ht f k x).continuousAt).smul
      continuous_const

/-- The Euclidean heat semigroup has the packaged spatial gradient as its
genuine Frechet derivative at every positive time. -/
theorem hasFDerivAt_heatSemigroupND
    {n : ℕ} {t : ℝ} (ht : 0 < t)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (x : Fin n → ℝ) :
    HasFDerivAt (heatSemigroupND t f)
      (heatSemigroupGradientCLM t f x) x := by
  classical
  apply hasFDerivAt_of_continuous_coordinate_derivatives
  · exact continuous_heatSemigroupGradientCLM ht f
  · intro z k
    have h := (hasDerivAt_heatSemigroupND_coord_update ht z k
      f.continuous.aestronglyMeasurable
      (fun y => f.norm_coe_le_norm y) (z k)).hasFDerivAt
    have hval : heatSemigroupGradientCLM t f z (Pi.single k 1) =
        heatSemigroupGradientCoordND t f k z :=
      coordinateLinearFunctional_single _ k
    rw [hval]
    simpa only [heatSemigroupGradientCoordND, Function.update_eq_self] using h

/-- The operator-valued spatial gradient has the full packaged Hessian as its
genuine Frechet derivative. -/
theorem hasFDerivAt_heatSemigroupGradientCLM
    {n : ℕ} {t : ℝ} (ht : 0 < t)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (x : Fin n → ℝ) :
    HasFDerivAt (heatSemigroupGradientCLM t f)
      (heatSemigroupHessianCLM t f x) x := by
  classical
  apply hasFDerivAt_of_continuous_coordinate_derivatives
  · exact continuous_heatSemigroupHessianCLM ht f
  · intro z j
    have hderiv : HasDerivAt
        (fun a => heatSemigroupGradientCLM t f (Function.update z j a))
        (∑ k : Fin n, heatHessianEntryConvolutionND t f j k z •
          (ContinuousLinearMap.proj k : (Fin n → ℝ) →L[ℝ] ℝ)) (z j) := by
      unfold heatSemigroupGradientCLM coordinateLinearFunctional
      have hfun : (fun a => ∑ k : Fin n,
          heatSemigroupGradientCoordND t f k (Function.update z j a) •
            (ContinuousLinearMap.proj k : (Fin n → ℝ) →L[ℝ] ℝ)) =
          ∑ k : Fin n, fun a => heatSemigroupGradientCoordND t f k
            (Function.update z j a) •
              (ContinuousLinearMap.proj k : (Fin n → ℝ) →L[ℝ] ℝ) := by
        funext a
        simp only [Finset.sum_apply]
      rw [hfun]
      exact HasDerivAt.sum (u := Finset.univ) fun k _ =>
        ((hasDerivAt_heatSemigroupND_coordGradient_entry ht z j k
          f.continuous.aestronglyMeasurable
          (fun y => f.norm_coe_le_norm y)).congr_of_eventuallyEq
            (Filter.Eventually.of_forall fun a => by
              rfl)).smul_const
                (ContinuousLinearMap.proj k : (Fin n → ℝ) →L[ℝ] ℝ)
    have h := hderiv.hasFDerivAt
    simpa [heatSemigroupHessianCLM, coordinateHessianCLM, coordinateRankOne,
      coordinateLinearFunctional, Pi.single_apply] using h

/-- At every positive time, the Euclidean heat semigroup is genuinely twice
continuously Frechet differentiable in space. -/
theorem contDiff_two_heatSemigroupND
    {n : ℕ} {t : ℝ} (ht : 0 < t)
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ) :
    ContDiff ℝ 2 (heatSemigroupND t f) := by
  apply (contDiff_succ_iff_hasFDerivAt (n := 1)).mpr
  refine ⟨heatSemigroupGradientCLM t f, ?_,
    hasFDerivAt_heatSemigroupND ht f⟩
  exact contDiff_one_iff_hasFDerivAt.mpr
    ⟨heatSemigroupHessianCLM t f,
      continuous_heatSemigroupHessianCLM ht f,
      hasFDerivAt_heatSemigroupGradientCLM ht f⟩

end AnalyticPDE
end RicciFlow
