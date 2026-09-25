/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatEllipticity
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.MatrixZeroInitialOperator
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.SpatialLinearChange
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiberLinearChange
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.FiniteSourceExtension

/-!
# A genuine inverse for the frozen tensor-heat operator

At a point of a Riemannian chart, the inverse-metric principal contraction
is the trace in an orthonormal tangent basis.  Pulling that basis through the
inverse chart derivative therefore conjugates the actual frozen operator to
the standard coefficientwise Euclidean heat operator.  This file proves the
normalization identity and packages the resulting bounded zero-initial
Schauder inverse.
-/

@[expose] public noncomputable section
open Bundle FiberBundle TensorProduct
open scoped Manifold ContDiff BigOperators

namespace RicciFlow
namespace AnalyticPDE

open CovariantDerivative

private theorem value_spatialFiberPostcomp
    {X Y V W : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {t₀ T α : ℝ} (hα : 0 ≤ α) (L : Y →L[ℝ] X) (B : V →L[ℝ] W)
    (u : FiniteParabolicC2AlphaBanach X V t₀ T α)
    (z : ℝ × Y) (hz : z ∈ parabolicFiniteCylinder Y t₀ T) :
    FiniteParabolicC2AlphaBanach.value
        (FiniteParabolicC2AlphaBanach.spatialPullbackL hα L
          (FiniteParabolicC2AlphaBanach.fiberPostcompL B u)) z =
      B (FiniteParabolicC2AlphaBanach.value u (parabolicSpatialLinearMapBetween L z)) := by
  rw [FiniteParabolicC2AlphaBanach.value_spatialPullbackL hα L _ z hz]
  exact FiniteParabolicC2AlphaBanach.value_fiberPostcompL B u _
    (parabolicSpatialLinearMapBetween_mapsTo L t₀ T hz)

private theorem timeDeriv_spatialFiberPostcomp
    {X Y V W : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {t₀ T α : ℝ} (hα : 0 ≤ α) (L : Y →L[ℝ] X) (B : V →L[ℝ] W)
    (u : FiniteParabolicC2AlphaBanach X V t₀ T α)
    (z : ℝ × Y) (hz : z ∈ parabolicFiniteCylinder Y t₀ T) :
    FiniteParabolicC2AlphaBanach.timeDeriv
        (FiniteParabolicC2AlphaBanach.spatialPullbackL hα L
          (FiniteParabolicC2AlphaBanach.fiberPostcompL B u)) z =
      B (FiniteParabolicC2AlphaBanach.timeDeriv u (parabolicSpatialLinearMapBetween L z)) := by
  rw [FiniteParabolicC2AlphaBanach.timeDeriv_spatialPullbackL hα L _ z hz]
  exact FiniteParabolicC2AlphaBanach.timeDeriv_fiberPostcompL B u _
    (parabolicSpatialLinearMapBetween_mapsTo L t₀ T hz)

private theorem spaceSecondDeriv_spatialFiberPostcomp
    {X Y V W : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {t₀ T α : ℝ} (hα : 0 ≤ α) (L : Y →L[ℝ] X) (B : V →L[ℝ] W)
    (u : FiniteParabolicC2AlphaBanach X V t₀ T α)
    (z : ℝ × Y) (hz : z ∈ parabolicFiniteCylinder Y t₀ T) (v w : Y) :
    FiniteParabolicC2AlphaBanach.spaceSecondDeriv
        (FiniteParabolicC2AlphaBanach.spatialPullbackL hα L
          (FiniteParabolicC2AlphaBanach.fiberPostcompL B u)) z v w =
      B (FiniteParabolicC2AlphaBanach.spaceSecondDeriv u
        (parabolicSpatialLinearMapBetween L z) (L v) (L w)) := by
  rw [FiniteParabolicC2AlphaBanach.spaceSecondDeriv_spatialPullbackL hα L _ z hz]
  simp only [pullbackSecondDerivativeL_apply]
  rw [FiniteParabolicC2AlphaBanach.spaceSecondDeriv_fiberPostcompL B u _
    (parabolicSpatialLinearMapBetween_mapsTo L t₀ T hz)]
  rfl

private theorem spaceSecondDeriv_spatialFiberPostcomp_clm
    {X Y V W : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {t₀ T α : ℝ} (hα : 0 ≤ α) (L : Y →L[ℝ] X) (B : V →L[ℝ] W)
    (u : FiniteParabolicC2AlphaBanach X V t₀ T α)
    (z : ℝ × Y) (hz : z ∈ parabolicFiniteCylinder Y t₀ T) :
    FiniteParabolicC2AlphaBanach.spaceSecondDeriv
        (FiniteParabolicC2AlphaBanach.spatialPullbackL hα L
          (FiniteParabolicC2AlphaBanach.fiberPostcompL B u)) z =
      pullbackSecondDerivativeL L (postcomposeSecondDerivativeL B
        (FiniteParabolicC2AlphaBanach.spaceSecondDeriv u
          (parabolicSpatialLinearMapBetween L z))) := by
  rw [FiniteParabolicC2AlphaBanach.spaceSecondDeriv_spatialPullbackL hα L _ z hz,
    FiniteParabolicC2AlphaBanach.spaceSecondDeriv_fiberPostcompL B u _
      (parabolicSpatialLinearMapBetween_mapsTo L t₀ T hz)]

private theorem euclideanTrace_postcompose {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (n : ℕ) (B : V →L[ℝ] W)
    (D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] V) :
    euclideanVectorBilinearTraceCLM n W (postcomposeSecondDerivativeL B D) =
      B (∑ k : Fin n, D (Pi.single k 1) (Pi.single k 1)) := by
  rw [euclideanVectorBilinearTraceCLM_apply]
  simp_rw [postcomposeSecondDerivativeL_apply]
  rw [map_sum]

private theorem matrixZeroInitialOperator_cauchy {n d : ℕ} {t₀ T α : ℝ}
    (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (q : ParabolicC0AlphaBanach (Fin n → ℝ) (Fin d → Fin d → ℝ) α Set.univ)
    (z : ℝ × (Fin n → ℝ)) (hz : z ∈ parabolicFiniteCylinder (Fin n → ℝ) t₀ T) :
    FiniteParabolicC2AlphaBanach.timeDeriv (matrixZeroInitialOperator hT hα hα1 q) z -
        (∑ k : Fin n, FiniteParabolicC2AlphaBanach.spaceSecondDeriv
          (matrixZeroInitialOperator hT hα hα1 q) z (Pi.single k 1) (Pi.single k 1)) =
      ParabolicC0AlphaBanach.evalCLM z (Set.mem_univ _) q := by
  have ht : z.1 ∈ Set.Ioc t₀ T := by
    simpa [parabolicFiniteCylinder] using hz
  have hheat := matrixZeroInitialSolution_heatEquation hT hα hα1 q ht z.2
  change FiniteParabolicC2AlphaBanach.timeDeriv (matrixZeroInitialSolution hT hα hα1 q) z -
      (∑ k : Fin n, FiniteParabolicC2AlphaBanach.spaceSecondDeriv
        (matrixZeroInitialSolution hT hα hα1 q) z (Pi.single k 1) (Pi.single k 1)) = _
  rw [hheat]
  abel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- The inverse-chart differential written without a dependent cast.  By
the inverse-function identities for an extended chart, this forward chart
differential is the inverse of the differential of the chart inverse. -/
def inverseExtChartDerivativeAt
    (p : M) (x : M) (hxChart : x ∈ (extChartAt I p).source) :
    TM x →L[ℝ] E :=
  mfderiv% (extChartAt I p) x

/-- At a point in a fixed chart, the pulled-back local frame is precisely
the inverse chart derivative applied to the intrinsic local frame. -/
theorem localFrameInChart_at_eq_inverseChartDerivative
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M}
    (hxChart : x ∈ (extChartAt I p).source) (i : ι) :
    localFrameInChart (I := I) p e b i ((extChartAt I p) x) =
      inverseExtChartDerivativeAt (I := I) p x hxChart
        (e.localFrame b i x) := by
  unfold localFrameInChart
  rw [VectorField.mpullbackWithin_apply]
  rw [(extChartAt I p).left_inv hxChart]
  rw [ContinuousLinearMap.inverse_eq
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
      (I := I) (x := p) hxChart)
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm'
      (I := I) (x := p) hxChart)]
  rfl

/-- **Orthonormal normalization of the actual principal coefficient.**
The inverse-Gram contraction obtained from the genuine Riemannian metric is
the sum of the Hessian on any orthonormal tangent basis pulled back through
the inverse chart derivative. -/
theorem localTensorHeatPrincipalCoefficient_eq_orthonormalTrace
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    (o : OrthonormalBasis κ ℝ (TM x))
    (A : E →L[ℝ] E →L[ℝ] (ι × ι → ℝ)) :
    localTensorHeatPrincipalCoefficient (I := I) p e b
        ((extChartAt I p) x) A =
      ∑ k : κ, A
        (inverseExtChartDerivativeAt (I := I) p x hxChart (o k))
        (inverseExtChartDerivativeAt (I := I) p x hxChart (o k)) := by
  let Dinv : TM x →L[ℝ] E :=
    inverseExtChartDerivativeAt (I := I) p x hxChart
  let K : TM x →ₗ[ℝ] TM x →ₗ[ℝ] (ι × ι → ℝ) :=
    { toFun := fun v =>
        (A (Dinv v)).comp Dinv |>.toLinearMap
      map_add' := by
        intro u v
        ext w out
        simp
      map_smul' := by
        intro c v
        ext w out
        simp }
  have hframe := canonicalCovariantTensor_eq_sum_localFrame_inverseGram
    (I := I) e b hxFrame
  have hon := InnerProductSpace.canonicalCovariantTensor_eq_sum (TM x) o
  have htensor :
      (∑ i : ι, ∑ j : ι,
        localFrameInverseGramMatrix (I := I) e b x i j •
          (e.localFrame b i x ⊗ₜ[ℝ] e.localFrame b j x)) =
        ∑ k : κ, o k ⊗ₜ[ℝ] o k := hframe.symm.trans hon
  have htrace := congrArg (TensorProduct.lift K) htensor
  simp only [map_sum, LinearMapClass.map_smul, TensorProduct.lift.tmul] at htrace
  ext out
  change movingFramePrincipalCoefficient
      (fun i j => localFrameInverseGramMatrixInChart (I := I) p e b i j
        ((extChartAt I p) x))
      (fun i => localFrameInChart (I := I) p e b i ((extChartAt I p) x)) A out = _
  rw [movingFramePrincipalCoefficient_apply]
  simp_rw [localFrameInverseGramMatrixInChart_apply
    (I := I) p e b hxChart]
  simp_rw [localFrameInChart_at_eq_inverseChartDerivative
    (I := I) p e b hxChart]
  have hout := congrFun htrace out
  simpa [K, Dinv] using hout

/-! ## The normalizing coordinate equivalence -/

/-- The chart differential at a point, regarded as a continuous linear
equivalence from the tangent fibre to the model space. -/
def extChartDerivativeEquivAt
    (p : M) (x : M) (hxChart : x ∈ (extChartAt I p).source) :
    TM x ≃L[ℝ] E :=
  Classical.choose (isInvertible_mfderiv_extChartAt
    (I := I) (x := p) hxChart)

@[simp]
theorem extChartDerivativeEquivAt_apply
    (p : M) (x : M) (hxChart : x ∈ (extChartAt I p).source)
    (v : TM x) :
    extChartDerivativeEquivAt (I := I) p x hxChart v =
      mfderiv% (extChartAt I p) x v := by
  exact DFunLike.congr_fun
    (Classical.choose_spec (isInvertible_mfderiv_extChartAt
      (I := I) (x := p) hxChart)) v

/-- Orthonormal tangent coordinates followed by the chart differential.
This is the spatial linear equivalence which normalizes the actual frozen
inverse-metric contraction to the standard Euclidean trace. -/
def chartOrthonormalSpatialEquiv
    (p : M) (x : M) (hxChart : x ∈ (extChartAt I p).source) :
    (Fin (Module.finrank ℝ (TM x)) → ℝ) ≃L[ℝ] E :=
  ((stdOrthonormalBasis ℝ (TM x)).toBasis.equivFun.symm
      |>.toContinuousLinearEquiv).trans
    (extChartDerivativeEquivAt (I := I) p x hxChart)

@[simp]
theorem chartOrthonormalSpatialEquiv_single
    (p : M) (x : M) (hxChart : x ∈ (extChartAt I p).source)
    (k : Fin (Module.finrank ℝ (TM x))) :
    chartOrthonormalSpatialEquiv (I := I) p x hxChart (Pi.single k 1) =
      inverseExtChartDerivativeAt (I := I) p x hxChart
        ((stdOrthonormalBasis ℝ (TM x)) k) := by
  simp [chartOrthonormalSpatialEquiv, inverseExtChartDerivativeAt,
    extChartDerivativeEquivAt_apply, Basis.equivFun_symm_single]
  rfl

/-- In the normalizing coordinates, the genuine frozen principal
coefficient is exactly the standard Euclidean trace. -/
theorem frozenPrincipalCoefficient_pullback_eq_euclideanTrace
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    (A : (Fin (Module.finrank ℝ (TM x)) → ℝ) →L[ℝ]
      (Fin (Module.finrank ℝ (TM x)) → ℝ) →L[ℝ] (ι × ι → ℝ)) :
    frozenLocalTensorHeatPrincipalCoefficient (I := I) p e b x
        (pullbackSecondDerivativeL
          (chartOrthonormalSpatialEquiv (I := I) p x hxChart).symm.toContinuousLinearMap A) =
      euclideanVectorBilinearTraceCLM
        (Module.finrank ℝ (TM x)) (ι × ι → ℝ) A := by
  rw [frozenLocalTensorHeatPrincipalCoefficient]
  rw [localTensorHeatPrincipalCoefficient_eq_orthonormalTrace
    (I := I) p e b hxFrame hxChart (stdOrthonormalBasis ℝ (TM x))]
  rw [euclideanVectorBilinearTraceCLM_apply]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [pullbackSecondDerivativeL_apply]
  have hcoord :
      (chartOrthonormalSpatialEquiv (I := I) p x hxChart).symm
          (inverseExtChartDerivativeAt (I := I) p x hxChart
            ((stdOrthonormalBasis ℝ (TM x)) k)) = Pi.single k 1 := by
    rw [← chartOrthonormalSpatialEquiv_single (I := I) p x hxChart k]
    exact (chartOrthonormalSpatialEquiv (I := I) p x hxChart).symm_apply_apply _
  change A
      ((chartOrthonormalSpatialEquiv (I := I) p x hxChart).symm
        (inverseExtChartDerivativeAt (I := I) p x hxChart
          ((stdOrthonormalBasis ℝ (TM x)) k)))
      ((chartOrthonormalSpatialEquiv (I := I) p x hxChart).symm
        (inverseExtChartDerivativeAt (I := I) p x hxChart
          ((stdOrthonormalBasis ℝ (TM x)) k))) = _
  rw [hcoord]

/-! ## The bounded conjugated inverse -/

/-- Currying tensor coefficients identifies pair-indexed coordinates with
the nested finite matrices used by the coefficientwise Euclidean solver. -/
def tensorCoordinateCurryEquiv (d : ℕ) :
    (Fin d × Fin d → ℝ) ≃L[ℝ] (Fin d → Fin d → ℝ) :=
  (LinearEquiv.curry ℝ ℝ (Fin d) (Fin d)).toContinuousLinearEquiv

@[simp]
theorem tensorCoordinateCurryEquiv_apply
    (d : ℕ) (u : Fin d × Fin d → ℝ) (i j : Fin d) :
    tensorCoordinateCurryEquiv d u i j = u (i, j) := rfl

@[simp]
theorem tensorCoordinateCurryEquiv_symm_apply
    (d : ℕ) (u : Fin d → Fin d → ℝ) (ij : Fin d × Fin d) :
    (tensorCoordinateCurryEquiv d).symm u ij = u ij.1 ij.2 := rfl

/-- Pull a global tensor source into the normalizing orthonormal chart
coordinates and curry its tensor indices. -/
def frozenTensorHeatSourceToEuclideanL
    (p : M) (x : M) (hxChart : x ∈ (extChartAt I p).source)
    (d : ℕ) {α : ℝ} (hα0 : 0 ≤ α) :
    ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
        (Set.univ : Set (ℝ × E)) →L[ℝ]
      ParabolicC0AlphaBanach
        (Fin (Module.finrank ℝ (TM x)) → ℝ) (Fin d → Fin d → ℝ) α
        (Set.univ : Set (ℝ × (Fin (Module.finrank ℝ (TM x)) → ℝ))) :=
  (ParabolicC0AlphaBanach.compL
      (X := Fin (Module.finrank ℝ (TM x)) → ℝ)
      (E := Fin d × Fin d → ℝ) (F := Fin d → Fin d → ℝ)
      (α := α) (s := Set.univ)
      (tensorCoordinateCurryEquiv d).toContinuousLinearMap).comp
    (ParabolicC0AlphaBanach.globalSpatialPullbackL hα0
      (chartOrthonormalSpatialEquiv (I := I) p x hxChart).toContinuousLinearMap)

@[simp]
theorem evalCLM_frozenTensorHeatSourceToEuclideanL
    (p : M) (x : M) (hxChart : x ∈ (extChartAt I p).source)
    (d : ℕ) {α : ℝ} (hα0 : 0 ≤ α)
    (q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
      (Set.univ : Set (ℝ × E)))
    (z : ℝ × (Fin (Module.finrank ℝ (TM x)) → ℝ)) :
    ParabolicC0AlphaBanach.evalCLM z (Set.mem_univ z)
        (frozenTensorHeatSourceToEuclideanL
          (I := I) p x hxChart d hα0 q) =
      tensorCoordinateCurryEquiv d
        (ParabolicC0AlphaBanach.evalCLM
          (parabolicSpatialLinearMapBetween
            (chartOrthonormalSpatialEquiv (I := I) p x hxChart).toContinuousLinearMap z)
          (Set.mem_univ _) q) := by
  rw [frozenTensorHeatSourceToEuclideanL, ContinuousLinearMap.comp_apply,
    ParabolicC0AlphaBanach.evalCLM_compL_apply,
    ParabolicC0AlphaBanach.evalCLM_globalSpatialPullbackL]
  rfl

/-- The bounded zero-initial inverse of the genuine frozen tensor-heat
operator, obtained by spatial normalization, coefficientwise Euclidean
Duhamel solution, uncurrying, and transport back to the original chart. -/
def frozenTensorHeatZeroInitialInverseL
    (p : M) (x : M) (hxChart : x ∈ (extChartAt I p).source)
    (d : ℕ) {t₀ T α : ℝ}
    (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
        (Set.univ : Set (ℝ × E)) →L[ℝ]
      FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α :=
  (FiniteParabolicC2AlphaBanach.spatialPullbackL hα.le
      (chartOrthonormalSpatialEquiv (I := I) p x hxChart).symm.toContinuousLinearMap).comp
    ((FiniteParabolicC2AlphaBanach.fiberPostcompL
        (X := Fin (Module.finrank ℝ (TM x)) → ℝ)
        (tensorCoordinateCurryEquiv d).symm.toContinuousLinearMap).comp
      ((matrixZeroInitialOperator
          (n := Module.finrank ℝ (TM x)) (d := d) hT hα hα1).comp
        (frozenTensorHeatSourceToEuclideanL
          (I := I) p x hxChart d hα.le)))

/-- The value of the conjugated frozen inverse is obtained by evaluating the
Euclidean matrix solution in the normalized spatial coordinates and then
uncurrying the tensor indices. -/
@[simp]
theorem value_frozenTensorHeatZeroInitialInverseL
    (p : M) (x : M) (hxChart : x ∈ (extChartAt I p).source)
    (d : ℕ) {t₀ T α : ℝ}
    (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
      (Set.univ : Set (ℝ × E)))
    (z : ℝ × E) (hz : z ∈ parabolicFiniteCylinder E t₀ T) :
    FiniteParabolicC2AlphaBanach.value
        (frozenTensorHeatZeroInitialInverseL
          (I := I) p x hxChart d hT hα hα1 q) z =
      (tensorCoordinateCurryEquiv d).symm
        (FiniteParabolicC2AlphaBanach.value
          (matrixZeroInitialOperator
            (n := Module.finrank ℝ (TM x)) (d := d) hT hα hα1
            (frozenTensorHeatSourceToEuclideanL
              (I := I) p x hxChart d hα.le q))
          (parabolicSpatialLinearMapBetween
            (chartOrthonormalSpatialEquiv
              (I := I) p x hxChart).symm.toContinuousLinearMap z)) := by
  simpa only [frozenTensorHeatZeroInitialInverseL, ContinuousLinearMap.comp_apply] using!
    value_spatialFiberPostcomp hα.le
      (chartOrthonormalSpatialEquiv (I := I) p x hxChart).symm.toContinuousLinearMap
      (tensorCoordinateCurryEquiv d).symm.toContinuousLinearMap
      (matrixZeroInitialOperator
        (n := Module.finrank ℝ (TM x)) (d := d) hT hα hα1
        (frozenTensorHeatSourceToEuclideanL (I := I) p x hxChart d hα.le q)) z hz

/-- Explicit operator-norm Schauder estimate for the genuine frozen tensor
heat inverse.  The only geometric factors are the two spatial coordinate
changes and the finite-dimensional curry/uncurry maps; the analytic factor
is the proved Euclidean matrix Schauder constant. -/
theorem norm_frozenTensorHeatZeroInitialInverseL_le
    (p : M) (x : M) (hxChart : x ∈ (extChartAt I p).source)
    (d : ℕ) {t₀ T α : ℝ}
    (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ‖frozenTensorHeatZeroInitialInverseL
        (I := I) p x hxChart d hT hα hα1‖ ≤
      ‖FiniteParabolicC2AlphaBanach.spatialPullbackL
          (E := Fin d × Fin d → ℝ) (t₀ := t₀) (T := T) (α := α) hα.le
          (chartOrthonormalSpatialEquiv
            (I := I) p x hxChart).symm.toContinuousLinearMap‖ *
        (‖FiniteParabolicC2AlphaBanach.fiberPostcompL
            (X := Fin (Module.finrank ℝ (TM x)) → ℝ)
            (t₀ := t₀) (T := T) (α := α)
            (tensorCoordinateCurryEquiv d).symm.toContinuousLinearMap‖ *
          (matrixZeroInitialSchauderConstant
              (Module.finrank ℝ (TM x)) d t₀ T α *
            ‖frozenTensorHeatSourceToEuclideanL
              (I := I) p x hxChart d hα.le‖)) := by
  unfold frozenTensorHeatZeroInitialInverseL
  calc
    ‖(FiniteParabolicC2AlphaBanach.spatialPullbackL
          (E := Fin d × Fin d → ℝ) (t₀ := t₀) (T := T) (α := α) hα.le
          (chartOrthonormalSpatialEquiv
            (I := I) p x hxChart).symm.toContinuousLinearMap).comp
        ((FiniteParabolicC2AlphaBanach.fiberPostcompL
            (X := Fin (Module.finrank ℝ (TM x)) → ℝ)
            (t₀ := t₀) (T := T) (α := α)
            (tensorCoordinateCurryEquiv d).symm.toContinuousLinearMap).comp
          ((matrixZeroInitialOperator hT hα hα1).comp
            (frozenTensorHeatSourceToEuclideanL
              (I := I) p x hxChart d hα.le)))‖
        ≤ ‖FiniteParabolicC2AlphaBanach.spatialPullbackL
            (E := Fin d × Fin d → ℝ) (t₀ := t₀) (T := T) (α := α) hα.le
            (chartOrthonormalSpatialEquiv
              (I := I) p x hxChart).symm.toContinuousLinearMap‖ *
          ‖(FiniteParabolicC2AlphaBanach.fiberPostcompL
              (X := Fin (Module.finrank ℝ (TM x)) → ℝ)
              (t₀ := t₀) (T := T) (α := α)
              (tensorCoordinateCurryEquiv d).symm.toContinuousLinearMap).comp
            ((matrixZeroInitialOperator hT hα hα1).comp
              (frozenTensorHeatSourceToEuclideanL
                (I := I) p x hxChart d hα.le))‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ _ := by
      have hmatrix :
          ‖(matrixZeroInitialOperator hT hα hα1).comp
              (frozenTensorHeatSourceToEuclideanL
                (I := I) p x hxChart d hα.le)‖ ≤
            matrixZeroInitialSchauderConstant
                (Module.finrank ℝ (TM x)) d t₀ T α *
              ‖frozenTensorHeatSourceToEuclideanL
                (I := I) p x hxChart d hα.le‖ := by
        calc
          ‖(matrixZeroInitialOperator hT hα hα1).comp
              (frozenTensorHeatSourceToEuclideanL
                (I := I) p x hxChart d hα.le)‖
              ≤ ‖matrixZeroInitialOperator
                  (n := Module.finrank ℝ (TM x)) (d := d)
                  hT hα hα1‖ *
                ‖frozenTensorHeatSourceToEuclideanL
                  (I := I) p x hxChart d hα.le‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (norm_matrixZeroInitialOperator_le hT hα hα1)
            (norm_nonneg _)
      have hinner :
          ‖(FiniteParabolicC2AlphaBanach.fiberPostcompL
                (X := Fin (Module.finrank ℝ (TM x)) → ℝ)
                (t₀ := t₀) (T := T) (α := α)
                (tensorCoordinateCurryEquiv d).symm.toContinuousLinearMap).comp
              ((matrixZeroInitialOperator hT hα hα1).comp
                (frozenTensorHeatSourceToEuclideanL
                  (I := I) p x hxChart d hα.le))‖ ≤
            ‖FiniteParabolicC2AlphaBanach.fiberPostcompL
                (X := Fin (Module.finrank ℝ (TM x)) → ℝ)
                (t₀ := t₀) (T := T) (α := α)
                (tensorCoordinateCurryEquiv d).symm.toContinuousLinearMap‖ *
              (matrixZeroInitialSchauderConstant
                  (Module.finrank ℝ (TM x)) d t₀ T α *
                ‖frozenTensorHeatSourceToEuclideanL
                  (I := I) p x hxChart d hα.le‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left hmatrix (norm_nonneg _))
      exact mul_le_mul_of_nonneg_left hinner
        (norm_nonneg
          (FiniteParabolicC2AlphaBanach.spatialPullbackL
            (E := Fin d × Fin d → ℝ) (t₀ := t₀) (T := T) (α := α) hα.le
            (chartOrthonormalSpatialEquiv
              (I := I) p x hxChart).symm.toContinuousLinearMap))

/-- Closed-time value path for the frozen inverse.  This transports the
strong Euclidean zero trace through the spatial normalizing equivalence and
the tensor-coordinate equivalence. -/
def frozenTensorHeatZeroInitialValuePathIcc
    (p : M) (x : M) (hxChart : x ∈ (extChartAt I p).source)
    (d : ℕ) {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
      (Set.univ : Set (ℝ × E))) :
    BoundedContinuousFunction (↥(Set.Icc t₀ T))
      (BoundedContinuousFunction E (Fin d × Fin d → ℝ)) :=
  ((tensorCoordinateCurryEquiv d).symm.toContinuousLinearMap
      |>.compLeftContinuousBounded E |>.compLeftContinuousBounded
        (↥(Set.Icc t₀ T)))
    (((BoundedContinuousFunction.compContinuousCLM
        (Fin d → Fin d → ℝ) ℝ
        ({ toFun := fun y =>
              (chartOrthonormalSpatialEquiv
                (I := I) p x hxChart).symm y
           continuous_toFun :=
              (chartOrthonormalSpatialEquiv
                (I := I) p x hxChart).symm.continuous } :
          C(E, Fin (Module.finrank ℝ (TM x)) → ℝ)))
        |>.compLeftContinuousBounded (↥(Set.Icc t₀ T)))
      (matrixZeroInitialValuePathIcc hT hα
        (frozenTensorHeatSourceToEuclideanL
          (I := I) p x hxChart d hα.le q)))

@[simp]
theorem frozenTensorHeatZeroInitialValuePathIcc_initial
    (p : M) (x : M) (hxChart : x ∈ (extChartAt I p).source)
    (d : ℕ) {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
      (Set.univ : Set (ℝ × E))) :
    frozenTensorHeatZeroInitialValuePathIcc
        (I := I) p x hxChart d hT hα q ⟨t₀, le_rfl, hT.le⟩ = 0 := by
  ext y ij
  simp [frozenTensorHeatZeroInitialValuePathIcc,
    matrixZeroInitialValuePathIcc_initial hT hα]

/-- At every positive time, the closed-time frozen value path agrees with
the value component of the packaged `C^{2+α,1+α/2}` inverse. -/
theorem frozenTensorHeatZeroInitialValuePathIcc_eq_inverse
    (p : M) (x : M) (hxChart : x ∈ (extChartAt I p).source)
    (d : ℕ) {t₀ T α : ℝ}
    (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
      (Set.univ : Set (ℝ × E)))
    (t : ↥(Set.Ioc t₀ T)) (y : E) :
    frozenTensorHeatZeroInitialValuePathIcc
        (I := I) p x hxChart d hT hα q
        ⟨t, (Set.mem_Ioc.mp t.2).1.le, (Set.mem_Ioc.mp t.2).2⟩ y =
      FiniteParabolicC2AlphaBanach.value
        (frozenTensorHeatZeroInitialInverseL
          (I := I) p x hxChart d hT hα hα1 q) (t, y) := by
  simp only [frozenTensorHeatZeroInitialValuePathIcc,
    ContinuousLinearMap.compLeftContinuousBounded_apply,
    BoundedContinuousFunction.compContinuousCLM_apply,
    BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk]
  rw [value_frozenTensorHeatZeroInitialInverseL
    (I := I) p x hxChart d hT hα hα1 q
    (hz := by simpa [parabolicFiniteCylinder] using t.2)]
  rw [matrixZeroInitialValuePathIcc_eq_solution hT hα hα1
    (frozenTensorHeatSourceToEuclideanL
      (I := I) p x hxChart d hα.le q) t
    ((chartOrthonormalSpatialEquiv (I := I) p x hxChart).symm y)]
  rfl

/-- The source restriction appearing in the frozen right-inverse identity. -/
def restrictGlobalFrozenTensorSourceToFiniteL
    (d : ℕ) (t₀ T α : ℝ) :
    ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
        (Set.univ : Set (ℝ × E)) →L[ℝ]
      ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
        (parabolicFiniteCylinder E t₀ T) :=
  ParabolicC0AlphaBanach.restrictL (fun _ _ => Set.mem_univ _)

@[simp]
theorem timeDeriv_frozenTensorHeatZeroInitialInverseL
    (p : M) (x : M) (hxChart : x ∈ (extChartAt I p).source)
    (d : ℕ) {t₀ T α : ℝ}
    (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
      (Set.univ : Set (ℝ × E)))
    (z : ℝ × E) (hz : z ∈ parabolicFiniteCylinder E t₀ T) :
    FiniteParabolicC2AlphaBanach.timeDeriv
        (frozenTensorHeatZeroInitialInverseL
          (I := I) p x hxChart d hT hα hα1 q) z =
      (tensorCoordinateCurryEquiv d).symm
        (FiniteParabolicC2AlphaBanach.timeDeriv
          (matrixZeroInitialOperator
            (n := Module.finrank ℝ (TM x)) (d := d) hT hα hα1
            (frozenTensorHeatSourceToEuclideanL
              (I := I) p x hxChart d hα.le q))
          (parabolicSpatialLinearMapBetween
            (chartOrthonormalSpatialEquiv
              (I := I) p x hxChart).symm.toContinuousLinearMap z)) := by
  simpa only [frozenTensorHeatZeroInitialInverseL, ContinuousLinearMap.comp_apply] using!
    timeDeriv_spatialFiberPostcomp hα.le
      (chartOrthonormalSpatialEquiv (I := I) p x hxChart).symm.toContinuousLinearMap
      (tensorCoordinateCurryEquiv d).symm.toContinuousLinearMap
      (matrixZeroInitialOperator
        (n := Module.finrank ℝ (TM x)) (d := d) hT hα hα1
        (frozenTensorHeatSourceToEuclideanL (I := I) p x hxChart d hα.le q)) z hz

@[simp]
theorem spaceSecondDeriv_frozenTensorHeatZeroInitialInverseL_apply
    (p : M) (x : M) (hxChart : x ∈ (extChartAt I p).source)
    (d : ℕ) {t₀ T α : ℝ}
    (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
      (Set.univ : Set (ℝ × E)))
    (z : ℝ × E) (hz : z ∈ parabolicFiniteCylinder E t₀ T)
    (v w : E) :
    FiniteParabolicC2AlphaBanach.spaceSecondDeriv
        (frozenTensorHeatZeroInitialInverseL
          (I := I) p x hxChart d hT hα hα1 q) z v w =
      (tensorCoordinateCurryEquiv d).symm
        (FiniteParabolicC2AlphaBanach.spaceSecondDeriv
          (matrixZeroInitialOperator
            (n := Module.finrank ℝ (TM x)) (d := d) hT hα hα1
            (frozenTensorHeatSourceToEuclideanL
              (I := I) p x hxChart d hα.le q))
          (parabolicSpatialLinearMapBetween
            (chartOrthonormalSpatialEquiv
              (I := I) p x hxChart).symm.toContinuousLinearMap z)
          ((chartOrthonormalSpatialEquiv
            (I := I) p x hxChart).symm v)
          ((chartOrthonormalSpatialEquiv
            (I := I) p x hxChart).symm w)) := by
  simpa only [frozenTensorHeatZeroInitialInverseL, ContinuousLinearMap.comp_apply] using!
    spaceSecondDeriv_spatialFiberPostcomp hα.le
      (chartOrthonormalSpatialEquiv (I := I) p x hxChart).symm.toContinuousLinearMap
      (tensorCoordinateCurryEquiv d).symm.toContinuousLinearMap
      (matrixZeroInitialOperator
        (n := Module.finrank ℝ (TM x)) (d := d) hT hα hα1
        (frozenTensorHeatSourceToEuclideanL (I := I) p x hxChart d hα.le q)) z hz v w

/-- **Frozen Schauder right inverse for the actual tensor-heat symbol.**
The conjugated Duhamel operator is a bounded right inverse of
`∂ₜ - AₓD²`; the only map on the right is restriction of the global source
to the positive finite cylinder. -/
private theorem frozenTensorHeatCauchyL_zeroInitialInverseL_eval
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α Set.univ)
    (z : ℝ × E) (hz : z ∈ parabolicFiniteCylinder E t₀ T) :
    ParabolicC0AlphaBanach.evalCLM z hz
        (frozenTensorHeatCauchyL (I := I) p e b x t₀ T α
          (frozenTensorHeatZeroInitialInverseL (I := I) p x hxChart d hT hα hα1 q)) =
      ParabolicC0AlphaBanach.evalCLM z hz
        (restrictGlobalFrozenTensorSourceToFiniteL (E := E) d t₀ T α q) := by
  let n := Module.finrank ℝ (TM x)
  let N := chartOrthonormalSpatialEquiv (I := I) p x hxChart
  let C := tensorCoordinateCurryEquiv d
  let q' := frozenTensorHeatSourceToEuclideanL
    (I := I) p x hxChart d hα.le q
  let v := matrixZeroInitialOperator (n := n) (d := d) hT hα hα1 q'
  have hr : parabolicSpatialLinearMapBetween N.symm.toContinuousLinearMap z ∈
      parabolicFiniteCylinder (Fin n → ℝ) t₀ T :=
    parabolicSpatialLinearMapBetween_mapsTo
      N.symm.toContinuousLinearMap t₀ T hz
  have ht : z.1 ∈ Set.Ioc t₀ T := by
    simpa [parabolicFiniteCylinder] using hz
  rw [evalCLM_frozenTensorHeatCauchyL]
  rw [timeDeriv_frozenTensorHeatZeroInitialInverseL
    (I := I) p x hxChart d hT hα hα1 q z hz]
  have hD2 :
      FiniteParabolicC2AlphaBanach.spaceSecondDeriv
          (frozenTensorHeatZeroInitialInverseL
            (I := I) p x hxChart d hT hα hα1 q) z =
        pullbackSecondDerivativeL N.symm.toContinuousLinearMap
          (postcomposeSecondDerivativeL C.symm.toContinuousLinearMap
            (FiniteParabolicC2AlphaBanach.spaceSecondDeriv v
              (parabolicSpatialLinearMapBetween
                N.symm.toContinuousLinearMap z))) := by
    simpa only [frozenTensorHeatZeroInitialInverseL, ContinuousLinearMap.comp_apply,
      N, C, v, n, q'] using!
      spaceSecondDeriv_spatialFiberPostcomp_clm hα.le
        N.symm.toContinuousLinearMap C.symm.toContinuousLinearMap v z hz
  rw [hD2]
  rw [frozenPrincipalCoefficient_pullback_eq_euclideanTrace
    (I := I) p e b hxFrame hxChart]
  have htrace := euclideanTrace_postcompose n C.symm.toContinuousLinearMap
    (FiniteParabolicC2AlphaBanach.spaceSecondDeriv v
      (parabolicSpatialLinearMapBetween N.symm.toContinuousLinearMap z))
  rw [htrace]
  have hcauchy := matrixZeroInitialOperator_cauchy hT hα hα1 q'
    (parabolicSpatialLinearMapBetween N.symm.toContinuousLinearMap z) hr
  calc
    C.symm
          (FiniteParabolicC2AlphaBanach.timeDeriv v
            (parabolicSpatialLinearMapBetween N.symm.toContinuousLinearMap z)) -
        C.symm
          (∑ k : Fin n,
            FiniteParabolicC2AlphaBanach.spaceSecondDeriv v
              (parabolicSpatialLinearMapBetween N.symm.toContinuousLinearMap z)
              (Pi.single k 1) (Pi.single k 1)) =
        C.symm
          (FiniteParabolicC2AlphaBanach.timeDeriv v
              (parabolicSpatialLinearMapBetween N.symm.toContinuousLinearMap z) -
            ∑ k : Fin n,
              FiniteParabolicC2AlphaBanach.spaceSecondDeriv v
                (parabolicSpatialLinearMapBetween N.symm.toContinuousLinearMap z)
                (Pi.single k 1) (Pi.single k 1)) := by
          rw [map_sub]
    _ = C.symm
          (ParabolicC0AlphaBanach.evalCLM
            (parabolicSpatialLinearMapBetween N.symm.toContinuousLinearMap z)
            (Set.mem_univ _) q') := by rw [hcauchy]
    _ = ParabolicC0AlphaBanach.evalCLM z (Set.mem_univ z) q := by
      rw [evalCLM_frozenTensorHeatSourceToEuclideanL
        (I := I) p x hxChart d hα.le q]
      simp [q', C, N, parabolicSpatialLinearMapBetween]
    _ = ParabolicC0AlphaBanach.evalCLM z hz
          (restrictGlobalFrozenTensorSourceToFiniteL
            (E := E) d t₀ T α q) := by
      unfold restrictGlobalFrozenTensorSourceToFiniteL
      rw [ParabolicC0AlphaBanach.evalCLM_restrictL_apply
        (Set.subset_univ _) z hz q]


theorem frozenTensorHeatCauchyL_comp_zeroInitialInverseL
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    (frozenTensorHeatCauchyL (I := I) p e b x t₀ T α).comp
        (frozenTensorHeatZeroInitialInverseL
          (I := I) p x hxChart d hT hα hα1) =
      restrictGlobalFrozenTensorSourceToFiniteL
        (E := E) d t₀ T α := by
  ext q
  apply (ParabolicC0AlphaBanach.eq_iff_forall_evalCLM _ _).2
  intro z hz
  exact frozenTensorHeatCauchyL_zeroInitialInverseL_eval
    p e b hxFrame hxChart hT hα hα1 q z hz

/-! ## Finite-cylinder source inverse -/

/-- The genuine frozen tensor-heat inverse on its natural finite-cylinder
source space.  The source is first extended by the exact bounded extension,
then solved by the global-source Duhamel construction. -/
def frozenTensorHeatFiniteZeroInitialInverseL
    (p : M) (x : M) (hxChart : x ∈ (extChartAt I p).source)
    (d : ℕ) {t₀ T α : ℝ}
    (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α :=
  (frozenTensorHeatZeroInitialInverseL
      (I := I) p x hxChart d hT hα hα1).comp
    (ParabolicC0AlphaBanach.finiteSourceExtensionL hT hα)

/-- The finite-cylinder inverse has the frozen Schauder bound with only the
universal extension factor three added. -/
theorem norm_frozenTensorHeatFiniteZeroInitialInverseL_le
    (p : M) (x : M) (hxChart : x ∈ (extChartAt I p).source)
    (d : ℕ) {t₀ T α : ℝ}
    (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    ‖frozenTensorHeatFiniteZeroInitialInverseL
        (I := I) p x hxChart d hT hα hα1‖ ≤
      ‖frozenTensorHeatZeroInitialInverseL
        (I := I) p x hxChart d hT hα hα1‖ * 3 := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left
      (ParabolicC0AlphaBanach.norm_finiteSourceExtensionL_le hT hα)
      (norm_nonneg _))

/-- **Exact finite-cylinder frozen right inverse.**  No global-source
hypothesis remains: every finite parabolic Hölder source is solved exactly. -/
theorem frozenTensorHeatCauchyL_comp_finiteZeroInitialInverseL
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1) :
    (frozenTensorHeatCauchyL (I := I) p e b x t₀ T α).comp
        (frozenTensorHeatFiniteZeroInitialInverseL
          (I := I) p x hxChart d hT hα hα1) =
      ContinuousLinearMap.id ℝ
        (ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
          (parabolicFiniteCylinder E t₀ T)) := by
  rw [frozenTensorHeatFiniteZeroInitialInverseL,
    ← ContinuousLinearMap.comp_assoc,
    frozenTensorHeatCauchyL_comp_zeroInitialInverseL
      (I := I) p e b hxFrame hxChart hT hα hα1]
  exact ParabolicC0AlphaBanach.restrictL_comp_finiteSourceExtensionL hT hα

/-- Closed-time value path for the finite-cylinder frozen inverse. -/
def frozenTensorHeatFiniteZeroInitialValuePathIcc
    (p : M) (x : M) (hxChart : x ∈ (extChartAt I p).source)
    (d : ℕ) {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
      (parabolicFiniteCylinder E t₀ T)) :
    BoundedContinuousFunction (↥(Set.Icc t₀ T))
      (BoundedContinuousFunction E (Fin d × Fin d → ℝ)) :=
  frozenTensorHeatZeroInitialValuePathIcc
    (I := I) p x hxChart d hT hα
      (ParabolicC0AlphaBanach.finiteSourceExtensionL hT hα q)

@[simp]
theorem frozenTensorHeatFiniteZeroInitialValuePathIcc_initial
    (p : M) (x : M) (hxChart : x ∈ (extChartAt I p).source)
    (d : ℕ) {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α)
    (q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
      (parabolicFiniteCylinder E t₀ T)) :
    frozenTensorHeatFiniteZeroInitialValuePathIcc
        (I := I) p x hxChart d hT hα q ⟨t₀, le_rfl, hT.le⟩ = 0 := by
  exact frozenTensorHeatZeroInitialValuePathIcc_initial
    (I := I) p x hxChart d hT hα
      (ParabolicC0AlphaBanach.finiteSourceExtensionL hT hα q)

/-- At positive times the finite closed-time path is the value component of
the finite-cylinder inverse. -/
theorem frozenTensorHeatFiniteZeroInitialValuePathIcc_eq_inverse
    (p : M) (x : M) (hxChart : x ∈ (extChartAt I p).source)
    (d : ℕ) {t₀ T α : ℝ}
    (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
      (parabolicFiniteCylinder E t₀ T))
    (t : ↥(Set.Ioc t₀ T)) (y : E) :
    frozenTensorHeatFiniteZeroInitialValuePathIcc
        (I := I) p x hxChart d hT hα q
        ⟨t, (Set.mem_Ioc.mp t.2).1.le, (Set.mem_Ioc.mp t.2).2⟩ y =
      FiniteParabolicC2AlphaBanach.value
        (frozenTensorHeatFiniteZeroInitialInverseL
          (I := I) p x hxChart d hT hα hα1 q) (t, y) := by
  exact frozenTensorHeatZeroInitialValuePathIcc_eq_inverse
    (I := I) p x hxChart d hT hα hα1
      (ParabolicC0AlphaBanach.finiteSourceExtensionL hT hα q) t y

end AnalyticPDE
end RicciFlow
