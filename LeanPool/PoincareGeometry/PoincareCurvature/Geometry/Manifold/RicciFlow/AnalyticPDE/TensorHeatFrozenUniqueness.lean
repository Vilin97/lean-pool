/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatUniqueness
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatFrozenInverse
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatLocalInverse
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatCoordinatePerturbation
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatLocalizedInverse
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ZeroInitialTrace

/-!
# Uniqueness for the frozen tensor heat equation

The frozen tensor heat operator is conjugate to the coefficientwise
Euclidean heat operator.  This file transports the genuine bounded-classical
Euclidean uniqueness theorem through the spatial and fibre equivalences.
-/

@[expose] public section

@[expose] public noncomputable section
open Bundle FiberBundle TensorProduct
open scoped Manifold ContDiff BigOperators

namespace RicciFlow
namespace AnalyticPDE

variable {X Y E F : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-! ## Initial traces commute with bounded linear coordinate changes -/

theorem FiniteParabolicC2AlphaBanach.initialTraceL_fiberPostcompL
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α)
    (B : E →L[ℝ] F)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) :
    FiniteParabolicC2AlphaBanach.initialTraceL hT hα
        (FiniteParabolicC2AlphaBanach.fiberPostcompL B u) =
      B.compLeftContinuousBounded X
        (FiniteParabolicC2AlphaBanach.initialTraceL hT hα u) := by
  apply BoundedContinuousFunction.ext
  intro x
  change ParabolicC0AlphaBanach.finiteInitialTrace hT hα
      (FiniteParabolicC2AlphaBanach.valueComponentL
        (FiniteParabolicC2AlphaBanach.fiberPostcompL B u)) x = _
  let g : ↥(Set.Icc t₀ T) → BoundedContinuousFunction X F := fun t =>
    B.compLeftContinuousBounded X
      (ParabolicC0AlphaBanach.finiteClosedTimeSlice hT hα
        (FiniteParabolicC2AlphaBanach.valueComponentL u) t)
  rw [ParabolicC0AlphaBanach.finiteInitialTrace_eq_of_continuous
    hT hα _ g]
  · rfl
  · exact (B.compLeftContinuousBounded X).continuous.comp
      (ParabolicC0AlphaBanach.continuous_finiteClosedTimeSlice hT hα _)
  · intro t
    apply BoundedContinuousFunction.ext
    intro y
    simp only [g, ContinuousLinearMap.compLeftContinuousBounded_apply]
    rw [ParabolicC0AlphaBanach.finiteClosedTimeSlice_apply_positive]
    rw [ParabolicC0AlphaBanach.finiteTimeSlice_apply]
    rw [ParabolicC0AlphaBanach.finiteTimeSlice_apply]
    let hy := ParabolicC0AlphaBanach.positiveTimeInIcc_mem_parabolicFiniteCylinder t y
    rw [FiniteParabolicC2AlphaBanach.evalCLM_valueComponentL u _ hy]
    rw [FiniteParabolicC2AlphaBanach.evalCLM_valueComponentL
      (FiniteParabolicC2AlphaBanach.fiberPostcompL B u) _ hy]
    exact (FiniteParabolicC2AlphaBanach.value_fiberPostcompL B u _ hy).symm

theorem FiniteParabolicC2AlphaBanach.initialTraceL_spatialPullbackL
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α)
    (L : Y →L[ℝ] X)
    (u : FiniteParabolicC2AlphaBanach X E t₀ T α) :
    FiniteParabolicC2AlphaBanach.initialTraceL hT hα
        (FiniteParabolicC2AlphaBanach.spatialPullbackL hα.le L u) =
      BoundedContinuousFunction.compContinuousCLM E ℝ
        ({ toFun := L
           continuous_toFun := L.continuous } : C(Y, X))
        (FiniteParabolicC2AlphaBanach.initialTraceL hT hα u) := by
  apply BoundedContinuousFunction.ext
  intro y
  change ParabolicC0AlphaBanach.finiteInitialTrace hT hα
      (FiniteParabolicC2AlphaBanach.valueComponentL
        (FiniteParabolicC2AlphaBanach.spatialPullbackL hα.le L u)) y = _
  let g : ↥(Set.Icc t₀ T) → BoundedContinuousFunction Y E := fun t =>
    BoundedContinuousFunction.compContinuousCLM E ℝ
      ({ toFun := L
         continuous_toFun := L.continuous } : C(Y, X))
      (ParabolicC0AlphaBanach.finiteClosedTimeSlice hT hα
        (FiniteParabolicC2AlphaBanach.valueComponentL u) t)
  rw [ParabolicC0AlphaBanach.finiteInitialTrace_eq_of_continuous
    hT hα _ g]
  · rfl
  · exact (BoundedContinuousFunction.compContinuousCLM E ℝ
        ({ toFun := L
           continuous_toFun := L.continuous } : C(Y, X))).continuous.comp
      (ParabolicC0AlphaBanach.continuous_finiteClosedTimeSlice hT hα _)
  · intro t
    apply BoundedContinuousFunction.ext
    intro z
    simp only [g, BoundedContinuousFunction.compContinuousCLM_apply,
      BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk]
    rw [ParabolicC0AlphaBanach.finiteClosedTimeSlice_apply_positive]
    rw [ParabolicC0AlphaBanach.finiteTimeSlice_apply]
    rw [ParabolicC0AlphaBanach.finiteTimeSlice_apply]
    let hz := ParabolicC0AlphaBanach.positiveTimeInIcc_mem_parabolicFiniteCylinder t z
    let hLz := ParabolicC0AlphaBanach.positiveTimeInIcc_mem_parabolicFiniteCylinder t (L z)
    rw [FiniteParabolicC2AlphaBanach.evalCLM_valueComponentL u _ hLz]
    rw [FiniteParabolicC2AlphaBanach.evalCLM_valueComponentL
      (FiniteParabolicC2AlphaBanach.spatialPullbackL hα.le L u) _ hz]
    exact (FiniteParabolicC2AlphaBanach.value_spatialPullbackL hα.le L u _ hz).symm

/-! ## Coefficientwise matrix uniqueness -/

theorem eq_zero_of_euclideanMatrixHeatCauchy_eq_zero_of_initialTrace_eq_zero
    {n d : ℕ} {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach (Fin n → ℝ)
      (Fin d → Fin d → ℝ) t₀ T α)
    (hu : euclideanMatrixHeatCauchyL n d t₀ T α u = 0)
    (hu0 : FiniteParabolicC2AlphaBanach.initialTraceL hT hα u = 0) :
    u = 0 := by
  apply FiniteParabolicC2AlphaBanach.ext_value hα hT
  intro z hz
  funext i j
  let uij := FiniteParabolicC2AlphaBanach.fiberPostcompL
    (matrixEntryCLM d i j) u
  have hijP : euclideanHeatCauchyL n t₀ T α uij = 0 := by
    apply (ParabolicC0AlphaBanach.eq_iff_forall_evalCLM _ _).2
    intro y hy
    have hmatrix := congrArg
      (fun q : ParabolicC0AlphaBanach (Fin n → ℝ)
          (Fin d → Fin d → ℝ) α
          (parabolicFiniteCylinder (Fin n → ℝ) t₀ T) =>
        ParabolicC0AlphaBanach.evalCLM y hy q i j) hu
    simp only [map_zero] at hmatrix
    rw [evalCLM_euclideanMatrixHeatCauchyL] at hmatrix
    have hmatrix' :
        FiniteParabolicC2AlphaBanach.timeDeriv u y i j -
          (∑ k : Fin n, FiniteParabolicC2AlphaBanach.spaceSecondDeriv u y
            (Pi.single k 1) (Pi.single k 1)) i j = 0 := by
      simpa using hmatrix
    rw [evalCLM_euclideanHeatCauchyL]
    rw [FiniteParabolicC2AlphaBanach.timeDeriv_fiberPostcompL
        (z := y) (hz := hy),
      FiniteParabolicC2AlphaBanach.spaceSecondDeriv_fiberPostcompL
        (z := y) (hz := hy)]
    simpa [uij, matrixEntryCLM_apply, map_sum] using hmatrix'
  have hij0 : FiniteParabolicC2AlphaBanach.initialTraceL hT hα uij = 0 := by
    rw [FiniteParabolicC2AlphaBanach.initialTraceL_fiberPostcompL]
    rw [hu0, map_zero]
  have hij := eq_zero_of_euclideanHeatCauchy_eq_zero_of_initialTrace_eq_zero
    hT hα uij hijP hij0
  have hv := congrArg (fun v => FiniteParabolicC2AlphaBanach.value v z) hij
  have hv' : FiniteParabolicC2AlphaBanach.value uij z = 0 := by
    simpa using hv
  dsimp [uij] at hv'
  rw [FiniteParabolicC2AlphaBanach.value_fiberPostcompL _ _ _ hz] at hv'
  simpa [matrixEntryCLM_apply] using hv'

/-! ## Frozen tensor heat uniqueness -/

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

@[reducible] local instance frozenUniquenessFirstNormedAddCommGroup {d : ℕ} :
    NormedAddCommGroup (E →L[ℝ] (Fin d × Fin d → ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance frozenUniquenessFirstNormedSpace {d : ℕ} :
    NormedSpace ℝ (E →L[ℝ] (Fin d × Fin d → ℝ)) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance frozenUniquenessSecondNormedAddCommGroup {d : ℕ} :
    NormedAddCommGroup
      (E →L[ℝ] E →L[ℝ] (Fin d × Fin d → ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance frozenUniquenessSecondNormedSpace {d : ℕ} :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] (Fin d × Fin d → ℝ)) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance frozenUniquenessPrincipalNormedAddCommGroup {d : ℕ} :
    NormedAddCommGroup
      ((E →L[ℝ] E →L[ℝ] (Fin d × Fin d → ℝ)) →L[ℝ]
        (Fin d × Fin d → ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance frozenUniquenessPrincipalNormedSpace {d : ℕ} :
    NormedSpace ℝ
      ((E →L[ℝ] E →L[ℝ] (Fin d × Fin d → ℝ)) →L[ℝ]
        (Fin d × Fin d → ℝ)) :=
  ContinuousLinearMap.toNormedSpace
@[reducible] local instance frozenUniquenessFirstCoeffNormedAddCommGroup {d : ℕ} :
    NormedAddCommGroup
      ((E →L[ℝ] (Fin d × Fin d → ℝ)) →L[ℝ]
        (Fin d × Fin d → ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup
@[reducible] local instance frozenUniquenessFirstCoeffNormedSpace {d : ℕ} :
    NormedSpace ℝ
      ((E →L[ℝ] (Fin d × Fin d → ℝ)) →L[ℝ]
        (Fin d × Fin d → ℝ)) :=
  ContinuousLinearMap.toNormedSpace

/-- Pull an arbitrary frozen-coordinate tensor jet into orthonormal spatial
coordinates and curry its tensor indices. -/
def frozenTensorHeatToEuclideanL
    (p : M) (x : M) (hxChart : x ∈ (extChartAt I p).source)
    (d : ℕ) {t₀ T α : ℝ} (hα0 : 0 ≤ α) :
    FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α →L[ℝ]
      FiniteParabolicC2AlphaBanach
        (Fin (Module.finrank ℝ (TM x)) → ℝ)
        (Fin d → Fin d → ℝ) t₀ T α :=
  (FiniteParabolicC2AlphaBanach.fiberPostcompL
      (X := Fin (Module.finrank ℝ (TM x)) → ℝ)
      (tensorCoordinateCurryEquiv d).toContinuousLinearMap).comp
    (FiniteParabolicC2AlphaBanach.spatialPullbackL hα0
      (chartOrthonormalSpatialEquiv
        (I := I) p x hxChart).toContinuousLinearMap)

/-- The reverse frozen-coordinate transform conjugates the actual frozen
tensor heat Cauchy operator to the coefficientwise Euclidean one. -/
theorem euclideanMatrixHeatCauchyL_frozenTensorHeatToEuclideanL_eq_zero
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {t₀ T α : ℝ} (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α)
    (hu : frozenTensorHeatCauchyL (I := I) p e b x t₀ T α u = 0) :
    euclideanMatrixHeatCauchyL (Module.finrank ℝ (TM x)) d t₀ T α
        (frozenTensorHeatToEuclideanL
          (I := I) p x hxChart d hα.le u) = 0 := by
  apply (ParabolicC0AlphaBanach.eq_iff_forall_evalCLM _ _).2
  intro z hz
  let N := chartOrthonormalSpatialEquiv (I := I) p x hxChart
  let C := tensorCoordinateCurryEquiv d
  let y : ℝ × E := parabolicSpatialLinearMapBetween
    N.toContinuousLinearMap z
  have hy : y ∈ parabolicFiniteCylinder E t₀ T :=
    parabolicSpatialLinearMapBetween_mapsTo N.toContinuousLinearMap t₀ T hz
  have hphysical := congrArg
    (fun q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
        (parabolicFiniteCylinder E t₀ T) =>
      ParabolicC0AlphaBanach.evalCLM y hy q) hu
  simp only [map_zero] at hphysical
  rw [evalCLM_frozenTensorHeatCauchyL] at hphysical
  rw [evalCLM_euclideanMatrixHeatCauchyL]
  rw [frozenTensorHeatToEuclideanL, ContinuousLinearMap.comp_apply]
  rw [FiniteParabolicC2AlphaBanach.timeDeriv_fiberPostcompL
      (z := z) (hz := hz),
    FiniteParabolicC2AlphaBanach.timeDeriv_spatialPullbackL
      (z := z) (hz := hz),
    FiniteParabolicC2AlphaBanach.spaceSecondDeriv_fiberPostcompL
      (z := z) (hz := hz),
    FiniteParabolicC2AlphaBanach.spaceSecondDeriv_spatialPullbackL
      (z := z) (hz := hz)]
  have htrace := localTensorHeatPrincipalCoefficient_eq_orthonormalTrace
    (I := I) p e b hxFrame hxChart
      (stdOrthonormalBasis ℝ (TM x))
      (FiniteParabolicC2AlphaBanach.spaceSecondDeriv u y)
  change C (FiniteParabolicC2AlphaBanach.timeDeriv u y) -
      (∑ k : Fin (Module.finrank ℝ (TM x)),
        C (FiniteParabolicC2AlphaBanach.spaceSecondDeriv u y
          (N (Pi.single k 1)) (N (Pi.single k 1)))) = 0
  rw [← map_sum]
  dsimp only [N]
  simp_rw [chartOrthonormalSpatialEquiv_single (I := I) p x hxChart]
  rw [← htrace]
  rw [← map_sub]
  have hphysical' : FiniteParabolicC2AlphaBanach.timeDeriv u y -
      localTensorHeatPrincipalCoefficient (I := I) p e b ((extChartAt I p) x)
        (FiniteParabolicC2AlphaBanach.spaceSecondDeriv u y) = 0 := by
    simpa [frozenLocalTensorHeatPrincipalCoefficient] using hphysical
  rw [hphysical']
  simp

/-- **Genuine frozen tensor heat uniqueness.** A bounded classical frozen
solution with zero Cauchy operator and zero initial trace is the zero jet. -/
theorem eq_zero_of_frozenTensorHeatCauchy_eq_zero_of_initialTrace_eq_zero
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α)
    (u : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α)
    (hu : frozenTensorHeatCauchyL (I := I) p e b x t₀ T α u = 0)
    (hu0 : FiniteParabolicC2AlphaBanach.initialTraceL hT hα u = 0) :
    u = 0 := by
  let N := chartOrthonormalSpatialEquiv (I := I) p x hxChart
  let C := tensorCoordinateCurryEquiv d
  let v := frozenTensorHeatToEuclideanL
    (I := I) p x hxChart d hα.le u
  have hvP : euclideanMatrixHeatCauchyL
      (Module.finrank ℝ (TM x)) d t₀ T α v = 0 :=
    euclideanMatrixHeatCauchyL_frozenTensorHeatToEuclideanL_eq_zero
      (I := I) p e b hxFrame hxChart hα u hu
  have hv0 : FiniteParabolicC2AlphaBanach.initialTraceL hT hα v = 0 := by
    dsimp only [v, frozenTensorHeatToEuclideanL]
    rw [ContinuousLinearMap.comp_apply]
    rw [FiniteParabolicC2AlphaBanach.initialTraceL_fiberPostcompL]
    rw [FiniteParabolicC2AlphaBanach.initialTraceL_spatialPullbackL]
    rw [hu0, map_zero, map_zero]
  have hv :=
    eq_zero_of_euclideanMatrixHeatCauchy_eq_zero_of_initialTrace_eq_zero
      hT hα v hvP hv0
  apply FiniteParabolicC2AlphaBanach.ext_value hα hT
  rintro ⟨t, y⟩ hy
  let z : ℝ × (Fin (Module.finrank ℝ (TM x)) → ℝ) := (t, N.symm y)
  have hz : z ∈ parabolicFiniteCylinder
      (Fin (Module.finrank ℝ (TM x)) → ℝ) t₀ T := by
    simpa [z, parabolicFiniteCylinder] using hy
  have hvz := congrArg (fun w => FiniteParabolicC2AlphaBanach.value w z) hv
  have hvz0 : FiniteParabolicC2AlphaBanach.value v z = 0 := by
    simpa using hvz
  dsimp only [v, frozenTensorHeatToEuclideanL] at hvz0
  rw [ContinuousLinearMap.comp_apply,
    FiniteParabolicC2AlphaBanach.value_fiberPostcompL _ _ _ hz,
    FiniteParabolicC2AlphaBanach.value_spatialPullbackL _ _ _ _ hz] at hvz0
  change C (FiniteParabolicC2AlphaBanach.value u
    (t, N (N.symm y))) = 0 at hvz0
  rw [N.apply_symm_apply] at hvz0
  exact C.injective (by simpa using hvz0)

/-! ## Injectivity is stable under the existing post-error contraction -/

@[simp]
theorem initialTraceL_frozenTensorHeatFiniteZeroInitialInverseL
    (p : M) (x : M) (hxChart : x ∈ (extChartAt I p).source)
    (d : ℕ) {t₀ T α : ℝ}
    (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
      (parabolicFiniteCylinder E t₀ T)) :
    FiniteParabolicC2AlphaBanach.initialTraceL hT hα
      (frozenTensorHeatFiniteZeroInitialInverseL
        (I := I) p x hxChart d hT hα hα1 q) = 0 := by
  unfold frozenTensorHeatFiniteZeroInitialInverseL
    frozenTensorHeatZeroInitialInverseL
  simp only [ContinuousLinearMap.comp_apply]
  rw [FiniteParabolicC2AlphaBanach.initialTraceL_spatialPullbackL]
  rw [FiniteParabolicC2AlphaBanach.initialTraceL_fiberPostcompL]
  rw [matrixZeroInitialOperator_apply]
  rw [initialTraceL_matrixZeroInitialSolution]
  simp

/-- A strict post-frozen error bound makes a variable operator injective on
the zero-initial-trace subspace.  The proof first represents a candidate by
the frozen inverse using frozen uniqueness, then applies the already available
post-error contraction to its frozen source. -/
theorem eq_zero_of_postFrozenError_norm_lt_one
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α)
    (P : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α →L[ℝ]
      ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
        (parabolicFiniteCylinder E t₀ T))
    (Q : ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
        (parabolicFiniteCylinder E t₀ T) →L[ℝ]
      FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α)
    (hright : (frozenTensorHeatCauchyL
      (I := I) p e b x t₀ T α).comp Q = ContinuousLinearMap.id ℝ _)
    (hQ0 : (FiniteParabolicC2AlphaBanach.initialTraceL
      (X := E) (E := Fin d × Fin d → ℝ) hT hα).comp Q = 0)
    (hsmall : ‖(P - frozenTensorHeatCauchyL
      (I := I) p e b x t₀ T α).comp Q‖ < 1)
    (u : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α)
    (hu : P u = 0)
    (hu0 : FiniteParabolicC2AlphaBanach.initialTraceL hT hα u = 0) :
    u = 0 := by
  let P₀ := frozenTensorHeatCauchyL (I := I) p e b x t₀ T α
  let q := P₀ u
  have hP₀Q : P₀ (Q q) = q := by
    have hrightq := congrArg (fun L => L q) hright
    simpa [P₀] using hrightq
  have hQq0 : FiniteParabolicC2AlphaBanach.initialTraceL hT hα (Q q) = 0 := by
    have htraceq := congrArg (fun L => L q) hQ0
    simpa using htraceq
  have hdiffP : P₀ (u - Q q) = 0 := by
    rw [map_sub, hP₀Q]
    exact sub_self q
  have hdiff0 :
      FiniteParabolicC2AlphaBanach.initialTraceL hT hα (u - Q q) = 0 := by
    rw [map_sub, hu0, hQq0, sub_zero]
  have hdiff :=
    eq_zero_of_frozenTensorHeatCauchy_eq_zero_of_initialTrace_eq_zero
      (I := I) p e b hxFrame hxChart hT hα (u - Q q) hdiffP hdiff0
  have huQ : u = Q q := sub_eq_zero.mp hdiff
  let R := (P - P₀).comp Q
  have hRq : R q = -q := by
    dsimp only [R]
    rw [ContinuousLinearMap.comp_apply]
    rw [← huQ]
    rw [sub_apply, hu]
    change 0 - q = -q
    exact zero_sub q
  have hq0 : q = 0 := by
    by_contra hq
    have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hq
    have hle : ‖R q‖ ≤ ‖R‖ * ‖q‖ := R.le_opNorm q
    have hlt : ‖R‖ * ‖q‖ < 1 * ‖q‖ := by
      exact mul_lt_mul_of_pos_right (by simpa [R, P₀] using hsmall) hqpos
    have : ‖q‖ < ‖q‖ := by
      calc
        ‖q‖ = ‖R q‖ := by rw [hRq, norm_neg]
        _ ≤ ‖R‖ * ‖q‖ := hle
        _ < 1 * ‖q‖ := hlt
        _ = ‖q‖ := one_mul _
    exact lt_irrefl _ this
  rw [huQ, hq0, map_zero]

theorem eq_zero_of_frozenTensorHeatPerturbation_norm_lt_one
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (P : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α →L[ℝ]
      ParabolicC0AlphaBanach E (Fin d × Fin d → ℝ) α
        (parabolicFiniteCylinder E t₀ T))
    (hsmall : ‖frozenTensorHeatPerturbationL
      (I := I) p e b x hxChart hT hα hα1 P‖ < 1)
    (u : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α)
    (hu : P u = 0)
    (hu0 : FiniteParabolicC2AlphaBanach.initialTraceL hT hα u = 0) :
    u = 0 := by
  let P₀ := frozenTensorHeatCauchyL (I := I) p e b x t₀ T α
  let Q := frozenTensorHeatFiniteZeroInitialInverseL
    (I := I) p x hxChart d hT hα hα1
  let q := P₀ u
  have hP₀Q : P₀ (Q q) = q := by
    have hright := congrArg (fun L => L q)
      (frozenTensorHeatCauchyL_comp_finiteZeroInitialInverseL
        (I := I) p e b hxFrame hxChart hT hα hα1)
    simpa [P₀, Q] using hright
  have hQ0 : FiniteParabolicC2AlphaBanach.initialTraceL hT hα (Q q) = 0 := by
    exact initialTraceL_frozenTensorHeatFiniteZeroInitialInverseL
      (I := I) p x hxChart d hT hα hα1 q
  have hdiffP : P₀ (u - Q q) = 0 := by
    rw [map_sub, hP₀Q]
    exact sub_self q
  have hdiff0 :
      FiniteParabolicC2AlphaBanach.initialTraceL hT hα (u - Q q) = 0 := by
    rw [map_sub, hu0, hQ0, sub_zero]
  have hdiff :=
    eq_zero_of_frozenTensorHeatCauchy_eq_zero_of_initialTrace_eq_zero
      (I := I) p e b hxFrame hxChart hT hα (u - Q q) hdiffP hdiff0
  have huQ : u = Q q := sub_eq_zero.mp hdiff
  let R := frozenTensorHeatPerturbationL
    (I := I) p e b x hxChart hT hα hα1 P
  have hRq : R q = -q := by
    dsimp only [R, frozenTensorHeatPerturbationL]
    rw [ContinuousLinearMap.comp_apply]
    change (P - P₀) (Q q) = -q
    rw [← huQ]
    rw [sub_apply, hu]
    change 0 - q = -q
    exact zero_sub q
  have hq0 : q = 0 := by
    by_contra hq
    have hqpos : 0 < ‖q‖ := (norm_pos_iff.mpr hq)
    have hle : ‖R q‖ ≤ ‖R‖ * ‖q‖ := R.le_opNorm q
    have hlt : ‖R‖ * ‖q‖ < 1 * ‖q‖ :=
      mul_lt_mul_of_pos_right hsmall hqpos
    have : ‖q‖ < ‖q‖ := by
      calc
        ‖q‖ = ‖R q‖ := by rw [hRq, norm_neg]
        _ ≤ ‖R‖ * ‖q‖ := hle
        _ < 1 * ‖q‖ := hlt
        _ = ‖q‖ := one_mul _
    exact (lt_irrefl _ this)
  rw [huQ, hq0, map_zero]

/-- Coordinate-form specialization: a post-error bound below one gives
uniqueness for the full principal/first/zero-order Cauchy operator. -/
theorem eq_zero_of_coordinateCauchy_eq_zero_of_initialTrace_eq_zero
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (A : FiniteParabolicC2AlphaBanach.PrincipalCoefficientSpace
      (X := E) (E := Fin d × Fin d → ℝ) (t₀ := t₀) (T := T) (α := α))
    (B : FiniteParabolicC2AlphaBanach.FirstCoefficientSpace
      (X := E) (E := Fin d × Fin d → ℝ) (t₀ := t₀) (T := T) (α := α))
    (C : FiniteParabolicC2AlphaBanach.ZeroCoefficientSpace
      (X := E) (E := Fin d × Fin d → ℝ) (t₀ := t₀) (T := T) (α := α))
    (hsmall : tensorHeatCoordinatePostErrorBound A
      (frozenTensorHeatPrincipalField (I := I) p e b x t₀ T α) B C
      (frozenTensorHeatFiniteZeroInitialInverseL
        (I := I) p x hxChart d hT hα hα1) < 1)
    (u : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α)
    (hu : FiniteParabolicC2AlphaBanach.coordinateCauchyL A B C u = 0)
    (hu0 : FiniteParabolicC2AlphaBanach.initialTraceL hT hα u = 0) :
    u = 0 := by
  apply eq_zero_of_frozenTensorHeatPerturbation_norm_lt_one
    (I := I) p e b hxFrame hxChart hT hα hα1
      (FiniteParabolicC2AlphaBanach.coordinateCauchyL A B C)
  · exact lt_of_le_of_lt
      (norm_frozenTensorHeatPerturbationL_coordinateCauchyL_le
        (I := I) p e b hxChart hT hα hα1 A B C) hsmall
  · exact hu
  · exact hu0

/-- Specialization to the radius-dependent localized coefficient data used
by the geometric atlas construction. -/
theorem eq_zero_of_localizedTensorHeatCauchy_eq_zero_of_initialTrace_eq_zero
    (p : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis (Fin d) ℝ E) {x : M}
    (hxFrame : x ∈ e.baseSet)
    (hxChart : x ∈ (extChartAt I p).source)
    {t₀ T α : ℝ} (hT : t₀ < T) (hα : 0 < α) (hα1 : α < 1)
    (D : TensorHeatLocalizedCoefficientData E (Fin d × Fin d → ℝ))
    (hcenter : D.principal D.center =
      frozenLocalTensorHeatPrincipalCoefficient (I := I) p e b x)
    (r : ℝ)
    (hsmall : D.errorMajorant
      (frozenTensorHeatFiniteZeroInitialInverseL
        (I := I) p x hxChart d hT hα hα1) r < 1)
    (u : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α)
    (hu : FiniteParabolicC2AlphaBanach.coordinateCauchyL
      (D.principalField hα hα1 r) (D.firstField hα hα1 r)
      (D.zeroField hα hα1 r) u = 0)
    (hu0 : FiniteParabolicC2AlphaBanach.initialTraceL hT hα u = 0) :
    u = 0 := by
  have hfreeze : ParabolicC0AlphaSpace.constL
      (X := E) (α := α) (s := parabolicFiniteCylinder E t₀ T)
      (D.principal D.center) =
      frozenTensorHeatPrincipalField (I := I) p e b x t₀ T α := by
    simp [frozenTensorHeatPrincipalField, hcenter]
  apply eq_zero_of_coordinateCauchy_eq_zero_of_initialTrace_eq_zero
    (I := I) p e b hxFrame hxChart hT hα hα1
      (D.principalField hα hα1 r) (D.firstField hα hα1 r)
      (D.zeroField hα hα1 r)
  · rw [← hfreeze]
    exact lt_of_le_of_lt
      (localizedCoordinatePostErrorBound_le_errorMajorant hα hα1 r D _) hsmall
  · exact hu
  · exact hu0

/-- The localized post-error majorant tends to zero with the radius, with an
arbitrary positive target margin. -/
theorem TensorHeatLocalizedCoefficientData.exists_radius_errorMajorant_lt
    {X W : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (D : TensorHeatLocalizedCoefficientData X W)
    {t₀ T α : ℝ}
    (Q : ParabolicC0AlphaBanach X W α
        (parabolicFiniteCylinder X t₀ T) →L[ℝ]
      FiniteParabolicC2AlphaBanach X W t₀ T α)
    {c : ℝ} (hc : 0 < c) :
    ∃ δ > 0, ∀ r : ℝ, |r| < δ → D.errorMajorant Q r < c := by
  have hevent : ∀ᶠ r in nhds (0 : ℝ), D.errorMajorant Q r < c := by
    have hlim : Filter.Tendsto (D.errorMajorant Q) (nhds (0 : ℝ))
        (nhds (D.errorMajorant Q 0)) :=
      (D.continuous_errorMajorant Q).continuousAt
    have hiio : Set.Iio c ∈ nhds (D.errorMajorant Q 0) := by
      rw [D.errorMajorant_zero Q]
      exact (isOpen_Iio : IsOpen (Set.Iio c)).mem_nhds hc
    exact hlim hiio
  rw [Metric.eventually_nhds_iff] at hevent
  obtain ⟨δ, hδ, hball⟩ := hevent
  refine ⟨δ, hδ, fun r hr => hball ?_⟩
  simpa [Real.dist_eq] using hr

end AnalyticPDE
end RicciFlow
