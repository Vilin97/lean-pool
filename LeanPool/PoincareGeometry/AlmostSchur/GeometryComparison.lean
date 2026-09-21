/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.GeometryStatements
public import LeanPool.PoincareGeometry.AlmostSchur.AlmostSchurEquality

/-! # Geometry Comparison -/

@[expose] public noncomputable section
open Bundle FiberBundle Set MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace AlmostSchurEntry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [T2Space M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local instance comparisonFiniteTangent (x : M) : FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E TM x
local instance metricTwo : IsContMDiffRiemannianBundle I (↑(2 : ℕ)) E TM :=
  IsContMDiffRiemannianBundle.of_le (n := ∞) (by
    exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
local instance metricThree : IsContMDiffRiemannianBundle I (↑(3 : ℕ)) E TM :=
  IsContMDiffRiemannianBundle.of_le (n := ∞) (by
    exact WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ ⊤ from le_top))

theorem curvature_eq (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1] (x : M) (u v w : TM x) :
    curvature cov x u v w = cov.curvatureTensor x u v w := by
  rfl

theorem ricci_eq (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1] (x : M) (u v : TM x) :
    ricci cov x u v = cov.ricciCurvature x u v := by
  rw [CovariantDerivative.ricciCurvature_apply,
    LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ (TM x))]
  unfold ricci
  apply Finset.sum_congr rfl
  intro i _
  rw [curvature_eq, real_inner_comm]
  rfl

theorem scalar_eq (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1] (x : M) :
    scalar cov x = cov.scalarCurvature x := by
  simp only [scalar, ricci_eq, CovariantDerivative.scalarCurvature]

theorem traceFreeRicciSq_eq (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1] (x : M) :
    traceFreeRicciSq cov x = AlmostSchur.hilbertSchmidtSq
      (AlmostSchur.traceFree (AlmostSchur.ricciRaisedEndomorphism cov x)) := by
  rw [AlmostSchur.hilbertSchmidtSq_eq_sum_sq _ (stdOrthonormalBasis ℝ (TM x))]
  unfold traceFreeRicciSq
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [AlmostSchur.traceFree, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    inner_sub_left, real_inner_smul_left, AlmostSchur.inner_ricciRaisedEndomorphism,
    ← AlmostSchur.scalarCurvature_eq_trace_ricciRaisedEndomorphism,
    ricci_eq, scalar_eq]

theorem einstein_iff (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1] :
    (∀ (x : M) (u v : TM x), ricci cov x u v =
      (scalar cov x / Module.finrank ℝ (TM x)) * inner ℝ u v) ↔
    ∀ x, AlmostSchur.traceFree (AlmostSchur.ricciRaisedEndomorphism cov x) = 0 := by
  have hpair (x : M) (u v : TM x) :
      inner ℝ ((AlmostSchur.traceFree (AlmostSchur.ricciRaisedEndomorphism cov x)) u) v =
        ricci cov x u v - (scalar cov x / Module.finrank ℝ (TM x)) * inner ℝ u v := by
    simp only [AlmostSchur.traceFree, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      inner_sub_left, real_inner_smul_left, AlmostSchur.inner_ricciRaisedEndomorphism,
      ← AlmostSchur.scalarCurvature_eq_trace_ricciRaisedEndomorphism,
      ricci_eq, scalar_eq]
  constructor
  · intro h x
    ext u
    apply ext_inner_right ℝ
    intro v
    rw [hpair, h x u v]
    simp
  · intro h x u v
    have hz := hpair x u v
    rw [h x] at hz
    have hz' : (0 : ℝ) = ricci cov x u v -
        (scalar cov x / Module.finrank ℝ (TM x)) * inner ℝ u v := by
      simpa only [zero_apply, inner_zero_left] using hz
    exact sub_eq_zero.mp hz'.symm

variable [MeasurableSpace M] [BorelSpace M]
  [Nonempty M] [LindelofSpace M] [CompactSpace M] [PreconnectedSpace M]

local instance comparisonMeasurableSpace : MeasurableSpace E := borel E
local instance comparisonBorelSpace : BorelSpace E := ⟨rfl⟩
local instance comparisonContinuousMetric : IsContinuousRiemannianBundle E TM :=
  AlmostSchur.continuousRiemannianBundle_of_contMDiff (I := I)

theorem riemannianVolume_spec :
    isRiemannianVolume (I := I) (AlmostSchur.riemannianVolume (I := I) (M := M)) := by
  intro c s hs hc
  have h := AlmostSchur.riemannianVolume_apply (I := I) (Module.finBasis ℝ E) c hs hc
  simpa only [AlmostSchur.chartMetricLIntegral, mul_one, AlmostSchur.matrixDensity,
    AlmostSchur.coordinateMetric, AlmostSchur.tangentChartGram,
    AlmostSchur.tangentTrivializationGram] using h

/-- The independent geometric statement follows from the complete manifold
proof, with all curvature, volume, and Einstein identifications discharged. -/
theorem geometricStatement_proved : geometricStatement (I := I) (M := M) := by
  let cov := AlmostSchur.leviCivitaConnection (I := I) (M := M)
  let μ := AlmostSchur.riemannianVolume (I := I) (M := M)
  have hvolume := AlmostSchur.riemannianVolume_finite_positive (I := I) (M := M)
  refine ⟨cov, μ, AlmostSchur.leviCivitaConnection_metricCompatible,
    AlmostSchur.leviCivitaConnection_torsion, ⟨inferInstance⟩,
    riemannianVolume_spec, hvolume.1, hvolume.2, ?_⟩
  intro hRic hd
  have hRic' : ∀ (x : M) (v : TM x), 0 ≤ cov.ricciCurvature x v v := by
    simpa only [ricci_eq] using hRic
  have hb := AlmostSchur.almostSchur_bound_complete (I := I) (M := M) hRic' hd
  have he := AlmostSchur.almostSchur_equality_iff (I := I) (M := M) hRic' hd
  constructor
  · simpa only [scalar_eq, traceFreeRicciSq_eq, average, AlmostSchur.riemannianMean,
      cov, μ] using hb
  · rw [einstein_iff]
    simpa only [scalar_eq, traceFreeRicciSq_eq, average, AlmostSchur.riemannianMean,
      cov, μ] using he

end AlmostSchurEntry.Geometry
