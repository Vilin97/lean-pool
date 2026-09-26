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

public import LeanPool.PoincareGeometry.LichnerowiczObata.GeometryStatements
public import LeanPool.PoincareGeometry.LichnerowiczObata.LichnerowiczObata

/-! # Closing the independent geometric statement -/

@[expose] public noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff BigOperators
namespace LichnerowiczObataEntry.Geometry
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
local instance metricTwo : IsContMDiffRiemannianBundle I 2 E TM :=
  IsContMDiffRiemannianBundle.of_le (n := ∞) (by decide)
local instance metricThree : IsContMDiffRiemannianBundle I 3 E TM :=
  IsContMDiffRiemannianBundle.of_le (n := ∞) (by decide)

/-- The independent smooth-extension commutator is the actual curvature tensor. -/
theorem curvature_eq (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1] (x : M) (u v w : TM x) :
    curvature cov x u v w = cov.curvatureTensorAlmostSchur x u v w := by
  rfl

/-- The independent orthonormal contraction is the implementation's Ricci tensor. -/
theorem ricci_eq (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1] (x : M) (u v : TM x) :
    ricci cov x u v = cov.ricciCurvatureAlmostSchur x u v := by
  rw [CovariantDerivative.ricciCurvature_applyAlmostSchur,
    LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ (TM x))]
  unfold ricci
  apply Finset.sum_congr rfl
  intro i _
  rw [curvature_eq, real_inner_comm]
  rfl

/-- The independently specified gradient uses the same actual metric Riesz map. -/
theorem gradient_eq (f : M → ℝ) (x : M) :
    gradient (I := I) f x = AlmostSchur.gradient (I := I) f x := rfl

/-- The independently specified Laplacian is the actual div-grad operator. -/
theorem laplacian_eq (cov : CovariantDerivative I E TM) (f : M → ℝ) (x : M) :
    laplacian cov f x = AlmostSchur.laplacian cov f x := rfl

variable [Nonempty M] [LindelofSpace M] [CompactSpace M] [PreconnectedSpace M]

/-- The complete theorem closes the Mathlib-only statement, including the
construction of the connection and every comparison of geometric objects. -/
theorem geometricStatement_proved : geometricStatement (I := I) (M := M) := by
  let cov := AlmostSchur.leviCivitaConnection (I := I) (M := M)
  refine ⟨cov, AlmostSchur.leviCivitaConnection_metricCompatible,
    AlmostSchur.leviCivitaConnection_torsion, ⟨inferInstance⟩, ?_⟩
  intro K hK hdim hRic
  have hRic' : ∀ (x : M) (v : TM x),
      ((Module.finrank ℝ E : ℝ) - 1) * K * ‖v‖ ^ 2 ≤ cov.ricciCurvatureAlmostSchur x v v := by
    simpa only [ricci_eq] using hRic
  obtain ⟨μ, hμ, hbound, heigen, hmin, heq⟩ :=
    LichnerowiczObata.lichnerowicz_obata hdim hK hRic'
  refine ⟨μ, ⟨hμ, ?_, ?_⟩, hbound, ?_⟩
  · simpa only [laplacian_eq] using heigen
  · intro s hs hf
    exact hmin s hs (by simpa only [laplacian_eq] using hf)
  · exact heq

end LichnerowiczObataEntry.Geometry
