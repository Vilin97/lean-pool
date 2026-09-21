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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.TimeDependent
/-!
# Ricci-flow local existence and uniqueness boundary

This file packages the theorem-level interface for roadmap point 4 on top of the
time-dependent geometry layer from `TimeDependent.lean`.

We define:

- metric-valued time derivatives for evolving Riemannian metrics
- Ricci-flow solutions and initial-value problems
- local solutions on compact manifolds
- a bundled local existence/uniqueness theorem package

The analytic proof of local existence is not developed internally here. Instead,
this file records the precise solution and theorem boundary that later Ricci-flow
developments should target.

Under the repository's proof-only standard, this file is preparatory
infrastructure only: it does **not** count as completing roadmap point 4 until
local existence and uniqueness are actually proved in Lean with no proof holes
or placeholder constants.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

/-- If the model vector space is a subsingleton, every tangent fiber is a subsingleton. -/
instance (priority := 100) instSubsingletonTangentSpaceOfSubsingletonModel
    [Subsingleton E] (x : M) : Subsingleton (TM x) := by
  rw [TangentSpace]
  infer_instance

/-- The bundle of time-dependent smooth metrics used by Ricci-flow solutions. -/
abbrev MetricFamily :=
  CovariantDerivative.TimeDependentRiemannianMetric (I := I) (M := M)

/-- The bundle of time-dependent affine connections used alongside a metric family. -/
abbrev ConnectionFamily :=
  CovariantDerivative.TimeDependentCovariantDerivative
    (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM)

/-- A time-dependent symmetric bilinear form on the tangent bundle. -/
abbrev MetricTensorFamily :=
  CovariantDerivative.TimeFamily (Π x : M, TM x → TM x → ℝ)

/-- The metric tensor associated to a time-dependent smooth metric. -/
def metricTensor (g : MetricFamily (I := I) (M := M)) : MetricTensorFamily (I := I) (M := M) :=
  fun t x u v ↦ (g t).inner x u v

@[simp] lemma metricTensor_apply
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (x : M) :
    metricTensor (I := I) (M := M) g t x = fun u v ↦ (g t).inner x u v := rfl

/-- If every tangent fiber is zero-dimensional as a type, every metric tensor component is zero. -/
lemma metricTensor_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (g : MetricFamily (I := I) (M := M)) (t : ℝ) (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) g t x u v = 0 := by
  have hu : u = 0 := Subsingleton.elim u 0
  subst u
  have hzero : (g t).inner x 0 = 0 := ContinuousLinearMap.map_zero ((g t).inner x)
  simpa [metricTensor, hzero]

/-- The Ricci tensor attached to a time-dependent metric and a slicewise smooth connection family. -/
def ricciTensor
    (g : MetricFamily (I := I) (M := M))
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1) :
    MetricTensorFamily (I := I) (M := M) :=
  fun t x u v ↦ by
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    exact CovariantDerivative.ricciCurvature (cov := cov t) x u v

@[simp] lemma ricciTensor_apply
    (g : MetricFamily (I := I) (M := M))
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) (u v : TM x) :
    ricciTensor (I := I) (M := M) g cov hcov t x = (by
      letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      exact fun u v ↦ CovariantDerivative.ricciCurvature (cov := cov t) x u v) := rfl

/-- Ricci-tensor symmetry from first Bianchi and curvature pair symmetry in each time slice. -/
theorem ricciTensor_symm_of_curvature_inner_pair_symm_of_firstBianchi
    (g : MetricFamily (I := I) (M := M))
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hBianchi : ∀ (t : ℝ) (x : M) (a b c : TM x),
      CovariantDerivative.curvatureTensor (cov := cov t) x a b c +
          CovariantDerivative.curvatureTensor (cov := cov t) x b c a +
          CovariantDerivative.curvatureTensor (cov := cov t) x c a b = 0)
    (hpair : ∀ (t : ℝ) (x : M),
      letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩;
      ∀ (a b c d : TM x),
        Inner.inner ℝ (CovariantDerivative.curvatureTensor (cov := cov t) x a b c) d =
          Inner.inner ℝ (CovariantDerivative.curvatureTensor (cov := cov t) x c d a) b)
    (t : ℝ) (x : M) (u v : TM x) :
    ricciTensor (I := I) (M := M) g cov hcov t x u v =
      ricciTensor (I := I) (M := M) g cov hcov t x v u := by
  change
    CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature
        (I := I) (M := M) g cov hcov t x u v =
      CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature
        (I := I) (M := M) g cov hcov t x v u
  exact CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature_symm_of_curvature_inner_pair_symm_of_firstBianchi
      (I := I) (M := M) g cov hcov hBianchi hpair t x u v

/-- Ricci-tensor symmetry from torsion-freeness and curvature pair symmetry in each time slice. -/
theorem ricciTensor_symm_of_curvature_inner_pair_symm_of_torsion_eq_zero
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (g : MetricFamily (I := I) (M := M))
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hT : ∀ t : ℝ, (cov t).torsion = 0)
    (hpair : ∀ (t : ℝ) (x : M),
      letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩;
      ∀ (a b c d : TM x),
        Inner.inner ℝ (CovariantDerivative.curvatureTensor (cov := cov t) x a b c) d =
          Inner.inner ℝ (CovariantDerivative.curvatureTensor (cov := cov t) x c d a) b)
    (t : ℝ) (x : M) (u v : TM x) :
    ricciTensor (I := I) (M := M) g cov hcov t x u v =
      ricciTensor (I := I) (M := M) g cov hcov t x v u := by
  exact ricciTensor_symm_of_curvature_inner_pair_symm_of_firstBianchi
    (I := I) (M := M) g cov hcov
    (fun t x a b c =>
      CovariantDerivative.firstBianchi_curvatureTensor_of_torsion_eq_zero
        (cov := cov t) (hT t) x a b c)
    hpair t x u v

/-- Ricci-tensor symmetry from first Bianchi and skew-adjointness of curvature operators in each
time slice. -/
theorem ricciTensor_symm_of_curvature_inner_skew_adjoint_of_firstBianchi
    (g : MetricFamily (I := I) (M := M))
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hBianchi : ∀ (t : ℝ) (x : M) (a b c : TM x),
      CovariantDerivative.curvatureTensor (cov := cov t) x a b c +
          CovariantDerivative.curvatureTensor (cov := cov t) x b c a +
          CovariantDerivative.curvatureTensor (cov := cov t) x c a b = 0)
    (hskew : ∀ (t : ℝ) (x : M),
      letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩;
      ∀ (a b c d : TM x),
        Inner.inner ℝ (CovariantDerivative.curvatureTensor (cov := cov t) x a b c) d +
          Inner.inner ℝ c (CovariantDerivative.curvatureTensor (cov := cov t) x a b d) = 0)
    (t : ℝ) (x : M) (u v : TM x) :
    ricciTensor (I := I) (M := M) g cov hcov t x u v =
      ricciTensor (I := I) (M := M) g cov hcov t x v u := by
  change
    CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature
        (I := I) (M := M) g cov hcov t x u v =
      CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature
        (I := I) (M := M) g cov hcov t x v u
  exact CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature_symm_of_curvature_inner_skew_adjoint_of_firstBianchi
    (I := I) (M := M) g cov hcov hBianchi hskew t x u v

/-- Ricci-tensor symmetry from torsion-freeness and skew-adjointness of curvature operators in
each time slice. -/
theorem ricciTensor_symm_of_curvature_inner_skew_adjoint_of_torsion_eq_zero
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (g : MetricFamily (I := I) (M := M))
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hT : ∀ t : ℝ, (cov t).torsion = 0)
    (hskew : ∀ (t : ℝ) (x : M),
      letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩;
      ∀ (a b c d : TM x),
        Inner.inner ℝ (CovariantDerivative.curvatureTensor (cov := cov t) x a b c) d +
          Inner.inner ℝ c (CovariantDerivative.curvatureTensor (cov := cov t) x a b d) = 0)
    (t : ℝ) (x : M) (u v : TM x) :
    ricciTensor (I := I) (M := M) g cov hcov t x u v =
      ricciTensor (I := I) (M := M) g cov hcov t x v u := by
  exact ricciTensor_symm_of_curvature_inner_skew_adjoint_of_firstBianchi
    (I := I) (M := M) g cov hcov
    (fun t x a b c =>
      CovariantDerivative.firstBianchi_curvatureTensor_of_torsion_eq_zero
        (cov := cov t) (hT t) x a b c)
    hskew t x u v

/-- Ricci-tensor symmetry from torsion-freeness and metric compatibility in each time slice. -/
theorem ricciTensor_symm_of_metricCompatible_of_torsion_eq_zero
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (g : MetricFamily (I := I) (M := M))
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hT : ∀ t : ℝ, (cov t).torsion = 0)
    (hmetric : CovariantDerivative.TimeDependentRiemannianMetric.IsMetricCompatible
      (I := I) (M := M) g cov)
    (t : ℝ) (x : M) (u v : TM x) :
    ricciTensor (I := I) (M := M) g cov hcov t x u v =
      ricciTensor (I := I) (M := M) g cov hcov t x v u := by
  change
    CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature
        (I := I) (M := M) g cov hcov t x u v =
      CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature
        (I := I) (M := M) g cov hcov t x v u
  exact CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature_symm_of_metricCompatible_of_torsion_eq_zero
    (I := I) (M := M) g cov hcov hT hmetric t x u v

/-- Ricci-tensor symmetry for Levi-Civita connection families. -/
theorem ricciTensor_symm_of_isLeviCivita
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (g : MetricFamily (I := I) (M := M))
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hLevi : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g cov)
    (t : ℝ) (x : M) (u v : TM x) :
    ricciTensor (I := I) (M := M) g cov hcov t x u v =
      ricciTensor (I := I) (M := M) g cov hcov t x v u := by
  change
    CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature
        (I := I) (M := M) g cov hcov t x u v =
      CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature
        (I := I) (M := M) g cov hcov t x v u
  exact CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature_symm_of_isLeviCivita
    (I := I) (M := M) g cov hcov hLevi t x u v

/-- Ricci tensor components vanish when every tangent fiber is zero-dimensional as a type. -/
lemma ricciTensor_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (g : MetricFamily (I := I) (M := M))
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) (u v : TM x) :
    ricciTensor (I := I) (M := M) g cov hcov t x u v = 0 := by
  unfold ricciTensor
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  exact CovariantDerivative.ricciCurvature_eq_zero_of_subsingleton_tangent
    (I := I) (M := M) (cov := cov t) x u v

/-- If the model vector space has dimension at most one, each tangent fiber has dimension at most
one. -/
lemma tangent_finrank_le_one_of_model
    [Fact (Module.finrank ℝ E ≤ 1)] (x : M) :
    Module.finrank ℝ (TM x) ≤ 1 := by
  change Module.finrank ℝ E ≤ 1
  exact Fact.out

/-- Ricci tensor components vanish when every tangent fiber has dimension at most one. -/
lemma ricciTensor_eq_zero_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1)
    (g : MetricFamily (I := I) (M := M))
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) (u v : TM x) :
    ricciTensor (I := I) (M := M) g cov hcov t x u v = 0 := by
  unfold ricciTensor
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  exact CovariantDerivative.ricciCurvature_eq_zero_of_finrank_le_one
    (I := I) (M := M) (cov := cov t) x (hfin x) u v

/-- Model-space version of `ricciTensor_eq_zero_of_finrank_le_one`. -/
lemma ricciTensor_eq_zero_of_finrank_model_le_one
    [Fact (Module.finrank ℝ E ≤ 1)]
    (g : MetricFamily (I := I) (M := M))
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) (u v : TM x) :
    ricciTensor (I := I) (M := M) g cov hcov t x u v = 0 :=
  ricciTensor_eq_zero_of_finrank_le_one
    (I := I) (M := M) (fun x ↦ tangent_finrank_le_one_of_model (I := I) (M := M) x)
    g cov hcov t x u v

/-- The Ricci tensor associated to a time-dependent metric family is independent of the chosen
Levi-Civita family used to compute it. -/
theorem ricciTensor_eq_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    {cov cov' : ConnectionFamily (I := I) (M := M)}
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hcov' : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov' t) 1)
    (hLevi : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g cov)
    (hLevi' : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g cov') :
    ricciTensor (I := I) (M := M) g cov hcov = ricciTensor (I := I) (M := M) g cov' hcov' := by
  funext t x u v
  change
    CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature (I := I) (M := M) g cov hcov t x u v =
      CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature
        (I := I) (M := M) g cov' hcov' t x u v
  exact CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature_eq_of_isLeviCivita
    (I := I) (M := M) (g := g) hcov hcov' hLevi hLevi' t x u v

/-- The right-hand side of the Ricci-flow equation `∂ₜ g = -2 Ric(g)`. -/
def ricciFlowRHS
    (g : MetricFamily (I := I) (M := M))
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1) :
    MetricTensorFamily (I := I) (M := M) :=
  fun t x u v ↦ (-2 : ℝ) * ricciTensor (I := I) (M := M) g cov hcov t x u v

@[simp] lemma ricciFlowRHS_apply
    (g : MetricFamily (I := I) (M := M))
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) (u v : TM x) :
    ricciFlowRHS (I := I) (M := M) g cov hcov t x =
      fun u v ↦ (-2 : ℝ) * ricciTensor (I := I) (M := M) g cov hcov t x u v := rfl

/-- Symmetry of the Ricci tensor implies symmetry of the Ricci-flow right-hand side. -/
theorem ricciFlowRHS_symm_of_ricciTensor_symm
    (g : MetricFamily (I := I) (M := M))
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hRicciSymm : ∀ t : ℝ, ∀ x : M, ∀ u v : TM x,
      ricciTensor (I := I) (M := M) g cov hcov t x u v =
        ricciTensor (I := I) (M := M) g cov hcov t x v u)
    (t : ℝ) (x : M) (u v : TM x) :
    ricciFlowRHS (I := I) (M := M) g cov hcov t x u v =
      ricciFlowRHS (I := I) (M := M) g cov hcov t x v u := by
  simp [ricciFlowRHS, hRicciSymm t x u v]

/-- Ricci-flow RHS symmetry from torsion-freeness and skew-adjointness of curvature operators in
each time slice. -/
theorem ricciFlowRHS_symm_of_curvature_inner_skew_adjoint_of_torsion_eq_zero
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (g : MetricFamily (I := I) (M := M))
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hT : ∀ t : ℝ, (cov t).torsion = 0)
    (hskew : ∀ (t : ℝ) (x : M),
      letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩;
      ∀ (a b c d : TM x),
        Inner.inner ℝ (CovariantDerivative.curvatureTensor (cov := cov t) x a b c) d +
          Inner.inner ℝ c (CovariantDerivative.curvatureTensor (cov := cov t) x a b d) = 0)
    (t : ℝ) (x : M) (u v : TM x) :
    ricciFlowRHS (I := I) (M := M) g cov hcov t x u v =
      ricciFlowRHS (I := I) (M := M) g cov hcov t x v u := by
  exact ricciFlowRHS_symm_of_ricciTensor_symm (I := I) (M := M) g cov hcov
    (ricciTensor_symm_of_curvature_inner_skew_adjoint_of_torsion_eq_zero
      (I := I) (M := M) g cov hcov hT hskew)
    t x u v

/-- Ricci-flow RHS symmetry from torsion-freeness and metric compatibility in each time slice. -/
theorem ricciFlowRHS_symm_of_metricCompatible_of_torsion_eq_zero
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (g : MetricFamily (I := I) (M := M))
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hT : ∀ t : ℝ, (cov t).torsion = 0)
    (hmetric : CovariantDerivative.TimeDependentRiemannianMetric.IsMetricCompatible
      (I := I) (M := M) g cov)
    (t : ℝ) (x : M) (u v : TM x) :
    ricciFlowRHS (I := I) (M := M) g cov hcov t x u v =
      ricciFlowRHS (I := I) (M := M) g cov hcov t x v u := by
  exact ricciFlowRHS_symm_of_ricciTensor_symm (I := I) (M := M) g cov hcov
    (ricciTensor_symm_of_metricCompatible_of_torsion_eq_zero
      (I := I) (M := M) g cov hcov hT hmetric)
    t x u v

/-- Ricci-flow RHS symmetry for Levi-Civita connection families. -/
theorem ricciFlowRHS_symm_of_isLeviCivita
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (g : MetricFamily (I := I) (M := M))
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hLevi : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g cov)
    (t : ℝ) (x : M) (u v : TM x) :
    ricciFlowRHS (I := I) (M := M) g cov hcov t x u v =
      ricciFlowRHS (I := I) (M := M) g cov hcov t x v u := by
  exact ricciFlowRHS_symm_of_ricciTensor_symm (I := I) (M := M) g cov hcov
    (ricciTensor_symm_of_isLeviCivita (I := I) (M := M) g cov hcov hLevi)
    t x u v

/-- The Ricci-flow right-hand side vanishes when every tangent fiber is zero-dimensional as a
type. -/
lemma ricciFlowRHS_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (g : MetricFamily (I := I) (M := M))
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) (u v : TM x) :
    ricciFlowRHS (I := I) (M := M) g cov hcov t x u v = 0 := by
  simp [ricciFlowRHS, ricciTensor_eq_zero_of_subsingleton_tangent
    (I := I) (M := M) g cov hcov t x u v]

/-- The Ricci-flow right-hand side vanishes wherever the corresponding Ricci tensor vanishes. -/
lemma ricciFlowRHS_eq_zero_of_ricciTensor_eq_zero
    (g : MetricFamily (I := I) (M := M))
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    {t : ℝ} {x : M} {u v : TM x}
    (hRicciZero : ricciTensor (I := I) (M := M) g cov hcov t x u v = 0) :
    ricciFlowRHS (I := I) (M := M) g cov hcov t x u v = 0 := by
  simp [ricciFlowRHS, hRicciZero]

/-- The Ricci-flow right-hand side depends only on the metric family once the connection family is
known to be Levi-Civita. -/
theorem ricciFlowRHS_eq_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    {cov cov' : ConnectionFamily (I := I) (M := M)}
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hcov' : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov' t) 1)
    (hLevi : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g cov)
    (hLevi' : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g cov') :
    ricciFlowRHS (I := I) (M := M) g cov hcov = ricciFlowRHS (I := I) (M := M) g cov' hcov' := by
  funext t x u v
  change
    (-2 : ℝ) * ricciTensor (I := I) (M := M) g cov hcov t x u v =
      (-2 : ℝ) * ricciTensor (I := I) (M := M) g cov' hcov' t x u v
  exact congrArg (fun z => (-2 : ℝ) * z)
    (congrArg (fun F => F t x u v)
      (ricciTensor_eq_of_isLeviCivita (I := I) (M := M) g hcov hcov' hLevi hLevi'))

section ChosenLeviCivita

variable [SigmaCompactSpace M]

/-- The Ricci tensor of a metric family, computed using the chosen smooth Levi-Civita family. -/
def intrinsicRicciTensor
    (g : MetricFamily (I := I) (M := M)) :
    MetricTensorFamily (I := I) (M := M) :=
  ricciTensor (I := I) (M := M) g
    (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
      (I := I) (M := M) g)
    (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g)

@[simp] lemma intrinsicRicciTensor_apply
    (g : MetricFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciTensor (I := I) (M := M) g t x u v =
      ricciTensor (I := I) (M := M) g
        (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
          (I := I) (M := M) g)
        (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
          (I := I) (M := M) g)
        t x u v := rfl

/-- Intrinsic Ricci-tensor symmetry from the algebraic curvature pair-symmetry identity for the
chosen smooth Levi-Civita family. First Bianchi is discharged from the chosen family's
torsion-freeness. -/
theorem intrinsicRicciTensor_symm_of_curvature_inner_pair_symm
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (g : MetricFamily (I := I) (M := M))
    (hpair : ∀ (t : ℝ) (x : M),
      letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩;
      letI : CovariantDerivative.ContMDiffCovariantDerivative
          (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
            (I := I) (M := M) g t) 1 :=
        CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
          (I := I) (M := M) g t;
      ∀ (a b c d : TM x),
        Inner.inner ℝ
            (CovariantDerivative.curvatureTensor
              (cov := CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
                (I := I) (M := M) g t) x a b c) d =
          Inner.inner ℝ
            (CovariantDerivative.curvatureTensor
              (cov := CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
                (I := I) (M := M) g t) x c d a) b)
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciTensor (I := I) (M := M) g t x u v =
      intrinsicRicciTensor (I := I) (M := M) g t x v u := by
  let cov :=
    CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
      (I := I) (M := M) g
  let hcov :=
    CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g
  exact ricciTensor_symm_of_curvature_inner_pair_symm_of_torsion_eq_zero
    (I := I) (M := M) g cov hcov
    (fun t => by
      have hLevi :=
        CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_isLeviCivita
          (I := I) (M := M) (g := g) t
      simpa [CovariantDerivative.IsTorsionFree] using hLevi.1)
    (by
      intro t x
      simpa [cov] using hpair t x)
    t x u v

/-- Intrinsic Ricci-tensor symmetry from skew-adjointness of the chosen Levi-Civita curvature
operators. This is the metric-compatibility-facing version of the intrinsic Ricci symmetry bridge. -/
theorem intrinsicRicciTensor_symm_of_curvature_inner_skew_adjoint
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (g : MetricFamily (I := I) (M := M))
    (hskew : ∀ (t : ℝ) (x : M),
      letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩;
      letI : CovariantDerivative.ContMDiffCovariantDerivative
          (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
            (I := I) (M := M) g t) 1 :=
        CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
          (I := I) (M := M) g t;
      ∀ (a b c d : TM x),
        Inner.inner ℝ
            (CovariantDerivative.curvatureTensor
              (cov := CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
                (I := I) (M := M) g t) x a b c) d +
          Inner.inner ℝ c
            (CovariantDerivative.curvatureTensor
              (cov := CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
                (I := I) (M := M) g t) x a b d) = 0)
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciTensor (I := I) (M := M) g t x u v =
      intrinsicRicciTensor (I := I) (M := M) g t x v u := by
  let cov :=
    CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
      (I := I) (M := M) g
  let hcov :=
    CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g
  exact ricciTensor_symm_of_curvature_inner_skew_adjoint_of_torsion_eq_zero
    (I := I) (M := M) g cov hcov
    (fun t => by
      have hLevi :=
        CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_isLeviCivita
          (I := I) (M := M) (g := g) t
      simpa [CovariantDerivative.IsTorsionFree] using hLevi.1)
    (by
      intro t x
      simpa [cov] using hskew t x)
    t x u v

/-- The intrinsic Ricci tensor of a metric family is symmetric, using the chosen smooth
Levi-Civita family. -/
theorem intrinsicRicciTensor_symm
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (g : MetricFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciTensor (I := I) (M := M) g t x u v =
      intrinsicRicciTensor (I := I) (M := M) g t x v u := by
  let cov :=
    CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
      (I := I) (M := M) g
  let hcov :=
    CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g
  exact ricciTensor_symm_of_isLeviCivita
    (I := I) (M := M) g cov hcov
    (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_isLeviCivita
      (I := I) (M := M) g)
    t x u v

lemma intrinsicRicciTensor_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (g : MetricFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciTensor (I := I) (M := M) g t x u v = 0 := by
  exact ricciTensor_eq_zero_of_subsingleton_tangent (I := I) (M := M) g
    (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
      (I := I) (M := M) g)
    (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g)
    t x u v

/-- The intrinsic Ricci tensor vanishes when every tangent fiber has dimension at most one. -/
lemma intrinsicRicciTensor_eq_zero_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1)
    (g : MetricFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciTensor (I := I) (M := M) g t x u v = 0 := by
  exact ricciTensor_eq_zero_of_finrank_le_one (I := I) (M := M) hfin g
    (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
      (I := I) (M := M) g)
    (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g)
    t x u v

/-- Model-space version of `intrinsicRicciTensor_eq_zero_of_finrank_le_one`. -/
lemma intrinsicRicciTensor_eq_zero_of_finrank_model_le_one
    [Fact (Module.finrank ℝ E ≤ 1)]
    (g : MetricFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciTensor (I := I) (M := M) g t x u v = 0 :=
  intrinsicRicciTensor_eq_zero_of_finrank_le_one
    (I := I) (M := M) (fun x ↦ tangent_finrank_le_one_of_model (I := I) (M := M) x)
    g t x u v

theorem intrinsicRicciTensor_eq_ricciTensor_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    {cov : ConnectionFamily (I := I) (M := M)}
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hLevi : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g cov) :
    intrinsicRicciTensor (I := I) (M := M) g =
      ricciTensor (I := I) (M := M) g cov hcov := by
  exact ricciTensor_eq_of_isLeviCivita (I := I) (M := M) g
    (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g)
    hcov
    (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_isLeviCivita
      (I := I) (M := M) g)
    hLevi

/-- The intrinsic Ricci-flow right-hand side `-2 Ric(g)`, using the chosen smooth Levi-Civita
family. -/
def intrinsicRicciFlowRHS
    (g : MetricFamily (I := I) (M := M)) :
    MetricTensorFamily (I := I) (M := M) :=
  ricciFlowRHS (I := I) (M := M) g
    (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
      (I := I) (M := M) g)
    (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g)

@[simp] lemma intrinsicRicciFlowRHS_apply
    (g : MetricFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciFlowRHS (I := I) (M := M) g t x u v =
      ricciFlowRHS (I := I) (M := M) g
        (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
          (I := I) (M := M) g)
        (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
          (I := I) (M := M) g)
        t x u v := rfl

/-- Symmetry of the intrinsic Ricci tensor implies symmetry of the intrinsic Ricci-flow right-hand
side. -/
theorem intrinsicRicciFlowRHS_symm_of_intrinsicRicciTensor_symm
    (g : MetricFamily (I := I) (M := M))
    (hRicciSymm : ∀ t : ℝ, ∀ x : M, ∀ u v : TM x,
      intrinsicRicciTensor (I := I) (M := M) g t x u v =
        intrinsicRicciTensor (I := I) (M := M) g t x v u)
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciFlowRHS (I := I) (M := M) g t x u v =
      intrinsicRicciFlowRHS (I := I) (M := M) g t x v u := by
  exact ricciFlowRHS_symm_of_ricciTensor_symm (I := I) (M := M) g
    (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
      (I := I) (M := M) g)
    (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g)
    (by
      intro t x u v
      simpa [intrinsicRicciTensor] using hRicciSymm t x u v)
    t x u v

/-- Intrinsic Ricci-flow RHS symmetry from skew-adjointness of the chosen Levi-Civita curvature
operators. -/
theorem intrinsicRicciFlowRHS_symm_of_curvature_inner_skew_adjoint
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (g : MetricFamily (I := I) (M := M))
    (hskew : ∀ (t : ℝ) (x : M),
      letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩;
      letI : CovariantDerivative.ContMDiffCovariantDerivative
          (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
            (I := I) (M := M) g t) 1 :=
        CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
          (I := I) (M := M) g t;
      ∀ (a b c d : TM x),
        Inner.inner ℝ
            (CovariantDerivative.curvatureTensor
              (cov := CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
                (I := I) (M := M) g t) x a b c) d +
          Inner.inner ℝ c
            (CovariantDerivative.curvatureTensor
              (cov := CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
                (I := I) (M := M) g t) x a b d) = 0)
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciFlowRHS (I := I) (M := M) g t x u v =
      intrinsicRicciFlowRHS (I := I) (M := M) g t x v u := by
  exact intrinsicRicciFlowRHS_symm_of_intrinsicRicciTensor_symm
    (I := I) (M := M) g
    (intrinsicRicciTensor_symm_of_curvature_inner_skew_adjoint
      (I := I) (M := M) g hskew)
    t x u v

/-- The intrinsic Ricci-flow right-hand side is symmetric, using the chosen smooth
Levi-Civita family. -/
theorem intrinsicRicciFlowRHS_symm
    [IsManifold I (minSmoothness ℝ 3) M]
    [IsManifold I ((2 : ℕ∞) + 1) M]
    (g : MetricFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciFlowRHS (I := I) (M := M) g t x u v =
      intrinsicRicciFlowRHS (I := I) (M := M) g t x v u := by
  exact intrinsicRicciFlowRHS_symm_of_intrinsicRicciTensor_symm
    (I := I) (M := M) g
    (intrinsicRicciTensor_symm (I := I) (M := M) g)
    t x u v

lemma intrinsicRicciFlowRHS_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (g : MetricFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciFlowRHS (I := I) (M := M) g t x u v = 0 := by
  exact ricciFlowRHS_eq_zero_of_subsingleton_tangent (I := I) (M := M) g
    (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
      (I := I) (M := M) g)
    (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g)
    t x u v

/-- The intrinsic Ricci-flow right-hand side vanishes when every tangent fiber has dimension at
most one. -/
lemma intrinsicRicciFlowRHS_eq_zero_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1)
    (g : MetricFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciFlowRHS (I := I) (M := M) g t x u v = 0 := by
  exact ricciFlowRHS_eq_zero_of_ricciTensor_eq_zero (I := I) (M := M) g
    (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
      (I := I) (M := M) g)
    (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g)
    (by
      simpa [intrinsicRicciTensor] using
        intrinsicRicciTensor_eq_zero_of_finrank_le_one
          (I := I) (M := M) hfin g t x u v)

/-- Model-space version of `intrinsicRicciFlowRHS_eq_zero_of_finrank_le_one`. -/
lemma intrinsicRicciFlowRHS_eq_zero_of_finrank_model_le_one
    [Fact (Module.finrank ℝ E ≤ 1)]
    (g : MetricFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    intrinsicRicciFlowRHS (I := I) (M := M) g t x u v = 0 :=
  intrinsicRicciFlowRHS_eq_zero_of_finrank_le_one
    (I := I) (M := M) (fun x ↦ tangent_finrank_le_one_of_model (I := I) (M := M) x)
    g t x u v

/-- The intrinsic Ricci-flow right-hand side vanishes wherever the intrinsic Ricci tensor
vanishes. -/
lemma intrinsicRicciFlowRHS_eq_zero_of_intrinsicRicciTensor_eq_zero
    (g : MetricFamily (I := I) (M := M))
    {t : ℝ} {x : M} {u v : TM x}
    (hRicciZero : intrinsicRicciTensor (I := I) (M := M) g t x u v = 0) :
    intrinsicRicciFlowRHS (I := I) (M := M) g t x u v = 0 := by
  exact ricciFlowRHS_eq_zero_of_ricciTensor_eq_zero (I := I) (M := M) g
    (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
      (I := I) (M := M) g)
    (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g)
    (by simpa [intrinsicRicciTensor] using hRicciZero)

theorem intrinsicRicciFlowRHS_eq_ricciFlowRHS_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    {cov : ConnectionFamily (I := I) (M := M)}
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hLevi : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g cov) :
    intrinsicRicciFlowRHS (I := I) (M := M) g =
      ricciFlowRHS (I := I) (M := M) g cov hcov := by
  exact ricciFlowRHS_eq_of_isLeviCivita (I := I) (M := M) g
    (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) g)
    hcov
    (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_isLeviCivita
      (I := I) (M := M) g)
    hLevi

end ChosenLeviCivita

/-- A metric family has time derivative `gdot` at time `t` if each fibrewise metric tensor has that
derivative as a bilinear form. -/
def HasTimeDerivativeAt
    (g : MetricFamily (I := I) (M := M))
    (gdot : MetricTensorFamily (I := I) (M := M)) (t : ℝ) : Prop :=
  ∀ x : M, ∀ u v : TM x,
    HasDerivAt (fun s ↦ metricTensor (I := I) (M := M) g s x u v) (gdot t x u v) t

/-- A metric family has time derivative `gdot` on a set of times if this holds at each time in the
set. -/
def HasTimeDerivativeOn
    (g : MetricFamily (I := I) (M := M))
    (gdot : MetricTensorFamily (I := I) (M := M)) (s : Set ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ s → HasTimeDerivativeAt (I := I) (M := M) g gdot t

lemma HasTimeDerivativeAt.congr
    {g g' : MetricFamily (I := I) (M := M)}
    {gdot gdot' : MetricTensorFamily (I := I) (M := M)}
    {t : ℝ}
    (h : HasTimeDerivativeAt (I := I) (M := M) g gdot t)
    (hg : ∀ τ : ℝ, ∀ x : M, ∀ u v : TM x,
      metricTensor (I := I) (M := M) g τ x u v =
        metricTensor (I := I) (M := M) g' τ x u v)
    (hgdot : ∀ x : M, ∀ u v : TM x, gdot t x u v = gdot' t x u v) :
    HasTimeDerivativeAt (I := I) (M := M) g' gdot' t := by
  intro x u v
  have hmetric :
      (fun τ : ℝ ↦ metricTensor (I := I) (M := M) g' τ x u v) =
        (fun τ : ℝ ↦ metricTensor (I := I) (M := M) g τ x u v) := by
    funext τ
    exact (hg τ x u v).symm
  have hvelocity : gdot' t x u v = gdot t x u v := (hgdot x u v).symm
  change HasDerivAt
    (fun τ : ℝ ↦ metricTensor (I := I) (M := M) g' τ x u v) (gdot' t x u v) t
  rw [hmetric, hvelocity]
  exact h x u v

lemma HasTimeDerivativeOn.congr
    {g g' : MetricFamily (I := I) (M := M)}
    {gdot gdot' : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (h : HasTimeDerivativeOn (I := I) (M := M) g gdot s)
    (hg : ∀ τ : ℝ, ∀ x : M, ∀ u v : TM x,
      metricTensor (I := I) (M := M) g τ x u v =
        metricTensor (I := I) (M := M) g' τ x u v)
    (hgdot : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M, ∀ u v : TM x,
      gdot t x u v = gdot' t x u v) :
    HasTimeDerivativeOn (I := I) (M := M) g' gdot' s := by
  intro t ht
  exact (h ht).congr hg (hgdot ht)

lemma HasTimeDerivativeAt.congr_velocity
    {g : MetricFamily (I := I) (M := M)}
    {gdot gdot' : MetricTensorFamily (I := I) (M := M)}
    {t : ℝ}
    (h : HasTimeDerivativeAt (I := I) (M := M) g gdot t)
    (hgdot : ∀ x : M, ∀ u v : TM x, gdot t x u v = gdot' t x u v) :
    HasTimeDerivativeAt (I := I) (M := M) g gdot' t :=
  h.congr (fun _ _ _ _ ↦ rfl) hgdot

lemma HasTimeDerivativeOn.congr_velocity
    {g : MetricFamily (I := I) (M := M)}
    {gdot gdot' : MetricTensorFamily (I := I) (M := M)}
    {s : Set ℝ}
    (h : HasTimeDerivativeOn (I := I) (M := M) g gdot s)
    (hgdot : ∀ ⦃t : ℝ⦄, t ∈ s → ∀ x : M, ∀ u v : TM x,
      gdot t x u v = gdot' t x u v) :
    HasTimeDerivativeOn (I := I) (M := M) g gdot' s :=
  h.congr (fun _ _ _ _ ↦ rfl) hgdot

lemma HasTimeDerivativeOn.mono
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {s t : Set ℝ}
    (h : HasTimeDerivativeOn (I := I) (M := M) g gdot t) (hst : s ⊆ t) :
    HasTimeDerivativeOn (I := I) (M := M) g gdot s := by
  intro u hu
  exact h (hst hu)

/-- Time-derivative data on the open interior of a closed interval, together
with endpoint time-derivative data, gives time-derivative data on the whole
closed interval. -/
lemma HasTimeDerivativeOn.of_Ioo_endpoints
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {a b : ℝ}
    (hIoo : HasTimeDerivativeOn (I := I) (M := M) g gdot (Set.Ioo a b))
    (ha : HasTimeDerivativeAt (I := I) (M := M) g gdot a)
    (hb : HasTimeDerivativeAt (I := I) (M := M) g gdot b) :
    HasTimeDerivativeOn (I := I) (M := M) g gdot (Set.Icc a b) := by
  intro t ht
  by_cases hta : t = a
  · simpa [hta] using ha
  by_cases htb : t = b
  · simpa [htb] using hb
  exact hIoo ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htb⟩

/-- Time-derivative data on the open interior of a closed interval, together
with derivative data at every non-interior boundary point of that closed
interval, gives time-derivative data on the whole closed interval. -/
lemma HasTimeDerivativeOn.of_Ioo_boundary
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)}
    {a b : ℝ}
    (hIoo : HasTimeDerivativeOn (I := I) (M := M) g gdot (Set.Ioo a b))
    (hboundary : ∀ ⦃t : ℝ⦄, t ∈ Set.Icc a b → t ∉ Set.Ioo a b →
      HasTimeDerivativeAt (I := I) (M := M) g gdot t) :
    HasTimeDerivativeOn (I := I) (M := M) g gdot (Set.Icc a b) := by
  intro t ht
  by_cases htInterior : t ∈ Set.Ioo a b
  · exact hIoo htInterior
  · exact hboundary ht htInterior

/-- The Ricci-flow equation at a single time, written for the metric tensor. -/
def SatisfiesEquationAt
    (g : MetricFamily (I := I) (M := M))
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (gdot : MetricTensorFamily (I := I) (M := M)) (t : ℝ) : Prop :=
  ∀ x : M, ∀ u v : TM x,
    gdot t x u v = ricciFlowRHS (I := I) (M := M) g cov hcov t x u v

/-- Transfer a pointwise connection-parametrized Ricci-flow equation across a pointwise-equal
velocity. -/
theorem SatisfiesEquationAt.congr_velocity
    {g : MetricFamily (I := I) (M := M)}
    {cov : ConnectionFamily (I := I) (M := M)}
    {hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1}
    {gdot gdot' : MetricTensorFamily (I := I) (M := M)} {t : ℝ}
    (h : SatisfiesEquationAt (I := I) (M := M) g cov hcov gdot t)
    (hgdot : ∀ x : M, ∀ u v : TM x, gdot t x u v = gdot' t x u v) :
    SatisfiesEquationAt (I := I) (M := M) g cov hcov gdot' t := by
  intro x u v
  calc
    gdot' t x u v = gdot t x u v := (hgdot x u v).symm
    _ = ricciFlowRHS (I := I) (M := M) g cov hcov t x u v := h x u v

/-- On zero-dimensional tangent fibers, the Ricci-flow equation forces the metric velocity to
vanish pointwise. -/
theorem SatisfiesEquationAt.metricVelocity_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {g : MetricFamily (I := I) (M := M)}
    {cov : ConnectionFamily (I := I) (M := M)}
    {hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1}
    {gdot : MetricTensorFamily (I := I) (M := M)} {t : ℝ}
    (h : SatisfiesEquationAt (I := I) (M := M) g cov hcov gdot t)
    (x : M) (u v : TM x) :
    gdot t x u v = 0 := by
  rw [h x u v]
  exact ricciFlowRHS_eq_zero_of_subsingleton_tangent
    (I := I) (M := M) g cov hcov t x u v

/-- If the Ricci tensor vanishes in a component satisfying the Ricci-flow equation, then that
metric-velocity component vanishes. -/
theorem SatisfiesEquationAt.metricVelocity_eq_zero_of_ricciTensor_eq_zero
    {g : MetricFamily (I := I) (M := M)}
    {cov : ConnectionFamily (I := I) (M := M)}
    {hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1}
    {gdot : MetricTensorFamily (I := I) (M := M)} {t : ℝ}
    (h : SatisfiesEquationAt (I := I) (M := M) g cov hcov gdot t)
    {x : M} {u v : TM x}
    (hRicciZero : ricciTensor (I := I) (M := M) g cov hcov t x u v = 0) :
    gdot t x u v = 0 := by
  rw [h x u v]
  exact ricciFlowRHS_eq_zero_of_ricciTensor_eq_zero
    (I := I) (M := M) g cov hcov hRicciZero

/-- The Ricci-flow equation at a fixed time is independent of the chosen Levi-Civita family. -/
theorem satisfiesEquationAt_iff_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    {cov cov' : ConnectionFamily (I := I) (M := M)}
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hcov' : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov' t) 1)
    (gdot : MetricTensorFamily (I := I) (M := M)) (t : ℝ)
    (hLevi : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g cov)
    (hLevi' : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g cov') :
    SatisfiesEquationAt (I := I) (M := M) g cov hcov gdot t ↔
      SatisfiesEquationAt (I := I) (M := M) g cov' hcov' gdot t := by
  constructor <;> intro hEq x u v
  · calc
      gdot t x u v = ricciFlowRHS (I := I) (M := M) g cov hcov t x u v := hEq x u v
      _ = ricciFlowRHS (I := I) (M := M) g cov' hcov' t x u v := by
        simpa using congrArg (fun F => F t x u v)
          (ricciFlowRHS_eq_of_isLeviCivita
            (I := I) (M := M) g hcov hcov' hLevi hLevi')
  · calc
      gdot t x u v = ricciFlowRHS (I := I) (M := M) g cov' hcov' t x u v := hEq x u v
      _ = ricciFlowRHS (I := I) (M := M) g cov hcov t x u v := by
        simpa using congrArg (fun F => F t x u v)
          (ricciFlowRHS_eq_of_isLeviCivita
            (I := I) (M := M) g hcov hcov' hLevi hLevi').symm

section ChosenLeviCivitaEquation

variable [SigmaCompactSpace M]

/-- The pointwise Ricci-flow equation written using the chosen smooth Levi-Civita family. -/
def SatisfiesIntrinsicEquationAt
    (g : MetricFamily (I := I) (M := M))
    (gdot : MetricTensorFamily (I := I) (M := M)) (t : ℝ) : Prop :=
  ∀ x : M, ∀ u v : TM x,
    gdot t x u v = intrinsicRicciFlowRHS (I := I) (M := M) g t x u v

theorem SatisfiesIntrinsicEquationAt.metricVelocity_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)} {t : ℝ}
    (h : SatisfiesIntrinsicEquationAt (I := I) (M := M) g gdot t)
    (x : M) (u v : TM x) :
    gdot t x u v = 0 := by
  rw [h x u v]
  exact intrinsicRicciFlowRHS_eq_zero_of_subsingleton_tangent
    (I := I) (M := M) g t x u v

/-- If the intrinsic Ricci tensor vanishes in a component satisfying the intrinsic Ricci-flow
equation, then that metric-velocity component vanishes. -/
theorem SatisfiesIntrinsicEquationAt.metricVelocity_eq_zero_of_intrinsicRicciTensor_eq_zero
    {g : MetricFamily (I := I) (M := M)}
    {gdot : MetricTensorFamily (I := I) (M := M)} {t : ℝ}
    (h : SatisfiesIntrinsicEquationAt (I := I) (M := M) g gdot t)
    {x : M} {u v : TM x}
    (hRicciZero : intrinsicRicciTensor (I := I) (M := M) g t x u v = 0) :
    gdot t x u v = 0 := by
  rw [h x u v]
  exact intrinsicRicciFlowRHS_eq_zero_of_intrinsicRicciTensor_eq_zero
    (I := I) (M := M) g hRicciZero

theorem satisfiesIntrinsicEquationAt_iff_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    {cov : ConnectionFamily (I := I) (M := M)}
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (gdot : MetricTensorFamily (I := I) (M := M)) (t : ℝ)
    (hLevi : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g cov) :
    SatisfiesIntrinsicEquationAt (I := I) (M := M) g gdot t ↔
      SatisfiesEquationAt (I := I) (M := M) g cov hcov gdot t := by
  constructor <;> intro hEq <;> intro x u v
  · calc
      gdot t x u v = intrinsicRicciFlowRHS (I := I) (M := M) g t x u v := hEq x u v
      _ = ricciFlowRHS (I := I) (M := M) g cov hcov t x u v := by
        simpa using congrArg (fun F ↦ F t x u v)
          (intrinsicRicciFlowRHS_eq_ricciFlowRHS_of_isLeviCivita (I := I) (M := M) g hcov hLevi)
  · calc
      gdot t x u v = ricciFlowRHS (I := I) (M := M) g cov hcov t x u v := hEq x u v
      _ = intrinsicRicciFlowRHS (I := I) (M := M) g t x u v := by
        simpa using congrArg (fun F ↦ F t x u v)
          (intrinsicRicciFlowRHS_eq_ricciFlowRHS_of_isLeviCivita (I := I) (M := M) g hcov hLevi).symm

end ChosenLeviCivitaEquation

/-- A time-dependent metric and connection solve Ricci flow on `s` if the connection is Levi-Civita,
the metric has a time derivative on `s`, and that derivative satisfies `∂ₜ g = -2 Ric(g)` there. -/
def IsRicciFlowOn
    (g : MetricFamily (I := I) (M := M))
    (cov : ConnectionFamily (I := I) (M := M))
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (gdot : MetricTensorFamily (I := I) (M := M)) (s : Set ℝ) : Prop :=
  CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita (I := I) (M := M) g cov ∧
    HasTimeDerivativeOn (I := I) (M := M) g gdot s ∧
    ∀ ⦃t : ℝ⦄, t ∈ s →
      SatisfiesEquationAt (I := I) (M := M) g cov hcov gdot t

/-- Solving Ricci flow on a time set is independent of the chosen Levi-Civita family. -/
theorem isRicciFlowOn_iff_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    {cov cov' : ConnectionFamily (I := I) (M := M)}
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hcov' : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov' t) 1)
    (gdot : MetricTensorFamily (I := I) (M := M)) (s : Set ℝ)
    (hLevi : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g cov)
    (hLevi' : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g cov') :
    IsRicciFlowOn (I := I) (M := M) g cov hcov gdot s ↔
      IsRicciFlowOn (I := I) (M := M) g cov' hcov' gdot s := by
  constructor
  · intro hFlow
    refine ⟨hLevi', hFlow.2.1, ?_⟩
    intro t ht
    exact (satisfiesEquationAt_iff_of_isLeviCivita
      (I := I) (M := M) g hcov hcov' gdot t hLevi hLevi').1 (hFlow.2.2 ht)
  · intro hFlow
    refine ⟨hLevi, hFlow.2.1, ?_⟩
    intro t ht
    exact (satisfiesEquationAt_iff_of_isLeviCivita
      (I := I) (M := M) g hcov hcov' gdot t hLevi hLevi').2 (hFlow.2.2 ht)

/-- A Ricci-flow solution packages the evolving metric together with the Levi-Civita family and the
metric derivative appearing in the Ricci-flow equation. -/
structure Solution where
  /-- The time set on which the solution is defined. -/
  timeSet : Set ℝ
  /-- The evolving metric. -/
  metric : MetricFamily (I := I) (M := M)
  /-- A slicewise smooth connection family used to evaluate curvature. -/
  connection : ConnectionFamily (I := I) (M := M)
  /-- Smoothness of the connection family in the manifold variables at each time. -/
  hconnection : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (connection t) 1
  /-- The time derivative of the metric tensor. -/
  metricVelocity : MetricTensorFamily (I := I) (M := M)
  /-- The Ricci-flow equation on the time set. -/
  isRicciFlow : IsRicciFlowOn (I := I) (M := M)
    metric connection hconnection metricVelocity timeSet

lemma solution_isLeviCivita (sol : Solution) :
    CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) sol.metric sol.connection :=
  sol.isRicciFlow.1

lemma solution_hasTimeDerivativeOn (sol : Solution) :
    HasTimeDerivativeOn (I := I) (M := M) sol.metric sol.metricVelocity sol.timeSet :=
  sol.isRicciFlow.2.1

lemma solution_equation (sol : Solution) {t : ℝ} (ht : t ∈ sol.timeSet) :
    SatisfiesEquationAt (I := I) (M := M)
      sol.metric sol.connection sol.hconnection sol.metricVelocity t :=
  sol.isRicciFlow.2.2 ht

theorem Solution.metricVelocity_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (sol : Solution (E := E) (H := H) (I := I) (M := M))
    {t : ℝ} (ht : t ∈ sol.timeSet) (x : M) (u v : TM x) :
    sol.metricVelocity t x u v = 0 :=
  SatisfiesEquationAt.metricVelocity_eq_zero_of_subsingleton_tangent
    (I := I) (M := M) (solution_equation (I := I) (M := M) sol ht) x u v

/-- A Ricci-flow solution has zero velocity in any component where its Ricci tensor vanishes. -/
theorem Solution.metricVelocity_eq_zero_of_ricciTensor_eq_zero
    (sol : Solution (E := E) (H := H) (I := I) (M := M))
    {t : ℝ} (ht : t ∈ sol.timeSet) {x : M} {u v : TM x}
    (hRicciZero : ricciTensor (I := I) (M := M)
      sol.metric sol.connection sol.hconnection t x u v = 0) :
    sol.metricVelocity t x u v = 0 :=
  SatisfiesEquationAt.metricVelocity_eq_zero_of_ricciTensor_eq_zero
    (I := I) (M := M) (solution_equation (I := I) (M := M) sol ht) hRicciZero

/-- At a fixed time/component of a Ricci-flow solution, zero metric velocity is equivalent to
vanishing Ricci tensor. -/
theorem Solution.metricVelocity_eq_zero_iff_ricciTensor_eq_zero
    (sol : Solution (E := E) (H := H) (I := I) (M := M))
    {t : ℝ} (ht : t ∈ sol.timeSet) (x : M) (u v : TM x) :
    sol.metricVelocity t x u v = 0 ↔
      ricciTensor (I := I) (M := M)
        sol.metric sol.connection sol.hconnection t x u v = 0 := by
  constructor
  · intro hzero
    have heq :
        sol.metricVelocity t x u v =
          (-2 : ℝ) * ricciTensor (I := I) (M := M)
            sol.metric sol.connection sol.hconnection t x u v := by
      simpa [ricciFlowRHS] using solution_equation (I := I) (M := M) sol ht x u v
    linarith
  · intro hRicciZero
    exact sol.metricVelocity_eq_zero_of_ricciTensor_eq_zero
      (I := I) (M := M) ht hRicciZero

section ChosenLeviCivitaFlow

variable [SigmaCompactSpace M]

/-- A time-dependent metric solves Ricci flow on `s` when its tensor derivative satisfies the
intrinsic Ricci-flow equation written using the chosen smooth Levi-Civita family. -/
def IsIntrinsicRicciFlowOn
    (g : MetricFamily (I := I) (M := M))
    (gdot : MetricTensorFamily (I := I) (M := M)) (s : Set ℝ) : Prop :=
  HasTimeDerivativeOn (I := I) (M := M) g gdot s ∧
    ∀ ⦃t : ℝ⦄, t ∈ s →
      SatisfiesIntrinsicEquationAt (I := I) (M := M) g gdot t

theorem isIntrinsicRicciFlowOn_iff_of_isLeviCivita
    (g : MetricFamily (I := I) (M := M))
    {cov : ConnectionFamily (I := I) (M := M)}
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (gdot : MetricTensorFamily (I := I) (M := M)) (s : Set ℝ)
    (hLevi : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M) g cov) :
    IsIntrinsicRicciFlowOn (I := I) (M := M) g gdot s ↔
      IsRicciFlowOn (I := I) (M := M) g cov hcov gdot s := by
  constructor
  · intro hFlow
    refine ⟨hLevi, hFlow.1, ?_⟩
    intro t ht
    exact
      (satisfiesIntrinsicEquationAt_iff_of_isLeviCivita
        (I := I) (M := M) g hcov gdot t hLevi).1 (hFlow.2 ht)
  · intro hFlow
    refine ⟨hFlow.2.1, ?_⟩
    intro t ht
    exact
      (satisfiesIntrinsicEquationAt_iff_of_isLeviCivita
        (I := I) (M := M) g hcov gdot t hLevi).2 (hFlow.2.2 ht)

/-- An intrinsic Ricci-flow solution packages only the evolving metric and its tensor velocity; the
Levi-Civita family is recovered canonically from the chosen smooth Levi-Civita witness. -/
structure IntrinsicSolution where
  /-- The time set on which the solution is defined. -/
  timeSet : Set ℝ
  /-- The evolving metric. -/
  metric : MetricFamily (I := I) (M := M)
  /-- The time derivative of the metric tensor. -/
  metricVelocity : MetricTensorFamily (I := I) (M := M)
  /-- The intrinsic Ricci-flow equation on the time set. -/
  isRicciFlow : IsIntrinsicRicciFlowOn (I := I) (M := M)
    metric metricVelocity timeSet

lemma intrinsicSolution_hasTimeDerivativeOn (sol : IntrinsicSolution (E := E) (H := H) (I := I)
    (M := M)) :
    HasTimeDerivativeOn (I := I) (M := M)
      sol.metric sol.metricVelocity sol.timeSet :=
  sol.isRicciFlow.1

lemma intrinsicSolution_equation (sol : IntrinsicSolution (E := E) (H := H) (I := I) (M := M))
    {t : ℝ} (ht : t ∈ sol.timeSet) :
    SatisfiesIntrinsicEquationAt (I := I) (M := M)
      sol.metric sol.metricVelocity t :=
  sol.isRicciFlow.2 ht

theorem IntrinsicSolution.metricVelocity_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (sol : IntrinsicSolution (E := E) (H := H) (I := I) (M := M))
    {t : ℝ} (ht : t ∈ sol.timeSet) (x : M) (u v : TM x) :
    sol.metricVelocity t x u v = 0 :=
  SatisfiesIntrinsicEquationAt.metricVelocity_eq_zero_of_subsingleton_tangent
    (I := I) (M := M) (intrinsicSolution_equation (I := I) (M := M) sol ht) x u v

/-- An intrinsic Ricci-flow solution has zero velocity in any component where its intrinsic Ricci
tensor vanishes. -/
theorem IntrinsicSolution.metricVelocity_eq_zero_of_intrinsicRicciTensor_eq_zero
    (sol : IntrinsicSolution (E := E) (H := H) (I := I) (M := M))
    {t : ℝ} (ht : t ∈ sol.timeSet) {x : M} {u v : TM x}
    (hRicciZero : intrinsicRicciTensor (I := I) (M := M) sol.metric t x u v = 0) :
    sol.metricVelocity t x u v = 0 :=
  SatisfiesIntrinsicEquationAt.metricVelocity_eq_zero_of_intrinsicRicciTensor_eq_zero
    (I := I) (M := M) (intrinsicSolution_equation (I := I) (M := M) sol ht) hRicciZero

/-- At a fixed time/component of an intrinsic Ricci-flow solution, zero metric velocity is
equivalent to vanishing intrinsic Ricci tensor. -/
theorem IntrinsicSolution.metricVelocity_eq_zero_iff_intrinsicRicciTensor_eq_zero
    (sol : IntrinsicSolution (E := E) (H := H) (I := I) (M := M))
    {t : ℝ} (ht : t ∈ sol.timeSet) (x : M) (u v : TM x) :
    sol.metricVelocity t x u v = 0 ↔
      intrinsicRicciTensor (I := I) (M := M) sol.metric t x u v = 0 := by
  constructor
  · intro hzero
    have heq :
        sol.metricVelocity t x u v =
          (-2 : ℝ) * intrinsicRicciTensor (I := I) (M := M) sol.metric t x u v := by
      simpa [intrinsicRicciFlowRHS, ricciFlowRHS, intrinsicRicciTensor] using
        intrinsicSolution_equation (I := I) (M := M) sol ht x u v
    linarith
  · intro hRicciZero
    exact sol.metricVelocity_eq_zero_of_intrinsicRicciTensor_eq_zero
      (I := I) (M := M) ht hRicciZero

/-- Convert an intrinsic solution to the older connection-parametrized one using the chosen smooth
Levi-Civita family. -/
def IntrinsicSolution.toSolution
    (sol : IntrinsicSolution (E := E) (H := H) (I := I) (M := M)) :
    Solution (E := E) (H := H) (I := I) (M := M) where
  timeSet := sol.timeSet
  metric := sol.metric
  connection :=
    CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
      (I := I) (M := M) sol.metric
  hconnection :=
    CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
      (I := I) (M := M) sol.metric
  metricVelocity := sol.metricVelocity
  isRicciFlow :=
    (isIntrinsicRicciFlowOn_iff_of_isLeviCivita
      (I := I) (M := M) sol.metric
      (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_contMDiff
        (I := I) (M := M) sol.metric)
      sol.metricVelocity sol.timeSet
      (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_isLeviCivita
        (I := I) (M := M) sol.metric)).1
      sol.isRicciFlow

/-- Forget the auxiliary connection family from an ordinary solution by rewriting it intrinsically. -/
def Solution.toIntrinsicSolution
    (sol : Solution (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicSolution (E := E) (H := H) (I := I) (M := M) where
  timeSet := sol.timeSet
  metric := sol.metric
  metricVelocity := sol.metricVelocity
  isRicciFlow :=
    (isIntrinsicRicciFlowOn_iff_of_isLeviCivita
      (I := I) (M := M) sol.metric sol.hconnection sol.metricVelocity sol.timeSet
      (solution_isLeviCivita (sol := sol))).2
      sol.isRicciFlow

end ChosenLeviCivitaFlow

/-- Initial-value problem for Ricci flow at a time `t₀` with a `C^2` initial metric. -/
structure InitialValueProblem where
  /-- The initial time. -/
  initialTime : ℝ
  /-- The initial `C^2` Riemannian metric. -/
  initialMetric : Bundle.ContMDiffRiemannianMetric I 2 E TM

/-- A Ricci-flow solution matches the initial metric if the time-`t₀` metric tensor agrees
fibrewise with the prescribed initial metric. -/
def MatchesInitialMetric
    (sol : Solution (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) : Prop :=
  ∀ x : M, ∀ u v : TM x,
    metricTensor (I := I) (M := M) sol.metric ivp.initialTime x u v =
      ivp.initialMetric.inner x u v

/-- A local Ricci-flow solution is a Ricci-flow solution defined on an interval
`[t₀, T]` and matching the prescribed initial metric at `t₀`. -/
structure LocalSolution (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) where
  /-- Terminal time of the local solution interval. -/
  terminalTime : ℝ
  /-- The interval is genuinely forward in time. -/
  initial_lt_terminal : ivp.initialTime < terminalTime
  /-- The underlying Ricci-flow solution object. -/
  toSolution : Solution (E := E) (H := H) (I := I) (M := M)
  /-- The solution is defined on the whole interval `[t₀, T]`. -/
  interval_subset : Set.Icc ivp.initialTime terminalTime ⊆ toSolution.timeSet
  /-- The initial metric is matched at the initial time. -/
  matchesInitialMetric : MatchesInitialMetric (I := I) (M := M) toSolution ivp

/-- Restrict an ordinary local Ricci-flow solution to any shorter forward terminal time. -/
def LocalSolution.restrictTerminal
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {T : ℝ} (hT₀ : ivp.initialTime < T) (hT : T ≤ sol.terminalTime) :
    LocalSolution (E := E) (H := H) (I := I) (M := M) ivp where
  terminalTime := T
  initial_lt_terminal := hT₀
  toSolution := sol.toSolution
  interval_subset := by
    intro t ht
    exact sol.interval_subset ⟨ht.1, le_trans ht.2 hT⟩
  matchesInitialMetric := sol.matchesInitialMetric

@[simp] theorem LocalSolution.restrictTerminal_terminalTime
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {T : ℝ} (hT₀ : ivp.initialTime < T) (hT : T ≤ sol.terminalTime) :
    (sol.restrictTerminal hT₀ hT).terminalTime = T :=
  rfl

@[simp] theorem LocalSolution.restrictTerminal_toSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {T : ℝ} (hT₀ : ivp.initialTime < T) (hT : T ≤ sol.terminalTime) :
    (sol.restrictTerminal hT₀ hT).toSolution = sol.toSolution :=
  rfl

section ChosenLeviCivitaLocal

variable [SigmaCompactSpace M]

/-- The initial-metric matching condition for an intrinsic local solution. -/
def IntrinsicMatchesInitialMetric
    (sol : IntrinsicSolution (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) : Prop :=
  MatchesInitialMetric (I := I) (M := M) sol.toSolution ivp

/-- An intrinsic local Ricci-flow solution is a local solution package stated only in terms of the
evolving metric and its tensor velocity. -/
structure IntrinsicLocalSolution
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) where
  /-- Terminal time of the local solution interval. -/
  terminalTime : ℝ
  /-- The interval is genuinely forward in time. -/
  initial_lt_terminal : ivp.initialTime < terminalTime
  /-- The underlying intrinsic Ricci-flow solution object. -/
  toIntrinsicSolution : IntrinsicSolution (E := E) (H := H) (I := I) (M := M)
  /-- The solution is defined on the whole interval `[t₀, T]`. -/
  interval_subset : Set.Icc ivp.initialTime terminalTime ⊆ toIntrinsicSolution.timeSet
  /-- The initial metric is matched at the initial time. -/
  matchesInitialMetric : IntrinsicMatchesInitialMetric (I := I) (M := M) toIntrinsicSolution ivp

/-- Restrict an intrinsic local Ricci-flow solution to any shorter forward terminal time. -/
def IntrinsicLocalSolution.restrictTerminal
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {T : ℝ} (hT₀ : ivp.initialTime < T) (hT : T ≤ sol.terminalTime) :
    IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp where
  terminalTime := T
  initial_lt_terminal := hT₀
  toIntrinsicSolution := sol.toIntrinsicSolution
  interval_subset := by
    intro t ht
    exact sol.interval_subset ⟨ht.1, le_trans ht.2 hT⟩
  matchesInitialMetric := sol.matchesInitialMetric

@[simp] theorem IntrinsicLocalSolution.restrictTerminal_terminalTime
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {T : ℝ} (hT₀ : ivp.initialTime < T) (hT : T ≤ sol.terminalTime) :
    (sol.restrictTerminal hT₀ hT).terminalTime = T :=
  rfl

@[simp] theorem IntrinsicLocalSolution.restrictTerminal_toIntrinsicSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {T : ℝ} (hT₀ : ivp.initialTime < T) (hT : T ≤ sol.terminalTime) :
    (sol.restrictTerminal hT₀ hT).toIntrinsicSolution = sol.toIntrinsicSolution :=
  rfl

lemma intrinsicLocalSolution_initialTime_mem
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    ivp.initialTime ∈ sol.toIntrinsicSolution.timeSet :=
  sol.interval_subset ⟨le_rfl, le_of_lt sol.initial_lt_terminal⟩

lemma intrinsicLocalSolution_metric_eq_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol.toIntrinsicSolution.metric ivp.initialTime x u v =
      ivp.initialMetric.inner x u v :=
  sol.matchesInitialMetric x u v

/-- Convert an intrinsic local solution to the older connection-parametrized one. -/
def IntrinsicLocalSolution.toLocalSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    LocalSolution (E := E) (H := H) (I := I) (M := M) ivp where
  terminalTime := sol.terminalTime
  initial_lt_terminal := sol.initial_lt_terminal
  toSolution := sol.toIntrinsicSolution.toSolution
  interval_subset := sol.interval_subset
  matchesInitialMetric := sol.matchesInitialMetric

@[simp] theorem IntrinsicLocalSolution.restrictTerminal_toLocalSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {T : ℝ} (hT₀ : ivp.initialTime < T) (hT : T ≤ sol.terminalTime) :
    (sol.restrictTerminal hT₀ hT).toLocalSolution =
      sol.toLocalSolution.restrictTerminal hT₀ hT :=
  rfl

/-- Forget the auxiliary connection family from a local solution by rewriting it intrinsically. -/
def LocalSolution.toIntrinsicLocalSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp where
  terminalTime := sol.terminalTime
  initial_lt_terminal := sol.initial_lt_terminal
  toIntrinsicSolution := sol.toSolution.toIntrinsicSolution
  interval_subset := sol.interval_subset
  matchesInitialMetric := by
    change ∀ x : M, ∀ u v : TM x,
      metricTensor (I := I) (M := M) sol.toSolution.metric ivp.initialTime x u v =
        ivp.initialMetric.inner x u v
    exact sol.matchesInitialMetric

@[simp] theorem LocalSolution.restrictTerminal_toIntrinsicLocalSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {T : ℝ} (hT₀ : ivp.initialTime < T) (hT : T ≤ sol.terminalTime) :
    (sol.restrictTerminal hT₀ hT).toIntrinsicLocalSolution =
      sol.toIntrinsicLocalSolution.restrictTerminal hT₀ hT :=
  rfl

end ChosenLeviCivitaLocal

lemma localSolution_initialTime_mem
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    ivp.initialTime ∈ sol.toSolution.timeSet :=
  sol.interval_subset ⟨le_rfl, le_of_lt sol.initial_lt_terminal⟩

lemma localSolution_metric_eq_initial
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol.toSolution.metric ivp.initialTime x u v =
      ivp.initialMetric.inner x u v :=
  sol.matchesInitialMetric x u v

/-- Any two local solutions of the same initial-value problem have the same Levi-Civita connection
at the initial time. -/
theorem localSolution_initial_connection_eq
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.toSolution.connection ivp.initialTime σ x =
      sol₂.toSolution.connection ivp.initialTime σ x := by
  letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
  have hLevi₁ : (sol₁.toSolution.connection ivp.initialTime).IsLeviCivita := by
    exact
      (CovariantDerivative.isLeviCivita_iff_of_inner_eq
        (I := I) (E := E) (M := M) (cov := sol₁.toSolution.connection ivp.initialTime)
        (g := sol₁.toSolution.metric ivp.initialTime) (g' := ivp.initialMetric)
        (fun y u v ↦ localSolution_metric_eq_initial (I := I) (M := M) sol₁ y u v)).mp
        (solution_isLeviCivita (sol := sol₁.toSolution) ivp.initialTime)
  have hLevi₂ : (sol₂.toSolution.connection ivp.initialTime).IsLeviCivita := by
    exact
      (CovariantDerivative.isLeviCivita_iff_of_inner_eq
        (I := I) (E := E) (M := M) (cov := sol₂.toSolution.connection ivp.initialTime)
        (g := sol₂.toSolution.metric ivp.initialTime) (g' := ivp.initialMetric)
        (fun y u v ↦ localSolution_metric_eq_initial (I := I) (M := M) sol₂ y u v)).mp
        (solution_isLeviCivita (sol := sol₂.toSolution) ivp.initialTime)
  exact
    CovariantDerivative.eq_of_isLeviCivita
      (I := I) (E := E) (M := M)
      (cov := sol₁.toSolution.connection ivp.initialTime)
      (cov' := sol₂.toSolution.connection ivp.initialTime) hLevi₁ hLevi₂ hσ

/-- On a local Ricci-flow solution, vanishing metric velocity on the interval forces the Ricci
tensor to vanish there as well. -/
theorem localSolution_ricciTensor_eq_zero_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol.toSolution.metricVelocity t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    ricciTensor (I := I) (M := M)
      sol.toSolution.metric sol.toSolution.connection sol.toSolution.hconnection t x u v = 0 := by
  have htTime : t ∈ sol.toSolution.timeSet := sol.interval_subset ht
  have htEq :
      sol.toSolution.metricVelocity t x u v =
        (-2 : ℝ) *
          ricciTensor (I := I) (M := M)
            sol.toSolution.metric sol.toSolution.connection sol.toSolution.hconnection t x u v := by
    simpa [ricciFlowRHS] using solution_equation (sol := sol.toSolution) htTime x u v
  linarith [hzero t ht x u v, htEq]

/-- A local Ricci-flow solution has zero velocity in any interval component where its Ricci tensor
vanishes. -/
theorem localSolution_metricVelocity_eq_zero_of_ricciTensor_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    {x : M} {u v : TM x}
    (hRicciZero : ricciTensor (I := I) (M := M)
      sol.toSolution.metric sol.toSolution.connection sol.toSolution.hconnection t x u v = 0) :
    sol.toSolution.metricVelocity t x u v = 0 :=
  sol.toSolution.metricVelocity_eq_zero_of_ricciTensor_eq_zero
    (I := I) (M := M) (sol.interval_subset ht) hRicciZero

/-- On the local interval, zero metric velocity is equivalent to vanishing Ricci tensor at each
fixed component. -/
theorem localSolution_metricVelocity_eq_zero_iff_ricciTensor_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    sol.toSolution.metricVelocity t x u v = 0 ↔
      ricciTensor (I := I) (M := M)
        sol.toSolution.metric sol.toSolution.connection sol.toSolution.hconnection t x u v = 0 :=
  sol.toSolution.metricVelocity_eq_zero_iff_ricciTensor_eq_zero
    (I := I) (M := M) (sol.interval_subset ht) x u v

/-- Along a local Ricci-flow solution, zero metric velocity on the whole interval is equivalent to
vanishing Ricci tensor on the whole interval. -/
theorem localSolution_zero_velocity_iff_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    (∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol.toSolution.metricVelocity t x u v = 0) ↔
      (∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
        ricciTensor (I := I) (M := M)
          sol.toSolution.metric sol.toSolution.connection sol.toSolution.hconnection t x u v = 0) := by
  constructor
  · intro hzero t ht x u v
    exact localSolution_ricciTensor_eq_zero_of_zero_velocity
      (I := I) (M := M) sol hzero ht x u v
  · intro hRicciZero t ht x u v
    have htTime : t ∈ sol.toSolution.timeSet := sol.interval_subset ht
    calc
      sol.toSolution.metricVelocity t x u v
          = (-2 : ℝ) *
              ricciTensor (I := I) (M := M)
                sol.toSolution.metric sol.toSolution.connection sol.toSolution.hconnection t x u v := by
              simpa [ricciFlowRHS] using solution_equation (sol := sol.toSolution) htTime x u v
      _ = 0 := by simp [hRicciZero t ht x u v]

/-- If the metric velocity vanishes on the whole local-solution interval, then the metric tensor
stays equal to the initial metric tensor on that interval. -/
theorem localSolution_metric_eq_initial_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol.toSolution.metricVelocity t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol.toSolution.metric t x u v =
      ivp.initialMetric.inner x u v := by
  let f : ℝ → ℝ := fun s ↦ metricTensor (I := I) (M := M) sol.toSolution.metric s x u v
  let g : ℝ → ℝ := fun _ ↦ ivp.initialMetric.inner x u v
  have hderivf :
      ∀ y ∈ Set.Ico ivp.initialTime sol.terminalTime, HasDerivWithinAt f 0 (Set.Ici y) y := by
    intro y hy
    have hyIcc : y ∈ Set.Icc ivp.initialTime sol.terminalTime := Set.mem_Icc_of_Ico hy
    have hyTime : y ∈ sol.toSolution.timeSet := sol.interval_subset hyIcc
    have hyDeriv :
        HasDerivAt (fun s ↦ metricTensor (I := I) (M := M) sol.toSolution.metric s x u v) 0 y := by
      simpa [hzero y hyIcc x u v] using
        (solution_hasTimeDerivativeOn (sol := sol.toSolution) hyTime x u v)
    simpa [f] using hyDeriv.hasDerivWithinAt
  have hderivg :
      ∀ y ∈ Set.Ico ivp.initialTime sol.terminalTime, HasDerivWithinAt g 0 (Set.Ici y) y := by
    intro y hy
    simpa [g] using
      (hasDerivWithinAt_const (x := y) (s := Set.Ici y) (c := ivp.initialMetric.inner x u v) :
        HasDerivWithinAt (fun _ : ℝ ↦ ivp.initialMetric.inner x u v) 0 (Set.Ici y) y)
  have hfdiff : DifferentiableOn ℝ f (Set.Icc ivp.initialTime sol.terminalTime) := by
    intro y hy
    have hyTime : y ∈ sol.toSolution.timeSet := sol.interval_subset hy
    have hyDeriv :
        HasDerivAt (fun s ↦ metricTensor (I := I) (M := M) sol.toSolution.metric s x u v)
          (sol.toSolution.metricVelocity y x u v) y :=
      solution_hasTimeDerivativeOn (sol := sol.toSolution) hyTime x u v
    simpa [f] using hyDeriv.differentiableAt.differentiableWithinAt
  have hi : f ivp.initialTime = g ivp.initialTime := by
    simpa [f, g] using localSolution_metric_eq_initial (sol := sol) x u v
  exact (eq_of_has_deriv_right_eq hderivf hderivg hfdiff.continuousOn
    (continuousOn_const : ContinuousOn g (Set.Icc ivp.initialTime sol.terminalTime)) hi) t ht

/-- If the metric velocity vanishes on the whole local-solution interval, then the Levi-Civita
connection stays equal to the initial one there. -/
theorem localSolution_connection_eq_initial_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol.toSolution.metricVelocity t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol.toSolution.connection t σ x =
      sol.toSolution.connection ivp.initialTime σ x := by
  letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
  have hLevi_t : (sol.toSolution.connection t).IsLeviCivita := by
    exact
      (CovariantDerivative.isLeviCivita_iff_of_inner_eq
        (I := I) (E := E) (M := M) (cov := sol.toSolution.connection t)
        (g := sol.toSolution.metric t) (g' := ivp.initialMetric)
        (fun y u v ↦
          localSolution_metric_eq_initial_of_zero_velocity
            (I := I) (M := M) sol hzero ht y u v)).mp
        (solution_isLeviCivita (sol := sol.toSolution) t)
  have hLevi₀ : (sol.toSolution.connection ivp.initialTime).IsLeviCivita := by
    exact
      (CovariantDerivative.isLeviCivita_iff_of_inner_eq
        (I := I) (E := E) (M := M) (cov := sol.toSolution.connection ivp.initialTime)
        (g := sol.toSolution.metric ivp.initialTime) (g' := ivp.initialMetric)
        (fun y u v ↦ localSolution_metric_eq_initial (I := I) (M := M) sol y u v)).mp
        (solution_isLeviCivita (sol := sol.toSolution) ivp.initialTime)
  exact
    CovariantDerivative.eq_of_isLeviCivita
      (I := I) (E := E) (M := M)
      (cov := sol.toSolution.connection t)
      (cov' := sol.toSolution.connection ivp.initialTime) hLevi_t hLevi₀ hσ

/-- Two local solutions with zero metric velocity on their intervals have the same evolving metric
tensor on the common initial interval. -/
theorem localSolution_unique_metric_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero₁ : ∀ t ∈ Set.Icc ivp.initialTime sol₁.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol₁.toSolution.metricVelocity t x u v = 0)
    (hzero₂ : ∀ t ∈ Set.Icc ivp.initialTime sol₂.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol₂.toSolution.metricVelocity t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol₁.toSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.toSolution.metric t x u v := by
  have ht₁ : t ∈ Set.Icc ivp.initialTime sol₁.terminalTime :=
    ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩
  have ht₂ : t ∈ Set.Icc ivp.initialTime sol₂.terminalTime :=
    ⟨ht.1, le_trans ht.2 (min_le_right _ _)⟩
  rw [localSolution_metric_eq_initial_of_zero_velocity (I := I) (M := M) sol₁ hzero₁ ht₁ x u v,
    localSolution_metric_eq_initial_of_zero_velocity (I := I) (M := M) sol₂ hzero₂ ht₂ x u v]

/-- Two local solutions with zero metric velocity on their intervals have the same Levi-Civita
connection on the common initial interval. -/
theorem localSolution_unique_connection_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero₁ : ∀ t ∈ Set.Icc ivp.initialTime sol₁.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol₁.toSolution.metricVelocity t x u v = 0)
    (hzero₂ : ∀ t ∈ Set.Icc ivp.initialTime sol₂.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol₂.toSolution.metricVelocity t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.toSolution.connection t σ x = sol₂.toSolution.connection t σ x := by
  have ht₁ : t ∈ Set.Icc ivp.initialTime sol₁.terminalTime :=
    ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩
  have ht₂ : t ∈ Set.Icc ivp.initialTime sol₂.terminalTime :=
    ⟨ht.1, le_trans ht.2 (min_le_right _ _)⟩
  rw [localSolution_connection_eq_initial_of_zero_velocity
      (I := I) (M := M) sol₁ hzero₁ ht₁ hσ,
    localSolution_connection_eq_initial_of_zero_velocity
      (I := I) (M := M) sol₂ hzero₂ ht₂ hσ]
  exact localSolution_initial_connection_eq (I := I) (M := M) sol₁ sol₂ hσ

/-- On zero-dimensional tangent fibers, every local Ricci-flow solution has zero metric velocity on
its local interval. -/
theorem localSolution_metricVelocity_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    sol.toSolution.metricVelocity t x u v = 0 :=
  Solution.metricVelocity_eq_zero_of_subsingleton_tangent
    (I := I) (M := M) sol.toSolution (sol.interval_subset ht) x u v

/-- On zero-dimensional tangent fibers, every local Ricci-flow solution is stationary in metric
tensor components on its local interval. -/
theorem localSolution_metric_eq_initial_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol.toSolution.metric t x u v =
      ivp.initialMetric.inner x u v := by
  refine localSolution_metric_eq_initial_of_zero_velocity (I := I) (M := M) sol ?_ ht x u v
  intro τ hτ y a b
  exact localSolution_metricVelocity_eq_zero_of_subsingleton_tangent
    (I := I) (M := M) sol hτ y a b

/-- On zero-dimensional tangent fibers, any two local Ricci-flow solutions have the same metric
tensor on every common time. -/
theorem localSolution_unique_metric_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (_ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol₁.toSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.toSolution.metric t x u v := by
  rw [metricTensor_eq_zero_of_subsingleton_tangent
      (I := I) (M := M) sol₁.toSolution.metric t x u v,
    metricTensor_eq_zero_of_subsingleton_tangent
      (I := I) (M := M) sol₂.toSolution.metric t x u v]

/-- On zero-dimensional tangent fibers, all local-solution connection values agree. -/
theorem localSolution_connection_eq_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (t₁ t₂ : ℝ) {x : M} {σ : Π y : M, TM y} :
    sol₁.toSolution.connection t₁ σ x = sol₂.toSolution.connection t₂ σ x :=
  Subsingleton.elim _ _

/-- On zero-dimensional tangent fibers, every local Ricci-flow solution is stationary in connection
values on its local interval. -/
theorem localSolution_connection_eq_initial_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (_ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    {x : M} {σ : Π y : M, TM y} :
    sol.toSolution.connection t σ x =
      sol.toSolution.connection ivp.initialTime σ x :=
  localSolution_connection_eq_of_subsingleton_tangent
    (I := I) (M := M) sol sol t ivp.initialTime

/-- On zero-dimensional tangent fibers, any two local Ricci-flow solutions have the same connection
values on every common time. -/
theorem localSolution_unique_connection_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (_ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} :
    sol₁.toSolution.connection t σ x = sol₂.toSolution.connection t σ x :=
  localSolution_connection_eq_of_subsingleton_tangent
    (I := I) (M := M) sol₁ sol₂ t t

/-- If the Ricci tensor vanishes on the whole local-solution interval, then the metric tensor stays
equal to the initial metric tensor there. -/
theorem localSolution_metric_eq_initial_of_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hRicciZero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      ricciTensor (I := I) (M := M)
        sol.toSolution.metric sol.toSolution.connection sol.toSolution.hconnection t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol.toSolution.metric t x u v =
      ivp.initialMetric.inner x u v := by
  refine localSolution_metric_eq_initial_of_zero_velocity (I := I) (M := M) sol ?_ ht x u v
  exact (localSolution_zero_velocity_iff_ricciTensor_zero (I := I) (M := M) sol).2 hRicciZero

/-- If the Ricci tensor vanishes on the whole local-solution interval, then the Levi-Civita
connection stays equal to the initial one there. -/
theorem localSolution_connection_eq_initial_of_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hRicciZero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      ricciTensor (I := I) (M := M)
        sol.toSolution.metric sol.toSolution.connection sol.toSolution.hconnection t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol.toSolution.connection t σ x =
      sol.toSolution.connection ivp.initialTime σ x := by
  refine localSolution_connection_eq_initial_of_zero_velocity (I := I) (M := M) sol ?_ ht hσ
  exact (localSolution_zero_velocity_iff_ricciTensor_zero (I := I) (M := M) sol).2 hRicciZero

/-- Two local solutions whose Ricci tensors vanish on their intervals have the same evolving metric
tensor on the common initial interval. -/
theorem localSolution_unique_metric_of_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hRicciZero₁ : ∀ t ∈ Set.Icc ivp.initialTime sol₁.terminalTime, ∀ x : M, ∀ u v : TM x,
      ricciTensor (I := I) (M := M)
        sol₁.toSolution.metric sol₁.toSolution.connection sol₁.toSolution.hconnection t x u v = 0)
    (hRicciZero₂ : ∀ t ∈ Set.Icc ivp.initialTime sol₂.terminalTime, ∀ x : M, ∀ u v : TM x,
      ricciTensor (I := I) (M := M)
        sol₂.toSolution.metric sol₂.toSolution.connection sol₂.toSolution.hconnection t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol₁.toSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.toSolution.metric t x u v := by
  refine localSolution_unique_metric_of_zero_velocity (I := I) (M := M) sol₁ sol₂ ?_ ?_ ht x u v
  · exact (localSolution_zero_velocity_iff_ricciTensor_zero (I := I) (M := M) sol₁).2 hRicciZero₁
  · exact (localSolution_zero_velocity_iff_ricciTensor_zero (I := I) (M := M) sol₂).2 hRicciZero₂

/-- Two local solutions whose Ricci tensors vanish on their intervals have the same Levi-Civita
connection on the common initial interval. -/
theorem localSolution_unique_connection_of_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hRicciZero₁ : ∀ t ∈ Set.Icc ivp.initialTime sol₁.terminalTime, ∀ x : M, ∀ u v : TM x,
      ricciTensor (I := I) (M := M)
        sol₁.toSolution.metric sol₁.toSolution.connection sol₁.toSolution.hconnection t x u v = 0)
    (hRicciZero₂ : ∀ t ∈ Set.Icc ivp.initialTime sol₂.terminalTime, ∀ x : M, ∀ u v : TM x,
      ricciTensor (I := I) (M := M)
        sol₂.toSolution.metric sol₂.toSolution.connection sol₂.toSolution.hconnection t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.toSolution.connection t σ x = sol₂.toSolution.connection t σ x := by
  refine localSolution_unique_connection_of_zero_velocity (I := I) (M := M) sol₁ sol₂ ?_ ?_ ht hσ
  · exact (localSolution_zero_velocity_iff_ricciTensor_zero (I := I) (M := M) sol₁).2 hRicciZero₁
  · exact (localSolution_zero_velocity_iff_ricciTensor_zero (I := I) (M := M) sol₂).2 hRicciZero₂

/-- If two local solutions have the same metric tensor at a common time, then their Levi-Civita
connections agree at that time. -/
theorem localSolution_connection_eq_of_metric_eq
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ}
    (ht₁ : t ∈ sol₁.toSolution.timeSet) (ht₂ : t ∈ sol₂.toSolution.timeSet)
    (hmetric : ∀ x : M, ∀ u v : TM x,
      metricTensor (I := I) (M := M) sol₁.toSolution.metric t x u v =
        metricTensor (I := I) (M := M) sol₂.toSolution.metric t x u v)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.toSolution.connection t σ x = sol₂.toSolution.connection t σ x := by
  letI : Bundle.RiemannianBundle TM := ⟨(sol₁.toSolution.metric t).toRiemannianMetric⟩
  have hLevi₁ : (sol₁.toSolution.connection t).IsLeviCivita := by
    exact solution_isLeviCivita (sol := sol₁.toSolution) t
  have hLevi₂ : (sol₂.toSolution.connection t).IsLeviCivita := by
    exact
      (CovariantDerivative.isLeviCivita_iff_of_inner_eq
        (I := I) (E := E) (M := M) (cov := sol₂.toSolution.connection t)
        (g := sol₂.toSolution.metric t) (g' := sol₁.toSolution.metric t)
        (fun y u v ↦ (hmetric y u v).symm)).mp
        (solution_isLeviCivita (sol := sol₂.toSolution) t)
  exact
    CovariantDerivative.eq_of_isLeviCivita
      (I := I) (E := E) (M := M)
      (cov := sol₁.toSolution.connection t)
      (cov' := sol₂.toSolution.connection t) hLevi₁ hLevi₂ hσ

section IntrinsicLocalSolutionWrappers

variable [SigmaCompactSpace M]

/-- Any two intrinsic local solutions of the same initial-value problem have the same canonical
Levi-Civita connection at the initial time. -/
theorem intrinsicLocalSolution_initial_connection_eq
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.toIntrinsicSolution.toSolution.connection ivp.initialTime σ x =
      sol₂.toIntrinsicSolution.toSolution.connection ivp.initialTime σ x := by
  change sol₁.toLocalSolution.toSolution.connection ivp.initialTime σ x =
    sol₂.toLocalSolution.toSolution.connection ivp.initialTime σ x
  exact localSolution_initial_connection_eq
    (I := I) (M := M) sol₁.toLocalSolution sol₂.toLocalSolution hσ

/-- On an intrinsic local Ricci-flow solution, vanishing metric velocity on the interval forces the
intrinsic Ricci tensor to vanish there as well. -/
theorem intrinsicLocalSolution_ricciTensor_eq_zero_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol.toIntrinsicSolution.metricVelocity t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v = 0 := by
  simpa [IntrinsicLocalSolution.toLocalSolution, IntrinsicSolution.toSolution, intrinsicRicciTensor]
    using localSolution_ricciTensor_eq_zero_of_zero_velocity
      (I := I) (M := M) sol.toLocalSolution hzero ht x u v

/-- An intrinsic local Ricci-flow solution has zero velocity in any interval component where its
intrinsic Ricci tensor vanishes. -/
theorem intrinsicLocalSolution_metricVelocity_eq_zero_of_intrinsicRicciTensor_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    {x : M} {u v : TM x}
    (hRicciZero : intrinsicRicciTensor (I := I) (M := M)
      sol.toIntrinsicSolution.metric t x u v = 0) :
    sol.toIntrinsicSolution.metricVelocity t x u v = 0 :=
  sol.toIntrinsicSolution.metricVelocity_eq_zero_of_intrinsicRicciTensor_eq_zero
    (I := I) (M := M) (sol.interval_subset ht) hRicciZero

/-- On the intrinsic local interval, zero metric velocity is equivalent to vanishing intrinsic Ricci
tensor at each fixed component. -/
theorem intrinsicLocalSolution_metricVelocity_eq_zero_iff_intrinsicRicciTensor_eq_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    sol.toIntrinsicSolution.metricVelocity t x u v = 0 ↔
      intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v = 0 :=
  sol.toIntrinsicSolution.metricVelocity_eq_zero_iff_intrinsicRicciTensor_eq_zero
    (I := I) (M := M) (sol.interval_subset ht) x u v

/-- Along an intrinsic local Ricci-flow solution, zero metric velocity on the whole interval is
equivalent to vanishing intrinsic Ricci tensor on the whole interval. -/
theorem intrinsicLocalSolution_zero_velocity_iff_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :
    (∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol.toIntrinsicSolution.metricVelocity t x u v = 0) ↔
      (∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v = 0) := by
  constructor
  · intro hzero t ht x u v
    exact intrinsicLocalSolution_ricciTensor_eq_zero_of_zero_velocity
      (I := I) (M := M) sol hzero ht x u v
  · intro hRicciZero
    have hRicciZero' :
        ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
          ricciTensor (I := I) (M := M)
            sol.toLocalSolution.toSolution.metric
            sol.toLocalSolution.toSolution.connection
            sol.toLocalSolution.toSolution.hconnection t x u v = 0 := by
      intro t ht x u v
      simpa [IntrinsicLocalSolution.toLocalSolution, IntrinsicSolution.toSolution, intrinsicRicciTensor]
        using hRicciZero t ht x u v
    change ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol.toLocalSolution.toSolution.metricVelocity t x u v = 0
    exact (localSolution_zero_velocity_iff_ricciTensor_zero
      (I := I) (M := M) sol.toLocalSolution).2 hRicciZero'

/-- If the metric velocity vanishes on the whole intrinsic local-solution interval, then the metric
tensor stays equal to the initial metric tensor on that interval. -/
theorem intrinsicLocalSolution_metric_eq_initial_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol.toIntrinsicSolution.metricVelocity t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v =
      ivp.initialMetric.inner x u v := by
  simpa [IntrinsicLocalSolution.toLocalSolution, IntrinsicSolution.toSolution] using
    localSolution_metric_eq_initial_of_zero_velocity
      (I := I) (M := M) sol.toLocalSolution hzero ht x u v

/-- If the metric velocity vanishes on the whole intrinsic local-solution interval, then the
canonical Levi-Civita connection stays equal to the initial one there. -/
theorem intrinsicLocalSolution_connection_eq_initial_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol.toIntrinsicSolution.metricVelocity t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol.toIntrinsicSolution.toSolution.connection t σ x =
      sol.toIntrinsicSolution.toSolution.connection ivp.initialTime σ x := by
  simpa [IntrinsicLocalSolution.toLocalSolution, IntrinsicSolution.toSolution] using
    localSolution_connection_eq_initial_of_zero_velocity
      (I := I) (M := M) sol.toLocalSolution hzero ht hσ

/-- Two intrinsic local solutions with zero metric velocity on their intervals have the same
evolving metric tensor on the common initial interval. -/
theorem intrinsicLocalSolution_unique_metric_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero₁ : ∀ t ∈ Set.Icc ivp.initialTime sol₁.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol₁.toIntrinsicSolution.metricVelocity t x u v = 0)
    (hzero₂ : ∀ t ∈ Set.Icc ivp.initialTime sol₂.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol₂.toIntrinsicSolution.metricVelocity t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol₁.toIntrinsicSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.toIntrinsicSolution.metric t x u v := by
  simpa [IntrinsicLocalSolution.toLocalSolution, IntrinsicSolution.toSolution] using
    localSolution_unique_metric_of_zero_velocity
      (I := I) (M := M) sol₁.toLocalSolution sol₂.toLocalSolution hzero₁ hzero₂ ht x u v

/-- Two intrinsic local solutions with zero metric velocity on their intervals have the same
canonical Levi-Civita connection on the common initial interval. -/
theorem intrinsicLocalSolution_unique_connection_of_zero_velocity
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero₁ : ∀ t ∈ Set.Icc ivp.initialTime sol₁.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol₁.toIntrinsicSolution.metricVelocity t x u v = 0)
    (hzero₂ : ∀ t ∈ Set.Icc ivp.initialTime sol₂.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol₂.toIntrinsicSolution.metricVelocity t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.toIntrinsicSolution.toSolution.connection t σ x =
      sol₂.toIntrinsicSolution.toSolution.connection t σ x := by
  simpa [IntrinsicLocalSolution.toLocalSolution, IntrinsicSolution.toSolution] using
    localSolution_unique_connection_of_zero_velocity
      (I := I) (M := M) sol₁.toLocalSolution sol₂.toLocalSolution hzero₁ hzero₂ ht hσ

/-- On zero-dimensional tangent fibers, every intrinsic local Ricci-flow solution has zero metric
velocity on its local interval. -/
theorem intrinsicLocalSolution_metricVelocity_eq_zero_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    sol.toIntrinsicSolution.metricVelocity t x u v = 0 :=
  IntrinsicSolution.metricVelocity_eq_zero_of_subsingleton_tangent
    (I := I) (M := M) sol.toIntrinsicSolution (sol.interval_subset ht) x u v

/-- On zero-dimensional tangent fibers, every intrinsic local Ricci-flow solution is stationary in
metric tensor components on its local interval. -/
theorem intrinsicLocalSolution_metric_eq_initial_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v =
      ivp.initialMetric.inner x u v := by
  refine intrinsicLocalSolution_metric_eq_initial_of_zero_velocity (I := I) (M := M) sol ?_ ht x u v
  intro τ hτ y a b
  exact intrinsicLocalSolution_metricVelocity_eq_zero_of_subsingleton_tangent
    (I := I) (M := M) sol hτ y a b

/-- On zero-dimensional tangent fibers, any two intrinsic local Ricci-flow solutions have the same
metric tensor on every common time. -/
theorem intrinsicLocalSolution_unique_metric_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (_ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol₁.toIntrinsicSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.toIntrinsicSolution.metric t x u v := by
  rw [metricTensor_eq_zero_of_subsingleton_tangent
      (I := I) (M := M) sol₁.toIntrinsicSolution.metric t x u v,
    metricTensor_eq_zero_of_subsingleton_tangent
      (I := I) (M := M) sol₂.toIntrinsicSolution.metric t x u v]

/-- On zero-dimensional tangent fibers, all intrinsic local-solution canonical connection values
agree. -/
theorem intrinsicLocalSolution_connection_eq_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (t₁ t₂ : ℝ) {x : M} {σ : Π y : M, TM y} :
    sol₁.toIntrinsicSolution.toSolution.connection t₁ σ x =
      sol₂.toIntrinsicSolution.toSolution.connection t₂ σ x :=
  Subsingleton.elim _ _

/-- On zero-dimensional tangent fibers, every intrinsic local Ricci-flow solution is stationary in
canonical connection values on its local interval. -/
theorem intrinsicLocalSolution_connection_eq_initial_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (_ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    {x : M} {σ : Π y : M, TM y} :
    sol.toIntrinsicSolution.toSolution.connection t σ x =
      sol.toIntrinsicSolution.toSolution.connection ivp.initialTime σ x :=
  intrinsicLocalSolution_connection_eq_of_subsingleton_tangent
    (I := I) (M := M) sol sol t ivp.initialTime

/-- On zero-dimensional tangent fibers, any two intrinsic local Ricci-flow solutions have the same
canonical connection values on every common time. -/
theorem intrinsicLocalSolution_unique_connection_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (_ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} :
    sol₁.toIntrinsicSolution.toSolution.connection t σ x =
      sol₂.toIntrinsicSolution.toSolution.connection t σ x :=
  intrinsicLocalSolution_connection_eq_of_subsingleton_tangent
    (I := I) (M := M) sol₁ sol₂ t t

/-- If the intrinsic Ricci tensor vanishes on the whole local-solution interval, then the metric
tensor stays equal to the initial metric tensor there. -/
theorem intrinsicLocalSolution_metric_eq_initial_of_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hRicciZero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v =
      ivp.initialMetric.inner x u v := by
  have hRicciZero' :=
    (intrinsicLocalSolution_zero_velocity_iff_ricciTensor_zero
      (I := I) (M := M) sol).2 hRicciZero
  exact intrinsicLocalSolution_metric_eq_initial_of_zero_velocity
    (I := I) (M := M) sol hRicciZero' ht x u v

/-- If the intrinsic Ricci tensor vanishes on the whole local-solution interval, then the canonical
Levi-Civita connection stays equal to the initial one there. -/
theorem intrinsicLocalSolution_connection_eq_initial_of_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hRicciZero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime sol.terminalTime)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol.toIntrinsicSolution.toSolution.connection t σ x =
      sol.toIntrinsicSolution.toSolution.connection ivp.initialTime σ x := by
  have hRicciZero' :=
    (intrinsicLocalSolution_zero_velocity_iff_ricciTensor_zero
      (I := I) (M := M) sol).2 hRicciZero
  exact intrinsicLocalSolution_connection_eq_initial_of_zero_velocity
    (I := I) (M := M) sol hRicciZero' ht hσ

/-- Two intrinsic local solutions whose intrinsic Ricci tensors vanish on their intervals have the
same evolving metric tensor on the common initial interval. -/
theorem intrinsicLocalSolution_unique_metric_of_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hRicciZero₁ : ∀ t ∈ Set.Icc ivp.initialTime sol₁.terminalTime, ∀ x : M, ∀ u v : TM x,
      intrinsicRicciTensor (I := I) (M := M) sol₁.toIntrinsicSolution.metric t x u v = 0)
    (hRicciZero₂ : ∀ t ∈ Set.Icc ivp.initialTime sol₂.terminalTime, ∀ x : M, ∀ u v : TM x,
      intrinsicRicciTensor (I := I) (M := M) sol₂.toIntrinsicSolution.metric t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol₁.toIntrinsicSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.toIntrinsicSolution.metric t x u v := by
  exact intrinsicLocalSolution_unique_metric_of_zero_velocity
    (I := I) (M := M) sol₁ sol₂
    ((intrinsicLocalSolution_zero_velocity_iff_ricciTensor_zero
      (I := I) (M := M) sol₁).2 hRicciZero₁)
    ((intrinsicLocalSolution_zero_velocity_iff_ricciTensor_zero
      (I := I) (M := M) sol₂).2 hRicciZero₂)
    ht x u v

/-- Two intrinsic local solutions whose intrinsic Ricci tensors vanish on their intervals have the
same canonical Levi-Civita connection on the common initial interval. -/
theorem intrinsicLocalSolution_unique_connection_of_ricciTensor_zero
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hRicciZero₁ : ∀ t ∈ Set.Icc ivp.initialTime sol₁.terminalTime, ∀ x : M, ∀ u v : TM x,
      intrinsicRicciTensor (I := I) (M := M) sol₁.toIntrinsicSolution.metric t x u v = 0)
    (hRicciZero₂ : ∀ t ∈ Set.Icc ivp.initialTime sol₂.terminalTime, ∀ x : M, ∀ u v : TM x,
      intrinsicRicciTensor (I := I) (M := M) sol₂.toIntrinsicSolution.metric t x u v = 0)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.toIntrinsicSolution.toSolution.connection t σ x =
      sol₂.toIntrinsicSolution.toSolution.connection t σ x := by
  exact intrinsicLocalSolution_unique_connection_of_zero_velocity
    (I := I) (M := M) sol₁ sol₂
    ((intrinsicLocalSolution_zero_velocity_iff_ricciTensor_zero
      (I := I) (M := M) sol₁).2 hRicciZero₁)
    ((intrinsicLocalSolution_zero_velocity_iff_ricciTensor_zero
      (I := I) (M := M) sol₂).2 hRicciZero₂)
    ht hσ

/-- If two intrinsic local solutions have the same metric tensor at a common time, then their
canonical Levi-Civita connections agree at that time. -/
theorem intrinsicLocalSolution_connection_eq_of_metric_eq
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (sol₁ sol₂ : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ}
    (ht₁ : t ∈ sol₁.toIntrinsicSolution.timeSet) (ht₂ : t ∈ sol₂.toIntrinsicSolution.timeSet)
    (hmetric : ∀ x : M, ∀ u v : TM x,
      metricTensor (I := I) (M := M) sol₁.toIntrinsicSolution.metric t x u v =
        metricTensor (I := I) (M := M) sol₂.toIntrinsicSolution.metric t x u v)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.toIntrinsicSolution.toSolution.connection t σ x =
      sol₂.toIntrinsicSolution.toSolution.connection t σ x := by
  simpa [IntrinsicLocalSolution.toLocalSolution, IntrinsicSolution.toSolution] using
    localSolution_connection_eq_of_metric_eq
      (I := I) (M := M) sol₁.toLocalSolution sol₂.toLocalSolution ht₁ ht₂ hmetric hσ

end IntrinsicLocalSolutionWrappers

section Stationary

/-- A constant metric family has zero time derivative. -/
lemma hasTimeDerivativeAt_const_zero
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM) (t : ℝ) :
    HasTimeDerivativeAt (I := I) (M := M)
      (CovariantDerivative.TimeDependentRiemannianMetric.const (I := I) (M := M) g₀) 0 t := by
  intro x u v
  simpa [metricTensor, CovariantDerivative.TimeDependentRiemannianMetric.const_apply] using
    (hasDerivAt_const (x := t) (c := g₀.inner x u v) :
      HasDerivAt (fun _ : ℝ ↦ g₀.inner x u v) 0 t)

/-- A constant metric family has zero time derivative on every time set. -/
lemma hasTimeDerivativeOn_const_zero
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM) (s : Set ℝ) :
    HasTimeDerivativeOn (I := I) (M := M)
      (CovariantDerivative.TimeDependentRiemannianMetric.const (I := I) (M := M) g₀) 0 s := by
  intro t ht
  exact hasTimeDerivativeAt_const_zero (I := I) (M := M) g₀ t

/-- A constant family of a fixed Levi-Civita connection is Levi-Civita for the corresponding
constant metric family. -/
lemma const_isLeviCivita
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (cov₀ : CovariantDerivative I E TM)
    [hcov₀ : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1]
    (hLevi : letI : Bundle.RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩; cov₀.IsLeviCivita) :
    CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
      (I := I) (M := M)
      (CovariantDerivative.TimeDependentRiemannianMetric.const (I := I) (M := M) g₀)
      (CovariantDerivative.TimeDependentCovariantDerivative.const
        (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) cov₀) := by
  intro t
  simpa [CovariantDerivative.TimeDependentRiemannianMetric.const_apply,
    CovariantDerivative.TimeDependentCovariantDerivative.const_apply] using hLevi

/-- If the Ricci tensor of a smooth Levi-Civita connection vanishes, the constant metric family
satisfies the Ricci-flow equation with zero velocity. -/
lemma satisfiesEquationAt_const_of_ricciFlat
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (cov₀ : CovariantDerivative I E TM)
    [hcov₀ : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1]
    (hRicciFlat : ∀ x : M, ∀ u v : TM x,
      (letI : Bundle.RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩
       CovariantDerivative.ricciCurvature (cov := cov₀) x u v) = 0)
    (t : ℝ) :
    SatisfiesEquationAt (I := I) (M := M)
      (CovariantDerivative.TimeDependentRiemannianMetric.const (I := I) (M := M) g₀)
      (CovariantDerivative.TimeDependentCovariantDerivative.const
        (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) cov₀)
      (fun _ ↦ hcov₀) 0 t := by
  intro x u v
  have hRic : (letI : Bundle.RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩
      CovariantDerivative.ricciCurvature (cov := cov₀) x u v) = 0 := hRicciFlat x u v
  simp [ricciFlowRHS, ricciTensor, CovariantDerivative.TimeDependentRiemannianMetric.const_apply,
    CovariantDerivative.TimeDependentCovariantDerivative.const_apply, hRic]

/-- A Ricci-flat Levi-Civita connection yields a stationary Ricci-flow solution. -/
lemma isRicciFlowOn_const_of_ricciFlat
    (g₀ : Bundle.ContMDiffRiemannianMetric I 2 E TM)
    (cov₀ : CovariantDerivative I E TM)
    [hcov₀ : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1]
    (hLevi : letI : Bundle.RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩; cov₀.IsLeviCivita)
    (hRicciFlat : ∀ x : M, ∀ u v : TM x,
      (letI : Bundle.RiemannianBundle TM := ⟨g₀.toRiemannianMetric⟩
       CovariantDerivative.ricciCurvature (cov := cov₀) x u v) = 0)
    (s : Set ℝ) :
    IsRicciFlowOn (I := I) (M := M)
      (CovariantDerivative.TimeDependentRiemannianMetric.const (I := I) (M := M) g₀)
      (CovariantDerivative.TimeDependentCovariantDerivative.const
        (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) cov₀)
      (fun _ ↦ hcov₀) 0 s := by
  refine ⟨?_, ?_, ?_⟩
  · exact const_isLeviCivita (I := I) (M := M) g₀ cov₀ hLevi
  · exact hasTimeDerivativeOn_const_zero (I := I) (M := M) g₀ s
  · intro t ht
    exact satisfiesEquationAt_const_of_ricciFlat (I := I) (M := M) g₀ cov₀ hRicciFlat t

/-- Explicit stationary local Ricci-flow solution coming from Ricci-flat initial data. -/
def stationaryRicciFlatLocalSolution
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (cov₀ : CovariantDerivative I E TM)
    [hcov₀ : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1]
    (hLevi : letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
      cov₀.IsLeviCivita)
    (hRicciFlat : ∀ x : M, ∀ u v : TM x,
      (letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
       CovariantDerivative.ricciCurvature (cov := cov₀) x u v) = 0) :
    LocalSolution (E := E) (H := H) (I := I) (M := M) ivp where
  terminalTime := ivp.initialTime + 1
  initial_lt_terminal := by
    simpa using lt_add_of_pos_right ivp.initialTime zero_lt_one
  toSolution :=
    { timeSet := Set.univ
      metric := CovariantDerivative.TimeDependentRiemannianMetric.const
        (I := I) (M := M) ivp.initialMetric
      connection := CovariantDerivative.TimeDependentCovariantDerivative.const
        (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) cov₀
      hconnection := fun _ ↦ hcov₀
      metricVelocity := 0
      isRicciFlow := isRicciFlowOn_const_of_ricciFlat
        (I := I) (M := M) ivp.initialMetric cov₀ hLevi hRicciFlat Set.univ }
  interval_subset := by
    intro t ht
    trivial
  matchesInitialMetric := by
    intro x u v
    simp [metricTensor, CovariantDerivative.TimeDependentRiemannianMetric.const_apply]

/-- Ricci-flat initial data with a chosen smooth Levi-Civita connection has a local
stationary Ricci-flow solution. -/
theorem localSolution_nonempty_of_stationary_ricciFlat
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (cov₀ : CovariantDerivative I E TM)
    [hcov₀ : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1]
    (hLevi : letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
      cov₀.IsLeviCivita)
    (hRicciFlat : ∀ x : M, ∀ u v : TM x,
      (letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
       CovariantDerivative.ricciCurvature (cov := cov₀) x u v) = 0) :
    Nonempty (LocalSolution (E := E) (H := H) (I := I) (M := M) ivp) := by
  exact ⟨stationaryRicciFlatLocalSolution (I := I) (M := M) ivp cov₀ hLevi hRicciFlat⟩

namespace InitialValueProblem

def IsRicciFlat [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) : Prop := by
  letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  let cov₀ : CovariantDerivative I E TM :=
    CovariantDerivative.someContMDiffLeviCivitaConnection (I := I) (E := E) (M := M)
  letI : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1 :=
    CovariantDerivative.someContMDiffLeviCivitaConnection_contMDiff (I := I) (E := E) (M := M)
  exact ∀ x : M, ∀ u v : TM x, CovariantDerivative.ricciCurvature (cov := cov₀) x u v = 0

theorem isRicciFlat_iff [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (cov₀ : CovariantDerivative I E TM)
    [hcov₀ : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1]
    (hLevi : letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
      cov₀.IsLeviCivita) :
    ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M) ↔
      ∀ x : M, ∀ u v : TM x,
        (letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
         CovariantDerivative.ricciCurvature (cov := cov₀) x u v) = 0 := by
  letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  let cov : CovariantDerivative I E TM :=
    CovariantDerivative.someContMDiffLeviCivitaConnection (I := I) (E := E) (M := M)
  letI : CovariantDerivative.ContMDiffCovariantDerivative cov 1 :=
    CovariantDerivative.someContMDiffLeviCivitaConnection_contMDiff (I := I) (E := E) (M := M)
  have hEq : ∀ x : M, ∀ u v : TM x,
      CovariantDerivative.ricciCurvature (cov := cov) x u v =
        CovariantDerivative.ricciCurvature (cov := cov₀) x u v := by
    intro x u v
    exact CovariantDerivative.ricciCurvature_eq_of_isLeviCivita
      (I := I) (M := M) (cov := cov) (cov' := cov₀)
      (CovariantDerivative.someContMDiffLeviCivitaConnection_isLeviCivita
        (I := I) (E := E) (M := M))
      hLevi x u v
  constructor
  · intro h x u v
    rw [← hEq x u v]
    exact h x u v
  · intro h x u v
    rw [hEq x u v]
    exact h x u v

end InitialValueProblem

noncomputable def stationaryRicciFlatLocalSolutionOfIsRicciFlat
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    LocalSolution (E := E) (H := H) (I := I) (M := M) ivp := by
  letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  let cov₀ : CovariantDerivative I E TM :=
    CovariantDerivative.someContMDiffLeviCivitaConnection (I := I) (E := E) (M := M)
  letI : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1 :=
    CovariantDerivative.someContMDiffLeviCivitaConnection_contMDiff (I := I) (E := E) (M := M)
  exact stationaryRicciFlatLocalSolution (I := I) (M := M) ivp cov₀
    (CovariantDerivative.someContMDiffLeviCivitaConnection_isLeviCivita
      (I := I) (E := E) (M := M))
    hRicciFlat

theorem localSolution_nonempty_of_isRicciFlat
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (LocalSolution (E := E) (H := H) (I := I) (M := M) ivp) := by
  exact ⟨stationaryRicciFlatLocalSolutionOfIsRicciFlat (I := I) (M := M) ivp hRicciFlat⟩

theorem InitialValueProblem.isRicciFlat_of_subsingleton_tangent
    [SigmaCompactSpace M] [∀ x : M, Subsingleton (TM x)]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M) := by
  letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  let cov₀ : CovariantDerivative I E TM :=
    CovariantDerivative.someContMDiffLeviCivitaConnection (I := I) (E := E) (M := M)
  letI : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1 :=
    CovariantDerivative.someContMDiffLeviCivitaConnection_contMDiff (I := I) (E := E) (M := M)
  intro x u v
  exact CovariantDerivative.ricciCurvature_eq_zero_of_subsingleton_tangent
    (I := I) (M := M) (cov := cov₀) x u v

/-- Initial data is Ricci-flat when every tangent fiber has dimension at most one. -/
theorem InitialValueProblem.isRicciFlat_of_finrank_le_one
    [SigmaCompactSpace M]
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M) := by
  letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  let cov₀ : CovariantDerivative I E TM :=
    CovariantDerivative.someContMDiffLeviCivitaConnection (I := I) (E := E) (M := M)
  letI : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1 :=
    CovariantDerivative.someContMDiffLeviCivitaConnection_contMDiff (I := I) (E := E) (M := M)
  intro x u v
  exact CovariantDerivative.ricciCurvature_eq_zero_of_finrank_le_one
    (I := I) (M := M) (cov := cov₀) x (hfin x) u v

/-- Model-space version of `InitialValueProblem.isRicciFlat_of_finrank_le_one`. -/
theorem InitialValueProblem.isRicciFlat_of_finrank_model_le_one
    [SigmaCompactSpace M] [Fact (Module.finrank ℝ E ≤ 1)]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M) :=
  ivp.isRicciFlat_of_finrank_le_one (I := I) (M := M)
    (fun x ↦ tangent_finrank_le_one_of_model (I := I) (M := M) x)

theorem localSolution_nonempty_of_subsingleton_tangent
    [SigmaCompactSpace M] [∀ x : M, Subsingleton (TM x)]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (LocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :=
  localSolution_nonempty_of_isRicciFlat (I := I) (M := M) ivp
    (ivp.isRicciFlat_of_subsingleton_tangent (I := I) (M := M))

/-- If all tangent fibers have dimension at most one, every initial metric admits the stationary
Ricci-flow local solution. -/
theorem localSolution_nonempty_of_finrank_le_one
    [SigmaCompactSpace M]
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (LocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :=
  localSolution_nonempty_of_isRicciFlat (I := I) (M := M) ivp
    (ivp.isRicciFlat_of_finrank_le_one (I := I) (M := M) hfin)

/-- Model-space version of `localSolution_nonempty_of_finrank_le_one`. -/
theorem localSolution_nonempty_of_finrank_model_le_one
    [SigmaCompactSpace M] [Fact (Module.finrank ℝ E ≤ 1)]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (LocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :=
  localSolution_nonempty_of_finrank_le_one
    (I := I) (M := M) (fun x ↦ tangent_finrank_le_one_of_model (I := I) (M := M) x) ivp

theorem localSolution_nonempty_of_stationary_ricciFlat_someLeviCivitaConnection
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat :
      letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
      letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
      letI : CovariantDerivative.ContMDiffCovariantDerivative
          (CovariantDerivative.someContMDiffLeviCivitaConnection
            (I := I) (E := E) (M := M)) 1 :=
        CovariantDerivative.someContMDiffLeviCivitaConnection_contMDiff
          (I := I) (E := E) (M := M)
      ∀ x : M, ∀ u v : TM x,
        CovariantDerivative.ricciCurvature
          (cov := CovariantDerivative.someContMDiffLeviCivitaConnection
            (I := I) (E := E) (M := M)) x u v = 0) :
    Nonempty (LocalSolution (E := E) (H := H) (I := I) (M := M) ivp) := by
  have hRicciFlat' : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M) := by
    exact hRicciFlat
  exact localSolution_nonempty_of_isRicciFlat (I := I) (M := M) ivp hRicciFlat'

/-- The stationary Ricci-flat local solution has identically zero metric velocity. -/
theorem stationaryRicciFlatLocalSolution_metricVelocity_eq_zero
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (cov₀ : CovariantDerivative I E TM)
    [hcov₀ : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1]
    (hLevi : letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
      cov₀.IsLeviCivita)
    (hRicciFlat : ∀ x : M, ∀ u v : TM x,
      (letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
       CovariantDerivative.ricciCurvature (cov := cov₀) x u v) = 0) :
    ∀ t ∈ Set.Icc ivp.initialTime
        (stationaryRicciFlatLocalSolution (I := I) (M := M) ivp cov₀ hLevi hRicciFlat).terminalTime,
      ∀ x : M, ∀ u v : TM x,
        (stationaryRicciFlatLocalSolution (I := I) (M := M) ivp cov₀ hLevi hRicciFlat).toSolution.metricVelocity
          t x u v = 0 := by
  intro t ht x u v
  simp [stationaryRicciFlatLocalSolution]

theorem stationaryRicciFlatLocalSolution_ricciTensor_eq_zero
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (cov₀ : CovariantDerivative I E TM)
    [hcov₀ : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1]
    (hLevi : letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
      cov₀.IsLeviCivita)
    (hRicciFlat : ∀ x : M, ∀ u v : TM x,
      (letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
       CovariantDerivative.ricciCurvature (cov := cov₀) x u v) = 0) :
    ∀ t ∈ Set.Icc ivp.initialTime
        (stationaryRicciFlatLocalSolution (I := I) (M := M) ivp cov₀ hLevi hRicciFlat).terminalTime,
      ∀ x : M, ∀ u v : TM x,
        ricciTensor (I := I) (M := M)
          (stationaryRicciFlatLocalSolution
            (I := I) (M := M) ivp cov₀ hLevi hRicciFlat).toSolution.metric
          (stationaryRicciFlatLocalSolution
            (I := I) (M := M) ivp cov₀ hLevi hRicciFlat).toSolution.connection
          (stationaryRicciFlatLocalSolution
            (I := I) (M := M) ivp cov₀ hLevi hRicciFlat).toSolution.hconnection t x u v = 0 :=
  (localSolution_zero_velocity_iff_ricciTensor_zero
    (I := I) (M := M)
    (stationaryRicciFlatLocalSolution
      (I := I) (M := M) ivp cov₀ hLevi hRicciFlat)).1
    (stationaryRicciFlatLocalSolution_metricVelocity_eq_zero
      (I := I) (M := M) ivp cov₀ hLevi hRicciFlat)

theorem stationaryRicciFlatLocalSolution_ricciFlowRHS_eq_zero
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (cov₀ : CovariantDerivative I E TM)
    [hcov₀ : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1]
    (hLevi : letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
      cov₀.IsLeviCivita)
    (hRicciFlat : ∀ x : M, ∀ u v : TM x,
      (letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
       CovariantDerivative.ricciCurvature (cov := cov₀) x u v) = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (stationaryRicciFlatLocalSolution
        (I := I) (M := M) ivp cov₀ hLevi hRicciFlat).terminalTime)
    (x : M) (u v : TM x) :
    ricciFlowRHS (I := I) (M := M)
      (stationaryRicciFlatLocalSolution
        (I := I) (M := M) ivp cov₀ hLevi hRicciFlat).toSolution.metric
      (stationaryRicciFlatLocalSolution
        (I := I) (M := M) ivp cov₀ hLevi hRicciFlat).toSolution.connection
      (stationaryRicciFlatLocalSolution
        (I := I) (M := M) ivp cov₀ hLevi hRicciFlat).toSolution.hconnection t x u v = 0 :=
  ricciFlowRHS_eq_zero_of_ricciTensor_eq_zero
    (I := I) (M := M)
    (stationaryRicciFlatLocalSolution
      (I := I) (M := M) ivp cov₀ hLevi hRicciFlat).toSolution.metric
    (stationaryRicciFlatLocalSolution
      (I := I) (M := M) ivp cov₀ hLevi hRicciFlat).toSolution.connection
    (stationaryRicciFlatLocalSolution
      (I := I) (M := M) ivp cov₀ hLevi hRicciFlat).toSolution.hconnection
    (stationaryRicciFlatLocalSolution_ricciTensor_eq_zero
      (I := I) (M := M) ivp cov₀ hLevi hRicciFlat t ht x u v)

/-- The stationary Ricci-flat local solution keeps the initial metric fixed for all times. -/
theorem stationaryRicciFlatLocalSolution_metric_eq_initial
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (cov₀ : CovariantDerivative I E TM)
    [hcov₀ : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1]
    (hLevi : letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
      cov₀.IsLeviCivita)
    (hRicciFlat : ∀ x : M, ∀ u v : TM x,
      (letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
       CovariantDerivative.ricciCurvature (cov := cov₀) x u v) = 0)
    (t : ℝ) (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      (stationaryRicciFlatLocalSolution (I := I) (M := M) ivp cov₀ hLevi hRicciFlat).toSolution.metric
      t x u v =
        ivp.initialMetric.inner x u v := by
  simp [stationaryRicciFlatLocalSolution, metricTensor,
    CovariantDerivative.TimeDependentRiemannianMetric.const_apply]

/-- The stationary Ricci-flat local solution keeps its Levi-Civita connection fixed for all times. -/
theorem stationaryRicciFlatLocalSolution_connection_eq_initial
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (cov₀ : CovariantDerivative I E TM)
    [hcov₀ : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1]
    (hLevi : letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
      cov₀.IsLeviCivita)
    (hRicciFlat : ∀ x : M, ∀ u v : TM x,
      (letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
       CovariantDerivative.ricciCurvature (cov := cov₀) x u v) = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (stationaryRicciFlatLocalSolution (I := I) (M := M) ivp cov₀ hLevi hRicciFlat).terminalTime)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    (stationaryRicciFlatLocalSolution (I := I) (M := M) ivp cov₀ hLevi hRicciFlat).toSolution.connection
      t σ x =
        (stationaryRicciFlatLocalSolution
          (I := I) (M := M) ivp cov₀ hLevi hRicciFlat).toSolution.connection
          ivp.initialTime σ x := by
  exact
    localSolution_connection_eq_initial_of_zero_velocity
      (I := I) (M := M)
      (stationaryRicciFlatLocalSolution (I := I) (M := M) ivp cov₀ hLevi hRicciFlat)
      (stationaryRicciFlatLocalSolution_metricVelocity_eq_zero
        (I := I) (M := M) ivp cov₀ hLevi hRicciFlat) ht hσ

/-- The stationary Ricci-flat local solution agrees with any other zero-velocity local solution for
the same initial-value problem on the common interval. -/
theorem stationaryRicciFlatLocalSolution_unique_metric_of_zero_velocity
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (cov₀ : CovariantDerivative I E TM)
    [hcov₀ : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1]
    (hLevi : letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
      cov₀.IsLeviCivita)
    (hRicciFlat : ∀ x : M, ∀ u v : TM x,
      (letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
       CovariantDerivative.ricciCurvature (cov := cov₀) x u v) = 0)
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol.toSolution.metricVelocity t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min (stationaryRicciFlatLocalSolution (I := I) (M := M) ivp cov₀ hLevi hRicciFlat).terminalTime
        sol.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      (stationaryRicciFlatLocalSolution (I := I) (M := M) ivp cov₀ hLevi hRicciFlat).toSolution.metric
      t x u v =
        metricTensor (I := I) (M := M) sol.toSolution.metric t x u v := by
  have ht' : t ∈ Set.Icc ivp.initialTime
      (min sol.terminalTime
        (stationaryRicciFlatLocalSolution (I := I) (M := M) ivp cov₀ hLevi hRicciFlat).terminalTime) := by
    simpa [min_comm] using ht
  symm
  exact localSolution_unique_metric_of_zero_velocity
    (I := I) (M := M)
    (sol₁ := sol)
    (sol₂ := stationaryRicciFlatLocalSolution (I := I) (M := M) ivp cov₀ hLevi hRicciFlat)
    hzero
    (stationaryRicciFlatLocalSolution_metricVelocity_eq_zero
      (I := I) (M := M) ivp cov₀ hLevi hRicciFlat)
    ht' x u v

/-- The stationary Ricci-flat local solution agrees with any other zero-velocity local solution for
the same initial-value problem on the common interval, at the level of Levi-Civita connections. -/
theorem stationaryRicciFlatLocalSolution_unique_connection_of_zero_velocity
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (cov₀ : CovariantDerivative I E TM)
    [hcov₀ : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1]
    (hLevi : letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
      cov₀.IsLeviCivita)
    (hRicciFlat : ∀ x : M, ∀ u v : TM x,
      (letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
       CovariantDerivative.ricciCurvature (cov := cov₀) x u v) = 0)
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol.toSolution.metricVelocity t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min (stationaryRicciFlatLocalSolution (I := I) (M := M) ivp cov₀ hLevi hRicciFlat).terminalTime
        sol.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    (stationaryRicciFlatLocalSolution (I := I) (M := M) ivp cov₀ hLevi hRicciFlat).toSolution.connection
      t σ x =
        sol.toSolution.connection t σ x := by
  symm
  exact
    localSolution_unique_connection_of_zero_velocity (I := I) (M := M)
      (sol₁ := sol)
      (sol₂ := stationaryRicciFlatLocalSolution (I := I) (M := M) ivp cov₀ hLevi hRicciFlat)
      hzero
      (stationaryRicciFlatLocalSolution_metricVelocity_eq_zero
        (I := I) (M := M) ivp cov₀ hLevi hRicciFlat)
      (by simpa [min_comm] using ht) hσ

theorem stationaryRicciFlatLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    ∀ t ∈ Set.Icc ivp.initialTime
        (stationaryRicciFlatLocalSolutionOfIsRicciFlat (I := I) (M := M) ivp hRicciFlat).terminalTime,
      ∀ x : M, ∀ u v : TM x,
        (stationaryRicciFlatLocalSolutionOfIsRicciFlat (I := I) (M := M) ivp hRicciFlat).toSolution.metricVelocity
          t x u v = 0 := by
  letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  let cov₀ : CovariantDerivative I E TM :=
    CovariantDerivative.someContMDiffLeviCivitaConnection (I := I) (E := E) (M := M)
  letI : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1 :=
    CovariantDerivative.someContMDiffLeviCivitaConnection_contMDiff (I := I) (E := E) (M := M)
  simpa [stationaryRicciFlatLocalSolutionOfIsRicciFlat, cov₀] using
    (stationaryRicciFlatLocalSolution_metricVelocity_eq_zero (I := I) (M := M) ivp cov₀
      (CovariantDerivative.someContMDiffLeviCivitaConnection_isLeviCivita
        (I := I) (E := E) (M := M))
      hRicciFlat)

theorem stationaryRicciFlatLocalSolutionOfIsRicciFlat_ricciTensor_eq_zero
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    ∀ t ∈ Set.Icc ivp.initialTime
        (stationaryRicciFlatLocalSolutionOfIsRicciFlat
          (I := I) (M := M) ivp hRicciFlat).terminalTime,
      ∀ x : M, ∀ u v : TM x,
        ricciTensor (I := I) (M := M)
          (stationaryRicciFlatLocalSolutionOfIsRicciFlat
            (I := I) (M := M) ivp hRicciFlat).toSolution.metric
          (stationaryRicciFlatLocalSolutionOfIsRicciFlat
            (I := I) (M := M) ivp hRicciFlat).toSolution.connection
          (stationaryRicciFlatLocalSolutionOfIsRicciFlat
            (I := I) (M := M) ivp hRicciFlat).toSolution.hconnection t x u v = 0 :=
  (localSolution_zero_velocity_iff_ricciTensor_zero
    (I := I) (M := M)
    (stationaryRicciFlatLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat)).1
    (stationaryRicciFlatLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
      (I := I) (M := M) ivp hRicciFlat)

theorem stationaryRicciFlatLocalSolutionOfIsRicciFlat_ricciFlowRHS_eq_zero
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (stationaryRicciFlatLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).terminalTime)
    (x : M) (u v : TM x) :
    ricciFlowRHS (I := I) (M := M)
      (stationaryRicciFlatLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).toSolution.metric
      (stationaryRicciFlatLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).toSolution.connection
      (stationaryRicciFlatLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).toSolution.hconnection t x u v = 0 :=
  ricciFlowRHS_eq_zero_of_ricciTensor_eq_zero
    (I := I) (M := M)
    (stationaryRicciFlatLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat).toSolution.metric
    (stationaryRicciFlatLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat).toSolution.connection
    (stationaryRicciFlatLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat).toSolution.hconnection
    (stationaryRicciFlatLocalSolutionOfIsRicciFlat_ricciTensor_eq_zero
      (I := I) (M := M) ivp hRicciFlat t ht x u v)

theorem stationaryRicciFlatLocalSolutionOfIsRicciFlat_metric_eq_initial
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      (stationaryRicciFlatLocalSolutionOfIsRicciFlat (I := I) (M := M) ivp hRicciFlat).toSolution.metric
      t x u v =
        ivp.initialMetric.inner x u v := by
  letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  let cov₀ : CovariantDerivative I E TM :=
    CovariantDerivative.someContMDiffLeviCivitaConnection (I := I) (E := E) (M := M)
  letI : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1 :=
    CovariantDerivative.someContMDiffLeviCivitaConnection_contMDiff (I := I) (E := E) (M := M)
  simpa [stationaryRicciFlatLocalSolutionOfIsRicciFlat, cov₀] using
    (stationaryRicciFlatLocalSolution_metric_eq_initial (I := I) (M := M) ivp cov₀
      (CovariantDerivative.someContMDiffLeviCivitaConnection_isLeviCivita
        (I := I) (E := E) (M := M))
      hRicciFlat t x u v)

theorem stationaryRicciFlatLocalSolutionOfIsRicciFlat_connection_eq_initial
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (stationaryRicciFlatLocalSolutionOfIsRicciFlat (I := I) (M := M) ivp hRicciFlat).terminalTime)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    (stationaryRicciFlatLocalSolutionOfIsRicciFlat (I := I) (M := M) ivp hRicciFlat).toSolution.connection
      t σ x =
        (stationaryRicciFlatLocalSolutionOfIsRicciFlat
          (I := I) (M := M) ivp hRicciFlat).toSolution.connection
          ivp.initialTime σ x := by
  letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  let cov₀ : CovariantDerivative I E TM :=
    CovariantDerivative.someContMDiffLeviCivitaConnection (I := I) (E := E) (M := M)
  letI : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1 :=
    CovariantDerivative.someContMDiffLeviCivitaConnection_contMDiff (I := I) (E := E) (M := M)
  simpa [stationaryRicciFlatLocalSolutionOfIsRicciFlat, cov₀] using
    (stationaryRicciFlatLocalSolution_connection_eq_initial (I := I) (M := M) ivp cov₀
      (CovariantDerivative.someContMDiffLeviCivitaConnection_isLeviCivita
        (I := I) (E := E) (M := M))
      hRicciFlat ht hσ)

theorem stationaryRicciFlatLocalSolutionOfIsRicciFlat_unique_metric_of_zero_velocity
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol.toSolution.metricVelocity t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min (stationaryRicciFlatLocalSolutionOfIsRicciFlat (I := I) (M := M) ivp hRicciFlat).terminalTime
        sol.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      (stationaryRicciFlatLocalSolutionOfIsRicciFlat (I := I) (M := M) ivp hRicciFlat).toSolution.metric
      t x u v =
        metricTensor (I := I) (M := M) sol.toSolution.metric t x u v := by
  letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  let cov₀ : CovariantDerivative I E TM :=
    CovariantDerivative.someContMDiffLeviCivitaConnection (I := I) (E := E) (M := M)
  letI : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1 :=
    CovariantDerivative.someContMDiffLeviCivitaConnection_contMDiff (I := I) (E := E) (M := M)
  simpa [stationaryRicciFlatLocalSolutionOfIsRicciFlat, cov₀] using
    (stationaryRicciFlatLocalSolution_unique_metric_of_zero_velocity (I := I) (M := M) ivp cov₀
      (CovariantDerivative.someContMDiffLeviCivitaConnection_isLeviCivita
        (I := I) (E := E) (M := M))
      hRicciFlat sol hzero ht x u v)

theorem stationaryRicciFlatLocalSolutionOfIsRicciFlat_unique_connection_of_zero_velocity
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol.toSolution.metricVelocity t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min (stationaryRicciFlatLocalSolutionOfIsRicciFlat (I := I) (M := M) ivp hRicciFlat).terminalTime
        sol.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    (stationaryRicciFlatLocalSolutionOfIsRicciFlat (I := I) (M := M) ivp hRicciFlat).toSolution.connection
      t σ x =
        sol.toSolution.connection t σ x := by
  letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  let cov₀ : CovariantDerivative I E TM :=
    CovariantDerivative.someContMDiffLeviCivitaConnection (I := I) (E := E) (M := M)
  letI : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1 :=
    CovariantDerivative.someContMDiffLeviCivitaConnection_contMDiff (I := I) (E := E) (M := M)
  simpa [stationaryRicciFlatLocalSolutionOfIsRicciFlat, cov₀] using
    (stationaryRicciFlatLocalSolution_unique_connection_of_zero_velocity (I := I) (M := M) ivp cov₀
      (CovariantDerivative.someContMDiffLeviCivitaConnection_isLeviCivita
        (I := I) (E := E) (M := M))
      hRicciFlat sol hzero ht hσ)

theorem stationaryRicciFlatLocalSolutionOfIsRicciFlat_unique_metric_of_ricciTensor_zero
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hRicciZero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      ricciTensor (I := I) (M := M) sol.toSolution.metric sol.toSolution.connection
        sol.toSolution.hconnection t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min (stationaryRicciFlatLocalSolutionOfIsRicciFlat (I := I) (M := M) ivp hRicciFlat).terminalTime
        sol.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      (stationaryRicciFlatLocalSolutionOfIsRicciFlat (I := I) (M := M) ivp hRicciFlat).toSolution.metric
      t x u v =
        metricTensor (I := I) (M := M) sol.toSolution.metric t x u v := by
  exact stationaryRicciFlatLocalSolutionOfIsRicciFlat_unique_metric_of_zero_velocity
    (I := I) (M := M) ivp hRicciFlat sol
    ((localSolution_zero_velocity_iff_ricciTensor_zero (I := I) (M := M) sol).2 hRicciZero)
    ht x u v

theorem stationaryRicciFlatLocalSolutionOfIsRicciFlat_unique_connection_of_ricciTensor_zero
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (sol : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hRicciZero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      ricciTensor (I := I) (M := M) sol.toSolution.metric sol.toSolution.connection
        sol.toSolution.hconnection t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min (stationaryRicciFlatLocalSolutionOfIsRicciFlat (I := I) (M := M) ivp hRicciFlat).terminalTime
        sol.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    (stationaryRicciFlatLocalSolutionOfIsRicciFlat (I := I) (M := M) ivp hRicciFlat).toSolution.connection
      t σ x =
        sol.toSolution.connection t σ x := by
  exact stationaryRicciFlatLocalSolutionOfIsRicciFlat_unique_connection_of_zero_velocity
    (I := I) (M := M) ivp hRicciFlat sol
    ((localSolution_zero_velocity_iff_ricciTensor_zero (I := I) (M := M) sol).2 hRicciZero)
    ht hσ

/-- The canonical intrinsic stationary local Ricci-flow solution attached to Ricci-flat initial
data. -/
noncomputable def stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp :=
  (stationaryRicciFlatLocalSolutionOfIsRicciFlat
    (I := I) (M := M) ivp hRicciFlat).toIntrinsicLocalSolution

theorem intrinsicLocalSolution_nonempty_of_isRicciFlat
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) := by
  exact ⟨stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
    (I := I) (M := M) ivp hRicciFlat⟩

/-- If all tangent fibers have dimension at most one, every initial metric admits the stationary
intrinsic Ricci-flow local solution. -/
theorem intrinsicLocalSolution_nonempty_of_finrank_le_one
    [SigmaCompactSpace M]
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :=
  intrinsicLocalSolution_nonempty_of_isRicciFlat (I := I) (M := M) ivp
    (ivp.isRicciFlat_of_finrank_le_one (I := I) (M := M) hfin)

/-- Model-space version of `intrinsicLocalSolution_nonempty_of_finrank_le_one`. -/
theorem intrinsicLocalSolution_nonempty_of_finrank_model_le_one
    [SigmaCompactSpace M] [Fact (Module.finrank ℝ E ≤ 1)]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :=
  intrinsicLocalSolution_nonempty_of_finrank_le_one
    (I := I) (M := M) (fun x ↦ tangent_finrank_le_one_of_model (I := I) (M := M) x) ivp

theorem stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    ∀ t ∈ Set.Icc ivp.initialTime
        (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
          (I := I) (M := M) ivp hRicciFlat).terminalTime,
      ∀ x : M, ∀ u v : TM x,
        (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
          (I := I) (M := M) ivp hRicciFlat).toIntrinsicSolution.metricVelocity
          t x u v = 0 := by
  simpa [stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat,
    LocalSolution.toIntrinsicLocalSolution, Solution.toIntrinsicSolution] using
    stationaryRicciFlatLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
      (I := I) (M := M) ivp hRicciFlat

theorem stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat_intrinsicRicciTensor_eq_zero
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M)) :
    ∀ t ∈ Set.Icc ivp.initialTime
        (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
          (I := I) (M := M) ivp hRicciFlat).terminalTime,
      ∀ x : M, ∀ u v : TM x,
        intrinsicRicciTensor (I := I) (M := M)
          (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
            (I := I) (M := M) ivp hRicciFlat).toIntrinsicSolution.metric
          t x u v = 0 :=
  (intrinsicLocalSolution_zero_velocity_iff_ricciTensor_zero
    (I := I) (M := M)
    (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat)).1
    (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
      (I := I) (M := M) ivp hRicciFlat)

theorem stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat_intrinsicRicciFlowRHS_eq_zero
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).terminalTime)
    (x : M) (u v : TM x) :
    intrinsicRicciFlowRHS (I := I) (M := M)
      (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).toIntrinsicSolution.metric t x u v = 0 :=
  intrinsicRicciFlowRHS_eq_zero_of_intrinsicRicciTensor_eq_zero
    (I := I) (M := M)
    (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat).toIntrinsicSolution.metric
    (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat_intrinsicRicciTensor_eq_zero
      (I := I) (M := M) ivp hRicciFlat t ht x u v)

theorem stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat_metric_eq_initial
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).terminalTime)
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).toIntrinsicSolution.metric
      t x u v =
        ivp.initialMetric.inner x u v := by
  exact intrinsicLocalSolution_metric_eq_initial_of_zero_velocity
    (I := I) (M := M)
    (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat)
    (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
      (I := I) (M := M) ivp hRicciFlat)
    ht x u v

theorem stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat_connection_eq_initial
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).terminalTime)
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat).toIntrinsicSolution.toSolution.connection
      t σ x =
        (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
          (I := I) (M := M) ivp hRicciFlat).toIntrinsicSolution.toSolution.connection
          ivp.initialTime σ x := by
  exact intrinsicLocalSolution_connection_eq_initial_of_zero_velocity
    (I := I) (M := M)
    (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat)
    (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
      (I := I) (M := M) ivp hRicciFlat)
    ht hσ

theorem stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat_unique_metric_of_zero_velocity
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol.toIntrinsicSolution.metricVelocity t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).terminalTime
        sol.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).toIntrinsicSolution.metric
      t x u v =
        metricTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v := by
  exact intrinsicLocalSolution_unique_metric_of_zero_velocity
    (I := I) (M := M)
    (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat)
    sol
    (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
      (I := I) (M := M) ivp hRicciFlat)
    hzero
    ht x u v

theorem stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat_unique_connection_of_zero_velocity
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hzero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      sol.toIntrinsicSolution.metricVelocity t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).terminalTime
        sol.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat).toIntrinsicSolution.toSolution.connection
      t σ x =
        sol.toIntrinsicSolution.toSolution.connection t σ x := by
  exact intrinsicLocalSolution_unique_connection_of_zero_velocity
    (I := I) (M := M)
    (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat)
    sol
    (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
      (I := I) (M := M) ivp hRicciFlat)
    hzero
    ht hσ

theorem stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat_unique_metric_of_ricciTensor_zero
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hRicciZero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).terminalTime
        sol.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).toIntrinsicSolution.metric
      t x u v =
        metricTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v := by
  have hRicciZero₀ :
      ∀ t ∈ Set.Icc ivp.initialTime
          (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
            (I := I) (M := M) ivp hRicciFlat).terminalTime,
        ∀ x : M, ∀ u v : TM x,
          intrinsicRicciTensor (I := I) (M := M)
            (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
              (I := I) (M := M) ivp hRicciFlat).toIntrinsicSolution.metric
            t x u v = 0 :=
    (intrinsicLocalSolution_zero_velocity_iff_ricciTensor_zero
      (I := I) (M := M)
      (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat)).1
      (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
        (I := I) (M := M) ivp hRicciFlat)
  exact intrinsicLocalSolution_unique_metric_of_ricciTensor_zero
    (I := I) (M := M)
    (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat)
    sol
    hRicciZero₀
    hRicciZero
    ht x u v

theorem stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat_unique_connection_of_ricciTensor_zero
    [SigmaCompactSpace M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (hRicciFlat : ivp.IsRicciFlat (E := E) (H := H) (I := I) (M := M))
    (sol : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    (hRicciZero : ∀ t ∈ Set.Icc ivp.initialTime sol.terminalTime, ∀ x : M, ∀ u v : TM x,
      intrinsicRicciTensor (I := I) (M := M) sol.toIntrinsicSolution.metric t x u v = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat).terminalTime
        sol.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat).toIntrinsicSolution.toSolution.connection
      t σ x =
        sol.toIntrinsicSolution.toSolution.connection t σ x := by
  have hRicciZero₀ :
      ∀ t ∈ Set.Icc ivp.initialTime
          (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
            (I := I) (M := M) ivp hRicciFlat).terminalTime,
        ∀ x : M, ∀ u v : TM x,
          intrinsicRicciTensor (I := I) (M := M)
            (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
              (I := I) (M := M) ivp hRicciFlat).toIntrinsicSolution.metric
            t x u v = 0 :=
    (intrinsicLocalSolution_zero_velocity_iff_ricciTensor_zero
      (I := I) (M := M)
      (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
        (I := I) (M := M) ivp hRicciFlat)).1
      (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat_metricVelocity_eq_zero
        (I := I) (M := M) ivp hRicciFlat)
  exact intrinsicLocalSolution_unique_connection_of_ricciTensor_zero
    (I := I) (M := M)
    (stationaryRicciFlatIntrinsicLocalSolutionOfIsRicciFlat
      (I := I) (M := M) ivp hRicciFlat)
    sol
    hRicciZero₀
    hRicciZero
    ht hσ

/-- Any two stationary Ricci-flat local solutions with the same initial metric have identical
evolving metric tensors. -/
theorem stationaryRicciFlatLocalSolution_unique_metric
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (cov₀ cov₁ : CovariantDerivative I E TM)
    [hcov₀ : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1]
    [hcov₁ : CovariantDerivative.ContMDiffCovariantDerivative cov₁ 1]
    (hLevi₀ : letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
      cov₀.IsLeviCivita)
    (hRicciFlat₀ : ∀ x : M, ∀ u v : TM x,
      (letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
       CovariantDerivative.ricciCurvature (cov := cov₀) x u v) = 0)
    (hLevi₁ : letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
      cov₁.IsLeviCivita)
    (hRicciFlat₁ : ∀ x : M, ∀ u v : TM x,
      (letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
       CovariantDerivative.ricciCurvature (cov := cov₁) x u v) = 0)
    (t : ℝ) (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M)
      (stationaryRicciFlatLocalSolution (I := I) (M := M) ivp cov₀ hLevi₀ hRicciFlat₀).toSolution.metric
      t x u v =
        metricTensor (I := I) (M := M)
          (stationaryRicciFlatLocalSolution (I := I) (M := M) ivp cov₁ hLevi₁ hRicciFlat₁).toSolution.metric
          t x u v := by
  rw [stationaryRicciFlatLocalSolution_metric_eq_initial (I := I) (M := M) ivp cov₀ hLevi₀
      hRicciFlat₀ t x u v,
    stationaryRicciFlatLocalSolution_metric_eq_initial (I := I) (M := M) ivp cov₁ hLevi₁
      hRicciFlat₁ t x u v]

/-- Any two stationary Ricci-flat local solutions with the same initial metric have identical
Levi-Civita connections. -/
theorem stationaryRicciFlatLocalSolution_unique_connection
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (cov₀ cov₁ : CovariantDerivative I E TM)
    [hcov₀ : CovariantDerivative.ContMDiffCovariantDerivative cov₀ 1]
    [hcov₁ : CovariantDerivative.ContMDiffCovariantDerivative cov₁ 1]
    (hLevi₀ : letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
      cov₀.IsLeviCivita)
    (hRicciFlat₀ : ∀ x : M, ∀ u v : TM x,
      (letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
       CovariantDerivative.ricciCurvature (cov := cov₀) x u v) = 0)
    (hLevi₁ : letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩;
      cov₁.IsLeviCivita)
    (hRicciFlat₁ : ∀ x : M, ∀ u v : TM x,
      (letI : Bundle.RiemannianBundle TM := ⟨ivp.initialMetric.toRiemannianMetric⟩
       CovariantDerivative.ricciCurvature (cov := cov₁) x u v) = 0)
    {t : ℝ}
    (ht : t ∈ Set.Icc ivp.initialTime
      (min (stationaryRicciFlatLocalSolution (I := I) (M := M) ivp cov₀ hLevi₀ hRicciFlat₀).terminalTime
        (stationaryRicciFlatLocalSolution (I := I) (M := M) ivp cov₁ hLevi₁ hRicciFlat₁).terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    (stationaryRicciFlatLocalSolution (I := I) (M := M) ivp cov₀ hLevi₀ hRicciFlat₀).toSolution.connection
      t σ x =
        (stationaryRicciFlatLocalSolution
          (I := I) (M := M) ivp cov₁ hLevi₁ hRicciFlat₁).toSolution.connection
          t σ x := by
  exact
    localSolution_unique_connection_of_zero_velocity (I := I) (M := M)
      (sol₁ := stationaryRicciFlatLocalSolution (I := I) (M := M) ivp cov₀ hLevi₀ hRicciFlat₀)
      (sol₂ := stationaryRicciFlatLocalSolution (I := I) (M := M) ivp cov₁ hLevi₁ hRicciFlat₁)
      (stationaryRicciFlatLocalSolution_metricVelocity_eq_zero
        (I := I) (M := M) ivp cov₀ hLevi₀ hRicciFlat₀)
      (stationaryRicciFlatLocalSolution_metricVelocity_eq_zero
        (I := I) (M := M) ivp cov₁ hLevi₁ hRicciFlat₁)
      ht hσ

end Stationary

section Compact

variable [CompactSpace M]

/-- The point-4 theorem package on a compact manifold: a local Ricci-flow solution exists, and any
two local solutions with the same initial data agree on the common initial interval. -/
structure LocalExistenceUniqueness
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) where
  /-- Existence of a local Ricci-flow solution. -/
  exists_solution : Nonempty (LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
  /-- Uniqueness of the evolving metric on the overlap of two local solution intervals. -/
  unique_metric :
    ∀ sol₁ sol₂ : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime),
        ∀ x : M, ∀ u v : TM x,
          metricTensor (I := I) (M := M) sol₁.toSolution.metric t x u v =
            metricTensor (I := I) (M := M) sol₂.toSolution.metric t x u v

theorem localExistenceUniqueness_nonempty_localSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp) :
    Nonempty (LocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :=
  pkg.exists_solution

theorem localExistenceUniqueness_metric_eq_on_common_interval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp)
    (sol₁ sol₂ : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol₁.toSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.toSolution.metric t x u v :=
  pkg.unique_metric sol₁ sol₂ t ht x u v

theorem localExistenceUniqueness_connection_eq_on_common_interval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp)
    (sol₁ sol₂ : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.toSolution.connection t σ x = sol₂.toSolution.connection t σ x := by
  have ht₁ : t ∈ sol₁.toSolution.timeSet := sol₁.interval_subset ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩
  have ht₂ : t ∈ sol₂.toSolution.timeSet := sol₂.interval_subset ⟨ht.1, le_trans ht.2 (min_le_right _ _)⟩
  exact localSolution_connection_eq_of_metric_eq
    (I := I) (M := M) sol₁ sol₂ ht₁ ht₂
    (fun y u v ↦ pkg.unique_metric sol₁ sol₂ t ht y u v) hσ

/-- The theorem-family version of the ordinary compact point-4 theorem package. -/
structure LocalExistenceUniquenessFamily where
  package :
    ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp

theorem LocalExistenceUniquenessFamily.nonempty_localSolution
    (pkg : LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (LocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :=
  (pkg.package ivp).exists_solution

theorem LocalExistenceUniquenessFamily.connection_eq_on_common_interval
    (pkg : LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol₁ sol₂ : LocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.toSolution.connection t σ x = sol₂.toSolution.connection t σ x :=
  localExistenceUniqueness_connection_eq_on_common_interval
    (I := I) (M := M) (pkg := pkg.package ivp) sol₁ sol₂ ht hσ

section Intrinsic

variable [SigmaCompactSpace M]

/-- The compact-manifold point-4 theorem package stated intrinsically in terms of the evolving
metric. -/
structure IntrinsicLocalExistenceUniqueness
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) where
  /-- Existence of an intrinsic local Ricci-flow solution. -/
  exists_solution :
    Nonempty (IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
  /-- Uniqueness of the evolving metric on the overlap of two local solution intervals. -/
  unique_metric :
    ∀ sol₁ sol₂ : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime),
        ∀ x : M, ∀ u v : TM x,
          metricTensor (I := I) (M := M) sol₁.toIntrinsicSolution.metric t x u v =
            metricTensor (I := I) (M := M) sol₂.toIntrinsicSolution.metric t x u v

theorem intrinsicLocalExistenceUniqueness_nonempty_localSolution
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp) :
    Nonempty (IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :=
  pkg.exists_solution

theorem intrinsicLocalExistenceUniqueness_metric_eq_on_common_interval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp)
    (sol₁ sol₂ : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    (x : M) (u v : TM x) :
    metricTensor (I := I) (M := M) sol₁.toIntrinsicSolution.metric t x u v =
      metricTensor (I := I) (M := M) sol₂.toIntrinsicSolution.metric t x u v :=
  pkg.unique_metric sol₁ sol₂ t ht x u v

/-- Convert the connection-parametrized compact theorem package to the intrinsic one. -/
def LocalExistenceUniqueness.toIntrinsic
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp := by
  refine ⟨?_, ?_⟩
  · rcases pkg.exists_solution with ⟨sol⟩
    exact ⟨sol.toIntrinsicLocalSolution⟩
  · intro sol₁ sol₂ t ht x u v
    exact pkg.unique_metric sol₁.toLocalSolution sol₂.toLocalSolution t ht x u v

/-- Convert the intrinsic compact theorem package back to the connection-parametrized one. -/
def IntrinsicLocalExistenceUniqueness.toOrdinary
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp := by
  refine ⟨?_, ?_⟩
  · rcases pkg.exists_solution with ⟨sol⟩
    exact ⟨sol.toLocalSolution⟩
  · intro sol₁ sol₂ t ht x u v
    exact pkg.unique_metric sol₁.toIntrinsicLocalSolution sol₂.toIntrinsicLocalSolution t ht x u v

/-- The theorem-family version of the intrinsic compact point-4 theorem package. -/
structure IntrinsicLocalExistenceUniquenessFamily where
  package :
    ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp

def LocalExistenceUniquenessFamily.toIntrinsic
    (pkg : LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ (pkg.package ivp).toIntrinsic

def IntrinsicLocalExistenceUniquenessFamily.toOrdinary
    (pkg : IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M)) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ (pkg.package ivp).toOrdinary

theorem IntrinsicLocalExistenceUniquenessFamily.nonempty_localSolution
    (pkg : IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp) :=
  (pkg.package ivp).exists_solution

theorem intrinsicLocalExistenceUniqueness_connection_eq_on_common_interval
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp)
    (sol₁ sol₂ : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.toIntrinsicSolution.toSolution.connection t σ x =
      sol₂.toIntrinsicSolution.toSolution.connection t σ x := by
  exact localExistenceUniqueness_connection_eq_on_common_interval
    (I := I) (M := M) (pkg := pkg.toOrdinary) sol₁.toLocalSolution sol₂.toLocalSolution ht hσ

theorem IntrinsicLocalExistenceUniquenessFamily.connection_eq_on_common_interval
    (pkg : IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol₁ sol₂ : IntrinsicLocalSolution (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ Set.Icc ivp.initialTime (min sol₁.terminalTime sol₂.terminalTime))
    {x : M} {σ : Π y : M, TM y} (hσ : MDiffAt (T% σ) x) :
    sol₁.toIntrinsicSolution.toSolution.connection t σ x =
      sol₂.toIntrinsicSolution.toSolution.connection t σ x :=
  intrinsicLocalExistenceUniqueness_connection_eq_on_common_interval
    (I := I) (M := M) (pkg := pkg.package ivp) sol₁ sol₂ ht hσ

/-- On compact manifolds whose tangent fibers are all subsingletons, Ricci flow has a stationary
local solution for every initial metric and metric uniqueness is pointwise forced. This is a
genuine zero-dimensional local existence/uniqueness theorem, not an interface assumption. -/
noncomputable def intrinsicLocalExistenceUniqueness_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp where
  exists_solution := by
    rcases localSolution_nonempty_of_subsingleton_tangent (I := I) (M := M) ivp with ⟨sol⟩
    exact ⟨sol.toIntrinsicLocalSolution⟩
  unique_metric := by
    intro sol₁ sol₂ t ht x u v
    rw [metricTensor_eq_zero_of_subsingleton_tangent
        (I := I) (M := M) sol₁.toIntrinsicSolution.metric t x u v,
      metricTensor_eq_zero_of_subsingleton_tangent
        (I := I) (M := M) sol₂.toIntrinsicSolution.metric t x u v]

noncomputable def localExistenceUniqueness_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (intrinsicLocalExistenceUniqueness_of_subsingleton_tangent (I := I) (M := M) ivp).toOrdinary

noncomputable def intrinsicLocalExistenceUniquenessFamily_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)] :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    intrinsicLocalExistenceUniqueness_of_subsingleton_tangent (I := I) (M := M) ivp

noncomputable def localExistenceUniquenessFamily_of_subsingleton_tangent
    [∀ x : M, Subsingleton (TM x)] :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (intrinsicLocalExistenceUniquenessFamily_of_subsingleton_tangent
    (I := I) (M := M)).toOrdinary

/-- On compact manifolds with a subsingleton model vector space, Ricci flow has a stationary local
solution for every initial metric and metric uniqueness is pointwise forced. -/
noncomputable def intrinsicLocalExistenceUniqueness_of_subsingleton_model
    [Subsingleton E]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  intrinsicLocalExistenceUniqueness_of_subsingleton_tangent (I := I) (M := M) ivp

/-- Ordinary connection-parametrized version of
`intrinsicLocalExistenceUniqueness_of_subsingleton_model`. -/
noncomputable def localExistenceUniqueness_of_subsingleton_model
    [Subsingleton E]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (intrinsicLocalExistenceUniqueness_of_subsingleton_model (I := I) (M := M) ivp).toOrdinary

/-- The theorem-family version of
`intrinsicLocalExistenceUniqueness_of_subsingleton_model`. -/
noncomputable def intrinsicLocalExistenceUniquenessFamily_of_subsingleton_model
    [Subsingleton E] :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    intrinsicLocalExistenceUniqueness_of_subsingleton_model (I := I) (M := M) ivp

/-- Ordinary connection-parametrized theorem-family version of
`intrinsicLocalExistenceUniquenessFamily_of_subsingleton_model`. -/
noncomputable def localExistenceUniquenessFamily_of_subsingleton_model
    [Subsingleton E] :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (intrinsicLocalExistenceUniquenessFamily_of_subsingleton_model
    (I := I) (M := M)).toOrdinary

/-- On compact manifolds whose tangent fibers have dimension at most one, Ricci flow has a
stationary local solution for every initial metric and metric uniqueness follows because every
intrinsic Ricci tensor vanishes identically. -/
noncomputable def intrinsicLocalExistenceUniqueness_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp where
  exists_solution :=
    intrinsicLocalSolution_nonempty_of_finrank_le_one (I := I) (M := M) hfin ivp
  unique_metric := by
    intro sol₁ sol₂ t ht x u v
    exact intrinsicLocalSolution_unique_metric_of_ricciTensor_zero
      (I := I) (M := M) sol₁ sol₂
      (fun τ _hτ y a b =>
        intrinsicRicciTensor_eq_zero_of_finrank_le_one
          (I := I) (M := M) hfin sol₁.toIntrinsicSolution.metric τ y a b)
      (fun τ _hτ y a b =>
        intrinsicRicciTensor_eq_zero_of_finrank_le_one
          (I := I) (M := M) hfin sol₂.toIntrinsicSolution.metric τ y a b)
      ht x u v

/-- Ordinary connection-parametrized version of
`intrinsicLocalExistenceUniqueness_of_finrank_le_one`. -/
noncomputable def localExistenceUniqueness_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (intrinsicLocalExistenceUniqueness_of_finrank_le_one
    (I := I) (M := M) hfin ivp).toOrdinary

/-- The theorem-family version of
`intrinsicLocalExistenceUniqueness_of_finrank_le_one`. -/
noncomputable def intrinsicLocalExistenceUniquenessFamily_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    intrinsicLocalExistenceUniqueness_of_finrank_le_one (I := I) (M := M) hfin ivp

/-- Ordinary connection-parametrized theorem-family version of
`intrinsicLocalExistenceUniquenessFamily_of_finrank_le_one`. -/
noncomputable def localExistenceUniquenessFamily_of_finrank_le_one
    (hfin : ∀ x : M, Module.finrank ℝ (TM x) ≤ 1) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (intrinsicLocalExistenceUniquenessFamily_of_finrank_le_one
    (I := I) (M := M) hfin).toOrdinary

/-- On compact manifolds with model vector space of dimension at most one, Ricci flow has a
stationary local solution for every initial metric and metric uniqueness is pointwise forced by
rank-one Ricci flatness. -/
noncomputable def intrinsicLocalExistenceUniqueness_of_finrank_model_le_one
    [Fact (Module.finrank ℝ E ≤ 1)]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  intrinsicLocalExistenceUniqueness_of_finrank_le_one
    (I := I) (M := M) (fun x ↦ tangent_finrank_le_one_of_model (I := I) (M := M) x) ivp

/-- Ordinary connection-parametrized version of
`intrinsicLocalExistenceUniqueness_of_finrank_model_le_one`. -/
noncomputable def localExistenceUniqueness_of_finrank_model_le_one
    [Fact (Module.finrank ℝ E ≤ 1)]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (intrinsicLocalExistenceUniqueness_of_finrank_model_le_one
    (I := I) (M := M) ivp).toOrdinary

/-- The theorem-family version of
`intrinsicLocalExistenceUniqueness_of_finrank_model_le_one`. -/
noncomputable def intrinsicLocalExistenceUniquenessFamily_of_finrank_model_le_one
    [Fact (Module.finrank ℝ E ≤ 1)] :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦
    intrinsicLocalExistenceUniqueness_of_finrank_model_le_one (I := I) (M := M) ivp

/-- Ordinary connection-parametrized theorem-family version of
`intrinsicLocalExistenceUniquenessFamily_of_finrank_model_le_one`. -/
noncomputable def localExistenceUniquenessFamily_of_finrank_model_le_one
    [Fact (Module.finrank ℝ E ≤ 1)] :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (intrinsicLocalExistenceUniquenessFamily_of_finrank_model_le_one
    (I := I) (M := M)).toOrdinary

/-- On an empty compact manifold, the compact point-4 theorem package is provable for every initial
metric: the stationary construction exists because Ricci-flatness is vacuous, and uniqueness of the
metric tensor is also vacuous. -/
noncomputable def intrinsicLocalExistenceUniqueness_of_isEmpty
    [IsEmpty M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp where
  exists_solution := by
    refine intrinsicLocalSolution_nonempty_of_isRicciFlat (I := I) (M := M) ivp ?_
    intro x
    exact isEmptyElim x
  unique_metric := by
    intro sol₁ sol₂ t ht x
    exact isEmptyElim x

/-- Ordinary connection-parametrized version of
`intrinsicLocalExistenceUniqueness_of_isEmpty`. -/
noncomputable def localExistenceUniqueness_of_isEmpty
    [IsEmpty M]
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (intrinsicLocalExistenceUniqueness_of_isEmpty (I := I) (M := M) ivp).toOrdinary

noncomputable def intrinsicLocalExistenceUniquenessFamily_of_isEmpty
    [IsEmpty M] :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) where
  package := fun ivp ↦ intrinsicLocalExistenceUniqueness_of_isEmpty (I := I) (M := M) ivp

noncomputable def localExistenceUniquenessFamily_of_isEmpty
    [IsEmpty M] :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (intrinsicLocalExistenceUniquenessFamily_of_isEmpty
    (I := I) (M := M)).toOrdinary

end Intrinsic

end Compact

end RicciFlow
