/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatAtlasCutoff

/-!
# The geometric residual of the finite tensor-heat atlas

This file computes the actual connection-heat residual of every partitioned
local inverse.  The identity is global in space: on the support of a
partition function the stored normalized coordinate equation supplies the
source, while off that support the source term vanishes.  The only remaining
term is the genuine connection-Laplacian cutoff commutator.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology

namespace RicciFlow
namespace AnalyticPDE
namespace FiniteTensorHeatParametrixAtlas

open CovariantDerivative
open PoincareCurvature.Bundle.Trivialization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [CompactSpace M] [SigmaCompactSpace M] [I.Boundaryless]

variable {d : ℕ} {t₀ T α : ℝ}

local notation "TM" => (TangentSpace I : M → Type _)
local notation "W₂" => (Fin d × Fin d → ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)

@[reducible] local instance atlasResidualThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedAddCommGroup
@[reducible] local instance atlasResidualThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  CovariantDerivative.coordinateThreeModelNormedSpace
@[reducible] local instance atlasResidualThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedAddCommGroup x
@[reducible] local instance atlasResidualThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) :=
  CovariantDerivative.coordinateThreeFiberNormedSpace x
local instance atlasResidualThreeTotalSpaceTopology :
    TopologicalSpace (TotalSpace
      (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance atlasResidualThreeFiberBundle :
    FiberBundle (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂
local instance atlasResidualThreeVectorBundle :
    VectorBundle ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] E →L[ℝ] ℝ) T₂

/-- Two covariant bilinear forms agree if they agree on every pair from a
local trivialization frame at the point. -/
theorem continuousBilinearMap_ext_localFrame
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E)
    {x : M} (hx : x ∈ e.baseSet) {F G : T₂ x}
    (h : ∀ i j, F (e.localFrame b i x) (e.localFrame b j x) =
      G (e.localFrame b i x) (e.localFrame b j x)) :
    F = G := by
  apply ContinuousLinearMap.coe_injective
  refine (e.basisAt b hx).ext (fun i => ?_)
  apply ContinuousLinearMap.coe_injective
  refine (e.basisAt b hx).ext (fun j => ?_)
  change F ((e.basisAt b hx) i) ((e.basisAt b hx) j) =
    G ((e.basisAt b hx) i) ((e.basisAt b hx) j)
  simpa only [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
    (e := e) (b := b) hx] using h i j

/-- The normalized residual of one partitioned atlas summand is its
partitioned coordinate source minus the exact cutoff commutator. -/
theorem normalized_cutoffLocalSummand_residual_apply
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    (s : ℝ) (hs : s ∈ Ioc t₀ T) (x : M) (p k : Fin d) :
    let e := trivializationAt E TM (i : M)
    let u := A.normalizedLocalSolution cov i q
    let cutoffField := cutoffLocalTensorOfMatrix (I := I) e b
      (A.cover.partition i)
      (normalizedTensorHeatCoefficientSlice (I := I)
        (i : M) (A.radius (i : M)) u s)
    (normalizedTensorHeatTimeDerivative (I := I) (i : M)
          (A.radius (i : M)) b (A.cover.partition i) u s x -
        A.radius (i : M) ^ 2 •
          connectionLaplacian cov cutoffField x)
        (e.localFrame b p x) (e.localFrame b k x) =
      A.cover.partition i x *
          ParabolicC0AlphaBanach.representative q
            (s, normalizedTensorHeatCoordinate (I := I)
              (i : M) (A.radius (i : M)) x) (k, p) -
        A.radius (i : M) ^ 2 *
          connectionLaplacianCutoffCommutator cov
            (A.cover.partition i)
            (A.bufferedLocalSolutionSlice cov i q s) x
            (e.localFrame b p x) (e.localFrame b k x) := by
  dsimp only
  have hlap := A.connectionLaplacian_cutoffLocalSummand_eq_buffered_add_commutator
    cov i q hs x
  rw [hlap]
  simp only [sub_apply, smul_apply, smul_eq_mul, add_apply]
  by_cases hψ : A.cover.partition i x = 0
  · simp [normalizedTensorHeatTimeDerivative,
      cutoffLocalTensorOfMatrix, hψ]
  · have hxSupport : x ∈ Function.support (A.cover.partition i) := by
      simpa [Function.mem_support] using hψ
    have hxPiece : x ∈ (A.cover.pieces i : Set M) :=
      subset_closure hxSupport
    have hxPatch : x ∈ actualLocalTensorHeatPatch (I := I)
        (i : M) (A.radius (i : M)) :=
      A.cover.pieces_subset_domain i hxPiece
    have hxFrame : x ∈ (trivializationAt E TM (i : M)).baseSet :=
      A.patch_subset_trivialization (i : M) hxPatch
    have hz : (s, normalizedTensorHeatCoordinate (I := I)
        (i : M) (A.radius (i : M)) x) ∈
        parabolicFiniteCylinder E t₀ T := by
      simpa using hs
    have htime :
        normalizedTensorHeatTimeDerivative (I := I) (i : M)
            (A.radius (i : M)) b (A.cover.partition i)
            (A.normalizedLocalSolution cov i q) s x
            ((trivializationAt E TM (i : M)).localFrame b p x)
            ((trivializationAt E TM (i : M)).localFrame b k x) =
          A.cover.partition i x *
            FiniteParabolicC2AlphaBanach.timeDeriv
              (A.localInverse (i : M) q)
              (s, normalizedTensorHeatCoordinate (I := I)
                (i : M) (A.radius (i : M)) x) (k, p) := by
      rw [normalizedTensorHeatTimeDerivative,
        cutoffLocalTensorOfMatrix_localFrame
          (I := I) (trivializationAt E TM (i : M)) b _ _ hxFrame]
      unfold normalizedLocalSolution
      simp only [FiniteParabolicC2AlphaBanach.timeDeriv_fiberPostcompL _ _ _ hz]
      rfl
    have heq := A.normalized_buffered_tensorHeatEquation_apply
      cov i q s hs hxPiece p k
    have hbtime := A.normalizedTensorHeatTimeDerivative_buffered_apply
      cov i q s hs hxPiece p k
    simp only [sub_apply, smul_apply, smul_eq_mul] at heq
    rw [hbtime] at heq
    have heq' :
        FiniteParabolicC2AlphaBanach.timeDeriv
              (A.localInverse (i : M) q)
              (s, normalizedTensorHeatCoordinate (I := I)
                (i : M) (A.radius (i : M)) x) (k, p) -
            A.radius (i : M) ^ 2 *
              connectionLaplacian cov
                (A.bufferedLocalSolutionSlice cov i q s) x
                ((trivializationAt E TM (i : M)).localFrame b p x)
                ((trivializationAt E TM (i : M)).localFrame b k x) =
          ParabolicC0AlphaBanach.representative q
            (s, normalizedTensorHeatCoordinate (I := I)
              (i : M) (A.radius (i : M)) x) (k, p) := by
      rw [← ParabolicC0AlphaBanach.evalCLM_eq_representative q _ hz]
      simpa only [sub_apply, smul_apply, smul_eq_mul] using heq
    rw [htime]
    linear_combination (A.cover.partition i x) * heq'

/-- The physical source tensor represented by one normalized atlas datum. -/
def physicalLocalSourceSlice
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    (t : ℝ) : ∀ x : M, T₂ x :=
  cutoffLocalTensorOfMatrix (I := I)
    (trivializationAt E TM (i : M)) b (A.cover.partition i)
    (fun x p k =>
      (A.radius (i : M))⁻¹ ^ 2 *
        ParabolicC0AlphaBanach.representative q
          (FiniteClassicalTensorHeatField.normalizedTime
              t₀ (A.radius (i : M)) t,
            normalizedTensorHeatCoordinate (I := I)
              (i : M) (A.radius (i : M)) x) (k, p))

@[simp] theorem physicalLocalSourceSlice_localFrame
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    (t : ℝ) {x : M}
    (hx : x ∈ (trivializationAt E TM (i : M)).baseSet)
    (p k : Fin d) :
    A.physicalLocalSourceSlice cov i q t x
        ((trivializationAt E TM (i : M)).localFrame b p x)
        ((trivializationAt E TM (i : M)).localFrame b k x) =
      A.cover.partition i x *
        ((A.radius (i : M))⁻¹ ^ 2 *
          ParabolicC0AlphaBanach.representative q
            (FiniteClassicalTensorHeatField.normalizedTime
                t₀ (A.radius (i : M)) t,
              normalizedTensorHeatCoordinate (I := I)
                (i : M) (A.radius (i : M)) x) (k, p)) := by
  rw [physicalLocalSourceSlice,
    cutoffLocalTensorOfMatrix_localFrame
      (I := I) (trivializationAt E TM (i : M)) b _ _ hx]

/-- After parabolic time rescaling, one atlas summand has the actual physical
connection-heat residual: the normalized source carries the factor `r⁻²`,
whereas the cutoff commutator is unscaled. -/
theorem localField_tensorHeatOperator_apply
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [Nonempty M]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    (t : ℝ) (ht : t ∈ Ioo t₀ A.commonTerminalTime)
    (x : M) (p k : Fin d) :
    (A.localField cov i q).tensorHeatOperator cov t ht x
        ((trivializationAt E TM (i : M)).localFrame b p x)
        ((trivializationAt E TM (i : M)).localFrame b k x) =
      (A.radius (i : M))⁻¹ ^ 2 * A.cover.partition i x *
          ParabolicC0AlphaBanach.representative q
            (FiniteClassicalTensorHeatField.normalizedTime
                t₀ (A.radius (i : M)) t,
              normalizedTensorHeatCoordinate (I := I)
                (i : M) (A.radius (i : M)) x) (k, p) -
        connectionLaplacianCutoffCommutator cov
            (A.cover.partition i)
            (A.bufferedLocalSolutionSlice cov i q
              (FiniteClassicalTensorHeatField.normalizedTime
                t₀ (A.radius (i : M)) t)) x
            ((trivializationAt E TM (i : M)).localFrame b p x)
            ((trivializationAt E TM (i : M)).localFrame b k x) := by
  let r : ℝ := A.radius (i : M)
  let s : ℝ := FiniteClassicalTensorHeatField.normalizedTime t₀ r t
  have hr : r ≠ 0 := ne_of_gt (A.radius_pos (i : M))
  have htPhysical : t ∈ Ioc t₀
      (FiniteClassicalTensorHeatField.physicalTerminalTime t₀ T r) :=
    ⟨ht.1, ht.2.le.trans (A.commonTerminalTime_le cov i)⟩
  have hs : s ∈ Ioc t₀ T :=
    FiniteClassicalTensorHeatField.normalizedTime_mem_Ioc hr htPhysical
  have hnormalized := A.normalized_cutoffLocalSummand_residual_apply
    cov i q s hs x p k
  dsimp only at hnormalized
  simp only [sub_apply, smul_apply, smul_eq_mul] at hnormalized
  change r⁻¹ ^ 2 *
        normalizedTensorHeatTimeDerivative (I := I) (i : M) r b
          (A.cover.partition i) (A.normalizedLocalSolution cov i q) s x
          ((trivializationAt E TM (i : M)).localFrame b p x)
          ((trivializationAt E TM (i : M)).localFrame b k x) -
      connectionLaplacian cov
          (cutoffLocalTensorOfMatrix (I := I)
            (trivializationAt E TM (i : M)) b (A.cover.partition i)
            (normalizedTensorHeatCoefficientSlice (I := I)
              (i : M) r (A.normalizedLocalSolution cov i q) s)) x
          ((trivializationAt E TM (i : M)).localFrame b p x)
          ((trivializationAt E TM (i : M)).localFrame b k x) = _
  calc
    _ = r⁻¹ ^ 2 *
        (normalizedTensorHeatTimeDerivative (I := I) (i : M) r b
            (A.cover.partition i) (A.normalizedLocalSolution cov i q) s x
            ((trivializationAt E TM (i : M)).localFrame b p x)
            ((trivializationAt E TM (i : M)).localFrame b k x) -
          r ^ 2 *
            connectionLaplacian cov
              (cutoffLocalTensorOfMatrix (I := I)
                (trivializationAt E TM (i : M)) b (A.cover.partition i)
                (normalizedTensorHeatCoefficientSlice (I := I)
                  (i : M) r (A.normalizedLocalSolution cov i q) s)) x
              ((trivializationAt E TM (i : M)).localFrame b p x)
              ((trivializationAt E TM (i : M)).localFrame b k x)) := by
          field_simp [hr]
    _ = r⁻¹ ^ 2 *
        (A.cover.partition i x *
            ParabolicC0AlphaBanach.representative q
              (s, normalizedTensorHeatCoordinate (I := I)
                (i : M) r x) (k, p) -
          r ^ 2 *
            connectionLaplacianCutoffCommutator cov
              (A.cover.partition i)
              (A.bufferedLocalSolutionSlice cov i q s) x
              ((trivializationAt E TM (i : M)).localFrame b p x)
              ((trivializationAt E TM (i : M)).localFrame b k x)) := by
          dsimp only [r]
          rw [hnormalized]
    _ = _ := by
      dsimp only [r, s]
      field_simp [ne_of_gt (A.radius_pos (i : M))]

/-- Intrinsic tensor form of the physical residual identity for one atlas
summand. -/
theorem localField_tensorHeatOperator_eq_source_sub_commutator
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [Nonempty M]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (i : A.cover.Index)
    (q : ParabolicC0AlphaBanach E W₂ α
      (parabolicFiniteCylinder E t₀ T))
    (t : ℝ) (ht : t ∈ Ioo t₀ A.commonTerminalTime)
    (x : M) :
    (A.localField cov i q).tensorHeatOperator cov t ht x =
      A.physicalLocalSourceSlice cov i q t x -
        connectionLaplacianCutoffCommutator cov
          (A.cover.partition i)
          (A.bufferedLocalSolutionSlice cov i q
            (FiniteClassicalTensorHeatField.normalizedTime
              t₀ (A.radius (i : M)) t)) x := by
  let r : ℝ := A.radius (i : M)
  let s : ℝ := FiniteClassicalTensorHeatField.normalizedTime t₀ r t
  have hr : r ≠ 0 := ne_of_gt (A.radius_pos (i : M))
  have htPhysical : t ∈ Ioc t₀
      (FiniteClassicalTensorHeatField.physicalTerminalTime t₀ T r) :=
    ⟨ht.1, ht.2.le.trans (A.commonTerminalTime_le cov i)⟩
  have hs : s ∈ Ioc t₀ T :=
    FiniteClassicalTensorHeatField.normalizedTime_mem_Ioc hr htPhysical
  by_cases hpsi : A.cover.partition i x = 0
  · have hlap :=
      A.connectionLaplacian_cutoffLocalSummand_eq_buffered_add_commutator
        cov i q hs x
    change r⁻¹ ^ 2 •
          normalizedTensorHeatTimeDerivative (I := I) (i : M) r b
            (A.cover.partition i) (A.normalizedLocalSolution cov i q) s x -
        connectionLaplacian cov
          (cutoffLocalTensorOfMatrix (I := I)
            (trivializationAt E TM (i : M)) b (A.cover.partition i)
            (normalizedTensorHeatCoefficientSlice (I := I)
              (i : M) r (A.normalizedLocalSolution cov i q) s)) x =
      A.physicalLocalSourceSlice cov i q t x -
        connectionLaplacianCutoffCommutator cov
          (A.cover.partition i) (A.bufferedLocalSolutionSlice cov i q s) x
    dsimp only [r, s] at hlap ⊢
    rw [hlap]
    simp [physicalLocalSourceSlice, normalizedTensorHeatTimeDerivative,
      cutoffLocalTensorOfMatrix, hpsi]
    ext v w
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul,
      zero_mul, mul_zero, zero_sub, zero_add]
  · have hxSupport : x ∈ Function.support (A.cover.partition i) := by
      simpa [Function.mem_support] using hpsi
    have hxPiece : x ∈ (A.cover.pieces i : Set M) :=
      subset_closure hxSupport
    have hxPatch := A.cover.pieces_subset_domain i hxPiece
    have hxFrame : x ∈ (trivializationAt E TM (i : M)).baseSet :=
      A.patch_subset_trivialization (i : M) hxPatch
    apply continuousBilinearMap_ext_localFrame
      (I := I) (trivializationAt E TM (i : M)) b hxFrame
    intro p k
    simp only [sub_apply]
    rw [A.localField_tensorHeatOperator_apply cov i q t ht x p k]
    rw [A.physicalLocalSourceSlice_localFrame cov i q t hxFrame p k]
    ring

/-- The physical tensor source assembled from all normalized atlas data. -/
def physicalAtlasSourceSlice
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (q : A.cover.Index →
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ T))
    (t : ℝ) (x : M) : T₂ x :=
  ∑ i : A.cover.Index, A.physicalLocalSourceSlice cov i (q i) t x

/-- The finite sum of the genuine cutoff commutators generated by the atlas
parametrix. -/
def atlasCommutatorSlice
    (cov : CovariantDerivative I E TM)
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (q : A.cover.Index →
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ T))
    (t : ℝ) (x : M) : T₂ x :=
  ∑ i : A.cover.Index,
    connectionLaplacianCutoffCommutator cov
      (A.cover.partition i)
      (A.bufferedLocalSolutionSlice cov i (q i)
        (FiniteClassicalTensorHeatField.normalizedTime
          t₀ (A.radius (i : M)) t)) x

/-- Intrinsic residual identity for the whole finite atlas parametrix. -/
theorem parametrixField_tensorHeatOperator_eq_source_sub_commutator
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [Nonempty M]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (q : A.cover.Index →
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ T))
    (t : ℝ) (ht : t ∈ Ioo t₀ A.commonTerminalTime)
    (x : M) :
    (A.parametrixField cov q).tensorHeatOperator cov t ht x =
      A.physicalAtlasSourceSlice cov q t x -
        A.atlasCommutatorSlice cov q t x := by
  unfold parametrixField physicalAtlasSourceSlice atlasCommutatorSlice
  rw [FiniteClassicalTensorHeatField.tensorHeatOperator_finsetSum]
  calc
    _ = ∑ i : A.cover.Index,
          (A.physicalLocalSourceSlice cov i (q i) t x -
            connectionLaplacianCutoffCommutator cov
              (A.cover.partition i)
              (A.bufferedLocalSolutionSlice cov i (q i)
                (FiniteClassicalTensorHeatField.normalizedTime
                  t₀ (A.radius (i : M)) t)) x) := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact A.localField_tensorHeatOperator_eq_source_sub_commutator
          cov i (q i) t ht x
    _ = _ := by
      simpa only using
        (Finset.sum_sub_distrib
          (s := Finset.univ)
          (fun i : A.cover.Index =>
            A.physicalLocalSourceSlice cov i (q i) t x)
          (fun i : A.cover.Index =>
            connectionLaplacianCutoffCommutator cov
              (A.cover.partition i)
              (A.bufferedLocalSolutionSlice cov i (q i)
                (FiniteClassicalTensorHeatField.normalizedTime
                  t₀ (A.radius (i : M)) t)) x))

/-- The genuine connection-heat operator of the finite atlas parametrix is
the finite sum of its rescaled partitioned sources minus the finite sum of
the actual cutoff commutators. -/
theorem parametrixField_tensorHeatOperator_apply
    (cov : CovariantDerivative I E TM)
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [ContMDiffCovariantDerivative
      (covariantTwoTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 2]
    [ContMDiffCovariantDerivative
      (covariantThreeTensorCovariantDerivative
        (E := E) (I := I) (M := M) cov) 1]
    [Nonempty M]
    {b : Module.Basis (Fin d) ℝ E}
    (A : FiniteTensorHeatParametrixAtlas
      (E := E) (I := I) (M := M) cov b t₀ T α)
    (q : A.cover.Index →
      ParabolicC0AlphaBanach E W₂ α
        (parabolicFiniteCylinder E t₀ T))
    (t : ℝ) (ht : t ∈ Ioo t₀ A.commonTerminalTime)
    (x : M) (p k : Fin d) :
    (A.parametrixField cov q).tensorHeatOperator cov t ht x
        ((trivializationAt E TM x).localFrame b p x)
        ((trivializationAt E TM x).localFrame b k x) =
      ∑ i : A.cover.Index,
        (A.localField cov i (q i)).tensorHeatOperator cov t ht x
          ((trivializationAt E TM x).localFrame b p x)
          ((trivializationAt E TM x).localFrame b k x) := by
  unfold parametrixField
  rw [FiniteClassicalTensorHeatField.tensorHeatOperator_finsetSum]
  simp only [_root_.sum_apply]

end FiniteTensorHeatParametrixAtlas
end AnalyticPDE
end RicciFlow
