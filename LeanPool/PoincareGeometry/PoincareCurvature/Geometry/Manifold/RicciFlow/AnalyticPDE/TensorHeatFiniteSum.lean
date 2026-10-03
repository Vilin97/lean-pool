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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatOperator

/-!
# Finite sums of classical tensor-heat fields

The local-to-global parametrix is a finite partition-of-unity sum.  This file
establishes the exact algebraic bridge on the genuine geometric domain:
finite sums preserve the stored spatial and temporal differentiability, the
actual connection heat operator distributes over the sum, initial traces add,
and symmetry is preserved.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

namespace CovariantDerivative
namespace ClassicalTensorHeatField

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)

-- Break the nested operator-space instance-search cycle explicitly.
local instance finiteSumOneModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance finiteSumOneModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance finiteSumTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance finiteSumTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance finiteSumOneFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₁ x) := ContinuousLinearMap.toNormedAddCommGroup
local instance finiteSumOneFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₁ x) := ContinuousLinearMap.toNormedSpace
local instance finiteSumTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) := ContinuousLinearMap.toNormedAddCommGroup
local instance finiteSumTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) := ContinuousLinearMap.toNormedSpace

/-- Finite sum of classical tensor-heat fields. -/
def finsetSum (cov : _root_.CovariantDerivative I E TM)
    {ι : Type*} (s : Finset ι)
    (u : ι → _root_.CovariantDerivative.ClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov) :
    _root_.CovariantDerivative.ClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov where
  slice t := ∑ i ∈ s, (u i).slice t
  timeDerivative t x := ∑ i ∈ s, (u i).timeDerivative t x
  hasTimeDerivative := by
    intro t x
    have h :
        HasDerivAt
          (fun r : ℝ => ∑ i ∈ s, ((u i).slice r).1 x)
          (∑ i ∈ s, (u i).timeDerivative t x) t :=
      HasDerivAt.fun_sum fun i _ => (u i).hasTimeDerivative t x
    simpa only [Finset.sum_apply, Submodule.coe_sum] using h

@[simp]
theorem finsetSum_slice {ι : Type*} (s : Finset ι)
    (cov : _root_.CovariantDerivative I E TM)
    (u : ι → _root_.CovariantDerivative.ClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov) (t : ℝ) :
    (finsetSum cov s u).slice t = ∑ i ∈ s, (u i).slice t :=
  rfl

@[simp]
theorem finsetSum_timeDerivative {ι : Type*} (s : Finset ι)
    (cov : _root_.CovariantDerivative I E TM)
    (u : ι → _root_.CovariantDerivative.ClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov)
    (t : ℝ) (x : M) :
    (finsetSum cov s u).timeDerivative t x =
      ∑ i ∈ s, (u i).timeDerivative t x :=
  rfl

@[simp]
theorem toFun_finsetSum {ι : Type*} (s : Finset ι)
    (cov : _root_.CovariantDerivative I E TM)
    (u : ι → _root_.CovariantDerivative.ClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov)
    (t : ℝ) (x : M) :
    toFun (E := E) (I := I) (M := M) cov (finsetSum cov s u) t x =
      ∑ i ∈ s, toFun (E := E) (I := I) (M := M) cov (u i) t x := by
  simp only [toFun, finsetSum, Finset.sum_apply, Submodule.coe_sum]

/-- The genuine connection heat operator distributes over finite sums. -/
theorem tensorHeatOperator_finsetSum {ι : Type*} (s : Finset ι)
    (cov : _root_.CovariantDerivative I E TM)
    (u : ι → _root_.CovariantDerivative.ClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov)
    (t : ℝ) (x : M) :
    tensorHeatOperator (E := E) (I := I) (M := M) cov (finsetSum cov s u) t x =
      ∑ i ∈ s,
        tensorHeatOperator (E := E) (I := I) (M := M) cov (u i) t x := by
  change
    (∑ i ∈ s, (u i).timeDerivative t x) -
        connectionLaplacian cov (↑(∑ i ∈ s, (u i).slice t)) x =
      ∑ i ∈ s,
        ((u i).timeDerivative t x -
          connectionLaplacian cov (↑((u i).slice t)) x)
  have hLap :
      connectionLaplacian cov (↑(∑ i ∈ s, (u i).slice t)) x =
        ∑ i ∈ s, connectionLaplacian cov (↑((u i).slice t)) x := by
    change connectionLaplacianLinearMapAt cov x
        (∑ i ∈ s, (u i).slice t) =
      ∑ i ∈ s, connectionLaplacianLinearMapAt cov x ((u i).slice t)
    exact map_sum (connectionLaplacianLinearMapAt cov x) _ _
  rw [hLap]
  rw [Finset.sum_sub_distrib]

/-- Initial traces add under finite summation. -/
theorem tensorHeatInitialTrace_finsetSum {ι : Type*} (s : Finset ι)
    (cov : _root_.CovariantDerivative I E TM)
    (u : ι → _root_.CovariantDerivative.ClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov)
    (x : M) :
    tensorHeatInitialTrace (E := E) (I := I) (M := M) cov
        (finsetSum cov s u) x =
      ∑ i ∈ s,
        tensorHeatInitialTrace (E := E) (I := I) (M := M) cov (u i) x := by
  simp only [tensorHeatInitialTrace, toFun, finsetSum, Finset.sum_apply,
    Submodule.coe_sum]

/-- A finite sum of pointwise symmetric tensor fields remains symmetric. -/
theorem isSymmetric_finsetSum {ι : Type*} (s : Finset ι)
    (cov : _root_.CovariantDerivative I E TM)
    (u : ι → _root_.CovariantDerivative.ClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov)
    (hu : ∀ i ∈ s, (u i).IsSymmetric) :
    (finsetSum cov s u).IsSymmetric := by
  intro t x a b
  simp only [toFun_finsetSum]
  simp only [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact hu i hi t x a b

end ClassicalTensorHeatField
end CovariantDerivative
