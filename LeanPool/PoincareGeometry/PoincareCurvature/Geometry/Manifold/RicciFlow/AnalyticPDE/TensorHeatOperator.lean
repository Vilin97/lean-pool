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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacianLeibniz
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# The classical tensor heat operator

This module bundles the genuine domain of the time-dependent connection heat
operator. A field contains spatial slices in
`ConnectionLaplacianDomain cov` and an actual time-derivative witness at every
space-time point. On this domain the operator is literally

`P u = ∂ₜu - Δ u`.

No regularity or PDE identity is postulated: spatial differentiability is
carried by the connection-Laplacian domain and temporal differentiability by
`HasDerivAt`.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

namespace CovariantDerivative

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)

-- Break the nested operator-space instance-search cycle explicitly.
local instance heatOperatorOneModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance heatOperatorOneModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance heatOperatorTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance heatOperatorTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance heatOperatorOneFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₁ x) := ContinuousLinearMap.toNormedAddCommGroup
local instance heatOperatorOneFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₁ x) := ContinuousLinearMap.toNormedSpace
local instance heatOperatorTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) := ContinuousLinearMap.toNormedAddCommGroup
local instance heatOperatorTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) := ContinuousLinearMap.toNormedSpace

/-- Classical time-dependent covariant two-tensors on which both `∂ₜ` and
the genuine connection Laplacian are defined. -/
structure ClassicalTensorHeatField (cov : CovariantDerivative I E TM) where
  /-- Every fixed-time slice lies in the genuine second-order domain. -/
  slice : ℝ → ConnectionLaplacianDomain cov
  /-- The pointwise time derivative. -/
  timeDerivative : ℝ → ∀ x : M, T₂ x
  /-- The stored field is the genuine derivative of every fixed-space fibre
  curve. -/
  hasTimeDerivative : ∀ t x,
    HasDerivAt (fun s : ℝ => (slice s).1 x) (timeDerivative t x) t

namespace ClassicalTensorHeatField

/-- The underlying time-dependent tensor section. -/
def toFun (cov : CovariantDerivative I E TM)
    (u : ClassicalTensorHeatField cov) : ℝ → ∀ x : M, T₂ x :=
  fun t => (u.slice t).1

@[simp] theorem slice_coe (cov : CovariantDerivative I E TM)
    (u : ClassicalTensorHeatField cov) (t : ℝ) :
    (u.slice t).1 = toFun cov u t :=
  rfl

/-- Restatement of the field's temporal differentiability witness. -/
theorem hasDerivAt_toFun (cov : CovariantDerivative I E TM)
    (u : ClassicalTensorHeatField cov) (t : ℝ) (x : M) :
    HasDerivAt (fun s : ℝ => toFun cov u s x)
      (u.timeDerivative t x) t :=
  u.hasTimeDerivative t x

end ClassicalTensorHeatField

/-- Tensor-valued forcing fields for the connection heat equation. -/
abbrev TensorHeatForcing := ℝ → ∀ x : M, T₂ x

/-- The actual classical tensor heat operator `∂ₜ - Δ` on its genuine
time-and-space differentiability domain. -/
def tensorHeatOperator (cov : CovariantDerivative I E TM)
    (u : ClassicalTensorHeatField cov) : TensorHeatForcing (I := I) (M := M) :=
  fun t x => u.timeDerivative t x -
    connectionLaplacian cov (ClassicalTensorHeatField.toFun cov u t) x

@[simp]
theorem tensorHeatOperator_apply
    (cov : CovariantDerivative I E TM)
    (u : ClassicalTensorHeatField cov) (t : ℝ) (x : M) :
    tensorHeatOperator cov u t x =
      u.timeDerivative t x -
        connectionLaplacian cov (ClassicalTensorHeatField.toFun cov u t) x :=
  rfl

/-- Initial trace of a classical tensor heat field. -/
def tensorHeatInitialTrace (cov : CovariantDerivative I E TM)
    (u : ClassicalTensorHeatField cov) : ∀ x : M, T₂ x :=
  ClassicalTensorHeatField.toFun cov u 0

@[simp]
theorem tensorHeatInitialTrace_apply
    (cov : CovariantDerivative I E TM) (u : ClassicalTensorHeatField cov) :
    tensorHeatInitialTrace cov u = ClassicalTensorHeatField.toFun cov u 0 :=
  rfl

/-- Pointwise symmetry of every spatial slice of a classical tensor heat
field. -/
def ClassicalTensorHeatField.IsSymmetric
    {cov : CovariantDerivative I E TM} (u : ClassicalTensorHeatField cov) : Prop :=
  ∀ t x a b,
    ClassicalTensorHeatField.toFun cov u t x a b =
      ClassicalTensorHeatField.toFun cov u t x b a

/-- Evaluation of a bilinear form at two fixed fibre vectors, as a bounded
linear functional. -/
def bilinearEvaluationCLM (x : M) (a b : TM x) : T₂ x →L[ℝ] ℝ :=
  ((ContinuousLinearMap.apply ℝ ℝ) b).comp
    ((ContinuousLinearMap.apply ℝ (T₁ x)) a)

@[simp]
theorem bilinearEvaluationCLM_apply (x : M) (a b : TM x) (q : T₂ x) :
    bilinearEvaluationCLM x a b q = q a b :=
  rfl

/-- Differentiating a curve of symmetric bilinear forms preserves symmetry
of its genuine time derivative. -/
theorem ClassicalTensorHeatField.timeDerivative_swap
    (cov : CovariantDerivative I E TM) {u : ClassicalTensorHeatField cov}
    (hu : ClassicalTensorHeatField.IsSymmetric u)
    (t : ℝ) (x : M) (a b : TM x) :
    u.timeDerivative t x a b = u.timeDerivative t x b a := by
  have hbase := ClassicalTensorHeatField.hasDerivAt_toFun cov u t x
  have hab :=
    (bilinearEvaluationCLM x a b).hasFDerivAt.comp_hasDerivAt t hbase
  have hba :=
    (bilinearEvaluationCLM x b a).hasFDerivAt.comp_hasDerivAt t hbase
  have hfun :
      (bilinearEvaluationCLM x a b) ∘
          (fun s : ℝ => ClassicalTensorHeatField.toFun cov u s x) =
        (bilinearEvaluationCLM x b a) ∘
          (fun s : ℝ => ClassicalTensorHeatField.toFun cov u s x) := by
    funext s
    exact hu s x a b
  rw [hfun] at hab
  simpa using hab.unique hba

/-- The genuine heat operator preserves symmetry: both the temporal
derivative and the connection Laplacian preserve the final two tensor slots. -/
theorem tensorHeatOperator_swap
    (cov : CovariantDerivative I E TM) {u : ClassicalTensorHeatField cov}
    (hu : ClassicalTensorHeatField.IsSymmetric u)
    (t : ℝ) (x : M) (a b : TM x) :
    tensorHeatOperator cov u t x a b = tensorHeatOperator cov u t x b a := by
  change
    (u.timeDerivative t x -
      connectionLaplacian cov (ClassicalTensorHeatField.toFun cov u t) x) a b =
    (u.timeDerivative t x -
      connectionLaplacian cov (ClassicalTensorHeatField.toFun cov u t) x) b a
  simp only [ContinuousLinearMap.sub_apply]
  rw [ClassicalTensorHeatField.timeDerivative_swap cov hu t x a b]
  rw [connectionLaplacian_swap cov (hu t) x a b]

end CovariantDerivative
