/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatOperator

/-!
# Classical tensor heat fields on a finite forward interval

The global-in-time `ClassicalTensorHeatField` is intentionally too strong for
a parabolic Cauchy problem constructed on one finite cylinder.  This module
records exactly the available geometric regularity: genuine
connection-Laplacian domain membership for every positive-time slice and an
actual time derivative only in the open time interval.

The initial value is expressed separately by `HasInitialTrace`, as convergence
from `(t₀,T]`.  Thus no arbitrary value of a totalized coordinate
representative at the missing initial face can masquerade as initial data.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Filter Set
open scoped Manifold ContDiff Topology

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
local instance finiteIntervalOneModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance finiteIntervalOneModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance finiteIntervalTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance finiteIntervalTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance finiteIntervalOneFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₁ x) := ContinuousLinearMap.toNormedAddCommGroup
local instance finiteIntervalOneFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₁ x) := ContinuousLinearMap.toNormedSpace
local instance finiteIntervalTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) := ContinuousLinearMap.toNormedAddCommGroup
local instance finiteIntervalTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) := ContinuousLinearMap.toNormedSpace

/-- A classical covariant-two-tensor field on the finite forward interval
`(t₀,T]`, with temporal differentiability on `(t₀,T)`.

`toFun` is total only so that ordinary `HasDerivAt` can be used.  Its values
outside the stated interval carry no meaning and no regularity claim. -/
structure FiniteClassicalTensorHeatField
    (cov : CovariantDerivative I E TM) (t₀ T : ℝ) where
  /-- The underlying time-dependent tensor section. -/
  toFun : ℝ → ∀ x : M, T₂ x
  /-- Every positive-time slice lies in the genuine second-order domain. -/
  slice_mem : ∀ t ∈ Ioc t₀ T, toFun t ∈ ConnectionLaplacianDomain cov
  /-- The pointwise time derivative on the totalized carrier. -/
  timeDerivative : ℝ → ∀ x : M, T₂ x
  /-- Temporal differentiability is asserted exactly in the open interval,
  after evaluation on arbitrary fibre vectors.  This scalar formulation is
  equivalent to differentiability in the finite-dimensional tensor fibre and
  avoids committing the public geometric interface to a particular
  definitionally chosen norm topology on nested continuous-linear-map types. -/
  hasTimeDerivative : ∀ t ∈ Ioo t₀ T, ∀ x : M, ∀ a b : TM x,
    letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
    letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
    letI : TopologicalSpace ℝ :=
      Real.normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    HasDerivAt (fun s : ℝ => toFun s x a b) (timeDerivative t x a b) t

namespace FiniteClassicalTensorHeatField

variable {t₀ T : ℝ}

/-- A positive-time spatial slice as an element of the genuine
connection-Laplacian domain. -/
def slice (cov : CovariantDerivative I E TM)
    (u : FiniteClassicalTensorHeatField
    (E := E) (I := I) (M := M) cov t₀ T)
    (t : ℝ) (ht : t ∈ Ioc t₀ T) :
    ConnectionLaplacianDomain (E := E) (I := I) (M := M) cov :=
  ⟨u.toFun t, u.slice_mem t ht⟩

@[simp] theorem slice_coe (cov : CovariantDerivative I E TM)
    (u : FiniteClassicalTensorHeatField
    (E := E) (I := I) (M := M) cov t₀ T)
    (t : ℝ) (ht : t ∈ Ioc t₀ T) :
    (u.slice cov t ht).1 = u.toFun t :=
  rfl

/-- The actual finite-interval connection heat operator `∂ₜu - Δu`. -/
def tensorHeatOperator (cov : CovariantDerivative I E TM)
    (u : FiniteClassicalTensorHeatField
    (E := E) (I := I) (M := M) cov t₀ T)
    (t : ℝ) (ht : t ∈ Ioo t₀ T) : ∀ x : M, T₂ x :=
  fun x => u.timeDerivative t x -
    connectionLaplacian (E := E) (I := I) (M := M)
      cov (u.slice cov t ⟨ht.1, ht.2.le⟩).1 x

@[simp] theorem tensorHeatOperator_apply
    (cov : CovariantDerivative I E TM)
    (u : FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀ T)
    (t : ℝ) (ht : t ∈ Ioo t₀ T) (x : M) :
    u.tensorHeatOperator cov t ht x = u.timeDerivative t x -
      connectionLaplacian (E := E) (I := I) (M := M) cov (u.toFun t) x :=
  rfl

/-- `u₀` is the canonical initial trace when the positive-time field
converges to it pointwise from within `(t₀,T]`. -/
def HasInitialTrace (cov : CovariantDerivative I E TM)
    (u : FiniteClassicalTensorHeatField
    (E := E) (I := I) (M := M) cov t₀ T)
    (u₀ : ∀ x : M, T₂ x) : Prop :=
  ∀ x : M, Tendsto (fun t : ℝ => u.toFun t x)
    (nhdsWithin t₀ (Ioc t₀ T)) (nhds (u₀ x))

/-! ## Restriction to a shorter terminal time -/

/-- Restrict a finite-interval field to any no-later terminal time.  The
underlying totalized representative is unchanged; only the interval on which
its spatial and temporal regularity is asserted becomes smaller. -/
def restrictTerminal (cov : CovariantDerivative I E TM)
    (u : FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀ T)
    (T' : ℝ) (hT' : T' ≤ T) :
    FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀ T' where
  toFun := u.toFun
  slice_mem t ht := u.slice_mem t ⟨ht.1, ht.2.trans hT'⟩
  timeDerivative := u.timeDerivative
  hasTimeDerivative t ht :=
    u.hasTimeDerivative t ⟨ht.1, ht.2.trans_le hT'⟩

@[simp] theorem restrictTerminal_toFun (cov : CovariantDerivative I E TM)
    (u : FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀ T)
    (T' : ℝ) (hT' : T' ≤ T) :
    (restrictTerminal cov u T' hT').toFun = u.toFun :=
  rfl

@[simp] theorem restrictTerminal_timeDerivative
    (cov : CovariantDerivative I E TM)
    (u : FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀ T)
    (T' : ℝ) (hT' : T' ≤ T) :
    (restrictTerminal cov u T' hT').timeDerivative = u.timeDerivative :=
  rfl

theorem hasInitialTrace_restrictTerminal
    (cov : CovariantDerivative I E TM)
    (u : FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀ T)
    (u₀ : ∀ x : M, T₂ x) (T' : ℝ) (hT' : T' ≤ T)
    (hu : HasInitialTrace cov u u₀) :
    HasInitialTrace cov (restrictTerminal cov u T' hT') u₀ := by
  intro x
  exact (hu x).mono_left (nhdsWithin_mono t₀ fun _ ht =>
    ⟨ht.1, ht.2.trans hT'⟩)

/-! ## Finite synthesis on a common interval -/

/-- Finite sum of finite-interval classical tensor fields. -/
def finsetSum (cov : CovariantDerivative I E TM)
    {ι : Type*} (s : Finset ι)
    (u : ι → FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀ T) :
    FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀ T where
  toFun t x := ∑ i ∈ s, (u i).toFun t x
  slice_mem t ht := by
    change (fun x => ∑ i ∈ s, (u i).toFun t x) ∈
      ConnectionLaplacianDomain (E := E) (I := I) (M := M) cov
    have hsum :
        (fun x => ∑ i ∈ s, (u i).toFun t x) =
          ∑ i ∈ s, (u i).toFun t := by
      funext x
      exact (Finset.sum_apply x s (fun i => (u i).toFun t)).symm
    rw [hsum]
    exact Submodule.sum_mem
        (ConnectionLaplacianDomain (E := E) (I := I) (M := M) cov)
        (t := s) (f := fun i => (u i).toFun t)
        (fun i hi => (u i).slice_mem t ht)
  timeDerivative t x := ∑ i ∈ s, (u i).timeDerivative t x
  hasTimeDerivative := by
    intro t ht x v w
    have h : HasDerivAt
        (fun r : ℝ => ∑ i ∈ s, (u i).toFun r x v w)
        (∑ i ∈ s, (u i).timeDerivative t x v w) t :=
      HasDerivAt.fun_sum fun i _ => (u i).hasTimeDerivative t ht x v w
    simpa only [_root_.sum_apply] using h

@[simp] theorem finsetSum_toFun (cov : CovariantDerivative I E TM)
    {ι : Type*} (s : Finset ι)
    (u : ι → FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀ T)
    (t : ℝ) (x : M) :
    (finsetSum cov s u).toFun t x = ∑ i ∈ s, (u i).toFun t x :=
  rfl

@[simp] theorem finsetSum_timeDerivative
    (cov : CovariantDerivative I E TM)
    {ι : Type*} (s : Finset ι)
    (u : ι → FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀ T)
    (t : ℝ) (x : M) :
    (finsetSum cov s u).timeDerivative t x =
      ∑ i ∈ s, (u i).timeDerivative t x :=
  rfl

/-- Pointwise symmetry of a finite-interval tensor field. -/
def IsSymmetric (cov : CovariantDerivative I E TM)
    (u : FiniteClassicalTensorHeatField
    (E := E) (I := I) (M := M) cov t₀ T) : Prop :=
  ∀ t x a b, u.toFun t x a b = u.toFun t x b a

theorem isSymmetric_finsetSum (cov : CovariantDerivative I E TM)
    {ι : Type*} (s : Finset ι)
    (u : ι → FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀ T)
    (hu : ∀ i ∈ s, IsSymmetric cov (u i)) :
    IsSymmetric cov (finsetSum cov s u) := by
  intro t x a b
  simp only [finsetSum_toFun, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  exact hu i hi t x a b

/-- The genuine finite-interval connection heat operator distributes over a
finite sum. -/
theorem tensorHeatOperator_finsetSum (cov : CovariantDerivative I E TM)
    {ι : Type*} (s : Finset ι)
    (u : ι → FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀ T)
    (t : ℝ) (ht : t ∈ Ioo t₀ T) (x : M) :
    (finsetSum cov s u).tensorHeatOperator cov t ht x =
      ∑ i ∈ s, (u i).tensorHeatOperator cov t ht x := by
  change
    (∑ i ∈ s, (u i).timeDerivative t x) -
        connectionLaplacian cov (fun y => ∑ i ∈ s, (u i).toFun t y) x =
      ∑ i ∈ s,
        ((u i).timeDerivative t x -
          connectionLaplacian cov ((u i).toFun t) x)
  have hsection : (fun y => ∑ i ∈ s, (u i).toFun t y) =
      ∑ i ∈ s, (u i).toFun t := by
    funext y
    exact (Finset.sum_apply y s (fun i => (u i).toFun t)).symm
  rw [hsection]
  have hLap :
      connectionLaplacian cov (∑ i ∈ s, (u i).toFun t) x =
        ∑ i ∈ s, connectionLaplacian cov ((u i).toFun t) x := by
    have hLap' :
        connectionLaplacian cov
            (↑(∑ i ∈ s, (u i).slice cov t ⟨ht.1, ht.2.le⟩)) x =
          ∑ i ∈ s, connectionLaplacian cov
            (↑((u i).slice cov t ⟨ht.1, ht.2.le⟩)) x := by
      change connectionLaplacianLinearMapAt cov x
          (∑ i ∈ s, (u i).slice cov t ⟨ht.1, ht.2.le⟩) =
        ∑ i ∈ s, connectionLaplacianLinearMapAt cov x
          ((u i).slice cov t ⟨ht.1, ht.2.le⟩)
      exact map_sum (connectionLaplacianLinearMapAt cov x) _ _
    simpa only [Submodule.coe_sum, slice] using hLap'
  rw [hLap, Finset.sum_sub_distrib]

/-- Initial traces add under finite summation on a common interval. -/
theorem hasInitialTrace_finsetSum (cov : CovariantDerivative I E TM)
    {ι : Type*} (s : Finset ι)
    (u : ι → FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀ T)
    (u₀ : ι → ∀ x : M, T₂ x)
    (hu : ∀ i ∈ s, HasInitialTrace cov (u i) (u₀ i)) :
    HasInitialTrace cov (finsetSum cov s u)
      (fun x => ∑ i ∈ s, u₀ i x) := by
  intro x
  exact tendsto_finsetSum s fun i hi => hu i hi x

/-! ## Parabolic time rescaling -/

/-- The physical terminal time corresponding to the normalized interval at
spatial scale r. -/
def physicalTerminalTime (t₀ T r : ℝ) : ℝ :=
  t₀ + r ^ 2 * (T - t₀)

theorem lt_physicalTerminalTime {t₀ T r : ℝ} (hT : t₀ < T)
    (hr : r ≠ 0) : t₀ < physicalTerminalTime t₀ T r := by
  rw [physicalTerminalTime]
  have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  nlinarith

/-- Recover normalized time from physical time at parabolic scale r. -/
def normalizedTime (t₀ r t : ℝ) : ℝ :=
  t₀ + r⁻¹ ^ 2 * (t - t₀)

theorem normalizedTime_mem_Ioc {t₀ T r t : ℝ} (hr : r ≠ 0)
    (ht : t ∈ Ioc t₀ (physicalTerminalTime t₀ T r)) :
    normalizedTime t₀ r t ∈ Ioc t₀ T := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  have hrInv2 : 0 < r⁻¹ ^ 2 := sq_pos_of_ne_zero (inv_ne_zero hr)
  have hcancel : r⁻¹ ^ 2 * r ^ 2 = 1 := by field_simp
  rw [mem_Ioc] at ht ⊢
  constructor
  · rw [normalizedTime]
    nlinarith
  · rw [normalizedTime, physicalTerminalTime] at *
    have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 t₀)
      hrInv2.le
    have hright : t₀ + r ^ 2 * (T - t₀) - t₀ = r ^ 2 * (T - t₀) := by ring
    rw [hright, ← mul_assoc, hcancel, one_mul] at hmul
    nlinarith

theorem normalizedTime_mem_Ioo {t₀ T r t : ℝ} (hr : r ≠ 0)
    (ht : t ∈ Ioo t₀ (physicalTerminalTime t₀ T r)) :
    normalizedTime t₀ r t ∈ Ioo t₀ T := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  have hrInv2 : 0 < r⁻¹ ^ 2 := sq_pos_of_ne_zero (inv_ne_zero hr)
  have hcancel : r⁻¹ ^ 2 * r ^ 2 = 1 := by field_simp
  rw [mem_Ioo] at ht ⊢
  constructor
  · rw [normalizedTime]
    nlinarith
  · rw [normalizedTime, physicalTerminalTime] at *
    have hmul := mul_lt_mul_of_pos_left (sub_lt_sub_right ht.2 t₀) hrInv2
    have hright : t₀ + r ^ 2 * (T - t₀) - t₀ = r ^ 2 * (T - t₀) := by ring
    rw [hright, ← mul_assoc, hcancel, one_mul] at hmul
    nlinarith

theorem hasDerivAt_normalizedTime (t₀ r t : ℝ) :
    letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
    letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
    letI : TopologicalSpace ℝ :=
      Real.normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    HasDerivAt (normalizedTime t₀ r) (r⁻¹ ^ 2) t := by
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  letI : TopologicalSpace ℝ :=
    Real.normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have hsub : HasDerivAt (fun s : ℝ => s - t₀) 1 t :=
    hasDerivAt_id t |>.sub_const t₀
  have hmul : HasDerivAt (fun s : ℝ => r⁻¹ ^ 2 * (s - t₀))
      (r⁻¹ ^ 2) t := by
    simpa only [mul_one] using hsub.const_mul (r⁻¹ ^ 2)
  have hc : HasDerivAt (fun _ : ℝ => t₀) 0 t := hasDerivAt_const t t₀
  convert hc.add hmul using 1
  · funext s
    rfl
  · simp

/-- Push a normalized finite-interval tensor field to physical time. The
time derivative acquires the exact factor r⁻², and the terminal time acquires
the exact factor r². -/
def timePushforward (cov : CovariantDerivative I E TM)
    (u : FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀ T)
    (r : ℝ) (hr : r ≠ 0) :
    FiniteClassicalTensorHeatField
      (E := E) (I := I) (M := M) cov t₀
        (physicalTerminalTime t₀ T r) where
  toFun t := u.toFun (normalizedTime t₀ r t)
  slice_mem t ht := u.slice_mem _ (normalizedTime_mem_Ioc hr ht)
  timeDerivative t x := r⁻¹ ^ 2 •
    u.timeDerivative (normalizedTime t₀ r t) x
  hasTimeDerivative := by
    intro t ht x v w
    have hu := u.hasTimeDerivative _ (normalizedTime_mem_Ioo hr ht) x v w
    have h := hu.comp t (hasDerivAt_normalizedTime t₀ r t)
    simpa only [Function.comp_def, smul_eq_mul, _root_.smul_apply, mul_comm] using h

end FiniteClassicalTensorHeatField
end CovariantDerivative
