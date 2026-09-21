/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.RaisedRicci
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ScalarLaplacian

/-!
# Metric trace commutes with the connection Laplacian

For a metric-compatible connection, contraction with the metric is parallel.
This file proves the resulting trace--Laplacian identity for a genuine
covariant two-tensor.  The pointwise differentiability hypotheses are kept
explicit because the connection-Laplacian operators are defined on arbitrary
sections, including sections which may not be twice differentiable.
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

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)
local notation "T₃" => (fun x : M => TM x →L[ℝ] T₂ x)
local notation "EndTM" => (fun x : M => TM x →L[ℝ] TM x)

local instance traceLaplacianTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance traceLaplacianTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance traceLaplacianThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance traceLaplacianThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance traceLaplacianTwoFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₂ x) := inferInstance
local instance traceLaplacianTwoFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₂ x) := inferInstance
local instance traceLaplacianThreeFiberNormedAddCommGroup (x : M) :
    NormedAddCommGroup (T₃ x) := inferInstance
local instance traceLaplacianThreeFiberNormedSpace (x : M) :
    NormedSpace ℝ (T₃ x) := inferInstance
local instance traceLaplacianEndTopologicalSpace :
    TopologicalSpace
      (TotalSpace (E →L[ℝ] E)
        (fun x : M => TM x →L[ℝ] TM x)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM E TM
local instance traceLaplacianEndFiberBundle :
    FiberBundle (E →L[ℝ] E)
      (fun x : M => TM x →L[ℝ] TM x) :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM E TM
local instance traceLaplacianEndVectorBundle :
    VectorBundle ℝ (E →L[ℝ] E)
      (fun x : M => TM x →L[ℝ] TM x) :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM E TM
local instance traceLaplacianEndContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] E)
      (fun x : M => TM x →L[ℝ] TM x) I :=
  ContMDiffVectorBundle.continuousLinearMap
local instance traceLaplacianRieszTopologicalSpace :
    TopologicalSpace
      (TotalSpace ((E →L[ℝ] ℝ) →L[ℝ] E)
        (fun x : M => (TM x →L[ℝ] ℝ) →L[ℝ] TM x)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) (E →L[ℝ] ℝ)
      (fun x : M => TM x →L[ℝ] ℝ) E TM
local instance traceLaplacianRieszFiberBundle :
    FiberBundle ((E →L[ℝ] ℝ) →L[ℝ] E)
      (fun x : M => (TM x →L[ℝ] ℝ) →L[ℝ] TM x) :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) (E →L[ℝ] ℝ)
      (fun x : M => TM x →L[ℝ] ℝ) E TM
local instance traceLaplacianRieszVectorBundle :
    VectorBundle ℝ ((E →L[ℝ] ℝ) →L[ℝ] E)
      (fun x : M => (TM x →L[ℝ] ℝ) →L[ℝ] TM x) :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) (E →L[ℝ] ℝ)
      (fun x : M => TM x →L[ℝ] ℝ) E TM
local instance traceLaplacianRieszContMDiffVectorBundle :
    ContMDiffVectorBundle 2 ((E →L[ℝ] ℝ) →L[ℝ] E)
      (fun x : M => (TM x →L[ℝ] ℝ) →L[ℝ] TM x) I :=
  ContMDiffVectorBundle.continuousLinearMap

/-- Raise the first covariant slot of a genuine covariant two-tensor using
the Riemannian metric. -/
def raisedCovariantTwoTensor (h : ∀ x : M, T₂ x) : ∀ x : M, EndTM x :=
  fun x => (rieszMap (I := I) x).comp (h x)

/- The Riesz map is a genuine smooth hom-bundle section.  Keeping this as
an explicit lemma lets later tensor constructions use ordinary bundle
composition, rather than duplicating a local-frame coordinate argument. -/
theorem rieszMap_mdifferentiableAt
    [IsContMDiffRiemannianBundle I 2 E TM]
    (x₀ : M) :
    MDiffAt
      (fun y => TotalSpace.mk' ((E →L[ℝ] ℝ) →L[ℝ] E)
        (E := fun z : M =>
          (TangentSpace I z →L[ℝ] ℝ) →L[ℝ] TangentSpace I z) y
        (rieszMap (I := I) y)) x₀ := by
  classical
  let e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M) :=
    trivializationAt E TM x₀
  let eStar : Trivialization (E →L[ℝ] ℝ)
      (TotalSpace.proj : TotalSpace (E →L[ℝ] ℝ)
        (fun x : M => TangentSpace I x →L[ℝ] ℝ) → M) :=
    trivializationAt (E →L[ℝ] ℝ)
      (fun x : M => TangentSpace I x →L[ℝ] ℝ) x₀
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    Module.finBasis ℝ E
  let bStar : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (E →L[ℝ] ℝ) :=
    continuousDualBasis b
  let u : Set M := e.baseSet ∩ eStar.baseSet
  have hu : IsOpen u := e.open_baseSet.inter eStar.open_baseSet
  have huE : u ⊆ e.baseSet := Set.inter_subset_left
  have huStar : u ⊆ eStar.baseSet := Set.inter_subset_right
  have hω : ∀ i,
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
        (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) y
          (eStar.localFrame bStar i y)) u := by
    intro i
    exact (eStar.contMDiffOn_localFrame_baseSet
      (I := I) (n := (1 : WithTop ℕ∞)) bStar i).mono huStar
  have hraised : ∀ i,
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
        (fun y => TotalSpace.mk' E y
          (rieszMap (I := I) y (eStar.localFrame bStar i y))) u := by
    intro i
    exact contMDiffOn_rieszMap_section
      (I := I) (E := E) (M := M) e b hu huE (hω i)
  have hxU : x₀ ∈ u := by
    exact ⟨FiberBundle.mem_baseSet_trivializationAt' x₀,
      FiberBundle.mem_baseSet_trivializationAt' x₀⟩
  refine (contMDiffAt_homBundle_of_forall_apply_localFrame
    (IB := I) (E₁ := (fun x : M => TangentSpace I x →L[ℝ] ℝ))
    (E₂ := TM) x₀ bStar ?_).mdifferentiableAt one_ne_zero
  intro i
  have hi := (hraised i) x₀ hxU
  exact hi.contMDiffAt (hu.mem_nhds hxU)

/- A differentiable genuine two-tensor remains differentiable after raising
one covariant slot. -/
theorem raisedCovariantTwoTensor_mdifferentiableAt
    [IsContMDiffRiemannianBundle I 2 E TM]
    {h : ∀ x : M, T₂ x} {x₀ : M}
    (hh : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ))
        (E := T₂) y (h y)) x₀) :
    MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := EndTM) y
        (raisedCovariantTwoTensor (I := I) (E := E) h y)) x₀ := by
  have hRiesz := (rieszMap_mdifferentiableAt
    (I := I) (E := E) (M := M) x₀)
  have hcomp := hRiesz.clm_bundle_comp hh
  simpa only [raisedCovariantTwoTensor] using hcomp

/-- The scalar function given by the intrinsic metric trace of a genuine
covariant two-tensor. -/
def covariantTwoTensorTraceFunction (h : ∀ x : M, T₂ x) : M → ℝ :=
  fun x => covariantTwoTensorTrace (I := I) (E := E) (M := M)
    (covariantTwoTensorLinear (I := I) (M := M) h) x

/-- The metric trace of a covariant two-tensor is the ordinary fibrewise
endomorphism trace after raising one index. -/
theorem covariantTwoTensorTraceFunction_eq_endomorphismTrace_raised
    [IsContMDiffRiemannianBundle I 1 E TM]
    (h : ∀ x : M, T₂ x) :
    covariantTwoTensorTraceFunction (I := I) (E := E) h =
      endomorphismTrace (F := E) (V := TM)
        (raisedCovariantTwoTensor (I := I) (E := E) h) := by
  funext x
  letI : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  rw [covariantTwoTensorTraceFunction,
    covariantTwoTensorTrace_eq_sum_orthonormalBasis
      (I := I) (E := E) (M := M)
      (covariantTwoTensorLinear (I := I) (M := M) h) x b,
    endomorphismTrace, LinearMap.trace_eq_sum_inner _ b]
  apply Finset.sum_congr rfl
  intro i hi
  change h x (b i) (b i) =
    inner ℝ (b i)
      (raisedCovariantTwoTensor (I := I) (E := E) h x (b i))
  rw [real_inner_comm]
  exact (rieszMap_apply_inner (I := I) x (h x (b i)) (b i)).symm

/- The first-order trace identity also supplies the differentiability of the
   scalar gradient once the raised tensor and its covariant derivative are
   differentiable.  The local-frame reconstruction is important here: the
   tangent fibres vary with the base point, so a fixed model-space argument
   would not be an intrinsic proof. -/
theorem mdifferentiableAt_scalarDifferential_covariantTwoTensorTraceFunction
    [IsContMDiffRiemannianBundle I 2 E TM]
    (cov : CovariantDerivative I E TM)
    (hmetric : cov.IsMetricCompatibleTangent)
    (h : ∀ y : M, T₂ y)
    (hhRaised : ∀ y : M,
      MDiffAt
        (fun z => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun w : M => TM w →L[ℝ] TM w) z
          (raisedCovariantTwoTensor (I := I) (E := E) h z)) y)
    {x : M}
    (hfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
        (covariantTwoTensorCovariantDerivative cov h y)) x) :
    MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I)
          (covariantTwoTensorTraceFunction (I := I) (E := E) h) y)) x := by
  classical
  let e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M) :=
    trivializationAt E TM x
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    Module.finBasis ℝ E
  let f : M → ℝ := covariantTwoTensorTraceFunction (I := I) (E := E) h
  refine mdifferentiableAt_homBundle_of_forall_apply_localFrame
    (IB := I) (E₁ := TM) (F₁ := E)
    (s := fun y => scalarDifferential (I := I) f y) x b ?_
  intro i
  let frame : ∀ y : M, TM y := fun y => e.localFrame b i y
  let D : ∀ y : M, T₂ y := fun y =>
    covariantTwoTensorCovariantDerivative cov h y (frame y)
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hframe : MDiffAt (T% frame) x :=
    (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
      (n := (1 : ℕ∞)) (i := i) (hx := hx)).mdifferentiableAt one_ne_zero
  have hD : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ))
        (E := T₂) y (D y)) x := by
    have hD' := hfirst.clm_bundle_apply hframe
    simpa [D, frame] using hD'
  have hDraised := raisedCovariantTwoTensor_mdifferentiableAt
    (I := I) (E := E) (M := M) (h := D) hD
  have htraceD : MDiffAt
      (covariantTwoTensorTraceFunction (I := I) (E := E) D) x := by
    rw [covariantTwoTensorTraceFunction_eq_endomorphismTrace_raised
      (I := I) (E := E) (M := M) D]
    exact mdifferentiableAt_endomorphismTrace
      (F := E) (V := TM) hDraised
  have hvalue (y : M) :
      scalarDifferential (I := I) f y (frame y) =
        covariantTwoTensorTraceFunction (I := I) (E := E) D y := by
    letI : FiniteDimensional ℝ (TM y) :=
      VectorBundle.finiteDimensional ℝ E TM y
    let b' := stdOrthonormalBasis ℝ (TM y)
    have hderiv :=
      mvfderiv_covariantTwoTensorTrace_eq_sum_covariantDerivative
        (I := I) (E := E) (M := M) cov hmetric h (hhRaised y)
        (frame y) b'
    calc
      scalarDifferential (I := I) f y (frame y) =
          mvfderiv (I := I) f y (frame y) := rfl
      _ = ∑ j, covariantTwoTensorCovariantDerivative cov h y
          (frame y) (b' j) (b' j) := by
            change mvfderiv (I := I)
              (fun z => covariantTwoTensorTrace (I := I) (E := E) (M := M)
                (covariantTwoTensorLinear (I := I) (M := M) h) z) y
              (frame y) = _
            exact hderiv
      _ = covariantTwoTensorTraceFunction (I := I) (E := E) D y := by
        rw [covariantTwoTensorTraceFunction,
          covariantTwoTensorTrace_eq_sum_orthonormalBasis
            (I := I) (E := E) (M := M)
            (covariantTwoTensorLinear (I := I) (M := M) D) y b']
        simp [D, frame, covariantTwoTensorLinear_apply]
  have hcomponent : MDiffAt
      (fun y => scalarDifferential (I := I) f y (frame y)) x :=
    htraceD.congr_of_eventuallyEq
      (Filter.Eventually.of_forall hvalue)
  have htotal : MDifferentiableAt I (I.prod 𝓘(ℝ, ℝ))
      (fun y => TotalSpace.mk' ℝ (E := fun _ : M => ℝ) y
        (scalarDifferential (I := I) f y (frame y))) x := by
    rw [mdifferentiableAt_section]
    simpa [Bundle.Trivial.eq_trivialization M ℝ] using hcomponent
  simpa [f, frame, e, covariantTwoTensorTraceFunction] using htotal

/-- Fixing a vector field in the derivative slot of `∇h` gives a genuine
covariant two-tensor section. -/
def covariantTwoTensorDerivativeAlong
    (cov : CovariantDerivative I E TM) (h : ∀ x : M, T₂ x)
    (Y : ∀ x : M, TM x) : ∀ x : M, T₂ x :=
  fun x => covariantTwoTensorCovariantDerivative cov h x (Y x)

/-- The Hessian of the metric trace of `h` is the trace, in the tensor slots,
of the genuine covariant Hessian of `h`.  This is the second-order contraction
identity; no coordinate frame or assumed Laplacian identity is used. -/
theorem scalarHessian_covariantTwoTensorTraceFunction_eq_sum_covariantHessian
    [IsContMDiffRiemannianBundle I 1 E TM]
    (cov : CovariantDerivative I E TM)
    (hmetric : cov.IsMetricCompatibleTangent)
    (h : ∀ y : M, T₂ y)
    (hhRaised : ∀ y : M,
      MDiffAt
        (fun z => TotalSpace.mk' (E →L[ℝ] E) (E := EndTM) z
          (raisedCovariantTwoTensor (I := I) (E := E) h z)) y)
    {x : M}
    (hfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
        (covariantTwoTensorCovariantDerivative cov h y)) x)
    (htraceDifferential : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I)
          (covariantTwoTensorTraceFunction (I := I) (E := E) h) y)) x)
    (hsecondRaised : ∀ Y : TM x,
      MDiffAt
        (fun z => TotalSpace.mk' (E →L[ℝ] E) (E := EndTM) z
          (raisedCovariantTwoTensor (I := I) (E := E)
            (covariantTwoTensorDerivativeAlong cov h
              (smoothExtend (I := I) (F := E) (V := TM) x Y)) z)) x)
    (X Y : TM x) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TM x)) :
    scalarHessian cov (covariantTwoTensorTraceFunction (I := I) (E := E) h)
        x X Y =
      ∑ i, covariantHessianTwoTensor cov h x X Y (b i) (b i) := by
  let f : M → ℝ := covariantTwoTensorTraceFunction (I := I) (E := E) h
  let Yfield : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x Y
  let k : ∀ y : M, T₂ y := covariantTwoTensorDerivativeAlong cov h Yfield
  have hYfield : MDiffAt (T% Yfield) x :=
    ((smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x Y).of_le
      (by simp) x).mdifferentiableAt one_ne_zero
  have hk : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (k y)) x :=
    hfirst.clm_bundle_apply hYfield
  have hproductApply (u v : TM x) :
      covariantTwoTensorCovariantDerivative cov k x X u v =
        covariantHessianTwoTensor cov h x X Y u v +
          covariantTwoTensorCovariantDerivative cov h x
            (cov Yfield x X) u v := by
    rw [covariantTwoTensorCovariantDerivative_apply_of_mdifferentiableAt
        cov hk X u v,
      covariantHessianTwoTensor_apply_of_mdifferentiableAt
        cov h hfirst X Y u v]
    simp only [k, covariantTwoTensorDerivativeAlong, Yfield,
      smoothExtend_apply]
    ring
  have hvalue (y : M) :
      scalarDifferential (I := I) f y (Yfield y) =
        covariantTwoTensorTrace (I := I) (E := E) (M := M)
          (covariantTwoTensorLinear (I := I) (M := M) k) y := by
    letI : FiniteDimensional ℝ (TM y) :=
      VectorBundle.finiteDimensional ℝ E TM y
    let b' := stdOrthonormalBasis ℝ (TM y)
    have hderiv :=
      mvfderiv_covariantTwoTensorTrace_eq_sum_covariantDerivative
        (I := I) (E := E) (M := M) cov hmetric h (hhRaised y)
        (Yfield y) b'
    have hderiv' :
        mvfderiv (I := I) f y (Yfield y) =
          ∑ i, covariantTwoTensorCovariantDerivative cov h y
            (Yfield y) (b' i) (b' i) := by
      change mvfderiv (I := I)
        (fun z => covariantTwoTensorTrace (I := I) (E := E) (M := M)
          (covariantTwoTensorLinear (I := I) (M := M) h) z) y
          (Yfield y) = _
      exact hderiv
    calc
      scalarDifferential (I := I) f y (Yfield y) =
          mvfderiv (I := I) f y (Yfield y) := rfl
      _ = ∑ i, covariantTwoTensorCovariantDerivative cov h y
          (Yfield y) (b' i) (b' i) := hderiv'
      _ = covariantTwoTensorTrace (I := I) (E := E) (M := M)
          (covariantTwoTensorLinear (I := I) (M := M) k) y := by
            symm
            rw [covariantTwoTensorTrace_eq_sum_orthonormalBasis
              (I := I) (E := E) (M := M)
              (covariantTwoTensorLinear (I := I) (M := M) k) y b']
            simp [k, covariantTwoTensorDerivativeAlong,
              covariantTwoTensorLinear_apply]
  have hvalueFun :
      (fun y => scalarDifferential (I := I) f y (Yfield y)) =
        (fun y => covariantTwoTensorTrace (I := I) (E := E) (M := M)
          (covariantTwoTensorLinear (I := I) (M := M) k) y) := by
    funext y
    exact hvalue y
  have htraceSecond :=
    mvfderiv_covariantTwoTensorTrace_eq_sum_covariantDerivative
      (I := I) (E := E) (M := M) cov hmetric k (hsecondRaised Y) X b
  have htraceCorrection :=
    mvfderiv_covariantTwoTensorTrace_eq_sum_covariantDerivative
      (I := I) (E := E) (M := M) cov hmetric h (hhRaised x)
      (cov Yfield x X) b
  have hcorrection :
      scalarDifferential (I := I) f x (cov Yfield x X) =
        ∑ i, covariantTwoTensorCovariantDerivative cov h x
          (cov Yfield x X) (b i) (b i) := by
    change mvfderiv (I := I) f x (cov Yfield x X) = _
    change mvfderiv (I := I)
      (fun z => covariantTwoTensorTrace (I := I) (E := E) (M := M)
        (covariantTwoTensorLinear (I := I) (M := M) h) z) x
        (cov Yfield x X) = _ at htraceCorrection
    exact htraceCorrection
  have hsecond :
      mvfderiv (I := I)
        (fun y => covariantTwoTensorTrace (I := I) (E := E) (M := M)
          (covariantTwoTensorLinear (I := I) (M := M) k) y) x X =
        ∑ i, covariantTwoTensorCovariantDerivative cov k x X
          (b i) (b i) := by
    exact htraceSecond
  have hproductSum :
      (∑ i, covariantTwoTensorCovariantDerivative cov k x X
        (b i) (b i)) =
        (∑ i, covariantHessianTwoTensor cov h x X Y (b i) (b i)) +
          ∑ i, covariantTwoTensorCovariantDerivative cov h x
            (cov Yfield x X) (b i) (b i) := by
    calc
      _ = ∑ i,
          (covariantHessianTwoTensor cov h x X Y (b i) (b i) +
            covariantTwoTensorCovariantDerivative cov h x
              (cov Yfield x X) (b i) (b i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hproductApply (b i) (b i)
      _ = _ := Finset.sum_add_distrib
  calc
    scalarHessian cov f x X Y =
        mvfderiv (I := I) (fun y =>
          scalarDifferential (I := I) f y
            (smoothExtend (I := I) (F := E) (V := TM) x Y y)) x X -
          scalarDifferential (I := I) f x (cov Yfield x X) :=
      scalarHessian_apply_of_mdifferentiableAt cov f htraceDifferential X Y
    _ = (∑ i, covariantTwoTensorCovariantDerivative cov k x X
            (b i) (b i)) -
          (∑ i, covariantTwoTensorCovariantDerivative cov h x
            (cov Yfield x X) (b i) (b i)) := by
      rw [show (fun y => scalarDifferential (I := I) f y
          (smoothExtend (I := I) (F := E) (V := TM) x Y y)) =
            (fun y => scalarDifferential (I := I) f y (Yfield y)) by rfl,
        hvalueFun, hsecond, hcorrection]
    _ = ∑ i, covariantHessianTwoTensor cov h x X Y (b i) (b i) := by
      rw [hproductSum]
      ring

/-- The scalar Laplacian of the metric trace of a covariant two-tensor is the
metric trace of its genuine connection Laplacian. -/
theorem scalarLaplacian_covariantTwoTensorTraceFunction_eq_covariantTwoTensorTrace_connectionLaplacian
    [IsContMDiffRiemannianBundle I 1 E TM]
    (cov : CovariantDerivative I E TM)
    (hmetric : cov.IsMetricCompatibleTangent)
    (h : ∀ y : M, T₂ y)
    (hhRaised : ∀ y : M,
      MDiffAt
        (fun z => TotalSpace.mk' (E →L[ℝ] E) (E := EndTM) z
          (raisedCovariantTwoTensor (I := I) (E := E) h z)) y)
    {x : M}
    (hfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
        (covariantTwoTensorCovariantDerivative cov h y)) x)
    (htraceDifferential : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I)
          (covariantTwoTensorTraceFunction (I := I) (E := E) h) y)) x)
    (hsecondRaised : ∀ Y : TM x,
      MDiffAt
        (fun z => TotalSpace.mk' (E →L[ℝ] E) (E := EndTM) z
          (raisedCovariantTwoTensor (I := I) (E := E)
            (covariantTwoTensorDerivativeAlong cov h
              (smoothExtend (I := I) (F := E) (V := TM) x Y)) z)) x)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TM x)) :
    scalarLaplacian cov (covariantTwoTensorTraceFunction (I := I) (E := E) h) x =
      covariantTwoTensorTrace (I := I) (E := E) (M := M)
        (covariantTwoTensorLinear (I := I) (M := M)
          (fun y => connectionLaplacian cov h y)) x := by
  letI : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  rw [scalarLaplacian_eq_sum_orthonormalBasis cov
    (covariantTwoTensorTraceFunction (I := I) (E := E) h) x b,
    covariantTwoTensorTrace_eq_sum_orthonormalBasis
      (I := I) (E := E) (M := M)
      (covariantTwoTensorLinear (I := I) (M := M)
        (fun y => connectionLaplacian cov h y)) x b]
  calc
    _ = ∑ i, ∑ j,
        covariantHessianTwoTensor cov h x (b i) (b i) (b j) (b j) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact scalarHessian_covariantTwoTensorTraceFunction_eq_sum_covariantHessian
            (I := I) (E := E) (M := M) cov hmetric h hhRaised hfirst
            htraceDifferential hsecondRaised (b i) (b i) b
    _ = ∑ j, ∑ i,
        covariantHessianTwoTensor cov h x (b i) (b i) (b j) (b j) := by
          rw [Finset.sum_comm]
    _ = ∑ j, connectionLaplacian cov h x (b j) (b j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [connectionLaplacian_eq_sum_orthonormalBasis cov h x b]
          simp

end CovariantDerivative

end
