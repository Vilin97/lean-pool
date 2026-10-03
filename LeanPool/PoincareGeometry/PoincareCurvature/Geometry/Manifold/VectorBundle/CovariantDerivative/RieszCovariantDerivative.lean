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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.TraceLaplacian
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.MetricDefectTensorDerivative
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.HomEvaluation

/-!
# Covariant derivative of the Riesz lift

This module records the non-metric correction when an affine connection
differentiates the Riesz lift of a covector.  It is the intrinsic replacement
for differentiating an inverse metric in a local frame.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₀" => (Bundle.Trivial M ℝ)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)

/-- Differentiating the Riesz lift with an arbitrary affine connection
produces the covariant derivative of the covector minus the metric-defect
term.  No local or normal frame is chosen. -/
theorem inner_covariantDerivative_rieszMap_section_eq
    (cov : CovariantDerivative I E TM)
    {α : ∀ y : M, T₁ y} {x : M}
    (hα : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y (α y)) x)
    (X v : TM x) :
    inner ℝ (cov (fun y => rieszMap (I := I) y (α y)) x X) v =
      covectorCovariantDerivative cov α x X v -
        cov.metricDefect x (rieszMap (I := I) x (α x)) v X := by
  let S : ∀ y : M, TM y := fun y => rieszMap (I := I) y (α y)
  let V : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x v
  have hS : MDiffAt (T% S) x := by
    exact (rieszMap_mdifferentiableAt (I := I) (E := E) (M := M) x).clm_bundle_apply hα
  have hV : MDiffAt (T% V) x := by
    exact ((smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x v).of_le
      (by norm_num) x).mdifferentiableAt one_ne_zero
  have hdef :
      cov.metricDefect x (S x) (V x) X =
        mvfderiv (I := I) (fun y => inner ℝ (S y) (V y)) x X -
          inner ℝ (cov S x X) (V x) - inner ℝ (S x) (cov V x X) := by
    rw [cov.metricDefect_apply_sections hS hV,
      metricDefectAux_apply]
  have hcovector :=
    @inducedHomCovariantDerivative_apply_section_general
      E _ _ H _ I M _ _ _ _ _ _
      E ℝ _ _ _ _ _ _
      TM T₀ _ _
      (fun y => (inferInstance : NormedAddCommGroup (TM y)))
      (fun y => (inferInstance : NormedSpace ℝ (TM y)))
      (fun y => (inferInstance : FiniteDimensional ℝ (TM y)))
      _ _ _ _ _ _ _ _
      cov (realLineCovariantDerivative (I := I) (M := M)) α V x hα hV X
  change covectorCovariantDerivative cov α x X (V x) = _ at hcovector
  have hcovector' :
      covectorCovariantDerivative cov α x X (V x) =
        mvfderiv (I := I) (fun y => α y (V y)) x X -
          α x (cov V x X) := by
    simpa [realLineCovariantDerivative, trivialCovariantDerivative_apply] using hcovector
  have hpair : (fun y => α y (V y)) = (fun y => inner ℝ (S y) (V y)) := by
    funext y
    exact (rieszMap_apply_inner (I := I) y (α y) (V y)).symm
  rw [hpair] at hcovector'
  have hαcovV : α x (cov V x X) = inner ℝ (S x) (cov V x X) := by
    exact (rieszMap_apply_inner (I := I) x (α x) (cov V x X)).symm
  rw [hαcovV] at hcovector'
  have hresult :
      inner ℝ (cov S x X) (V x) =
        covectorCovariantDerivative cov α x X (V x) -
          cov.metricDefect x (S x) (V x) X := by
    linarith
  simpa [S, V, smoothExtend_apply] using hresult

/-- Raising the first slot of a covariant two-tensor commutes with an
arbitrary affine covariant derivative up to the metric defect.  This is the
intrinsic inverse-metric derivative rule needed before taking a trace. -/
theorem inner_endomorphismCovariantDerivative_raisedCovariantTwoTensor_eq
    (cov : CovariantDerivative I E TM)
    {h : ∀ y : M, T₂ y} {x : M}
    (hh : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] ℝ)) (E := T₂) y (h y)) x)
    (X u v : TM x) :
    inner ℝ
        (endomorphismCovariantDerivativeApply cov
          (raisedCovariantTwoTensor (I := I) (E := E) h) x X u) v =
      covariantTwoTensorCovariantDerivative cov h x X u v -
        cov.metricDefect x
          (raisedCovariantTwoTensor (I := I) (E := E) h x u) v X := by
  let U : ∀ y : M, TM y :=
    smoothExtend (I := I) (F := E) (V := TM) x u
  let α : ∀ y : M, T₁ y := fun y => h y (U y)
  let A : ∀ y : M, TM y →L[ℝ] TM y :=
    raisedCovariantTwoTensor (I := I) (E := E) h
  have hU : MDiffAt (T% U) x := by
    exact ((smoothExtend_contMDiff_two (I := I) (F := E) (V := TM) x u).of_le
      (by norm_num) x).mdifferentiableAt one_ne_zero
  have hα : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y (α y)) x := by
    simpa [α] using hh.clm_bundle_apply hU
  have hA : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M => TM z →L[ℝ] TM z) y (A y)) x := by
    simpa [A] using
      (raisedCovariantTwoTensor_mdifferentiableAt (I := I) (E := E) (M := M) hh)
  have hraised :=
    inner_covariantDerivative_rieszMap_section_eq (I := I) (E := E)
      (M := M) cov hα X v
  have hraised' :
      inner ℝ (cov (fun y => A y (U y)) x X) v =
        covectorCovariantDerivative cov α x X v -
          cov.metricDefect x (A x (U x)) v X := by
    simpa [A, α, raisedCovariantTwoTensor] using hraised
  have htwo :=
    @inducedHomCovariantDerivative_apply_section_general
      E _ _ H _ I M _ _ _ _ _ _
      E (E →L[ℝ] ℝ) _ _ _ _ _ _
      TM T₁ _ _
      (fun y => (inferInstance : NormedAddCommGroup (TM y)))
      (fun y => (inferInstance : NormedSpace ℝ (TM y)))
      (fun y => (inferInstance : FiniteDimensional ℝ (TM y)))
      _ _ _ _ _ _ _ _
      cov (covectorCovariantDerivative cov) h U x hh hU X
  change covariantTwoTensorCovariantDerivative cov h x X (U x) = _ at htwo
  have htwoV := congrArg (fun q : T₁ x => q v) htwo
  have htwo' :
      covectorCovariantDerivative cov α x X v =
        covariantTwoTensorCovariantDerivative cov h x X (U x) v +
          h x (cov U x X) v := by
    change covectorCovariantDerivative cov (fun y => h y (U y)) x X v = _
    rw [htwoV]
    simp only [sub_apply]
    ring
  have hEnd :
      endomorphismCovariantDerivativeApply cov A x X u =
        cov (fun y => A y (U y)) x X - A x (cov U x X) := by
    unfold endomorphismCovariantDerivativeApply endomorphismCovariantDerivativeAt
    dsimp only [inducedHomCovariantDerivative]
    split
    next _ => rfl
    next hnot => exact (hnot hA).elim
  have hinnerA : inner ℝ (A x (cov U x X)) v = h x (cov U x X) v := by
    simp [A, raisedCovariantTwoTensor, rieszMap_apply_inner]
  have hEndU :
      endomorphismCovariantDerivativeApply cov A x X (U x) =
        cov (fun y => A y (U y)) x X - A x (cov U x X) := by
    simpa [U, smoothExtend_apply] using hEnd
  have hresult :
      inner ℝ (endomorphismCovariantDerivativeApply cov A x X (U x)) v =
        covariantTwoTensorCovariantDerivative cov h x X (U x) v -
          cov.metricDefect x (A x (U x)) v X := by
    rw [hEndU, inner_sub_left, hraised', htwo', hinnerA]
    ring
  simpa [A, U, smoothExtend_apply] using hresult

end CovariantDerivative
