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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacian

/-!
# Hessian commutators and the Ricci--DeTurck second-order core

This module isolates the pointwise tensor calculation used by the
Ricci--DeTurck principal-part cancellation.  It does not introduce a
remainder term or assert a nonlinear parabolic equation.

The first result is the standard first-slot Hessian commutator for an
arbitrary covariant two-tensor.  The second result is the cleared-denominator
algebraic cancellation which combines the two Ricci connection-change
derivative slots with the two derivatives of the DeTurck trace.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff BigOperators

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun y : M => TM y →L[ℝ] ℝ)
local notation "T₂" => (fun y : M => TM y →L[ℝ] TM y →L[ℝ] ℝ)
local notation "T₃" => (fun y : M => TM y →L[ℝ] T₂ y)

/-! The induced tensor bundles need explicit local instances because the
dependent continuous-linear-map bundle dictionaries are not synthesized
through two nested Hom constructions. -/
local instance hessianCoreOneFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₁ y) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance hessianCoreOneFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₁ y) :=
  ContinuousLinearMap.toNormedSpace
local instance hessianCoreOneTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] ℝ) T₁) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance hessianCoreOneFiberBundle : FiberBundle (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance hessianCoreOneVectorBundle : VectorBundle ℝ (E →L[ℝ] ℝ) T₁ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM ℝ (Bundle.Trivial M ℝ)
local instance hessianCoreOneContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] ℝ) T₁ I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance hessianCoreTwoModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance hessianCoreTwoModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) := inferInstance
local instance hessianCoreTwoFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₂ y) := inferInstance
local instance hessianCoreTwoFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₂ y) := inferInstance
local instance hessianCoreTwoTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] (E →L[ℝ] ℝ)) T₂) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance hessianCoreTwoFiberBundle :
    FiberBundle (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance hessianCoreTwoVectorBundle :
    VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] ℝ) T₁
local instance hessianCoreTwoContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] ℝ)) T₂ I :=
  ContMDiffVectorBundle.continuousLinearMap

local instance hessianCoreThreeModelNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance hessianCoreThreeModelNormedSpace :
    NormedSpace ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) := inferInstance
local instance hessianCoreThreeFiberNormedAddCommGroup (y : M) :
    NormedAddCommGroup (T₃ y) := inferInstance
local instance hessianCoreThreeFiberNormedSpace (y : M) :
    NormedSpace ℝ (T₃ y) := inferInstance
local instance hessianCoreThreeTopologicalSpace :
    TopologicalSpace (TotalSpace (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance hessianCoreThreeFiberBundle :
    FiberBundle (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
  Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance hessianCoreThreeVectorBundle :
    VectorBundle ℝ (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ :=
  Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) E TM (E →L[ℝ] (E →L[ℝ] ℝ)) T₂
local instance hessianCoreThreeContMDiffVectorBundle :
    ContMDiffVectorBundle 2 (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) T₃ I :=
  ContMDiffVectorBundle.continuousLinearMap
/-- Antisymmetrizing the first two derivative slots of a genuine covariant
Hessian gives the curvature of the induced covariant-two-tensor connection.

This is pointwise and uses only the regularity required to form that Hessian;
it is independent of compactness and of any Ricci-flow structure. -/
theorem covariantHessianTwoTensor_firstSlot_commutator
    (cov : CovariantDerivative I E TM)
    {h : ∀ y : M, T₂ y} {x : M}
    (hfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
        (covariantTwoTensorCovariantDerivative cov h y)) x)
    (hT : cov.torsion = 0)
    (X₁ X₂ : TM x)
    (hXmd : MDiffAt
      (T% (smoothExtend (I := I) (F := E) (V := TM) x X₁)) x)
    (hYmd : MDiffAt
      (T% (smoothExtend (I := I) (F := E) (V := TM) x X₂)) x)
    (u v : TM x) :
    covariantHessianTwoTensor cov h x X₁ X₂ u v -
        covariantHessianTwoTensor cov h x X₂ X₁ u v =
      (covariantTwoTensorCovariantDerivative cov).curvatureAux
        (smoothExtend (I := I) (F := E) (V := TM) x X₁)
        (smoothExtend (I := I) (F := E) (V := TM) x X₂) h x u v := by
  let X := smoothExtend (I := I) (F := E) (V := TM) x X₁
  let Y := smoothExtend (I := I) (F := E) (V := TM) x X₂
  let D := covariantTwoTensorCovariantDerivative cov
  have hHXY :
      covariantHessianTwoTensor cov h x X₁ X₂ u v =
        D.along X (D.along Y h) x u v - D h x (cov.along X Y x) u v := by
    simp only [covariantHessianTwoTensor,
      covariantThreeTensorCovariantDerivative, inducedHomCovariantDerivative,
      dif_pos hfirst, inducedHomAtOfMDiff_apply, sub_apply]
    unfold CovariantDerivative.along
    simp [D, X, Y, smoothExtend_apply]
  have hHYX :
      covariantHessianTwoTensor cov h x X₂ X₁ u v =
        D.along Y (D.along X h) x u v - D h x (cov.along Y X x) u v := by
    simp only [covariantHessianTwoTensor,
      covariantThreeTensorCovariantDerivative, inducedHomCovariantDerivative,
      dif_pos hfirst, inducedHomAtOfMDiff_apply, sub_apply]
    unfold CovariantDerivative.along
    simp [D, X, Y, smoothExtend_apply]
  have htorsionx :=
    (CovariantDerivative.torsion_eq_zero_iff (cov := cov)).mp hT
      (X := X) (Y := Y) (x := x) hXmd hYmd
  rw [hHXY, hHYX]
  simp only [CovariantDerivative.curvatureAux_apply,
    CovariantDerivative.along, sub_apply]
  rw [← htorsionx]
  simp only [map_sub, sub_apply]
  ring

/-- The cleared-denominator second-order Ricci--DeTurck cancellation for a
single traced vector.  The first parenthesis is twice the derivative part of
the Ricci connection-change formula, while the next two are twice the two
DeTurck-trace derivatives. -/
theorem hessianCoreCancellation_summand_clearedDenominator
    (cov : CovariantDerivative I E TM)
    {h : ∀ y : M, T₂ y} {x : M}
    (hfirst : MDiffAt
      (fun y => TotalSpace.mk'
        (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] ℝ))) (E := T₃) y
        (covariantTwoTensorCovariantDerivative cov h y)) x)
    (hT : cov.torsion = 0)
    (hsymm : ∀ y a b, h y a b = h y b a)
    (e u v : TM x) :
    (-2 : ℝ) *
        (covariantHessianTwoTensor cov h x e u v e +
          covariantHessianTwoTensor cov h x e v u e -
          covariantHessianTwoTensor cov h x e e v u -
          covariantHessianTwoTensor cov h x u v e e) +
      (2 * covariantHessianTwoTensor cov h x u e e v -
        covariantHessianTwoTensor cov h x u v e e) +
      (2 * covariantHessianTwoTensor cov h x v e e u -
        covariantHessianTwoTensor cov h x v u e e) =
      2 * covariantHessianTwoTensor cov h x e e u v +
        2 * (covariantTwoTensorCovariantDerivative cov).curvatureAux
          (smoothExtend (I := I) (F := E) (V := TM) x u)
          (smoothExtend (I := I) (F := E) (V := TM) x e) h x e v +
        2 * (covariantTwoTensorCovariantDerivative cov).curvatureAux
          (smoothExtend (I := I) (F := E) (V := TM) x v)
          (smoothExtend (I := I) (F := E) (V := TM) x e) h x e u +
        (covariantTwoTensorCovariantDerivative cov).curvatureAux
          (smoothExtend (I := I) (F := E) (V := TM) x u)
          (smoothExtend (I := I) (F := E) (V := TM) x v) h x e e := by
  have hmd (w : TM x) : MDiffAt
      (T% (smoothExtend (I := I) (F := E) (V := TM) x w)) x := by
    exact ((smoothExtend_contMDiff_two
      (I := I) (F := E) (V := TM) x w).of_le (by simp) x).mdifferentiableAt one_ne_zero
  have hlast (a b c d : TM x) :
      covariantHessianTwoTensor cov h x a b c d =
        covariantHessianTwoTensor cov h x a b d c :=
    covariantHessianTwoTensor_swap cov hsymm x a b c d
  have hcomm (a b c d : TM x) :
      covariantHessianTwoTensor cov h x a b c d -
          covariantHessianTwoTensor cov h x b a c d =
        (covariantTwoTensorCovariantDerivative cov).curvatureAux
          (smoothExtend (I := I) (F := E) (V := TM) x a)
          (smoothExtend (I := I) (F := E) (V := TM) x b) h x c d :=
    covariantHessianTwoTensor_firstSlot_commutator cov hfirst hT a b
      (hmd a) (hmd b) c d
  have hue :
      covariantHessianTwoTensor cov h x u e e v =
        covariantHessianTwoTensor cov h x e u v e +
          (covariantTwoTensorCovariantDerivative cov).curvatureAux
            (smoothExtend (I := I) (F := E) (V := TM) x u)
            (smoothExtend (I := I) (F := E) (V := TM) x e) h x e v := by
    have hcomm' := hcomm u e e v
    rw [hlast e u e v] at hcomm'
    linarith
  have hve :
      covariantHessianTwoTensor cov h x v e e u =
        covariantHessianTwoTensor cov h x e v u e +
          (covariantTwoTensorCovariantDerivative cov).curvatureAux
            (smoothExtend (I := I) (F := E) (V := TM) x v)
            (smoothExtend (I := I) (F := E) (V := TM) x e) h x e u := by
    have hcomm' := hcomm v e e u
    rw [hlast e v e u] at hcomm'
    linarith
  have hvu :
      covariantHessianTwoTensor cov h x v u e e =
        covariantHessianTwoTensor cov h x u v e e -
          (covariantTwoTensorCovariantDerivative cov).curvatureAux
            (smoothExtend (I := I) (F := E) (V := TM) x u)
            (smoothExtend (I := I) (F := E) (V := TM) x v) h x e e := by
    linarith [hcomm u v e e]
  rw [hue, hve, hvu, hlast e e v u]
  ring

end CovariantDerivative
