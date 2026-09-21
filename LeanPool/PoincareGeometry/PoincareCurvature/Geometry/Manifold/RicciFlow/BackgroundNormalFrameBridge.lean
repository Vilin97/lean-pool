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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.FirstOrderParallelExtension
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita

/-!
# Calibrated local frames and first-order parallel extensions

This module records two small but useful bridges for pointwise tensor
calculations.  A compatible local trivialization can be calibrated so that
its standard local frame takes any prescribed tangent-fibre basis at the
center.  Separately, the existing first-order extension construction gives a
family with those prescribed values and vanishing covariant derivative at the
center.

The second construction is deliberately only a first-jet assertion here.  It
does not claim that the resulting global sections form a local frame on a
neighbourhood; that open-invertibility step is kept separate.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Transport a tangent-fibre basis to the model fibre of a compatible
trivialization.  The induced local frame then agrees with the original basis
at the selected point. -/
noncomputable def tangentModelBasisAt
    {ι : Type*} (x : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ (TM x)) (hx : x ∈ e.baseSet) :
    Module.Basis ι ℝ E :=
  b.map (e.linearEquivAt ℝ x hx)

/-- The local frame induced by `tangentModelBasisAt` has the prescribed
tangent-fibre basis value at its center. -/
@[simp] theorem localFrame_tangentModelBasisAt_apply_center
    {ι : Type*} (x : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ (TM x)) (hx : x ∈ e.baseSet) (i : ι) :
    e.localFrame (tangentModelBasisAt (I := I) x e b hx) i x = b i := by
  rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
    (e := e) (b := tangentModelBasisAt (I := I) x e b hx) hx]
  change (e.linearEquivAt ℝ x hx).symm
    ((e.linearEquivAt ℝ x hx) (b i)) = b i
  exact (e.linearEquivAt ℝ x hx).symm_apply_apply (b i)

/-- The pointwise normal extension associated to a tangent-fibre vector. -/
noncomputable def backgroundNormalExtension
    (cov : CovariantDerivative I E TM) (x : M) (v : TM x) :
    ∀ y : M, TM y :=
  CovariantDerivative.firstOrderParallelSmoothExtend
    (I := I) (F := E) (V := TM) cov x v

/-- A finite family of prescribed tangent values extended with zero first
covariant derivative at the center. -/
noncomputable def backgroundNormalFrame
    {ι : Type*} (cov : CovariantDerivative I E TM) (x : M)
    (b : Module.Basis ι ℝ (TM x)) : ι → ∀ y : M, TM y :=
  fun i => backgroundNormalExtension (I := I) cov x (b i)

@[simp] theorem backgroundNormalExtension_apply_center
    (cov : CovariantDerivative I E TM) (x : M) (v : TM x) :
    backgroundNormalExtension (I := I) cov x v x = v := by
  simp [backgroundNormalExtension]

theorem backgroundNormalExtension_mdifferentiableAt
    (cov : CovariantDerivative I E TM) (x : M) (v : TM x) :
    MDiffAt (T% (backgroundNormalExtension (I := I) cov x v)) x := by
  simpa [backgroundNormalExtension] using
    (CovariantDerivative.firstOrderParallelSmoothExtend_mdifferentiableAt
      (I := I) (F := E) (V := TM) cov x v)

@[simp] theorem covariantDerivative_backgroundNormalExtension_eq_zero
    (cov : CovariantDerivative I E TM) (x : M) (v : TM x) :
    cov (backgroundNormalExtension (I := I) cov x v) x = 0 := by
  simpa [backgroundNormalExtension] using
    (CovariantDerivative.covariantDerivative_firstOrderParallelSmoothExtend_eq_zero
      (I := I) (F := E) (V := TM) cov x v)

@[simp] theorem backgroundNormalFrame_apply_center
    {ι : Type*} (cov : CovariantDerivative I E TM) (x : M)
    (b : Module.Basis ι ℝ (TM x)) (i : ι) :
    backgroundNormalFrame (I := I) cov x b i x = b i := by
  simp [backgroundNormalFrame]

theorem backgroundNormalFrame_mdifferentiableAt
    {ι : Type*} (cov : CovariantDerivative I E TM) (x : M)
    (b : Module.Basis ι ℝ (TM x)) (i : ι) :
    MDiffAt (T% (backgroundNormalFrame (I := I) cov x b i)) x := by
  simpa [backgroundNormalFrame] using
    (backgroundNormalExtension_mdifferentiableAt (I := I) cov x (b i))

@[simp] theorem covariantDerivative_backgroundNormalFrame_eq_zero
    {ι : Type*} (cov : CovariantDerivative I E TM) (x : M)
    (b : Module.Basis ι ℝ (TM x)) (i : ι) :
    cov (backgroundNormalFrame (I := I) cov x b i) x = 0 := by
  simp [backgroundNormalFrame]

theorem backgroundNormalFrame_linearIndependent_at
    {ι : Type*} (cov : CovariantDerivative I E TM) (x : M)
    (b : Module.Basis ι ℝ (TM x)) :
    LinearIndependent ℝ (fun i => backgroundNormalFrame (I := I) cov x b i x) := by
  simpa only [backgroundNormalFrame_apply_center] using b.linearIndependent

theorem backgroundNormalFrame_spans_at
    {ι : Type*} (cov : CovariantDerivative I E TM) (x : M)
    (b : Module.Basis ι ℝ (TM x)) :
    ⊤ ≤ Submodule.span ℝ (Set.range (fun i => backgroundNormalFrame (I := I) cov x b i x)) := by
  simpa only [backgroundNormalFrame_apply_center] using b.span_eq.ge

/-- If the prescribed tangent basis is orthonormal, the calibrated local
frame has identity Gram matrix at its center. -/
theorem localFrameGramMatrix_tangentModelBasisAt_eq_one
    [RiemannianBundle TM]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : OrthonormalBasis ι ℝ (TM x)) (hx : x ∈ e.baseSet) :
    CovariantDerivative.localFrameGramMatrix (I := I) e
      (tangentModelBasisAt (I := I) x e b.toBasis hx) x =
        (1 : Matrix ι ι ℝ) := by
  ext i j
  simp only [CovariantDerivative.localFrameGramMatrix]
  rw [localFrame_tangentModelBasisAt_apply_center (I := I) x e b.toBasis hx i,
    localFrame_tangentModelBasisAt_apply_center (I := I) x e b.toBasis hx j]
  simp only [OrthonormalBasis.coe_toBasis]
  by_cases hij : i = j
  · subst j
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i]
    simp
  · rw [b.orthonormal.2 hij]
    simp [hij]

/-- Consequently, the inverse Gram matrix used in local trace formulae is
the identity at the calibrated orthonormal center. -/
theorem localFrameInverseGramMatrix_tangentModelBasisAt_eq_one
    [RiemannianBundle TM]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e]
    (b : OrthonormalBasis ι ℝ (TM x)) (hx : x ∈ e.baseSet) :
    CovariantDerivative.localFrameInverseGramMatrix (I := I) e
      (tangentModelBasisAt (I := I) x e b.toBasis hx) x =
        (1 : Matrix ι ι ℝ) := by
  rw [CovariantDerivative.localFrameInverseGramMatrix,
    localFrameGramMatrix_tangentModelBasisAt_eq_one (I := I) x e b hx]
  exact inv_one

end RicciFlow
