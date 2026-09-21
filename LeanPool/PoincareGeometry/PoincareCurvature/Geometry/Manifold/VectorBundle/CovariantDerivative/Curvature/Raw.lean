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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Along
public import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-!
# Raw curvature commutator

This file defines the section-valued commutator

`∇_X ∇_Y σ - ∇_Y ∇_X σ - ∇_[X,Y] σ`.

It is the unbundled precursor to the actual curvature tensor. The next milestone is to prove the
required tensoriality statements and package this operation as a multilinear map on fibres.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

variable {𝕜 : Type*} [hField : NontriviallyNormedField 𝕜]
  {E : Type*} [hEGroup : NormedAddCommGroup E] [hESpace : NormedSpace 𝕜 E]
  {H : Type*} [hHTop : TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [hMTop : TopologicalSpace M] [hCharted : ChartedSpace H M]
  {F : Type*} [hFGroup : NormedAddCommGroup F] [hFSpace : NormedSpace 𝕜 F]
  {V : M → Type*} [hTotalTop : TopologicalSpace (TotalSpace F V)]
  [hVAdd : ∀ x, AddCommGroup (V x)] [hVModule : ∀ x, Module 𝕜 (V x)]
  [hVTop : ∀ x, TopologicalSpace (V x)] [hVAddTop : ∀ x, IsTopologicalAddGroup (V x)]
  [hVSMul : ∀ x, ContinuousSMul 𝕜 (V x)] [hFiber : FiberBundle F V]
  [hVector : VectorBundle 𝕜 F V]

namespace CovariantDerivative

variable (cov : CovariantDerivative I F V)

/-- The raw curvature commutator associated to a covariant derivative. -/
abbrev curvatureAux (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) : Π x : M, V x :=
  cov.along X (cov.along Y σ) - cov.along Y (cov.along X σ) -
    cov.along (VectorField.mlieBracket I X Y) σ

@[simp]
lemma curvatureAux_apply (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (x : M) :
    cov.curvatureAux X Y σ x =
      cov.along X (cov.along Y σ) x - cov.along Y (cov.along X σ) x -
        cov.along (VectorField.mlieBracket I X Y) σ x :=
  rfl

lemma curvatureAux_swap (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) :
    cov.curvatureAux X Y σ = -cov.curvatureAux Y X σ := by
  funext x
  simp only [CovariantDerivative.curvatureAux, Pi.neg_apply, Pi.sub_apply]
  rw [VectorField.mlieBracket_swap, cov.along_neg_left]
  dsimp
  module

@[simp]
lemma curvatureAux_self (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) :
    cov.curvatureAux X X σ = 0 := by
  funext x
  simp [CovariantDerivative.curvatureAux]

end CovariantDerivative
