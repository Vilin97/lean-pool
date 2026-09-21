/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.SmoothManifoldInverse
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # A smooth homeomorphic immersion in equal dimensions is a diffeomorphism -/

@[expose] public noncomputable section
open scoped Manifold ContDiff Topology
namespace LichnerowiczObata
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N] [I.Boundaryless] [J.Boundaryless]

/-- Inverse smoothness follows from the actual derivative and dimension
equality; it is not an extra assumption on the given homeomorphism. -/
theorem contMDiff_homeomorph_symm_of_injective_mfderiv
    (f : M ≃ₜ N) (hDim : Module.finrank ℝ E = Module.finrank ℝ E')
    (hf : ContMDiff I J ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x)) :
    ContMDiff J I ∞ f.symm := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hi (x : M) : ContMDiffAt J I ∞ f.symm (f x) := by
    let : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
    let : FiniteDimensional ℝ (TangentSpace J (f x)) := inferInstanceAs (FiniteDimensional ℝ E')
    let : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
    let : T2Space (TangentSpace J (f x)) := inferInstanceAs (T2Space E')
    let e : TangentSpace I x ≃L[ℝ] TangentSpace J (f x) :=
      ((mfderiv I J f x).toLinearMap.linearEquivOfInjective (hinj x) hDim).toContinuousLinearEquiv
    have hd : HasMFDerivAt I J f x (e : _ →L[ℝ] _) :=
      ((hf x).mdifferentiableAt (by norm_num)).hasMFDerivAt
    exact contMDiffAt_local_inverse_of_equiv f f.symm x e hd (hf x)
      f.symm.continuous.continuousAt (f.symm_apply_apply x)
      (Filter.Eventually.of_forall f.apply_symm_apply)
  intro y
  simpa only [f.apply_symm_apply] using hi (f.symm y)

/-- Upgrade the specified homeomorphism, without changing either function. -/
theorem exists_diffeomorph_of_homeomorphic_immersion
    (f : M ≃ₜ N) (hDim : Module.finrank ℝ E = Module.finrank ℝ E')
    (hf : ContMDiff I J ∞ f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x)) :
    ∃ d : M ≃ₘ⟮I, J⟯ N, (d : M → N) = f ∧ (d.symm : N → M) = f.symm := by
  exact ⟨⟨f.toEquiv, hf, contMDiff_homeomorph_symm_of_injective_mfderiv f hDim hf hinj⟩,
    rfl, rfl⟩

end LichnerowiczObata
