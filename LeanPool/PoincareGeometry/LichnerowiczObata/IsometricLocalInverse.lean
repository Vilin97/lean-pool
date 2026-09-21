/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.ManifoldInverseDifferentiability
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Topology.VectorBundle.Riemannian
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Metric preservation for a continuous local inverse -/

@[expose] public noncomputable section
open Bundle
open scoped Manifold Topology
namespace LichnerowiczObata
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]

/-- A continuous local inverse of an isometric derivative has an
isometric derivative itself. Invertibility follows from the metric identity
and the dimension equality, rather than being an additional assumption. -/
theorem local_inverse_of_metric_derivative
    (f : P → M) (g : M → P) (x : P)
    (hDim : Module.finrank ℝ P = Module.finrank ℝ E)
    (hf : MDifferentiableAt 𝓘(ℝ, P) I f x)
    (hm : ∀ v w : P,
      inner ℝ (mfderiv 𝓘(ℝ, P) I f x v) (mfderiv 𝓘(ℝ, P) I f x w) = inner ℝ v w)
    (hg : ContinuousAt g (f x)) (hgx : g (f x) = x)
    (hfg : ∀ᶠ y in 𝓝 (f x), f (g y) = y) :
    MDifferentiableAt I 𝓘(ℝ, P) g (f x) ∧
      ∀ v w : TangentSpace I (f x),
        inner ℝ (mvfderiv I g (f x) v) (mvfderiv I g (f x) w) = inner ℝ v w := by
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, P) x) := inferInstanceAs (FiniteDimensional ℝ P)
  let : FiniteDimensional ℝ (TangentSpace I (f x)) := inferInstanceAs (FiniteDimensional ℝ E)
  let : T2Space (TangentSpace 𝓘(ℝ, P) x) := inferInstanceAs (T2Space P)
  let : T2Space (TangentSpace I (f x)) := inferInstanceAs (T2Space E)
  let D : P →L[ℝ] TangentSpace I (f x) :=
    (mfderiv 𝓘(ℝ, P) I f x).comp (NormedSpace.fromTangentSpace x).symm.toContinuousLinearMap
  have hinj : Function.Injective D := by
    intro v w hvw
    have hz : D (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    have hh := hm (v - w) (v - w)
    change inner ℝ (D (v - w)) (D (v - w)) = inner ℝ (v - w : P) (v - w) at hh
    rw [hz, inner_zero_left] at hh
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hh.symm)
  let e := (NormedSpace.fromTangentSpace x).trans
    (D.toLinearMap.linearEquivOfInjective hinj hDim).toContinuousLinearEquiv
  have he : (e : _ →L[ℝ] _) = mfderiv 𝓘(ℝ, P) I f x := by ext v; rfl
  have hfe : HasMFDerivAt 𝓘(ℝ, P) I f x (e : _ →L[ℝ] _) := by
    rw [he]
    exact hf.hasMFDerivAt
  have hgi := mdifferentiableAt_local_inverse_of_equiv f g x e hfe hg hgx hfg
  refine ⟨hgi, ?_⟩
  intro v w
  have hfx : MDifferentiableAt 𝓘(ℝ, P) I f (g (f x)) := by rw [hgx]; exact hf
  have hc := mfderiv_comp (f := g) (g := f) (f x) hfx hgi
  rw [hgx] at hc
  have hlocal : (f ∘ g) =ᶠ[𝓝 (f x)] id := hfg
  have hid := hlocal.mfderiv_eq (I := I) (I' := I)
  rw [mfderiv_id] at hid
  have hv := congrArg (fun T => T v) (hc.symm.trans hid)
  have hw := congrArg (fun T => T w) (hc.symm.trans hid)
  change mfderiv 𝓘(ℝ, P) I f x (mfderiv I 𝓘(ℝ, P) g (f x) v) = v at hv
  change mfderiv 𝓘(ℝ, P) I f x (mfderiv I 𝓘(ℝ, P) g (f x) w) = w at hw
  have hh := hm (mfderiv I 𝓘(ℝ, P) g (f x) v) (mfderiv I 𝓘(ℝ, P) g (f x) w)
  change inner ℝ (mfderiv 𝓘(ℝ, P) I f x (mfderiv I 𝓘(ℝ, P) g (f x) v))
    (mfderiv 𝓘(ℝ, P) I f x (mfderiv I 𝓘(ℝ, P) g (f x) w)) = _ at hh
  rw [hv, hw] at hh
  convert hh.symm using 1
  rfl

end LichnerowiczObata
