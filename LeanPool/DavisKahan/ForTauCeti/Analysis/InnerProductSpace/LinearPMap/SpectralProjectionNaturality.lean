/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralMeasure
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SeparatedIntertwiner
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.BorelNatural

/-!
# Spectral projections are natural under a unitary intertwiner

A unitary `e` commuting with a self-adjoint partial map `A` commutes with every
spectral projection `E_A(B)`.

This is the missing "Borel step" that `SeparatedIntertwiner` records as open in
general: it carries an intertwining relation past the *continuous* functional
calculus into the *bounded Borel* one.  In the generality of an arbitrary
bounded intertwiner that is a monotone-class argument on the sesquilinear form.
For a **unitary** intertwiner it is already available, because
`BorelCalculus.borelCalculus_comp_val_of_intertwines` transports the diagonal
measures themselves.  That is exactly the case a reducing-subspace argument
needs, since a subspace reduces `A` if and only if its *reflection* -- a
unitary -- commutes with `A`.

The one piece of glue is that `specProjection` and `BorelCalculus.specProjC`
index their sets differently: `specProjection` cuts the spectrum subtype by the
Cayley preimage of a real Borel set, while `specProjC` cuts by a Borel subset of
`ℂ`.  `cayleyCoordFun` is the map that makes the two agree, and
`specProjection_eq_specProjC` records the identification.

## Sources

*Follows nothing in particular*: the commutation that a reducing-subspace
uniqueness argument needs between a spectral projection and a projection onto a
reducing subspace.

## Provenance

*New.*  Composes `SeparatedIntertwiner.cayley_intertwines` with
`BorelCalculus.specProjC_apply_of_intertwines`.
-/

@[expose] public section

open scoped InnerProductSpace

namespace TauCeti
namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The inverse Cayley map read on all of `ℂ`, so that the *same* Borel set can be
handed to two operators' spectral projections.  On the spectrum of a Cayley
transform it agrees with `cayleyInv` by definition. -/
noncomputable def cayleyCoordPlane (z : ℂ) : ℝ := (Complex.I * (1 + z) / (1 - z)).re

/-- The plane-level inverse Cayley map is Borel measurable, which is all a spectral
projection needs of it: the singularity at `w = 1` is a single point. -/
theorem measurable_cayleyCoordPlane : Measurable cayleyCoordPlane := by
  unfold cayleyCoordPlane
  fun_prop

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- On the spectrum of a Cayley transform the plane-level map agrees with `cayleyInv`.
This is the equation that lets one Borel subset of `ℝ` be fed to `specProjection` and
its `ℂ`-indexed spelling `specProjC` at the same time. -/
theorem cayleyInv_eq_cayleyCoordPlane (w : _root_.spectrum ℂ (cayley hA)) :
    cayleyInv hA w = cayleyCoordPlane (w : ℂ) := by
  rw [cayleyInv_def, cayleyCoordPlane]

/-- **The two spellings of a spectral projection agree.**  `specProjection` cuts by a
real Borel set through `cayleyInv`; `specProjC` cuts by a complex Borel set through the
coordinate itself.  They are the same operator for the preimage set. -/
theorem specProjection_eq_specProjC (B : Set ℝ) (hB : MeasurableSet B) :
    specProjection hA B hB
      = BorelCalculus.specProjC (isStarNormal_cayley hA)
          (measurable_cayleyCoordPlane hB) := by
  rw [specProjection_eq_borelCalculus, BorelCalculus.specProjC_def]
  refine BorelCalculus.borelCalculus_congr_ae _ _ _ fun η => ?_
  refine Filter.Eventually.of_forall fun w => ?_
  have hEq : cayleyInv hA w = cayleyCoordPlane (w : ℂ) := cayleyInv_eq_cayleyCoordPlane hA w
  change (cayleyInv hA ⁻¹' B).indicator (fun _ => (1 : ℂ)) w
      = (cayleyCoordPlane ⁻¹' B).indicator (fun _ => (1 : ℂ)) (w : ℂ)
  by_cases h : cayleyInv hA w ∈ B
  · have h' : (w : ℂ) ∈ cayleyCoordPlane ⁻¹' B := by
      rw [Set.mem_preimage, ← hEq]; exact h
    rw [Set.indicator_of_mem (show w ∈ cayleyInv hA ⁻¹' B from h),
      Set.indicator_of_mem h']
  · have h' : (w : ℂ) ∉ cayleyCoordPlane ⁻¹' B := by
      rw [Set.mem_preimage, ← hEq]; exact h
    rw [Set.indicator_of_notMem (show w ∉ cayleyInv hA ⁻¹' B from h),
      Set.indicator_of_notMem h']

/-- **Spectral projections are natural under a unitary intertwiner.**

If the unitary `e` preserves `dom A` and commutes with `A` there, then it commutes
with every spectral projection of `A`. -/
theorem specProjection_apply_of_unitary_intertwines (e : H ≃ₗᵢ[ℂ] H)
    (hmaps : ∀ x : A.domain, e (x : H) ∈ A.domain)
    (hint : ∀ x : A.domain, A ⟨e (x : H), hmaps x⟩ = e (A x))
    (B : Set ℝ) (hB : MeasurableSet B) (x : H) :
    e (specProjection hA B hB x) = specProjection hA B hB (e x) := by
  have hcay : e.toLinearIsometry.toContinuousLinearMap ∘L cayley hA
      = cayley hA ∘L e.toLinearIsometry.toContinuousLinearMap :=
    cayley_intertwines hA hA hmaps hint
  have he : ∀ z : H, e (cayley hA z) = cayley hA (e z) := by
    intro z
    have h := congrArg (fun T : H →L[ℂ] H => T z) hcay
    simpa only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry] using h
  rw [specProjection_eq_specProjC hA B hB]
  exact BorelCalculus.specProjC_apply_of_intertwines (isStarNormal_cayley hA) e he
    (measurable_cayleyCoordPlane hB) x

end LinearPMap
end TauCeti
