/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.InjectiveMapping.CriticalSet

/-!
# Injective holomorphic maps in equal dimensions

An injective holomorphic map between equal-dimensional finite-dimensional complex spaces has
invertible derivative and is biholomorphic onto its open image. No connectedness or nonemptiness
is required. The critical-set argument proves nonsingularity; the inverse mapping theorem then
gives the global inverse onto the image. Supporting modules separate one-variable
nonsingularity, immersion points, the codimension-one reduction, and exclusion of the critical
set.

Reference: [Fritzsche–Grauert][FritzscheGrauert2002] I, Theorem 8.5 and Corollary 8.6.

## Main results

`isInvertible_fderiv_of_injOn` is nonsingularity of an injective holomorphic map in equal
dimensions. `exists_biholomorphic_of_injOn` produces a biholomorphism onto the image.
`isOpen_image_of_holomorphic_injOn` is openness of the image. `det_complexJacobian_ne_zero_of_injOn`
is the Jacobian form in coordinates.

## References

* [K. Fritzsche and H. Grauert, *From Holomorphic Functions to Complex
  Manifolds*][FritzscheGrauert2002]
-/

public noncomputable section

open Set Filter
open scoped Topology

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

/-- An injective holomorphic map in equal dimensions has invertible complex derivative. Equal
dimensions are essential: an injective parametrization of a cusp can have zero derivative. The
proof includes dimension zero and arbitrary finite-dimensional complex normed spaces. -/
theorem isInvertible_fderiv_of_injOn (hdim : Module.finrank ℂ E = Module.finrank ℂ F)
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U)
    (hi : InjOn f U) {a : E} (ha : a ∈ U) : (fderiv ℂ f a).IsInvertible := by
  let n := Module.finrank ℂ E
  let A : E ≃L[ℂ] (Fin n → ℂ) := (Module.finBasis ℂ E).equivFunL
  let B : F ≃L[ℂ] (Fin n → ℂ) := ContinuousLinearEquiv.ofFinrankEq (by simpa [n] using hdim.symm)
  let g := B ∘ f ∘ A.symm
  let V := A.symm ⁻¹' U
  have hV : IsOpen V := hU.preimage A.symm.continuous
  have hg : DifferentiableOn ℂ g V :=
    B.differentiable.comp_differentiableOn
      (hf.comp A.symm.differentiable.differentiableOn (fun _ hz => hz))
  have hgi : InjOn g V := by
    intro z hz w hw he
    apply A.symm.injective
    exact hi hz hw (B.injective he)
  have haV : A a ∈ V := by simpa [V]
  obtain ⟨T, hT⟩ := isInvertible_fderiv_of_injOn_coordinates hV hg hgi haV
  have hda : fderiv ℂ g (A a) =
      B.toContinuousLinearMap.comp ((fderiv ℂ f a).comp A.symm.toContinuousLinearMap) := by
    have hfa : HasFDerivAt f (fderiv ℂ f a) (A.symm (A a)) := by
      simpa only [A.symm_apply_apply] using
        ((hf a ha).differentiableAt (hU.mem_nhds ha)).hasFDerivAt
    exact (B.hasFDerivAt.comp (A a) (hfa.comp (A a) A.symm.hasFDerivAt)).fderiv
  refine ⟨A.trans (T.trans B.symm), ?_⟩
  ext v
  change B.symm (T (A v)) = (fderiv ℂ f a) v
  apply B.injective
  have he := DFunLike.congr_fun hT (A v)
  simpa only [hda, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    A.symm_apply_apply, B.apply_symm_apply] using he

/-- An injective holomorphic map between equal-dimensional spaces gives a biholomorphic map with
source exactly `U` and target exactly its image. This follows from nonsingularity. -/
theorem exists_biholomorphic_of_injOn (hdim : Module.finrank ℂ E = Module.finrank ℂ F)
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U)
    (hi : InjOn f U) :
    ∃ e : OpenPartialHomeomorph E F, IsBiholomorphic e ∧ e.source = U ∧
      e.target = f '' U ∧ (e : E → F) = f := by
  let g := Function.invFunOn f U
  have hlocal : ∀ a ∈ U, ∃ e : OpenPartialHomeomorph E F, IsBiholomorphic e ∧
      a ∈ e.source ∧ e.source ⊆ U ∧ (e : E → F) = f := fun a ha =>
    exists_biholomorphic_of_isInvertible_fderiv hU hf ha
      (isInvertible_fderiv_of_injOn hdim hU hf hi ha)
  have ho : IsOpen (f '' U) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨a, ha, rfl⟩
    obtain ⟨e, _, hae, heU, heq⟩ := hlocal a ha
    have htar : e.target ⊆ f '' U := by
      intro z hz
      exact ⟨e.symm z, heU (e.map_target hz), by rw [← heq]; exact e.right_inv hz⟩
    exact mem_of_superset (e.open_target.mem_nhds (by rw [← heq]; exact e.map_source hae)) htar
  have hg : DifferentiableOn ℂ g (f '' U) := by
    rintro y ⟨a, ha, rfl⟩
    obtain ⟨e, he, hae, heU, heq⟩ := hlocal a ha
    have hfa : f a ∈ e.target := by rw [← heq]; exact e.map_source hae
    have heqg : g =ᶠ[𝓝 (f a)] e.symm := by
      filter_upwards [e.open_target.mem_nhds hfa] with z hz
      have hzU : z ∈ f '' U := ⟨e.symm z, heU (e.map_target hz),
        by rw [← heq]; exact e.right_inv hz⟩
      apply hi (Function.invFunOn_mem hzU) (heU (e.map_target hz))
      exact (Function.invFunOn_eq hzU).trans (by rw [← heq]; exact (e.right_inv hz).symm)
    exact ((he.symm.differentiableAt hfa).congr_of_eventuallyEq heqg).differentiableWithinAt
  let e : OpenPartialHomeomorph E F :=
    { toFun := f
      invFun := g
      source := U
      target := f '' U
      map_source' := fun x hx => mem_image_of_mem f hx
      map_target' := fun y hy => Function.invFunOn_mem hy
      left_inv' := hi.leftInvOn_invFunOn
      right_inv' := fun y hy => Function.invFunOn_eq hy
      open_source := hU
      open_target := ho
      continuousOn_toFun := hf.continuousOn
      continuousOn_invFun := hg.continuousOn }
  exact ⟨e, ⟨hf, hg⟩, rfl, rfl, rfl⟩

/-- The image of an injective holomorphic map in equal dimensions is open. -/
theorem isOpen_image_of_holomorphic_injOn (hdim : Module.finrank ℂ E = Module.finrank ℂ F)
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U)
    (hi : InjOn f U) : IsOpen (f '' U) := by
  obtain ⟨e, _, _, ht, _⟩ := exists_biholomorphic_of_injOn hdim hU hf hi
  exact ht ▸ e.open_target

/-- The coordinate Jacobian determinant of an injective holomorphic map never vanishes. -/
theorem det_complexJacobian_ne_zero_of_injOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Set (ι → ℂ)} (hU : IsOpen U) {f : (ι → ℂ) → (ι → ℂ)}
    (hf : DifferentiableOn ℂ f U) (hi : InjOn f U) {a : ι → ℂ} (ha : a ∈ U) :
    (complexJacobian f a).det ≠ 0 :=
  (det_complexJacobian_ne_zero_iff ((hf a ha).differentiableAt (hU.mem_nhds ha))).mpr
    (isInvertible_fderiv_of_injOn rfl hU hf hi ha)

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
