/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Analyticity
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Derivatives

/-!
# Biholomorphic maps between open sets

`IsBiholomorphic` adds holomorphy of both maps to Mathlib's `OpenPartialHomeomorph`. The source
and target are already open; connectedness and nonemptiness are not required. The derivative
identities work in complex normed spaces. Equality of dimensions requires a nonempty source.
Local inverse results use finite-dimensional spaces and the existing holomorphic–analytic
equivalence and Mathlib's inverse function theorem.

Reference: [Range][Range1986] (1986), I §2.4, Theorem 2.5 and Corollary 2.6. The chain rule and
coordinate Jacobian are in `Derivatives`.

## Main definitions

* `IsBiholomorphic`: An equivalence between open sets is biholomorphic when both maps are
  holomorphic on their respective open domains.
* `affineOpenPartialHomeomorph`: An invertible complex linear map followed by a translation, as an
  equivalence of the whole spaces.
* `shearOpenPartialHomeomorph`: A continuous shear has an explicit inverse obtained by subtracting
  the same function.

## Main results

* `exists_biholomorphic_of_isInvertible_fderiv`: **Holomorphic inverse mapping theorem.** An
  invertible complex derivative gives a biholomorphic restriction to an open neighborhood inside the
  given open set.
* `exists_open_injOn_of_injective_fderiv`: **[Range][Range1986] I, Corollary 2.6.** An injective
  complex derivative gives local injectivity, also when the target has larger dimension.

## References

* [R. M. Range, *Holomorphic Functions and Integral Representations in Several Complex
  Variables*][Range1986]
-/

public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace SeveralComplexVariables

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- An equivalence between open sets is biholomorphic when both maps are holomorphic on their
respective open domains. No connectedness or nonemptiness is imposed. -/
@[expose] def IsBiholomorphic (e : OpenPartialHomeomorph E F) : Prop :=
  DifferentiableOn ℂ e e.source ∧ DifferentiableOn ℂ e.symm e.target

/-- The inverse of a biholomorphic map is biholomorphic. -/
theorem IsBiholomorphic.symm {e : OpenPartialHomeomorph E F} (he : IsBiholomorphic e) :
    IsBiholomorphic e.symm := ⟨he.2, he.1⟩

/-- The identity map of the whole space is biholomorphic. -/
theorem isBiholomorphic_refl : IsBiholomorphic (OpenPartialHomeomorph.refl E) :=
  ⟨differentiable_id.differentiableOn, differentiable_id.differentiableOn⟩

/-- Compositions of biholomorphic maps are biholomorphic on their natural open source. -/
theorem IsBiholomorphic.trans {e : OpenPartialHomeomorph E F}
    {e' : OpenPartialHomeomorph F G} (he : IsBiholomorphic e) (he' : IsBiholomorphic e') :
    IsBiholomorphic (e.trans e') := by
  constructor
  · exact he'.1.comp (he.1.mono inter_subset_left) (fun _ hx => hx.2)
  · exact he.2.comp (he'.2.mono inter_subset_left) (fun _ hx => hx.2)

/-- Restriction to the intersection of the source with the interior of any set preserves
biholomorphy. For an open set this is ordinary restriction. -/
theorem IsBiholomorphic.restr {e : OpenPartialHomeomorph E F} (he : IsBiholomorphic e)
    (s : Set E) : IsBiholomorphic (e.restr s) :=
  ⟨he.1.mono inter_subset_left, he.2.mono inter_subset_left⟩

/-- A biholomorphic map is complex differentiable at every point of its source. -/
theorem IsBiholomorphic.differentiableAt {e : OpenPartialHomeomorph E F}
    (he : IsBiholomorphic e) {a : E} (ha : a ∈ e.source) : DifferentiableAt ℂ e a :=
  (he.1 a ha).differentiableAt (e.open_source.mem_nhds ha)

/-- The derivative of the inverse composed with the forward derivative is the identity. -/
theorem IsBiholomorphic.fderiv_symm_comp {e : OpenPartialHomeomorph E F}
    (he : IsBiholomorphic e) {a : E} (ha : a ∈ e.source) :
    (fderiv ℂ e.symm (e a)).comp (fderiv ℂ e a) = ContinuousLinearMap.id ℂ E := by
  rw [← fderiv_comp a (he.symm.differentiableAt (e.map_source ha)) (he.differentiableAt ha)]
  have h : (e.symm ∘ e) =ᶠ[𝓝 a] id := e.eventually_left_inverse ha
  exact h.fderiv_eq.trans fderiv_id

/-- The forward derivative composed with the derivative of the inverse is the identity. -/
theorem IsBiholomorphic.fderiv_comp_symm {e : OpenPartialHomeomorph E F}
    (he : IsBiholomorphic e) {a : E} (ha : a ∈ e.source) :
    (fderiv ℂ e a).comp (fderiv ℂ e.symm (e a)) = ContinuousLinearMap.id ℂ F := by
  simpa only [OpenPartialHomeomorph.symm_symm, e.left_inv ha] using
    he.symm.fderiv_symm_comp (e.map_source ha)

/-- The derivative of a biholomorphic map is an invertible continuous complex linear map. -/
theorem IsBiholomorphic.isInvertible_fderiv {e : OpenPartialHomeomorph E F}
    (he : IsBiholomorphic e) {a : E} (ha : a ∈ e.source) :
    (fderiv ℂ e a).IsInvertible :=
  .of_inverse (he.fderiv_comp_symm ha) (he.fderiv_symm_comp ha)

/-- The derivative of the inverse is the inverse of the derivative. -/
theorem IsBiholomorphic.fderiv_symm {e : OpenPartialHomeomorph E F}
    (he : IsBiholomorphic e) {a : E} (ha : a ∈ e.source) :
    fderiv ℂ e.symm (e a) = (fderiv ℂ e a).inverse :=
  (ContinuousLinearMap.inverse_eq (he.fderiv_comp_symm ha) (he.fderiv_symm_comp ha)).symm

/-- Nonempty biholomorphically equivalent open sets have equal ambient complex dimensions.
Nonemptiness is essential: empty sets in different dimensions are equivalent. -/
theorem IsBiholomorphic.finrank_eq {e : OpenPartialHomeomorph E F}
    (he : IsBiholomorphic e) (hne : e.source.Nonempty) :
    Module.finrank ℂ E = Module.finrank ℂ F := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨L, hL⟩ := he.isInvertible_fderiv ha
  exact L.toLinearEquiv.finrank_eq

/-- Holomorphy of a function on the target is equivalent to holomorphy after a biholomorphic change
of coordinates on the source. -/
theorem IsBiholomorphic.differentiableOn_comp_iff {e : OpenPartialHomeomorph E F}
    (he : IsBiholomorphic e) {g : F → G} :
    DifferentiableOn ℂ (g ∘ e) e.source ↔ DifferentiableOn ℂ g e.target := by
  constructor
  · intro h
    have hc := h.comp he.2 e.symm.mapsTo
    exact hc.congr (fun y hy => congrArg g (e.right_inv hy).symm)
  · exact fun h => h.comp he.1 e.mapsTo

section Inverse

variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

/-- **Holomorphic inverse mapping theorem.** An invertible complex derivative gives
a biholomorphic restriction to an open neighborhood inside the given open set.
The forward representative agrees with the original map everywhere. -/
theorem exists_biholomorphic_of_isInvertible_fderiv {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : DifferentiableOn ℂ f U) {a : E} (ha : a ∈ U)
    (hinv : (fderiv ℂ f a).IsInvertible) :
    ∃ e : OpenPartialHomeomorph E F, IsBiholomorphic e ∧ a ∈ e.source ∧
      e.source ⊆ U ∧ (e : E → F) = f := by
  let := FiniteDimensional.complete ℂ E
  let := FiniteDimensional.complete ℂ F
  obtain ⟨L, hL⟩ := hinv
  have hfa := hf.analyticOnNhd_of_finiteDimensional hU a ha
  have hc : ContDiffAt ℂ ω f a := hfa.contDiffAt
  have hd : HasFDerivAt f (L : E →L[ℂ] F) a := by
    rw [hL]
    exact hfa.differentiableAt.hasFDerivAt
  let e := hc.toOpenPartialHomeomorph f hd (by simp)
  have hae : a ∈ e.source := hc.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hga : AnalyticAt ℂ e.symm (f a) := (hc.to_localInverse hd (by simp)).analyticAt
  have hn : U ∩ e ⁻¹' {y | AnalyticAt ℂ e.symm y} ∈ 𝓝 a :=
    inter_mem (hU.mem_nhds ha) (hfa.continuousAt.preimage_mem_nhds hga.eventually_analyticAt)
  obtain ⟨V, hVS, hV, haV⟩ := mem_nhds_iff.mp hn
  refine ⟨e.restr V, ?_, ?_, ?_, rfl⟩
  · constructor
    · exact hf.mono (fun x hx => (hVS (interior_subset hx.2)).1)
    · intro y hy
      have h := (hVS (interior_subset hy.2)).2
      change AnalyticAt ℂ e.symm (e (e.symm y)) at h
      have hg : AnalyticAt ℂ e.symm y := by simpa only [e.right_inv hy.1] using h
      exact hg.differentiableAt.differentiableWithinAt
  · exact ⟨hae, hV.interior_eq.symm ▸ haV⟩
  · exact fun x hx => (hVS (interior_subset hx.2)).1

/-- A holomorphic map is locally biholomorphic exactly when its derivative is invertible. -/
theorem isInvertible_fderiv_iff_exists_biholomorphic {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : DifferentiableOn ℂ f U) {a : E} (ha : a ∈ U) :
    (fderiv ℂ f a).IsInvertible ↔
      ∃ e : OpenPartialHomeomorph E F, IsBiholomorphic e ∧ a ∈ e.source ∧
        e.source ⊆ U ∧ (e : E → F) = f := by
  refine ⟨exists_biholomorphic_of_isInvertible_fderiv hU hf ha, ?_⟩
  rintro ⟨e, he, hae, _, rfl⟩
  exact he.isInvertible_fderiv hae

/-- **[Range][Range1986] I, Corollary 2.6.** An injective complex derivative gives local
injectivity,
also when the target has larger dimension. No surjectivity assumption is needed. -/
theorem exists_open_injOn_of_injective_fderiv {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : DifferentiableOn ℂ f U) {a : E} (ha : a ∈ U)
    (hi : Function.Injective (fderiv ℂ f a)) :
    ∃ V, IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧ InjOn f V := by
  let A := (fderiv ℂ f a).toLinearMap
  obtain ⟨B, hB⟩ := A.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  let L : F →L[ℂ] E := B.toContinuousLinearMap
  have hd : fderiv ℂ (L ∘ f) a = ContinuousLinearMap.id ℂ E := by
    rw [fderiv_comp a L.differentiableAt ((hf a ha).differentiableAt (hU.mem_nhds ha)),
      L.fderiv]
    ext x
    exact DFunLike.congr_fun hB x
  have hcomp : DifferentiableOn ℂ (L ∘ f) U := L.differentiable.comp_differentiableOn hf
  obtain ⟨e, he, hae, hsub, heq⟩ := exists_biholomorphic_of_isInvertible_fderiv hU hcomp ha
    (by rw [hd]; exact ⟨ContinuousLinearEquiv.refl ℂ E, rfl⟩)
  refine ⟨e.source, e.open_source, hae, hsub, ?_⟩
  intro x hx y hy hxy
  apply e.injOn hx hy
  rw [heq]
  exact congrArg L hxy

end Inverse

section Examples

/-- An invertible complex linear map followed by a translation, as an equivalence of the whole
spaces. -/
@[expose] def affineOpenPartialHomeomorph (L : E ≃L[ℂ] F) (b : F) : OpenPartialHomeomorph E F :=
  (L.toHomeomorph.trans (Homeomorph.addRight b)).toOpenPartialHomeomorph

/-- The forward affine map applies the linear map and then adds the translation. -/
@[simp] theorem affineOpenPartialHomeomorph_apply (L : E ≃L[ℂ] F) (b : F) (x : E) :
    affineOpenPartialHomeomorph L b x = L x + b := rfl

/-- The inverse affine map first subtracts the translation. -/
@[simp] theorem affineOpenPartialHomeomorph_symm_apply (L : E ≃L[ℂ] F) (b : F) (y : F) :
    (affineOpenPartialHomeomorph L b).symm y = L.symm (y - b) := by
  change L.symm (y + -b) = L.symm (y - b)
  rw [sub_eq_add_neg]

/-- Invertible complex affine maps are biholomorphic. -/
theorem isBiholomorphic_affine (L : E ≃L[ℂ] F) (b : F) :
    IsBiholomorphic (affineOpenPartialHomeomorph L b) := by
  constructor
  · exact (L.differentiable.add_const b).differentiableOn
  · exact (L.symm.differentiable.comp (differentiable_id.add_const (-b))).differentiableOn

/-- A continuous shear has an explicit inverse obtained by subtracting the same function. -/
@[expose] def shearOpenPartialHomeomorph (h : F → E) (hh : Continuous h) :
    OpenPartialHomeomorph (E × F) (E × F) :=
  ({ toFun := fun p => (p.1 + h p.2, p.2)
     invFun := fun p => (p.1 - h p.2, p.2)
     left_inv := by intro p; simp
     right_inv := by intro p; simp
     continuous_toFun := (continuous_fst.add (hh.comp continuous_snd)).prodMk continuous_snd
     continuous_invFun := (continuous_fst.sub (hh.comp continuous_snd)).prodMk continuous_snd } :
     (E × F) ≃ₜ (E × F)).toOpenPartialHomeomorph

omit [NormedSpace ℂ E] [NormedSpace ℂ F] in
/-- The forward shear adds a function of the second coordinate to the first. -/
@[simp] theorem shearOpenPartialHomeomorph_apply (h : F → E) (hh : Continuous h) (p : E × F) :
    shearOpenPartialHomeomorph h hh p = (p.1 + h p.2, p.2) := rfl

omit [NormedSpace ℂ E] [NormedSpace ℂ F] in
/-- The inverse shear subtracts the same function. -/
@[simp] theorem shearOpenPartialHomeomorph_symm_apply (h : F → E) (hh : Continuous h)
    (p : E × F) : (shearOpenPartialHomeomorph h hh).symm p = (p.1 - h p.2, p.2) := rfl

/-- An entire holomorphic function gives a biholomorphic shear, including nonlinear examples. -/
theorem isBiholomorphic_shear {h : F → E} (hh : Differentiable ℂ h) :
    IsBiholomorphic (shearOpenPartialHomeomorph h hh.continuous) := by
  constructor
  · exact ((differentiable_fst.add (hh.comp differentiable_snd)).prodMk
      differentiable_snd).differentiableOn
  · exact ((differentiable_fst.sub (hh.comp differentiable_snd)).prodMk
      differentiable_snd).differentiableOn

end Examples

section Coordinates

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Nonempty biholomorphically equivalent coordinate domains have the same number of complex
coordinates, including the possibility of zero coordinates. -/
theorem IsBiholomorphic.card_eq {κ : Type*} [Fintype κ]
    {e : OpenPartialHomeomorph (ι → ℂ) (κ → ℂ)} (he : IsBiholomorphic e)
    (hne : e.source.Nonempty) : Fintype.card ι = Fintype.card κ := by
  simpa using he.finrank_eq hne

/-- The coordinate determinant criterion in [Range][Range1986]'s local inverse theorem. -/
theorem exists_biholomorphic_of_det_complexJacobian_ne_zero {U : Set (ι → ℂ)}
    (hU : IsOpen U) {f : (ι → ℂ) → (ι → ℂ)} (hf : DifferentiableOn ℂ f U)
    {a : ι → ℂ} (ha : a ∈ U) (hd : (complexJacobian f a).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ι → ℂ) (ι → ℂ), IsBiholomorphic e ∧ a ∈ e.source ∧
      e.source ⊆ U ∧ (e : (ι → ℂ) → (ι → ℂ)) = f :=
  exists_biholomorphic_of_isInvertible_fderiv hU hf ha
    ((det_complexJacobian_ne_zero_iff ((hf a ha).differentiableAt (hU.mem_nhds ha))).mp hd)

/-- A biholomorphic map has nonvanishing complex Jacobian determinant throughout its source. -/
theorem IsBiholomorphic.det_complexJacobian_ne_zero
    {e : OpenPartialHomeomorph (ι → ℂ) (ι → ℂ)} (he : IsBiholomorphic e)
    {a : ι → ℂ} (ha : a ∈ e.source) : (complexJacobian e a).det ≠ 0 :=
  (det_complexJacobian_ne_zero_iff (he.differentiableAt ha)).mpr (he.isInvertible_fderiv ha)

end Coordinates

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
