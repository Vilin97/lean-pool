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

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# Fiberwise composition of smooth hom-bundle sections

Mathlib's `Mathlib.Geometry.Manifold.VectorBundle.Hom` provides `ContMDiff.clm_bundle_apply`
(applying a smooth family of linear maps to a smooth section) and `clm_bundle_apply₂`, but no lemma
composing two smooth hom-bundle sections into a smooth hom-bundle section.

This module supplies exactly that: given `C^n` sections
`ϕ : ∀ x, E₂ x →L[𝕜] E₃ x` and `ψ : ∀ x, E₁ x →L[𝕜] E₂ x` of the hom bundles, the fiberwise
composition `x ↦ (ϕ x).comp (ψ x)` is a `C^n` section of `Hom(E₁, E₃)`.

The proof reduces `ContMDiff*_hom_bundle` to the `inCoordinates` representation and uses the fact
that, on the base set of the middle trivialization, the coordinate readout of a composition is the
composition of the coordinate readouts (the middle `symmL ∘ continuousLinearMapAt = id`
cancellation), reducing to the ordinary normed-space `ContMDiff*.clm_comp`.

* `inCoordinates_comp_eq` — the coordinate-readout factorization on the middle base set.
* `ContMDiffWithinAt.clm_bundle_comp` / `ContMDiffAt.clm_bundle_comp` / `ContMDiffOn.clm_bundle_comp`
  / `ContMDiff.clm_bundle_comp` — the composition of two smooth hom-bundle sections is smooth.
-/

@[expose] public noncomputable section

open Bundle Set ContinuousLinearMap

open scoped Manifold Bundle Topology

section

variable {𝕜 B F₁ F₂ F₃ : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {E₃ : B → Type*} [∀ x, AddCommGroup (E₃ x)]
  [∀ x, Module 𝕜 (E₃ x)] [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  [TopologicalSpace (TotalSpace F₃ E₃)] [∀ x, TopologicalSpace (E₃ x)]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]

/-- The coordinate readout of a fiberwise composition factors through the coordinate readouts, on
the base set of the middle trivialization: the intermediate `symmL ∘ continuousLinearMapAt` cancels
to the identity. -/
theorem inCoordinates_comp_eq {x₀ x : B}
    (hx : x ∈ (trivializationAt F₂ E₂ x₀).baseSet)
    (ϕ : E₂ x →L[𝕜] E₃ x) (ψ : E₁ x →L[𝕜] E₂ x) :
    ContinuousLinearMap.inCoordinates F₁ E₁ F₃ E₃ x₀ x x₀ x (ϕ.comp ψ) =
      (ContinuousLinearMap.inCoordinates F₂ E₂ F₃ E₃ x₀ x x₀ x ϕ).comp
        (ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ x₀ x x₀ x ψ) := by
  simp only [ContinuousLinearMap.inCoordinates]
  ext y
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [Trivialization.symmL_continuousLinearMapAt (trivializationAt F₂ E₂ x₀) hx]

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [∀ x, IsTopologicalAddGroup (E₃ x)] [∀ x, ContinuousSMul 𝕜 (E₃ x)]

/-- The fiberwise composition of two `C^n` hom-bundle sections is a `C^n` hom-bundle section
(within-a-set-at-a-point version). -/
theorem ContMDiffWithinAt.clm_bundle_comp
    {ϕ : ∀ x, E₂ x →L[𝕜] E₃ x} {ψ : ∀ x, E₁ x →L[𝕜] E₂ x} {s : Set B} {x₀ : B}
    (hϕ : ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₃)) n
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₃) (E := fun x ↦ E₂ x →L[𝕜] E₃ x) x (ϕ x)) s x₀)
    (hψ : ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (ψ x)) s x₀) :
    ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₃)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₃) (E := fun x ↦ E₁ x →L[𝕜] E₃ x) x ((ϕ x).comp (ψ x)))
      s x₀ := by
  rw [contMDiffWithinAt_hom_bundle] at hϕ hψ ⊢
  refine ⟨hϕ.1, ?_⟩
  have hcomp := hϕ.2.clm_comp hψ.2
  have hmem : (trivializationAt F₂ E₂ x₀).baseSet ∈ 𝓝 x₀ :=
    (trivializationAt F₂ E₂ x₀).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' x₀)
  have hev :
      (fun x ↦ ContinuousLinearMap.inCoordinates F₁ E₁ F₃ E₃ x₀ x x₀ x ((ϕ x).comp (ψ x)))
        =ᶠ[𝓝[s] x₀]
      (fun x ↦ (ContinuousLinearMap.inCoordinates F₂ E₂ F₃ E₃ x₀ x x₀ x (ϕ x)).comp
        (ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ x₀ x x₀ x (ψ x))) := by
    refine Filter.eventuallyEq_of_mem (nhdsWithin_le_nhds hmem) ?_
    intro x hx
    exact inCoordinates_comp_eq hx (ϕ x) (ψ x)
  exact hcomp.congr_of_eventuallyEq hev
    (inCoordinates_comp_eq (FiberBundle.mem_baseSet_trivializationAt' x₀) (ϕ x₀) (ψ x₀))

/-- The fiberwise composition of two `C^n` hom-bundle sections is a `C^n` hom-bundle section
(at-a-point version). -/
theorem ContMDiffAt.clm_bundle_comp
    {ϕ : ∀ x, E₂ x →L[𝕜] E₃ x} {ψ : ∀ x, E₁ x →L[𝕜] E₂ x} {x₀ : B}
    (hϕ : ContMDiffAt IB (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₃)) n
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₃) (E := fun x ↦ E₂ x →L[𝕜] E₃ x) x (ϕ x)) x₀)
    (hψ : ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (ψ x)) x₀) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₃)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₃) (E := fun x ↦ E₁ x →L[𝕜] E₃ x) x ((ϕ x).comp (ψ x)))
      x₀ := by
  rw [← contMDiffWithinAt_univ] at hϕ hψ ⊢
  exact hϕ.clm_bundle_comp hψ

/-- The fiberwise composition of two differentiable hom-bundle sections is
differentiable.  This is the first-order companion of
`ContMDiffAt.clm_bundle_comp`; it is useful when regularity is naturally
available only as `MDiffAt`, as for curvature contractions. -/
theorem MDifferentiableAt.clm_bundle_comp
    {ϕ : ∀ x, E₂ x →L[𝕜] E₃ x} {ψ : ∀ x, E₁ x →L[𝕜] E₂ x} {x₀ : B}
    (hϕ : MDiffAt
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₃)
        (E := fun x ↦ E₂ x →L[𝕜] E₃ x) x (ϕ x)) x₀)
    (hψ : MDiffAt
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
        (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (ψ x)) x₀) :
    MDiffAt
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₃)
        (E := fun x ↦ E₁ x →L[𝕜] E₃ x) x ((ϕ x).comp (ψ x))) x₀ := by
  rw [mdifferentiableAt_hom_bundle] at hϕ hψ ⊢
  refine ⟨hϕ.1, ?_⟩
  have hcomp := hϕ.2.clm_comp hψ.2
  have hmem : (trivializationAt F₂ E₂ x₀).baseSet ∈ 𝓝 x₀ :=
    (trivializationAt F₂ E₂ x₀).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' x₀)
  have hev :
      (fun x ↦ ContinuousLinearMap.inCoordinates F₁ E₁ F₃ E₃ x₀ x x₀ x
        ((ϕ x).comp (ψ x))) =ᶠ[𝓝 x₀]
      (fun x ↦ (ContinuousLinearMap.inCoordinates F₂ E₂ F₃ E₃ x₀ x x₀ x (ϕ x)).comp
        (ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ x₀ x x₀ x (ψ x))) := by
    filter_upwards [hmem] with x hx
    exact inCoordinates_comp_eq hx (ϕ x) (ψ x)
  exact hcomp.congr_of_eventuallyEq hev

/-- A map into continuous linear maps between finite-dimensional spaces is
`C^n` at a point when all of its values on a fixed basis are `C^n` there.
This is the differentiable reconstruction analogue of extensionality for
linear maps and is useful for assembling tensor-bundle coordinate fields from
their frame components. -/
theorem contMDiffAt_clm_of_forall_apply_basis
    [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι 𝕜 F₁)
    {f : B → F₁ →L[𝕜] F₂} {x : B}
    (h : ∀ i, ContMDiffAt IB 𝓘(𝕜, F₂) n (fun y ↦ f y (b i)) x) :
    ContMDiffAt IB 𝓘(𝕜, F₁ →L[𝕜] F₂) n f x := by
  classical
  let recon : (ι → F₂) →L[𝕜] (F₁ →L[𝕜] F₂) :=
    LinearMap.toContinuousLinearMap <|
      (LinearMap.toContinuousLinearMap :
        (F₁ →ₗ[𝕜] F₂) ≃ₗ[𝕜] (F₁ →L[𝕜] F₂)).toLinearMap.comp
        (b.constr 𝕜 : (ι → F₂) ≃ₗ[𝕜] (F₁ →ₗ[𝕜] F₂)).toLinearMap
  have hg : ContMDiffAt IB 𝓘(𝕜, ι → F₂) n
      (fun y ↦ (fun i ↦ f y (b i))) x :=
    contMDiffAt_pi_space.mpr h
  have hr : ContMDiff 𝓘(𝕜, ι → F₂) 𝓘(𝕜, F₁ →L[𝕜] F₂) n recon :=
    recon.contDiff.contMDiff
  have hc := hr.contMDiffAt.comp x hg
  convert hc using 1
  funext y
  apply ContinuousLinearMap.coe_injective
  refine b.ext fun i ↦ ?_
  simp [recon]

/- The same finite-dimensional reconstruction at the differentiability level.
   This is kept separate from the `C^n` lemma because a first-order
   derivative is all that is needed for scalar-gradient regularity. -/
theorem mdifferentiableAt_clm_of_forall_apply_basis
    [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι 𝕜 F₁)
    {f : B → F₁ →L[𝕜] F₂} {x : B}
    (h : ∀ i, MDifferentiableAt IB 𝓘(𝕜, F₂)
      (fun y ↦ f y (b i)) x) :
    MDifferentiableAt IB 𝓘(𝕜, F₁ →L[𝕜] F₂) f x := by
  classical
  let recon : (ι → F₂) →L[𝕜] (F₁ →L[𝕜] F₂) :=
    LinearMap.toContinuousLinearMap <|
      (LinearMap.toContinuousLinearMap :
        (F₁ →ₗ[𝕜] F₂) ≃ₗ[𝕜] (F₁ →L[𝕜] F₂)).toLinearMap.comp
        (b.constr 𝕜 : (ι → F₂) ≃ₗ[𝕜] (F₁ →ₗ[𝕜] F₂)).toLinearMap
  have hg : MDifferentiableAt IB 𝓘(𝕜, ι → F₂)
      (fun y ↦ (fun i ↦ f y (b i))) x := by
    rw [mdifferentiableAt_iff]
    refine ⟨continuousAt_pi.2 (fun i ↦ (h i).continuousAt), ?_⟩
    rw [differentiableWithinAt_pi]
    intro i
    have hi := (h i).differentiableWithinAt_writtenInExtChartAt
    convert hi using 1 <;> rfl
  have hr : MDifferentiableAt 𝓘(𝕜, ι → F₂) 𝓘(𝕜, F₁ →L[𝕜] F₂) recon
      (fun i ↦ f x (b i)) := by
    exact (recon.differentiableAt).mdifferentiableAt
  have hc := hr.comp x hg
  convert hc using 1
  funext y
  apply ContinuousLinearMap.coe_injective
  refine b.ext fun i ↦ ?_
  simp [recon]

/- A hom-bundle section is differentiable at a point when its values on one
   genuine local frame are differentiable there. -/
theorem mdifferentiableAt_homBundle_of_forall_apply_localFrame
    [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]
    {s : ∀ x, E₁ x →L[𝕜] E₂ x} (x₀ : B)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι 𝕜 F₁)
    (h : ∀ i, MDifferentiableAt IB (IB.prod 𝓘(𝕜, F₂))
      (fun x ↦ TotalSpace.mk' F₂ x
        (s x ((trivializationAt F₁ E₁ x₀).localFrame b i x))) x₀) :
    MDifferentiableAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂))
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
        (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (s x)) x₀ := by
  classical
  rw [mdifferentiableAt_hom_bundle]
  refine ⟨mdifferentiableAt_id, ?_⟩
  apply mdifferentiableAt_clm_of_forall_apply_basis b
  intro i
  have hi := h i
  rw [mdifferentiableAt_section] at hi
  refine hi.congr_of_eventuallyEq ?_
  have hsrc : (trivializationAt F₁ E₁ x₀).baseSet ∈ 𝓝 x₀ :=
    (trivializationAt F₁ E₁ x₀).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' x₀)
  have hout : (trivializationAt F₂ E₂ x₀).baseSet ∈ 𝓝 x₀ :=
    (trivializationAt F₂ E₂ x₀).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' x₀)
  filter_upwards [hsrc, hout] with x hxsrc hxout
  rw [ContinuousLinearMap.inCoordinates_eq hxsrc hxout]
  rw [(trivializationAt F₁ E₁ x₀).localFrame_apply_of_mem_baseSet b hxsrc]
  rfl

/-- A hom-bundle section is `C^n` at a point when its values on one genuine local frame are
`C^n` sections at that point. -/
theorem contMDiffAt_homBundle_of_forall_apply_localFrame
    [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]
    {s : ∀ x, E₁ x →L[𝕜] E₂ x} (x₀ : B)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι 𝕜 F₁)
    (h : ∀ i, ContMDiffAt IB (IB.prod 𝓘(𝕜, F₂)) n
      (fun x ↦ TotalSpace.mk' F₂ x
        (s x ((trivializationAt F₁ E₁ x₀).localFrame b i x))) x₀) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
        (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (s x)) x₀ := by
  classical
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_clm_of_forall_apply_basis b
  intro i
  have hi := h i
  rw [Bundle.contMDiffAt_section] at hi
  refine hi.congr_of_eventuallyEq ?_
  have hsrc : (trivializationAt F₁ E₁ x₀).baseSet ∈ 𝓝 x₀ :=
    (trivializationAt F₁ E₁ x₀).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' x₀)
  have hout : (trivializationAt F₂ E₂ x₀).baseSet ∈ 𝓝 x₀ :=
    (trivializationAt F₂ E₂ x₀).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' x₀)
  filter_upwards [hsrc, hout] with x hxsrc hxout
  rw [ContinuousLinearMap.inCoordinates_eq hxsrc hxout]
  rw [(trivializationAt F₁ E₁ x₀).localFrame_apply_of_mem_baseSet b hxsrc]
  rfl

/-- The fiberwise composition of two `C^n` hom-bundle sections is a `C^n` hom-bundle section
(on-a-set version). -/
theorem ContMDiffOn.clm_bundle_comp
    {ϕ : ∀ x, E₂ x →L[𝕜] E₃ x} {ψ : ∀ x, E₁ x →L[𝕜] E₂ x} {s : Set B}
    (hϕ : ContMDiffOn IB (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₃)) n
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₃) (E := fun x ↦ E₂ x →L[𝕜] E₃ x) x (ϕ x)) s)
    (hψ : ContMDiffOn IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (ψ x)) s) :
    ContMDiffOn IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₃)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₃) (E := fun x ↦ E₁ x →L[𝕜] E₃ x) x ((ϕ x).comp (ψ x)))
      s :=
  fun x hx ↦ (hϕ x hx).clm_bundle_comp (hψ x hx)

/-- The fiberwise composition of two `C^n` hom-bundle sections is a `C^n` hom-bundle section. -/
theorem ContMDiff.clm_bundle_comp
    {ϕ : ∀ x, E₂ x →L[𝕜] E₃ x} {ψ : ∀ x, E₁ x →L[𝕜] E₂ x}
    (hϕ : ContMDiff IB (IB.prod 𝓘(𝕜, F₂ →L[𝕜] F₃)) n
      (fun x ↦ TotalSpace.mk' (F₂ →L[𝕜] F₃) (E := fun x ↦ E₂ x →L[𝕜] E₃ x) x (ϕ x)))
    (hψ : ContMDiff IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun x ↦ E₁ x →L[𝕜] E₂ x) x (ψ x))) :
    ContMDiff IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₃)) n
      (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₃) (E := fun x ↦ E₁ x →L[𝕜] E₃ x) x ((ϕ x).comp (ψ x))) :=
  fun x ↦ (hϕ x).clm_bundle_comp (hψ x)

end
