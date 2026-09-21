/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.EndomorphismTrace

/-!
# Evaluation of induced hom-bundle connections

The induced connection on `Hom(V₁,V₂)` satisfies the genuine product rule

`(∇φ)(X)(σ) = ∇⁲_X (φσ) - φ(∇¹_X σ)`

for arbitrary differentiable sections.  The primitive induced-connection
definition proves this first for the canonical smooth extension of a single
fibre vector.  This file removes that restriction by expanding the difference
between an arbitrary section and its canonical extension in a local frame.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  {F₁ F₂ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  {V₁ V₂ : M → Type*}
  [TopologicalSpace (TotalSpace F₁ V₁)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [∀ x, NormedAddCommGroup (V₁ x)] [∀ x, NormedSpace ℝ (V₁ x)]
  [∀ x, FiniteDimensional ℝ (V₁ x)]
  [∀ x, NormedAddCommGroup (V₂ x)] [∀ x, NormedSpace ℝ (V₂ x)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [ContMDiffVectorBundle 2 F₁ V₁ I] [ContMDiffVectorBundle 2 F₂ V₂ I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "Hom₁₂" => (fun x : M => V₁ x →L[ℝ] V₂ x)

/-- If a differentiable source section vanishes at a point, differentiating
its image under a differentiable hom section has no derivative-of-the-hom
term there. -/
theorem covariantDerivative_apply_hom_of_section_eq_zero
    (cov₁ : CovariantDerivative I F₁ V₁)
    (cov₂ : CovariantDerivative I F₂ V₂)
    {φ : ∀ x : M, Hom₁₂ x} {σ : ∀ x : M, V₁ x} {x : M}
    (hφ : MDiffAt
      (fun y => TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := Hom₁₂) y (φ y)) x)
    (hσ : MDiffAt (T% σ) x) (hσx : σ x = 0) (u : TM x) :
    cov₂ (fun y => φ y (σ y)) x u = φ x (cov₁ σ x u) := by
  classical
  let e : Trivialization F₁ (TotalSpace.proj : TotalSpace F₁ V₁ → M) :=
    trivializationAt F₁ V₁ x
  let b : Module.Basis (Fin (Module.finrank ℝ F₁)) ℝ F₁ :=
    Module.finBasis ℝ F₁
  let c : Fin (Module.finrank ℝ F₁) → M → ℝ := fun i y =>
    (e.localFrameCoeff I b i y) (σ y)
  let frame : Fin (Module.finrank ℝ F₁) → ∀ y : M, V₁ y := fun i =>
    e.localFrame b i
  let imageFrame : Fin (Module.finrank ℝ F₁) → ∀ y : M, V₂ y := fun i y =>
    φ y (frame i y)
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hframe : ∀ i, MDiffAt (T% (frame i)) x := by
    intro i
    exact (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
      (n := 1) (i := i) (hx := hx)).mdifferentiableAt one_ne_zero
  have hc : ∀ i, MDiffAt (c i) x := by
    intro i
    exact mdifferentiableAt_localFrameCoeff
      (I := I) (e := e) (b := b) (s := σ) hx hσ i
  have hcx : ∀ i, c i x = 0 := by
    intro i
    simp [c, hσx]
  have himageFrame : ∀ i, MDiffAt (T% (imageFrame i)) x := by
    intro i
    exact hφ.clm_bundle_apply (hframe i)
  have hsumFrame : MDiffAt (T% (∑ i, c i • frame i)) x := by
    have h := MDifferentiableAt.sum_section
      (s := (Finset.univ : Finset (Fin (Module.finrank ℝ F₁))))
      (fun i _ => (hc i).smul_section (hframe i))
    convert h using 1 <;> ext y <;> simp
  have hsumImageFrame : MDiffAt (T% (∑ i, c i • imageFrame i)) x := by
    have h := MDifferentiableAt.sum_section
      (s := (Finset.univ : Finset (Fin (Module.finrank ℝ F₁))))
      (fun i _ => (hc i).smul_section (himageFrame i))
    convert h using 1 <;> ext y <;> simp
  have heventσ : ∀ᶠ y in nhds x, σ y = (∑ i, c i • frame i) y := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    simpa [c, frame] using
      (e.eq_sum_localFrameCoeff_smul (I := I) (b := b) (s := σ) (x' := y) hy)
  have heventImage : ∀ᶠ y in nhds x,
      φ y (σ y) = (∑ i, c i • imageFrame i) y := by
    filter_upwards [heventσ] with y hy
    rw [hy]
    simp [imageFrame, frame]
  have hφσ : MDiffAt (T% (fun y => φ y (σ y))) x := hφ.clm_bundle_apply hσ
  have hcovσ := IsCovariantDerivativeOn.congr_of_eventuallyEq
    (hcov := cov₁.isCovariantDerivativeOnUniv) hσ hsumFrame
    (Filter.univ_mem) heventσ
  have hcovImage := IsCovariantDerivativeOn.congr_of_eventuallyEq
    (hcov := cov₂.isCovariantDerivativeOnUniv) hφσ hsumImageFrame
    (Filter.univ_mem) heventImage
  have hsumσ := covariantDerivative_sum_smul_apply
    (I := I) cov₁ c frame hc hframe u
  have hsumImage := covariantDerivative_sum_smul_apply
    (I := I) cov₂ c imageFrame hc himageFrame u
  have hcovσu := congrArg (fun L : TM x →L[ℝ] V₁ x => L u) hcovσ
  have hcovImageu := congrArg (fun L : TM x →L[ℝ] V₂ x => L u) hcovImage
  rw [hcovImageu, hsumImage, hcovσu, hsumσ]
  simp [hcx, imageFrame, frame, map_sum]

/-- Evaluation product rule for the connection induced on an arbitrary hom
bundle. -/
theorem inducedHomCovariantDerivative_apply_section_general
    (cov₁ : CovariantDerivative I F₁ V₁)
    (cov₂ : CovariantDerivative I F₂ V₂)
    {φ : ∀ x : M, Hom₁₂ x} {σ : ∀ x : M, V₁ x} {x : M}
    (hφ : MDiffAt
      (fun y => TotalSpace.mk' (F₁ →L[ℝ] F₂) (E := Hom₁₂) y (φ y)) x)
    (hσ : MDiffAt (T% σ) x) (u : TM x) :
    (inducedHomCovariantDerivative cov₁ cov₂ φ x u) (σ x) =
      cov₂ (fun y => φ y (σ y)) x u - φ x (cov₁ σ x u) := by
  classical
  let q : ∀ y : M, V₁ y :=
    smoothExtend (I := I) (F := F₁) (V := V₁) x (σ x)
  let δ : ∀ y : M, V₁ y := σ - q
  have hq : MDiffAt (T% q) x :=
    ((smoothExtend_contMDiff_two (I := I) (F := F₁) (V := V₁) x (σ x)).of_le
      (by simp) x).mdifferentiableAt one_ne_zero
  have hδ : MDiffAt (T% δ) x := mdifferentiableAt_sub_section hσ hq
  have hδx : δ x = 0 := by
    change σ x - smoothExtend (I := I) (F := F₁) (V := V₁) x (σ x) x = 0
    rw [smoothExtend_apply]
    simp
  have hφq : MDiffAt (T% (fun y => φ y (q y))) x := hφ.clm_bundle_apply hq
  have hφδ : MDiffAt (T% (fun y => φ y (δ y))) x := hφ.clm_bundle_apply hδ
  have hφσ : MDiffAt (T% (fun y => φ y (σ y))) x := hφ.clm_bundle_apply hσ
  have hqδ : MDiffAt (T% (q + δ)) x := mdifferentiableAt_add_section hq hδ
  have hφqφδ : MDiffAt
      (T% ((fun y => φ y (q y)) + fun y => φ y (δ y))) x :=
    mdifferentiableAt_add_section hφq hφδ
  have heventσ : ∀ᶠ y in nhds x, (q + δ) y = σ y := by
    filter_upwards [] with y
    simp [δ]
  have heventφ : ∀ᶠ y in nhds x,
      ((fun z => φ z (q z)) + fun z => φ z (δ z)) y = φ y (σ y) := by
    filter_upwards [] with y
    simp [δ, map_sub]
  have hcovqδ := cov₁.isCovariantDerivativeOn.add hq hδ (x := x)
  have hcovφqφδ := cov₂.isCovariantDerivativeOn.add hφq hφδ (x := x)
  have hcovσeq := IsCovariantDerivativeOn.congr_of_eventuallyEq
    (hcov := cov₁.isCovariantDerivativeOnUniv) hqδ hσ Filter.univ_mem heventσ
  have hcovφeq := IsCovariantDerivativeOn.congr_of_eventuallyEq
    (hcov := cov₂.isCovariantDerivativeOnUniv) hφqφδ hφσ Filter.univ_mem heventφ
  have hzero := covariantDerivative_apply_hom_of_section_eq_zero
    (I := I) cov₁ cov₂ hφ hδ hδx u
  have hcovqδu := congrArg (fun L : TM x →L[ℝ] V₁ x => L u) hcovqδ
  have hcovφqφδu := congrArg (fun L : TM x →L[ℝ] V₂ x => L u) hcovφqφδ
  have hcovσequ := congrArg (fun L : TM x →L[ℝ] V₁ x => L u) hcovσeq
  have hcovφequ := congrArg (fun L : TM x →L[ℝ] V₂ x => L u) hcovφeq
  rw [inducedHomCovariantDerivative_apply_of_mdifferentiableAt cov₁ cov₂ hφ,
    inducedHomAtOfMDiff_apply]
  change cov₂ (fun y => φ y (q y)) x u - φ x (cov₁ q x u) = _
  simp only [add_apply] at hcovqδu hcovφqφδu
  rw [← hcovσequ, hcovqδu, ← hcovφequ, hcovφqφδu, map_add, hzero]
  abel

end CovariantDerivative
