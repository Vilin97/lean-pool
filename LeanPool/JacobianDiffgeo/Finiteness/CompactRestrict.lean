/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Finiteness.BddHolo
import LeanPool.JacobianDiffgeo.Forms.Montel
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Montel compactness of `restrictCLM` (`finiteness-and-chi`)

Unit: finiteness-and-chi (`docs/design/finiteness-and-chi.md` §4.4, proof plan §6.3).

* `isCompactOperator_restrictCLM`: for `S' ⋐ S` inside a single chart source, the restriction
  `restrictCLM : BddHoloOn S →L[ℂ] BddHoloOn S'` is a compact operator (Montel's theorem,
  quoted from `Jacobian/Forms/Montel.lean`).

Placement note (deviation from the design doc's §3 file plan, flagged honestly): the design's
§4.4 header also lists the *cocycle-level* assembly (`isCompactOperator_resZ_UV`,
`isCompactOperator_tradeCompact`), but those need `ShrinkChain`/`NZ1`/`tradeCompact`, which are
defined in `Chain.lean` — built *after* this file per the same file plan's build order. To keep
this file gate-free and self-contained (no forward reference to a not-yet-written file), the
single-chart lemma lives here; the cocycle-level assembly is proved in `Chain.lean` immediately
after the relevant definitions, by `IsCompactOperator.comp_clm`/`.clm_comp` composed with this
lemma (per §6.3 step 5) — no mathematical content moves, only the file boundary.
-/

open scoped ContDiff Manifold BoundedContinuousFunction
open Set Filter Topology TopologicalSpace Metric

namespace RS.Finiteness

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [T1Space X] [T2Space X] [CompactSpace X]

/-- Compat: a `CLM` into a *closed* submodule is a compact operator as soon as its
composite with the ambient inclusion is (the closedness lets a compact "witness set" for the
ambient map be trimmed, via `Subtype.isCompact_iff`, to a compact witness set inside the
submodule itself). -/
theorem isCompactOperator_of_isCompactOperator_val {E N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup N] [NormedSpace ℂ N] {S : Submodule ℂ N}
    (hS : IsClosed (S : Set N)) (f : E →L[ℂ] S)
    (hf : IsCompactOperator (fun e => (f e : N))) : IsCompactOperator (f : E → S) := by
  obtain ⟨K, hK, hKmem⟩ := hf
  refine ⟨Subtype.val ⁻¹' K, ?_, hKmem⟩
  have heq : Subtype.val '' (Subtype.val ⁻¹' K : Set S) = K ∩ (S : Set N) := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨hy, y.2⟩
    · rintro ⟨hx, hxS⟩; exact ⟨⟨x, hxS⟩, hx, rfl⟩
  rw [Subtype.isCompact_iff, heq]
  exact hK.of_isClosed_subset (hK.isClosed.inter hS) inter_subset_left

omit [T1Space X] [T2Space X] in
/-- **Montel compactness of the restriction**: for `S' ⋐ S ⊆ source (chartAt ℂ x₀)`, the
restriction `BddHoloOn S → BddHoloOn S'` is a compact operator. -/
theorem isCompactOperator_restrictCLM {S' S : Opens X} {x₀ : X}
    (hsrc : (S : Set X) ⊆ (chartAt ℂ x₀).source) (hc : closure (S' : Set X) ⊆ (S : Set X)) :
    IsCompactOperator (restrictCLM (le_of_closure hc) : BddHoloOn S → BddHoloOn S') := by
  set e := chartAt ℂ x₀ with he_def
  set Ω : Set ℂ := e '' (S : Set X) with hΩ_def
  set K : Set ℂ := e '' closure (S' : Set X) with hK_def
  have hΩopen : IsOpen Ω := e.isOpen_image_of_subset_source S.2 hsrc
  have hcSsrc : closure (S' : Set X) ⊆ e.source := hc.trans hsrc
  have hKcompact : IsCompact K :=
    isClosed_closure.isCompact.image_of_continuousOn (e.continuousOn.mono hcSsrc)
  have hKΩ : K ⊆ Ω := Set.image_mono hc
  have hKtarget : K ⊆ e.target := fun w hw => by
    obtain ⟨y, hy, rfl⟩ := hw; exact e.map_source (hcSsrc hy)
  have : CompactSpace ↥K := isCompact_iff_compactSpace.mp hKcompact
  -- `Φ`: the chart-composite of the carrier witness, into `C(K, ℂ)`.
  have hΦcont : ∀ f : BddHoloOn S, Continuous (K.domRestrict (f.2.choose ∘ e.symm)) := by
    intro f
    apply ContinuousOn.domRestrict
    refine f.2.choose_spec.1.continuousOn.comp' (e.continuousOn_symm.mono hKtarget) ?_
    rintro w ⟨y, hy, rfl⟩
    rw [e.left_inv (hcSsrc hy)]
    exact hc hy
  set Φ : BddHoloOn S → C(↥K, ℂ) := fun f => ⟨K.domRestrict (f.2.choose ∘ e.symm), hΦcont f⟩
    with hΦ_def
  have hΦapp : ∀ (f : BddHoloOn S) (z : ↥K), Φ f z = f.2.choose (e.symm z) := fun _ _ => rfl
  have hmontel : Φ '' Metric.closedBall (0 : BddHoloOn S) 1 ⊆ montelFamily Ω K 1 := by
    rintro _ ⟨f, hfmem, rfl⟩
    refine ⟨f.2.choose ∘ e.symm, ?_, ?_, fun z => hΦapp f z⟩
    · exact ((RS.contMDiffOn_iff_analyticOnNhd_of_subset_source (chart_mem_atlas ℂ x₀) hsrc
        S.2).1 f.2.choose_spec.1).differentiableOn
    · rintro w ⟨y, hy, rfl⟩
      rw [Function.comp_apply, e.left_inv (hsrc hy)]
      calc ‖f.2.choose y‖ = ‖(f : ↥(S : Set X) →ᵇ ℂ) ⟨y, hy⟩‖ := by
            rw [f.2.choose_spec.2 ⟨y, hy⟩]
        _ ≤ ‖(f : BddHoloOn S)‖ := BoundedContinuousFunction.norm_coe_le_norm _ _
        _ ≤ 1 := by rw [← dist_zero_right (f : BddHoloOn S)]; exact Metric.mem_closedBall.mp hfmem
  have hC1 : IsCompact (closure (Φ '' Metric.closedBall (0 : BddHoloOn S) 1)) :=
    (isCompact_closure_montelFamily hΩopen hKcompact hKΩ 1).of_isClosed_subset
      isClosed_closure (closure_mono hmontel)
  -- `Ψ`: evaluate a `C(K, ℂ)`-function along `e` back onto `BddHoloOn S'`'s domain.
  set E : C(↥K, ℂ) ≃ₜ (↥K →ᵇ ℂ) := (ContinuousMap.isometryEquivBoundedOfCompact ↥K ℂ).toHomeomorph
    with hE_def
  have hEapp : ∀ (h : C(↥K, ℂ)) (y : ↥K), E h y = h y := fun _ _ => rfl
  have hΨmem : ∀ z : ↥(S' : Set X), e (z : X) ∈ K := fun z => ⟨z.1, subset_closure z.2, rfl⟩
  have hS'src : (S' : Set X) ⊆ e.source := subset_closure.trans hcSsrc
  set G : C(↥(S' : Set X), ↥K) :=
    ⟨fun z => ⟨e z.1, hΨmem z⟩,
      Continuous.subtype_mk ((e.continuousOn.mono hS'src).domRestrict) hΨmem⟩
    with hG_def
  set Ψ : C(↥K, ℂ) → (↥(S' : Set X) →ᵇ ℂ) := fun h => (E h).compContinuous G with hΨ_def
  have hΨcont : Continuous Ψ := (BoundedContinuousFunction.continuous_compContinuous G).comp
    E.continuous
  have hΨΦ : ∀ f : BddHoloOn S, Ψ (Φ f) = restrictCLM (le_of_closure hc) f := by
    intro f
    apply BoundedContinuousFunction.ext
    intro z
    change E (Φ f) (G z) = (restrictCLM (le_of_closure hc) f : ↥(S' : Set X) →ᵇ ℂ) z
    rw [hEapp, hΦapp]
    change f.2.choose (e.symm (e z.1)) =
      (f : ↥(S : Set X) →ᵇ ℂ) (Set.inclusion (le_of_closure hc) z)
    rw [e.left_inv (hsrc (le_of_closure hc z.2))]
    exact (f.2.choose_spec.2 ⟨z.1, le_of_closure hc z.2⟩).symm
  have hΨC1compact : IsCompact (Ψ '' closure (Φ '' Metric.closedBall (0 : BddHoloOn S) 1)) :=
    hC1.image hΨcont
  -- Work at the ambient (`↥S' →ᵇ ℂ`) level first, then transfer into the submodule.
  have hcompVal : IsCompactOperator
      (fun f : BddHoloOn S => (restrictCLM (le_of_closure hc) f : ↥(S' : Set X) →ᵇ ℂ)) := by
    refine ⟨Ψ '' closure (Φ '' Metric.closedBall (0 : BddHoloOn S) 1), hΨC1compact, ?_⟩
    refine mem_of_superset (Metric.ball_mem_nhds (0 : BddHoloOn S) one_pos) (fun f hf => ?_)
    rw [Set.mem_preimage, ← hΨΦ f]
    exact Set.mem_image_of_mem Ψ
      (subset_closure (Set.mem_image_of_mem Φ (Metric.ball_subset_closedBall hf)))
  exact isCompactOperator_of_isCompactOperator_val (isClosed_bddHoloOn S')
    (restrictCLM (le_of_closure hc)) hcompVal

end RS.Finiteness
