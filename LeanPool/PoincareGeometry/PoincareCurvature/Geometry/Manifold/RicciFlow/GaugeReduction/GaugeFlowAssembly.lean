/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

/-
Gauge-flow assembly toward the compact-manifold C³ gauge-flow existence
(roadmap point 4, Item 2).

This module re-exposes the project's raw `C³` gauge-flow adapter
`Diffeomorph3GaugeFlowOn.nonempty_of_inverse_hasMFDerivWithinAt` in a clean form,
isolating the exact data needed to inhabit `Diffeomorph3GaugeFlowOn`:

* mutually inverse, spatially-`C³` time-slice maps `F`, `G : ℝ → M → M`
  (`G t` is the spatial inverse of the diffeomorphism `F t`, NOT a backward
  time-flow — confirmed by the adapter's per-slice `LeftInverse`/`RightInverse`
  hypotheses);
* anchoring `F t₀ = id`;
* the forward family `τ ↦ F τ x` solving the gauge ODE
  (`HasMFDerivWithinAt … ((1).smulRight (X t (F t x)))`).

The `hderiv` field is exactly the manifold time-derivative that the autonomization
bridge in `ManifoldFlowExistence.lean`
(`isTimeDependentIntegralCurve_of_autonomous`) produces from an integral curve of
`(1, X)` on `ℝ × M`. The mutual-inverse data follows from the flow group law
(`flow_inverse_package`). The single genuinely-remaining analytic obligation is the
**spatial `C³` regularity of the flow map** `x ↦ F t x` (smooth dependence of the
ODE flow on the initial condition, `hF`/`hG`) — the project's `ModelGaugeFlowODE.lean`
already proves spatial `C¹` (Fréchet) differentiability, so this is a `C¹ → C³`
bootstrap, not a from-scratch development.
-/
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowExistence
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.ManifoldFlowExistence

/-! # Gauge Flow Assembly -/

@[expose] public section
open scoped Manifold Topology ContDiff

namespace PoincareCurvature.GaugeFlowAssembly

open RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

/-- **Gauge-flow from flow data.** Given mutually inverse spatially-`C³` time-slice
maps `F`, `G`, anchoring at `t₀`, and the pointwise within-time-set manifold ODE
derivative equation for the forward family, the raw `C³` DeTurck gauge-flow
`Diffeomorph3GaugeFlowOn` is inhabited.

This is the reduction target for Item 2: with the autonomization bridge supplying
`hderiv` and the flow group law supplying the mutual inverses, the only remaining
input is the spatial-`C³` regularity `hF`/`hG` of the flow map. -/
theorem gaugeFlow_of_inverse_flow
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {s : Set ℝ} {t₀ : ℝ}
    (F G : ℝ → M → M)
    (hleft : ∀ t : ℝ, Function.LeftInverse (G t) (F t))
    (hright : ∀ t : ℝ, Function.RightInverse (G t) (F t))
    (hF : ∀ t : ℝ, ContMDiff I I 3 (F t))
    (hG : ∀ t : ℝ, ContMDiff I I 3 (G t))
    (hanchored : ∀ x : M, F t₀ x = x)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasMFDerivAt[s] (fun τ : ℝ ↦ F τ x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (F t x)))) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X s t₀) :=
  Diffeomorph3GaugeFlowOn.nonempty_of_inverse_hasMFDerivWithinAt
    (I := I) (M := M) (X := X) (s := s) (t₀ := t₀)
    F G hleft hright hF hG hanchored hderiv

/-- **Global-`ℝ` extension of a windowed inverse flow to the `C³` gauge-flow datum.**

The compact-manifold time-dependent flow
(`ManifoldFlow.exists_timeDependent_flow_compact_inverse`) produces mutually inverse, anchored
slice maps `Φ`, `G` solving the gauge ODE only on a *window* `Ioo (-ε) ε`, whereas the adapter
`gaugeFlow_of_inverse_flow` wants the mutual-inverse / spatial-`C³` data for *every* `t : ℝ`.
Extending both families by the identity outside the window closes that `∀ t`-gap: the extended
slices stay mutually inverse (`id` is its own inverse), spatially `C³` (`id` is smooth), anchored,
and — since the extension agrees with `Φ` on the window — solve the *same* gauge ODE on
`Ioo (-ε) ε` (`HasMFDerivWithinAt.congr_mono`).  This is the pure windowed → global assembly step
in the compact-manifold gauge-flow lift; the only remaining Item-2 analytic input is the
spatial-`C³` regularity `hΦC3`/`hGC3` of the *windowed* slices (the `C¹ → C³` bootstrap). -/
theorem exists_diffeomorph3GaugeFlowOn_of_windowed_inverse_flow
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    {ε : ℝ} (hε : 0 < ε)
    (Φ G : ℝ → M → M)
    (hanchor : ∀ x : M, Φ 0 x = x)
    (hΦC3 : ∀ t ∈ Set.Ioo (-ε) ε, ContMDiff I I 3 (Φ t))
    (hGC3 : ∀ t ∈ Set.Ioo (-ε) ε, ContMDiff I I 3 (G t))
    (hleft : ∀ t ∈ Set.Ioo (-ε) ε, Function.LeftInverse (G t) (Φ t))
    (hright : ∀ t ∈ Set.Ioo (-ε) ε, Function.RightInverse (G t) (Φ t))
    (hderiv : ∀ x : M, ∀ t ∈ Set.Ioo (-ε) ε,
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ : ℝ ↦ Φ τ x) (Set.Ioo (-ε) ε) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) :
    Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Set.Ioo (-ε) ε) 0) := by
  classical
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
  refine gaugeFlow_of_inverse_flow (X := X) (s := Set.Ioo (-ε) ε) (t₀ := 0)
    (fun t => if t ∈ Set.Ioo (-ε) ε then Φ t else id)
    (fun t => if t ∈ Set.Ioo (-ε) ε then G t else id)
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro t
    by_cases ht : t ∈ Set.Ioo (-ε) ε
    · simp only [if_pos ht]; exact hleft t ht
    · simp only [if_neg ht]; exact fun _ => rfl
  · intro t
    by_cases ht : t ∈ Set.Ioo (-ε) ε
    · simp only [if_pos ht]; exact hright t ht
    · simp only [if_neg ht]; exact fun _ => rfl
  · intro t
    by_cases ht : t ∈ Set.Ioo (-ε) ε
    · simp only [if_pos ht]; exact hΦC3 t ht
    · simp only [if_neg ht]; exact contMDiff_id
  · intro t
    by_cases ht : t ∈ Set.Ioo (-ε) ε
    · simp only [if_pos ht]; exact hGC3 t ht
    · simp only [if_neg ht]; exact contMDiff_id
  · intro x
    simp only [if_pos h0mem]; exact hanchor x
  · intro t ht x
    rw [if_pos ht]
    refine (hderiv x t ht).congr_mono ?_ ?_ (subset_refl _)
    · intro τ hτ; simp only [if_pos hτ]
    · simp only [if_pos ht]

/-- **Compact-manifold gauge-flow existence, reduced to spatial-`C³` regularity of the flow slices.**

Wires the compact-manifold time-dependent flow
(`ManifoldFlow.exists_timeDependent_flow_compact_inverse`, which only needs the `C¹` field datum
`hX`) into the raw `C³` gauge-flow adapter through the identity-extension assembly
`exists_diffeomorph3GaugeFlowOn_of_windowed_inverse_flow`.  The flow supplies, on some window
`Ioo (-ε) ε`, the anchored mutually-inverse slice maps `Φ`, `G` solving the gauge ODE; the *only*
remaining analytic input is their spatial-`C³` regularity, isolated here as the hypothesis
`hslicesC3` (the `C¹ → C³` bootstrap, characterising the — necessarily unique — compact flow of `X`).
Given that, the raw `C³` DeTurck gauge-flow `Diffeomorph3GaugeFlowOn X (Ioo (-ε) ε) 0` is inhabited
for some `ε > 0`.  This is the first wiring of the compact-flow existence machinery into the
gauge-flow adapter — the honest current state of Item 2: *unconditional up to the flow-slice `C³`
regularity*. -/
theorem exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3
    [BoundarylessManifold I M] [CompactSpace M] [Nonempty M]
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ :
        TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    (hslicesC3 : ∀ (ε : ℝ), 0 < ε → ∀ (Φ G : ℝ → M → M),
      (∀ x, Φ 0 x = x) →
      (∀ x, ∀ t ∈ Set.Ioo (-ε) ε,
        HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ : ℝ ↦ Φ τ x) (Set.Ioo (-ε) ε) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) →
      (∀ t ∈ Set.Ioo (-ε) ε, Function.LeftInverse (G t) (Φ t)) →
      (∀ t ∈ Set.Ioo (-ε) ε, Function.RightInverse (G t) (Φ t)) →
      (∀ t ∈ Set.Ioo (-ε) ε, ContMDiff I I 3 (Φ t)) ∧
        (∀ t ∈ Set.Ioo (-ε) ε, ContMDiff I I 3 (G t))) :
    ∃ ε > 0, Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Set.Ioo (-ε) ε) 0) := by
  obtain ⟨ε, hε, Φ, G, hΦ0, _hG0, hderiv, hleft, hright⟩ :=
    ManifoldFlow.exists_timeDependent_flow_compact_inverse (I := I) (M := M) (X := X) hX
  obtain ⟨hΦC3, hGC3⟩ := hslicesC3 ε hε Φ G hΦ0 hderiv hleft hright
  exact ⟨ε, hε, exists_diffeomorph3GaugeFlowOn_of_windowed_inverse_flow
    hε Φ G hΦ0 hΦC3 hGC3 hleft hright hderiv⟩

/-- **Compact-manifold gauge-flow existence, reduced to spatial-`C³` regularity of the flow slices on
a *sub-window*.**

The sub-window relaxation of `exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3`.  The
compact-manifold time-dependent flow (`ManifoldFlow.exists_timeDependent_flow_compact_inverse`)
produces the anchored mutually-inverse slice maps `Φ`, `G` solving the gauge ODE on some window
`Ioo (-ε) ε`; but every confinement-based slice-`C³` route anchors its model comparison flow at `0`
and confines the orbit over the whole span `[0, t]`, so it only delivers `ContMDiff I I 3 (Φ t)` /
`ContMDiff I I 3 (G t)` on a possibly *smaller* symmetric sub-window `Ioo (-δ) δ` (the uniform
chart-exit time over the finite cover) rather than on the full inverse-supplier lifespan
`Ioo (-ε) ε`.  This theorem accepts exactly that: `hslicesC3` is asked only to produce **some**
`0 < δ ≤ ε` on whose window the slices are spatially `C³`.  Since the final gauge-flow datum is
returned as `∃ ε > 0`, a symmetric sub-window suffices — the mutual-inverse / anchoring / ODE data
restrict from `Ioo (-ε) ε` to `Ioo (-δ) δ` (the ODE via `HasMFDerivWithinAt.mono`), and
`exists_diffeomorph3GaugeFlowOn_of_windowed_inverse_flow` is applied at the sub-window `δ`.  This
removes the window obstruction that blocked the full-window `_of_compact_of_flowSlicesC3` from
consuming the confinement routes' sub-window output. -/
theorem exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSubwindowSlicesC3
    [BoundarylessManifold I M] [CompactSpace M] [Nonempty M]
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ :
        TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    (hslicesC3 : ∀ (ε : ℝ), 0 < ε → ∀ (Φ G : ℝ → M → M),
      (∀ x, Φ 0 x = x) →
      (∀ x, ∀ t ∈ Set.Ioo (-ε) ε,
        HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ : ℝ ↦ Φ τ x) (Set.Ioo (-ε) ε) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) →
      (∀ t ∈ Set.Ioo (-ε) ε, Function.LeftInverse (G t) (Φ t)) →
      (∀ t ∈ Set.Ioo (-ε) ε, Function.RightInverse (G t) (Φ t)) →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧
        (∀ t ∈ Set.Ioo (-δ) δ, ContMDiff I I 3 (Φ t)) ∧
          (∀ t ∈ Set.Ioo (-δ) δ, ContMDiff I I 3 (G t))) :
    ∃ ε > 0, Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Set.Ioo (-ε) ε) 0) := by
  obtain ⟨ε, hε, Φ, G, hΦ0, _hG0, hderiv, hleft, hright⟩ :=
    ManifoldFlow.exists_timeDependent_flow_compact_inverse (I := I) (M := M) (X := X) hX
  obtain ⟨δ, hδ, hδε, hΦC3, hGC3⟩ := hslicesC3 ε hε Φ G hΦ0 hderiv hleft hright
  have hsub : Set.Ioo (-δ) δ ⊆ Set.Ioo (-ε) ε := fun t ht =>
    ⟨lt_of_le_of_lt (neg_le_neg hδε) ht.1, lt_of_lt_of_le ht.2 hδε⟩
  exact ⟨δ, hδ, exists_diffeomorph3GaugeFlowOn_of_windowed_inverse_flow
    hδ Φ G hΦ0 hΦC3 hGC3 (fun t ht => hleft t (hsub ht)) (fun t ht => hright t (hsub ht))
    (fun x t ht => (hderiv x t (hsub ht)).mono hsub)⟩

/-- **Compact-manifold gauge-flow existence from *independent* forward / backward slice-`C³`
sub-windows.**

A refinement of `exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSubwindowSlicesC3` in which the
forward slice `Φ t` and the backward slice `G t` are allowed to be spatially `C³` on *different*
sub-windows `Ioo (-δ₁) δ₁` and `Ioo (-δ₂) δ₂`.  This matches the honest structure of the two
slice-`C³` routes: the forward regularity comes from the finite-cover field-jet capstone
(`exists_flow_Ioo_forall_contMDiff_of_field_jets_finite_cover_windowLip_of_flow`) and the backward
regularity from the cutoff-orbit-control route
(`contMDiff_symm_flowSlice_of_forall_cutoff_orbit_control_of_graph_subset`), each producing its own
uniform chart-exit sub-window with no a-priori common size.  Taking the common sub-window
`δ := min δ₁ δ₂` reduces to the paired sub-window capstone: both `C³` families restrict to
`Ioo (-δ) δ` (`Ioo`-monotonicity), and the gauge-flow datum is returned on that intersection. -/
theorem exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSubwindowSlicesC3_indep
    [BoundarylessManifold I M] [CompactSpace M] [Nonempty M]
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ :
        TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    (hslicesC3 : ∀ (ε : ℝ), 0 < ε → ∀ (Φ G : ℝ → M → M),
      (∀ x, Φ 0 x = x) →
      (∀ x, ∀ t ∈ Set.Ioo (-ε) ε,
        HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ : ℝ ↦ Φ τ x) (Set.Ioo (-ε) ε) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) →
      (∀ t ∈ Set.Ioo (-ε) ε, Function.LeftInverse (G t) (Φ t)) →
      (∀ t ∈ Set.Ioo (-ε) ε, Function.RightInverse (G t) (Φ t)) →
      (∃ δ₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ ε ∧ ∀ t ∈ Set.Ioo (-δ₁) δ₁, ContMDiff I I 3 (Φ t)) ∧
        (∃ δ₂ : ℝ, 0 < δ₂ ∧ δ₂ ≤ ε ∧ ∀ t ∈ Set.Ioo (-δ₂) δ₂, ContMDiff I I 3 (G t))) :
    ∃ ε > 0, Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Set.Ioo (-ε) ε) 0) := by
  refine exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSubwindowSlicesC3 hX ?_
  intro ε hε Φ G hΦ0 hderiv hleft hright
  obtain ⟨⟨δ₁, hδ₁, hδ₁ε, hΦC3⟩, ⟨δ₂, hδ₂, hδ₂ε, hGC3⟩⟩ :=
    hslicesC3 ε hε Φ G hΦ0 hderiv hleft hright
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, (min_le_left δ₁ δ₂).trans hδ₁ε, ?_, ?_⟩
  · intro t ht
    exact hΦC3 t ⟨lt_of_le_of_lt (neg_le_neg (min_le_left δ₁ δ₂)) ht.1,
      lt_of_lt_of_le ht.2 (min_le_left δ₁ δ₂)⟩
  · intro t ht
    exact hGC3 t ⟨lt_of_le_of_lt (neg_le_neg (min_le_right δ₁ δ₂)) ht.1,
      lt_of_lt_of_le ht.2 (min_le_right δ₁ δ₂)⟩

/-- **Compact-manifold gauge-flow existence from forward / backward slice-`C³` on *asymmetric*
sub-windows `Ioo c d ∋ 0`.**

The directly-consumable form of `exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSubwindowSlicesC3_indep`:
the forward and backward slice-`C³` regularity are supplied on possibly *asymmetric* open windows
`Ioo c₁ d₁ ∋ 0` and `Ioo c₂ d₂ ∋ 0` — precisely the conclusion shape of the finite-cover forward
producer `exists_flow_Ioo_forall_contMDiff_of_field_jets_finite_cover_windowLip_of_flow`
(`∃ c d, 0 ∈ Ioo c d ∧ ∀ t ∈ Ioo c d, ContMDiff I I 3 (Φ t)`) and its backward counterpart, which
never return symmetric windows.  Each asymmetric window is symmetrised internally to
`Ioo (-δ) δ` with `δ := min (min (-c) d) ε > 0` (so `Ioo (-δ) δ ⊆ Ioo c d` and `δ ≤ ε`), then handed to
the independent-sub-window capstone.  This lets a caller feed the raw producer outputs with no manual
window bookkeeping. -/
theorem exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowAsymSubwindowSlicesC3
    [BoundarylessManifold I M] [CompactSpace M] [Nonempty M]
    {X : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun p : ℝ × M => (⟨p, ((1 : ℝ), X p.1 p.2)⟩ :
        TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    (hslicesC3 : ∀ (ε : ℝ), 0 < ε → ∀ (Φ G : ℝ → M → M),
      (∀ x, Φ 0 x = x) →
      (∀ x, ∀ t ∈ Set.Ioo (-ε) ε,
        HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ : ℝ ↦ Φ τ x) (Set.Ioo (-ε) ε) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x)))) →
      (∀ t ∈ Set.Ioo (-ε) ε, Function.LeftInverse (G t) (Φ t)) →
      (∀ t ∈ Set.Ioo (-ε) ε, Function.RightInverse (G t) (Φ t)) →
      (∃ c₁ d₁ : ℝ, (0 : ℝ) ∈ Set.Ioo c₁ d₁ ∧ ∀ t ∈ Set.Ioo c₁ d₁, ContMDiff I I 3 (Φ t)) ∧
        (∃ c₂ d₂ : ℝ, (0 : ℝ) ∈ Set.Ioo c₂ d₂ ∧ ∀ t ∈ Set.Ioo c₂ d₂, ContMDiff I I 3 (G t))) :
    ∃ ε > 0, Nonempty (Diffeomorph3GaugeFlowOn (I := I) (M := M) X (Set.Ioo (-ε) ε) 0) := by
  refine exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSubwindowSlicesC3_indep hX ?_
  intro ε hε Φ G hΦ0 hderiv hleft hright
  obtain ⟨⟨c₁, d₁, hcd₁, hΦC3⟩, ⟨c₂, d₂, hcd₂, hGC3⟩⟩ :=
    hslicesC3 ε hε Φ G hΦ0 hderiv hleft hright
  obtain ⟨hc₁, hd₁⟩ := hcd₁
  obtain ⟨hc₂, hd₂⟩ := hcd₂
  refine ⟨⟨min (min (-c₁) d₁) ε, lt_min (lt_min (neg_pos.mpr hc₁) hd₁) hε, min_le_right _ _, ?_⟩,
    ⟨min (min (-c₂) d₂) ε, lt_min (lt_min (neg_pos.mpr hc₂) hd₂) hε, min_le_right _ _, ?_⟩⟩
  · intro t ht
    have h1 : min (min (-c₁) d₁) ε ≤ -c₁ := (min_le_left _ _).trans (min_le_left _ _)
    have h2 : min (min (-c₁) d₁) ε ≤ d₁ := (min_le_left _ _).trans (min_le_right _ _)
    exact hΦC3 t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · intro t ht
    have h1 : min (min (-c₂) d₂) ε ≤ -c₂ := (min_le_left _ _).trans (min_le_left _ _)
    have h2 : min (min (-c₂) d₂) ε ≤ d₂ := (min_le_left _ _).trans (min_le_right _ _)
    exact hGC3 t ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- **Chart-conjugation `C³` transfer for a flow slice.**  If, on an open set `U` contained in the
source chart at `x₀`, the map `F` is represented in the extended charts at `x₀` (source) and `F x₀`
(target) by a globally `C³` model map `Ψ : E → E` — i.e.
`extChartAt I (F x₀) (F x) = Ψ (extChartAt I x₀ x)` for every `x ∈ U` — and `F` maps `U` into the
source chart at `F x₀`, then `F` is `ContMDiffOn I I 3` on `U`.

This is the manifold-level `C³` regularity transfer for a flow slice: the model-manifold
smooth-dependence tower (`SmoothDependenceManifold.exists_flow_diffeomorph_three` etc.) produces a
globally `C³` chart-local flow `Ψ`, and this lemma lifts that `C³` regularity to `ContMDiffOn I I 3`
of the genuine manifold flow slice on a chart-confined patch — exactly the
`forward_contMDiffOn`/`backward_contMDiffOn` field of `LocalGluingData 3` the compact gauge-flow
gluing route (`Diffeomorph3FlowExistence.exists_Ioo_gaugeFlow_…_localGluingData_…`) consumes.  The
proof factors `F` as `(extChartAt I (F x₀)).symm ∘ Ψ ∘ (extChartAt I x₀)` on `U` (using the chart
left-inverse identity) and composes the two `ContMDiffOn` chart maps with the globally-`C³` `Ψ`. -/
theorem contMDiffOn_of_extChartAt_conjugation
    {x₀ : M} {F : M → M} {U : Set M} {Ψ : E → E}
    (hU : U ⊆ (chartAt H x₀).source)
    (hΨ : ContDiff ℝ 3 Ψ)
    (hFU : Set.MapsTo F U (chartAt H (F x₀)).source)
    (hconj : ∀ x ∈ U, extChartAt I (F x₀) (F x) = Ψ (extChartAt I x₀ x)) :
    ContMDiffOn I I 3 F U := by
  have hchart : ContMDiffOn I 𝓘(ℝ, E) 3 (extChartAt I x₀) U :=
    (contMDiffOn_extChartAt (I := I) (n := 3) (x := x₀)).mono hU
  have hΨm : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3 Ψ := contMDiff_iff_contDiff.mpr hΨ
  have hmid : ContMDiffOn I 𝓘(ℝ, E) 3 (fun x => Ψ (extChartAt I x₀ x)) U :=
    hΨm.comp_contMDiffOn hchart
  have hmaps : Set.MapsTo (fun x => Ψ (extChartAt I x₀ x)) U (extChartAt I (F x₀)).target := by
    intro x hx
    show Ψ (extChartAt I x₀ x) ∈ (extChartAt I (F x₀)).target
    rw [← hconj x hx]
    exact PartialEquiv.map_source (extChartAt I (F x₀))
      (by rw [extChartAt_source]; exact hFU hx)
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I 3 (extChartAt I (F x₀)).symm
      (extChartAt I (F x₀)).target := contMDiffOn_extChartAt_symm (F x₀)
  have hcomp : ContMDiffOn I I 3
      (fun x => (extChartAt I (F x₀)).symm (Ψ (extChartAt I x₀ x))) U :=
    hsymm.comp hmid hmaps
  refine hcomp.congr (fun x hx => ?_)
  show F x = (extChartAt I (F x₀)).symm (Ψ (extChartAt I x₀ x))
  rw [← hconj x hx]
  exact (PartialEquiv.left_inv (extChartAt I (F x₀))
    (by rw [extChartAt_source]; exact hFU hx)).symm

/-- **`LocalGluingData 3` from chart-conjugation data.**  Packages the two chart-conjugation `C³`
transfers (`contMDiffOn_of_extChartAt_conjugation`, applied to the forward slice `F` and its local
inverse `G`) together with the mutual-inverse / mapping data into the exact
`RicciFlow.LocalGluingData 3 F G U V` structure the compact gauge-flow gluing theorems
(`Diffeomorph3FlowExistence.exists_…_gaugeFlow_…_localGluingData_…`) consume as their per-chart
`hlocal` hypothesis.

The two genuinely-analytic fields (`forward_contMDiffOn`/`backward_contMDiffOn`) are discharged by the
chart-conjugation transfer from globally-`C³` model representatives `ΨF`, `ΨG` (supplied by the
model-manifold smooth-dependence tower in each chart); the remaining fields are the topological
open-ness, the mapping, and the local mutual-inverse identities, which the flow group law provides. -/
theorem localGluingData_ofChartConjugation
    {F G : M → M} {U V : Set M} {xF xG : M} {ΨF ΨG : E → E}
    (hUopen : IsOpen U) (hVopen : IsOpen V)
    (hFmaps : Set.MapsTo F U V) (hGmaps : Set.MapsTo G V U)
    (hleft : Set.LeftInvOn G F U) (hright : Set.RightInvOn G F V)
    (hUF : U ⊆ (chartAt H xF).source) (hΨF : ContDiff ℝ 3 ΨF)
    (hFchart : Set.MapsTo F U (chartAt H (F xF)).source)
    (hconjF : ∀ x ∈ U, extChartAt I (F xF) (F x) = ΨF (extChartAt I xF x))
    (hVG : V ⊆ (chartAt H xG).source) (hΨG : ContDiff ℝ 3 ΨG)
    (hGchart : Set.MapsTo G V (chartAt H (G xG)).source)
    (hconjG : ∀ x ∈ V, extChartAt I (G xG) (G x) = ΨG (extChartAt I xG x)) :
    LocalGluingData (I := I) (M := M) 3 F G U V where
  source_open := hUopen
  target_open := hVopen
  forward_mapsTo := by simpa only [Set.univ_inter] using hFmaps
  backward_mapsTo := by simpa only [Set.univ_inter] using hGmaps
  forward_contMDiffOn := contMDiffOn_of_extChartAt_conjugation hUF hΨF hFchart hconjF
  backward_contMDiffOn := contMDiffOn_of_extChartAt_conjugation hVG hΨG hGchart hconjG
  left_invOn := by simpa only [Set.univ_inter] using hleft
  right_invOn := by simpa only [Set.univ_inter] using hright

/-- **Global slice `C³` regularity from per-point chart-conjugation.**  If every point `x : M` has a
neighbourhood `U` on which the map `F` is represented, in the extended charts at some centre `x₀`
(source) and `F x₀` (target), by a globally-`C³` model map `Ψ : E → E`, then `F` is globally
`ContMDiff I I 3`.

This is the `ContMDiff I I 3 (Φ t)` content of the compact gauge-flow reduction's `hslicesC3`
hypothesis (`GaugeFlowAssembly.exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3`): each
flow slice `Φ t : M → M` is, near every point, the chart-representation of a model `C³` flow supplied
by the smooth-dependence tower, and this lemma glues those local chart-conjugation witnesses into
global spatial `C³` regularity of the slice.  `ContMDiff` unfolds to `∀ x, ContMDiffAt`, each of which
is `contMDiffOn_of_extChartAt_conjugation` restricted to the neighbourhood via
`ContMDiffOn.contMDiffAt`. -/
theorem contMDiff_of_forall_extChartAt_conjugation
    {F : M → M}
    (h : ∀ x : M, ∃ (x₀ : M) (U : Set M) (Ψ : E → E),
      U ∈ 𝓝 x ∧ U ⊆ (chartAt H x₀).source ∧ ContDiff ℝ 3 Ψ ∧
      Set.MapsTo F U (chartAt H (F x₀)).source ∧
      (∀ y ∈ U, extChartAt I (F x₀) (F y) = Ψ (extChartAt I x₀ y))) :
    ContMDiff I I 3 F := by
  intro x
  obtain ⟨x₀, U, Ψ, hUmem, hU, hΨ, hFU, hconj⟩ := h x
  exact (contMDiffOn_of_extChartAt_conjugation hU hΨ hFU hconj).contMDiffAt hUmem

/-- **Raw-flow chart-representation derivative.**  The chart-conjugation `C³` transfer
(`contMDiffOn_of_extChartAt_conjugation`) is fed by identifying a flow slice with a model `C³` map in
charts; that identification, in turn, rests on the flow curve's *chart representation* solving a model
ODE.  This lemma supplies exactly that at the RAW (pre-`C³`) level: for an abstract curve `γ : ℝ → M`
that satisfies the manifold flow ODE `HasMFDerivWithinAt … γ s t ((1).smulRight w)` at time `t` — the
hypothesis form produced by the compact-manifold flow
(`ManifoldFlow.exists_timeDependent_flow_compact_inverse`) *before* any spatial regularity is known —
the chart representation `τ ↦ extChartAt I p (γ τ)`, in any preferred chart whose source contains
`γ t`, has the within-set derivative `tangentCoordChange I (γ t) p (γ t) w`.

This is the abstract-curve analogue of
`RicciFlow.Diffeomorph3GaugeFlowOn.hasDerivWithinAt_extChartAt_eval_of_mem_source`, but with the
gauge-flow structure (which presupposes `C³`) replaced by the bare `HasMFDerivWithinAt` datum, so it
applies to the *raw* compact flow whose `C³` regularity is exactly what the `hslicesC3` hypothesis of
`exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3` must establish.  The proof is the
model ODE chain rule: compose the chart map's `HasMFDerivWithinAt` (`hasMFDerivWithinAt_extChartAt`)
with the curve's, then rewrite the composite `mfderiv` through
`mfderiv_chartAt_eq_tangentCoordChange`. -/
theorem hasDerivWithinAt_extChartAt_comp_of_hasMFDerivWithinAt
    {γ : ℝ → M} {s : Set ℝ} {t : ℝ} {p : M} {w : TangentSpace I (γ t)}
    (hγ : HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ s t ((1 : ℝ →L[ℝ] ℝ).smulRight w))
    (hsrc_ext : γ t ∈ (extChartAt I p).source) :
    HasDerivWithinAt (fun τ : ℝ ↦ extChartAt I p (γ τ))
      (tangentCoordChange I (γ t) p (γ t) w) s t := by
  have hsrc : γ t ∈ (chartAt H p).source := by
    simpa only [extChartAt_source] using hsrc_ext
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← hasMFDerivWithinAt_iff_hasFDerivWithinAt]
  apply (HasMFDerivWithinAt.comp t (hasMFDerivWithinAt_extChartAt (I := I) hsrc) hγ
    (Set.subset_preimage_image _ _)).congr_mfderiv
  rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  exact ContinuousLinearMap.comp_toSpanSingleton _ _

/-- **Raw-flow chart-representation derivative in the centered chart.**  Specialization of
`hasDerivWithinAt_extChartAt_comp_of_hasMFDerivWithinAt` to the preferred chart centered at the
time-`t` value `γ t`, where the tangent-coordinate change is the identity (`tangentCoordChange_self`),
so the chart representation's within-set derivative is the flow velocity `w` itself.  This is the
abstract-curve (raw-flow) analogue of
`RicciFlow.Diffeomorph3GaugeFlowOn.hasDerivWithinAt_extChartAt_eval_self`. -/
theorem hasDerivWithinAt_extChartAt_comp_self_of_hasMFDerivWithinAt
    {γ : ℝ → M} {s : Set ℝ} {t : ℝ} {w : TangentSpace I (γ t)}
    (hγ : HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ s t ((1 : ℝ →L[ℝ] ℝ).smulRight w)) :
    HasDerivWithinAt (fun τ : ℝ ↦ extChartAt I (γ t) (γ τ)) w s t := by
  have h := hasDerivWithinAt_extChartAt_comp_of_hasMFDerivWithinAt hγ
    (mem_extChartAt_source (γ t))
  rwa [tangentCoordChange_self (I := I) (x := γ t) (z := γ t) (v := w)
    (mem_extChartAt_source (γ t))] at h

/-- **Raw-flow chart-representation derivative, upgraded to `HasDerivAt`.**  When the time set `s`
is a neighbourhood of `t` — the situation for the *open* flow window `Set.Ioo (-ε) ε` at an interior
time, which is exactly the shape of the ODE hypothesis in
`exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3` — the within-set derivative of
`hasDerivWithinAt_extChartAt_comp_of_hasMFDerivWithinAt` upgrades to a full `HasDerivAt`.  This is the
form consumed by Mathlib's model integral-curve / ODE-uniqueness API (`IsIntegralCurve`,
`ODE_solution_unique`), the next step in the raw-flow chart-conjugation route. -/
theorem hasDerivAt_extChartAt_comp_of_hasMFDerivWithinAt
    {γ : ℝ → M} {s : Set ℝ} {t : ℝ} {p : M} {w : TangentSpace I (γ t)}
    (hγ : HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ s t ((1 : ℝ →L[ℝ] ℝ).smulRight w))
    (hs : s ∈ nhds t)
    (hsrc_ext : γ t ∈ (extChartAt I p).source) :
    HasDerivAt (fun τ : ℝ ↦ extChartAt I p (γ τ))
      (tangentCoordChange I (γ t) p (γ t) w) t :=
  (hasDerivWithinAt_extChartAt_comp_of_hasMFDerivWithinAt hγ hsrc_ext).hasDerivAt hs

/-- **Raw-flow chart-representation derivative in the centered chart, upgraded to `HasDerivAt`.**
The centered (`p := γ t`) `HasDerivAt` form of `hasDerivAt_extChartAt_comp_of_hasMFDerivWithinAt`,
whose derivative is the flow velocity `w` itself.  Together with the fixed-chart version this is the
model-ODE datum the raw compact flow supplies to the integral-curve uniqueness comparison against the
model-`C³` flow tower. -/
theorem hasDerivAt_extChartAt_comp_self_of_hasMFDerivWithinAt
    {γ : ℝ → M} {s : Set ℝ} {t : ℝ} {w : TangentSpace I (γ t)}
    (hγ : HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ s t ((1 : ℝ →L[ℝ] ℝ).smulRight w))
    (hs : s ∈ nhds t) :
    HasDerivAt (fun τ : ℝ ↦ extChartAt I (γ t) (γ τ)) w t :=
  (hasDerivWithinAt_extChartAt_comp_self_of_hasMFDerivWithinAt hγ).hasDerivAt hs

variable (I) in
/-- **Chart pushforward vector field.**  The time-dependent vector field `X : ℝ → M → E` on the base
manifold, transported into the model space `E` of the preferred chart `extChartAt I p`: a model point
`q : E` is pulled back to `M` via the chart inverse `(extChartAt I p).symm`, the base field `X τ` is
evaluated there, and the resulting tangent vector is pushed forward to the `p`-chart coordinates by the
tangent coordinate change `tangentCoordChange`.

This is the model-space vector field `f : ℝ → E → E` whose integral curves are the chart representations
of the raw manifold flow curves; it is the object fed to the model ODE uniqueness API
(`RicciFlow.ModelGaugeFlowODE.eqOn_Icc_of_lipschitzOnWith` and friends) to identify the raw compact
flow's chart representation with the model-`C³` flow tower.  Because `X` lands in the model space `E`
(rather than a point-dependent `TangentSpace I x`), the definition and its chart-image reduction below
carry no dependent-type obstruction. -/
noncomputable def chartPushforwardField (X : ℝ → M → E) (p : M) (τ : ℝ) (q : E) : E :=
  tangentCoordChange I ((extChartAt I p).symm q) p ((extChartAt I p).symm q)
    (X τ ((extChartAt I p).symm q))

/-- Evaluated at the `p`-chart image of a base point `y ∈ (extChartAt I p).source`, the chart pushforward
field reduces — via the chart's left inverse `PartialEquiv.left_inv` — to the tangent coordinate change
of `X τ y` from the chart at `y` to the chart at `p`, evaluated at `y`. -/
theorem chartPushforwardField_extChartAt (X : ℝ → M → E) {p y : M} (τ : ℝ)
    (hy : y ∈ (extChartAt I p).source) :
    chartPushforwardField I X p τ (extChartAt I p y) = tangentCoordChange I y p y (X τ y) := by
  unfold chartPushforwardField
  rw [(extChartAt I p).left_inv hy]

/-- **The raw flow's chart representation is an integral curve of the chart pushforward field.**  Combining
the raw-flow chart-representation derivative
(`hasDerivWithinAt_extChartAt_comp_of_hasMFDerivWithinAt`) with the field's chart-image value
(`chartPushforwardField_extChartAt`): for an abstract curve `γ : ℝ → M` satisfying the bare manifold flow
ODE `HasMFDerivWithinAt … γ s t ((1).smulRight (X t (γ t)))` at time `t` with `γ t` in the source of the
preferred chart `extChartAt I p`, the chart representation `τ ↦ extChartAt I p (γ τ)` has within-set
derivative `chartPushforwardField I X p t` evaluated at the *current* chart point `extChartAt I p (γ t)`.

This is exactly the `RicciFlow.ModelGaugeFlowODE.LocalFlowSolution`-shaped integral-curve datum
`HasDerivWithinAt (flow) (f t (flow t)) s t` (with `f := chartPushforwardField I X p`), now supplied by
the RAW compact flow with **no spatial regularity assumed** — the first genuine consumer of the
raw-flow chart-representation toolkit, feeding the model ODE uniqueness comparison against the
model-`C³` flow. -/
theorem hasDerivWithinAt_extChartAt_comp_chartPushforwardField
    {γ : ℝ → M} {s : Set ℝ} {t : ℝ} {p : M} {X : ℝ → M → E}
    (hγ : HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ s t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t))))
    (hsrc_ext : γ t ∈ (extChartAt I p).source) :
    HasDerivWithinAt (fun τ : ℝ ↦ extChartAt I p (γ τ))
      (chartPushforwardField I X p t (extChartAt I p (γ t))) s t := by
  rw [chartPushforwardField_extChartAt X t hsrc_ext]
  exact hasDerivWithinAt_extChartAt_comp_of_hasMFDerivWithinAt hγ hsrc_ext

/-- **`HasDerivAt` form of the chart-representation integral-curve property.**  When the time set `s` is
a neighbourhood of `t` — the situation for the *open* flow window `Set.Ioo (-ε) ε` at an interior time —
the within-set integral-curve derivative of
`hasDerivWithinAt_extChartAt_comp_chartPushforwardField` upgrades to a full `HasDerivAt`, the form
consumed by Mathlib's model integral-curve / ODE-uniqueness API. -/
theorem hasDerivAt_extChartAt_comp_chartPushforwardField
    {γ : ℝ → M} {s : Set ℝ} {t : ℝ} {p : M} {X : ℝ → M → E}
    (hγ : HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ s t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t))))
    (hs : s ∈ nhds t)
    (hsrc_ext : γ t ∈ (extChartAt I p).source) :
    HasDerivAt (fun τ : ℝ ↦ extChartAt I p (γ τ))
      (chartPushforwardField I X p t (extChartAt I p (γ t))) t :=
  (hasDerivWithinAt_extChartAt_comp_chartPushforwardField hγ hsrc_ext).hasDerivAt hs

/-- **Chart-representation uniqueness against a co-integral curve of the chart pushforward field.**
Given the raw manifold flow ODE for `γ` in the source of the preferred chart `extChartAt I p` over an
open time window `Ioo a b`, and a second curve `g : ℝ → E` that is an integral curve of the *same*
chart pushforward field `chartPushforwardField I X p` on that window and agrees with the chart
representation `extChartAt I p ∘ γ` at an interior time `t₀`, if the field is `LipschitzOnWith K` on a
state tube `state t` containing both curves then the two coincide on the whole window.

This is the integral-curve uniqueness step that identifies the raw compact flow's chart representation
with a comparison curve `g` — in the intended application `g` is the model-`C³` flow tower `Ψ`, so the
conclusion upgrades the chart representation to `C³` (the `hslicesC3` content of
`exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3`).  The Lipschitz hypothesis `hlip` is the
`tangentCoordChange`/transition-map regularity supplied separately; everything else is now available
unconditionally from the raw flow via `hasDerivAt_extChartAt_comp_chartPushforwardField`. -/
theorem extChartAt_comp_eqOn_of_lipschitzOnWith
    {γ : ℝ → M} {g : ℝ → E} {p : M} {X : ℝ → M → E}
    {a b t₀ : ℝ} {K : NNReal} {state : ℝ → Set E}
    (hγ : ∀ t ∈ Set.Ioo a b,
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ (Set.Ioo a b) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t))))
    (hγ_src : ∀ t ∈ Set.Ioo a b, γ t ∈ (extChartAt I p).source)
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hlip : ∀ t ∈ Set.Ioo a b, LipschitzOnWith K (chartPushforwardField I X p t) (state t))
    (hg' : ∀ t ∈ Set.Ioo a b, HasDerivAt g (chartPushforwardField I X p t (g t)) t)
    (hγ_mem : ∀ t ∈ Set.Ioo a b, extChartAt I p (γ t) ∈ state t)
    (hg_mem : ∀ t ∈ Set.Ioo a b, g t ∈ state t)
    (heq : extChartAt I p (γ t₀) = g t₀) :
    Set.EqOn (fun τ : ℝ ↦ extChartAt I p (γ τ)) g (Set.Ioo a b) :=
  ODE_solution_unique_of_mem_Ioo (v := chartPushforwardField I X p) (s := state)
    hlip ht₀
    (fun t ht ↦ ⟨hasDerivAt_extChartAt_comp_chartPushforwardField (hγ t ht)
      (Ioo_mem_nhds ht.1 ht.2) (hγ_src t ht), hγ_mem t ht⟩)
    (fun t ht ↦ ⟨hg' t ht, hg_mem t ht⟩)
    heq

/-- **Chart-conjugation `C³` transfer with an independent target chart centre.**  Generalisation of
`contMDiffOn_of_extChartAt_conjugation` in which the target chart is centred at an arbitrary `y₀ : M`
rather than the image centre `F x₀`.  This is the form the *temporal* integral-curve identification
produces: the chart representation `τ ↦ extChartAt I p (Φ τ x)` uses a single fixed chart `p` for both
source and target, so the spatial conjugation identity it yields at a fixed time,
`extChartAt I p (Φ t x) = Ψ (extChartAt I p x)`, has target centre `p` — generally distinct from
`Φ t p`.  With this variant that fixed-chart identity discharges `ContMDiffOn I I 3 (Φ t)` on the
chart-confined patch, feeding the `hslicesC3` spatial-`C³` obligation via
`contMDiff_of_forall_extChartAt_conjugation`.

The proof is identical to `contMDiffOn_of_extChartAt_conjugation` with `y₀` in place of `F x₀`; nothing
in that argument uses `y₀ = F x₀`. -/
theorem contMDiffOn_of_extChartAt_conjugation'
    {x₀ y₀ : M} {F : M → M} {U : Set M} {Ψ : E → E}
    (hU : U ⊆ (chartAt H x₀).source)
    (hΨ : ContDiff ℝ 3 Ψ)
    (hFU : Set.MapsTo F U (chartAt H y₀).source)
    (hconj : ∀ x ∈ U, extChartAt I y₀ (F x) = Ψ (extChartAt I x₀ x)) :
    ContMDiffOn I I 3 F U := by
  have hchart : ContMDiffOn I 𝓘(ℝ, E) 3 (extChartAt I x₀) U :=
    (contMDiffOn_extChartAt (I := I) (n := 3) (x := x₀)).mono hU
  have hΨm : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3 Ψ := contMDiff_iff_contDiff.mpr hΨ
  have hmid : ContMDiffOn I 𝓘(ℝ, E) 3 (fun x => Ψ (extChartAt I x₀ x)) U :=
    hΨm.comp_contMDiffOn hchart
  have hmaps : Set.MapsTo (fun x => Ψ (extChartAt I x₀ x)) U (extChartAt I y₀).target := by
    intro x hx
    show Ψ (extChartAt I x₀ x) ∈ (extChartAt I y₀).target
    rw [← hconj x hx]
    exact PartialEquiv.map_source (extChartAt I y₀)
      (by rw [extChartAt_source]; exact hFU hx)
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I 3 (extChartAt I y₀).symm
      (extChartAt I y₀).target := contMDiffOn_extChartAt_symm y₀
  have hcomp : ContMDiffOn I I 3
      (fun x => (extChartAt I y₀).symm (Ψ (extChartAt I x₀ x))) U :=
    hsymm.comp hmid hmaps
  refine hcomp.congr (fun x hx => ?_)
  show F x = (extChartAt I y₀).symm (Ψ (extChartAt I x₀ x))
  rw [← hconj x hx]
  exact (PartialEquiv.left_inv (extChartAt I y₀)
    (by rw [extChartAt_source]; exact hFU hx)).symm

/-- **Backward chart-conjugation `C³` transfer for a flow slice.**  The inverse-map companion of
`contMDiffOn_of_extChartAt_conjugation'`: if the forward slice `Φt` is represented on `U` by a globally
`C³` model map `Ψ` in the single fixed chart at `x₀`
(`extChartAt I x₀ (Φt x) = Ψ (extChartAt I x₀ x)`), the model map has a `C³` left inverse `Ψsymm`
(`Ψsymm (Ψ (extChartAt I x₀ x)) = extChartAt I x₀ x` on the chart image of `U`), and `Gt` is a left
inverse of `Φt` on `U` (`Gt (Φt x) = x`), then the inverse slice `Gt` is `ContMDiffOn I I 3` on the
forward image `Φt '' U`.

The backward conjugation `extChartAt I x₀ (Gt y) = Ψsymm (extChartAt I x₀ y)` at `y = Φt x ∈ Φt '' U`
is derived algebraically from the forward one: `extChartAt I x₀ (Gt (Φt x)) = extChartAt I x₀ x` (left
inverse) equals `Ψsymm (Ψ (extChartAt I x₀ x)) = Ψsymm (extChartAt I x₀ (Φt x))` (left-inverse of the
model map applied to the forward conjugation).  The result then follows from
`contMDiffOn_of_extChartAt_conjugation'` applied to `Gt` with model map `Ψsymm`, source and target chart
both centred at `x₀`.  When `Ψ` is the model gauge-flow diffeomorph slice `(G.maps3 τ : E → E)` and
`Ψsymm := (G.maps3 τ).symm` — a genuine `C³` self-diffeomorph of `E` — the left-inverse hypothesis is
automatic; this supplies the backward slice-`C³` (inverse `G t`) half of the `hslicesC3` obligation of
`exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3` directly from the same forward flow data,
requiring no separate backward orbit confinement. -/
theorem contMDiffOn_symm_of_extChartAt_conjugation'
    {x₀ : M} {Φt Gt : M → M} {U : Set M} {Ψ Ψsymm : E → E}
    (hΨsymm : ContDiff ℝ 3 Ψsymm)
    (hΦU : Set.MapsTo Φt U (chartAt H x₀).source)
    (hU : U ⊆ (chartAt H x₀).source)
    (hconj : ∀ x ∈ U, extChartAt I x₀ (Φt x) = Ψ (extChartAt I x₀ x))
    (hΨsymmΨ : ∀ x ∈ U, Ψsymm (Ψ (extChartAt I x₀ x)) = extChartAt I x₀ x)
    (hGleft : ∀ x ∈ U, Gt (Φt x) = x) :
    ContMDiffOn I I 3 Gt (Φt '' U) := by
  refine contMDiffOn_of_extChartAt_conjugation' (x₀ := x₀) (y₀ := x₀)
    (F := Gt) (Ψ := Ψsymm) ?_ hΨsymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    exact hΦU hx
  · rintro y ⟨x, hx, rfl⟩
    rw [hGleft x hx]
    exact hU hx
  · rintro y ⟨x, hx, rfl⟩
    rw [hGleft x hx, hconj x hx, hΨsymmΨ x hx]

/-- **Backward flow-slice `C³` transfer against a genuine model diffeomorph.**  The
`Diffeomorph`-specialised form of `contMDiffOn_symm_of_extChartAt_conjugation'`: when the forward slice
`Φt` is chart-conjugate on `U` to a genuine `C³` self-diffeomorph `Ψ` of the model space `E`
(`extChartAt I x₀ (Φt x) = Ψ (extChartAt I x₀ x)`) and `Gt` left-inverts `Φt` on `U`, the inverse slice
`Gt` is `ContMDiffOn I I 3` on the forward image `Φt '' U`.  The `C³` left inverse and its left-inverse
identity are supplied by the diffeomorph's own `Ψ.symm` (`Ψ.symm.contMDiff` / `Ψ.symm_apply_apply`), so
no separate model-inverse data is needed.  This is the directly-consumable backward companion for the
model gauge-flow slice `Ψ := (G.maps3 τ : E → E)` (which is exactly such a `C³` self-diffeomorph, its
`C³`-ness being `contDiff_three_maps3_of_model_diffeomorph3GaugeFlowOn`), delivering the inverse-slice
`C³` half of `hslicesC3` from the forward conjugation alone. -/
theorem contMDiffOn_symm_of_extChartAt_conjugation_diffeomorph'
    {x₀ : M} {Φt Gt : M → M} {U : Set M}
    (Ψ : E ≃ₘ^3⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E)
    (hΦU : Set.MapsTo Φt U (chartAt H x₀).source)
    (hU : U ⊆ (chartAt H x₀).source)
    (hconj : ∀ x ∈ U, extChartAt I x₀ (Φt x) = Ψ (extChartAt I x₀ x))
    (hGleft : ∀ x ∈ U, Gt (Φt x) = x) :
    ContMDiffOn I I 3 Gt (Φt '' U) :=
  contMDiffOn_symm_of_extChartAt_conjugation' (Ψ := (Ψ : E → E)) (Ψsymm := (Ψ.symm : E → E))
    (contMDiff_iff_contDiff.mp Ψ.symm.contMDiff) hΦU hU hconj
    (fun x _ => Ψ.symm_apply_apply _) hGleft

/-- **`ContinuousOn` of the chart pushforward field from a continuous tangent-bundle section.**

The isolated varying-source-centre coordinate change `y ↦ tangentCoordChange I y p y` is *not*
continuous — its source chart `chartAt H y` jumps discontinuously with `y` (and, via
`tangentCoordChange_comp`, `tangentCoordChange I y p y` is the *inverse* of `tangentCoordChange I p y y`,
which still reads the varying chart at `y`).  `chartPushforwardField` is continuous only through its
identification with a genuine tangent-bundle chart representation: for `y ∈ (extChartAt I p).source`, the
value `tangentCoordChange I y p y (X τ y)` (`chartPushforwardField_extChartAt`) is exactly the second
component of the trivialization `trivializationAt E (TangentSpace I) p` applied to the section value
`⟨y, X τ y⟩` (`trivializationAt_apply` — both unfold to the same
`fderivWithin ℝ (extChartAt I p ∘ (extChartAt I y).symm) (range I) (extChartAt I y y)`).

Consequently, whenever the section `y ↦ ⟨y, X τ y⟩` is `ContinuousOn` the chart source — the shape a
genuine (e.g. DeTurck) vector field supplies, being a continuous section of the tangent bundle — the
model field `chartPushforwardField I X p τ` is `ContinuousOn` the chart target.  This is the
correctly-hypothesised field-regularity step feeding the `LipschitzOnWith` input of
`extChartAt_comp_eqOn_of_lipschitzOnWith` (the plan's "`chartPushforwardField` `ContinuousOn`" target,
here supplied with the section hypothesis it genuinely requires). -/
theorem continuousOn_chartPushforwardField
    {X : ℝ → M → E} {p : M} {τ : ℝ}
    (hX : ContinuousOn (fun y : M => (⟨y, X τ y⟩ : TangentBundle I M))
      (extChartAt I p).source) :
    ContinuousOn (chartPushforwardField I X p τ) (extChartAt I p).target := by
  have hsymm : Set.MapsTo (fun q => (extChartAt I p).symm q)
      (extChartAt I p).target (extChartAt I p).source :=
    fun q hq => (extChartAt I p).map_target hq
  have h2 : ContinuousOn (fun q => (⟨(extChartAt I p).symm q,
      X τ ((extChartAt I p).symm q)⟩ : TangentBundle I M)) (extChartAt I p).target :=
    hX.comp (continuousOn_extChartAt_symm p) hsymm
  have h3 : ContinuousOn (fun q => (trivializationAt E (TangentSpace I) p)
      (⟨(extChartAt I p).symm q, X τ ((extChartAt I p).symm q)⟩ : TangentBundle I M))
      (extChartAt I p).target := by
    refine (trivializationAt E (TangentSpace I) p).continuousOn.comp h2 (fun q hq => ?_)
    rw [TangentBundle.trivializationAt_source]
    have hmem := (extChartAt I p).map_target hq
    rw [extChartAt_source] at hmem
    exact hmem
  have hg : ContinuousOn (fun q => ((trivializationAt E (TangentSpace I) p)
      (⟨(extChartAt I p).symm q, X τ ((extChartAt I p).symm q)⟩ : TangentBundle I M)).2)
      (extChartAt I p).target :=
    continuous_snd.comp_continuousOn h3
  refine hg.congr (fun q hq => ?_)
  have hy : (extChartAt I p).symm q ∈ (extChartAt I p).source := (extChartAt I p).map_target hq
  have hqe : extChartAt I p ((extChartAt I p).symm q) = q := (extChartAt I p).right_inv hq
  have hL : chartPushforwardField I X p τ q
      = tangentCoordChange I ((extChartAt I p).symm q) p ((extChartAt I p).symm q)
          (X τ ((extChartAt I p).symm q)) := by
    conv_lhs => rw [← hqe]
    exact chartPushforwardField_extChartAt X τ hy
  change chartPushforwardField I X p τ q =
    ((trivializationAt E (TangentSpace I) p)
      (⟨(extChartAt I p).symm q, X τ ((extChartAt I p).symm q)⟩ : TangentBundle I M)).2
  rw [hL, TangentBundle.trivializationAt_apply, tangentCoordChange_def]
  rfl

/-- **`ContDiffOn` of the chart pushforward field from a `C^n` tangent-bundle section.**

The smooth analogue of `continuousOn_chartPushforwardField`, upgrading continuity to `C^n`
regularity — the form needed to discharge the `LipschitzOnWith` (`hlip`) hypothesis of
`extChartAt_comp_eqOn_of_lipschitzOnWith` (a `C^1` field on a convex compact tube is Lipschitz).
Again the varying-source-centre coordinate change is smooth only through the tangent-bundle chart
representation: the fixed-trivialization section characterisation
`Bundle.Trivialization.contMDiffOn_iff` (centred at `p`, not at the varying base point, using
`MemTrivializationAtlas (trivializationAt E (TangentSpace I) p)`) turns `C^n`-ness of the section
`y ↦ ⟨y, X τ y⟩` into `C^n`-ness of `y ↦ (trivializationAt E (TangentSpace I) p ⟨y, X τ y⟩).2`, whose
value along the chart is exactly `chartPushforwardField` (`TangentBundle.trivializationAt_apply`).
Composing with the `C^n` chart inverse and reading off `contMDiffOn_iff_contDiffOn` yields the model
`ContDiffOn ℝ n` statement. -/
theorem contDiffOn_chartPushforwardField {n : WithTop ℕ∞}
    [IsManifold I n M] [ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I]
    {X : ℝ → M → E} {p : M} {τ : ℝ}
    (hX : ContMDiffOn I (I.prod 𝓘(ℝ, E)) n
      (fun y : M => (⟨y, X τ y⟩ : TangentBundle I M)) (extChartAt I p).source) :
    ContDiffOn ℝ n (chartPushforwardField I X p τ) (extChartAt I p).target := by
  have hmaps : Set.MapsTo (fun y : M => (⟨y, X τ y⟩ : TangentBundle I M))
      (extChartAt I p).source (trivializationAt E (TangentSpace I) p).source := by
    intro y hy
    rw [TangentBundle.trivializationAt_source]
    rw [extChartAt_source] at hy
    exact hy
  have hsnd : ContMDiffOn I 𝓘(ℝ, E) n
      (fun y => (trivializationAt E (TangentSpace I) p (⟨y, X τ y⟩ : TangentBundle I M)).2)
      (extChartAt I p).source :=
    (((trivializationAt E (TangentSpace I) p).contMDiffOn_iff hmaps).mp hX).2
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) n
      (fun q => (trivializationAt E (TangentSpace I) p
        (⟨(extChartAt I p).symm q, X τ ((extChartAt I p).symm q)⟩ : TangentBundle I M)).2)
      (extChartAt I p).target :=
    hsnd.comp (contMDiffOn_extChartAt_symm p)
      (fun q hq => (extChartAt I p).map_target hq)
  rw [← contMDiffOn_iff_contDiffOn]
  refine hcomp.congr (fun q hq => ?_)
  have hy : (extChartAt I p).symm q ∈ (extChartAt I p).source := (extChartAt I p).map_target hq
  have hqe : extChartAt I p ((extChartAt I p).symm q) = q := (extChartAt I p).right_inv hq
  have hL : chartPushforwardField I X p τ q
      = tangentCoordChange I ((extChartAt I p).symm q) p ((extChartAt I p).symm q)
          (X τ ((extChartAt I p).symm q)) := by
    conv_lhs => rw [← hqe]
    exact chartPushforwardField_extChartAt X τ hy
  rw [hL, TangentBundle.trivializationAt_apply, tangentCoordChange_def]
  rfl

/-- **`LipschitzOnWith` of the chart pushforward field on a convex compact tube.**  The field-regularity
datum consumed by the `hlip` hypothesis of `extChartAt_comp_eqOn_of_lipschitzOnWith`: combining the `C^n`
regularity `contDiffOn_chartPushforwardField` (`n ≠ 0`, so `C^1` suffices) with
`ContDiffOn.exists_lipschitzOnWith` (a `C^1` function on a convex compact set is Lipschitz), the chart
pushforward field of a `C^n` tangent-bundle section is `LipschitzOnWith` some constant `K` on any convex
compact subset `s` of the chart target.  This closes the field-Lipschitz step of the temporal
integral-curve uniqueness comparison (with `s` the state tube `state t`), reducing the remaining GAP-1
analytic content to the existence of the model-`C³` comparison flow `Ψ` itself. -/
theorem exists_lipschitzOnWith_chartPushforwardField {n : WithTop ℕ∞}
    [IsManifold I n M] [ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I]
    {X : ℝ → M → E} {p : M} {τ : ℝ}
    (hX : ContMDiffOn I (I.prod 𝓘(ℝ, E)) n
      (fun y : M => (⟨y, X τ y⟩ : TangentBundle I M)) (extChartAt I p).source)
    (hn : n ≠ 0) {s : Set E} (hs_sub : s ⊆ (extChartAt I p).target)
    (hs_conv : Convex ℝ s) (hs_comp : IsCompact s) :
    ∃ K, LipschitzOnWith K (chartPushforwardField I X p τ) s :=
  ((contDiffOn_chartPushforwardField hX).mono hs_sub).exists_lipschitzOnWith hn hs_conv hs_comp

/-- **Joint `(τ, q)` `ContDiffOn` of the chart pushforward field from a jointly-`C^n`
time-dependent tangent-bundle section.**  The time-uniform (product-domain) strengthening of
`contDiffOn_chartPushforwardField`: from joint `C^n` regularity of the time-dependent section
`(τ, y) ↦ ⟨y, X τ y⟩` on `ℝ ×ˢ (extChartAt I p).source` (as a map into the tangent bundle with the
product model `𝓘(ℝ, ℝ).prod I`), the uncurried chart pushforward field
`(τ, q) ↦ chartPushforwardField I X p τ q` is `ContDiffOn ℝ n` on `ℝ ×ˢ (extChartAt I p).target`.

The proof runs the fixed-time argument of `contDiffOn_chartPushforwardField` with the product source
manifold `ℝ × M`: the fixed-trivialization section characterisation
(`Bundle.Trivialization.contMDiffOn_iff`, centred at `p`) turns the joint section smoothness into joint
`C^n`-ness of `(τ, y) ↦ (trivializationAt E (TangentSpace I) p ⟨y, X τ y⟩).2`, which is composed with the
time-passenger chart inverse `(τ, q) ↦ (τ, (extChartAt I p).symm q)` and read off through
`modelWithCornersSelf_prod`/`chartedSpaceSelf_prod` + `contMDiffOn_iff_contDiffOn` on the model product
`ℝ × E`.  This is the joint-in-time field regularity feeding the bump-function globalisation of the model
gauge flow: a compactly-supported `C^N` representative of the pushforward field is what
`exists_diffeomorph3GaugeFlowOn_of_contDiff_hasCompactSupport` consumes. -/
theorem contDiffOn_prod_chartPushforwardField {n : WithTop ℕ∞}
    [IsManifold I n M] [ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I]
    {X : ℝ → M → E} {p : M}
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) n
      (fun r : ℝ × M => (⟨r.2, X r.1 r.2⟩ : TangentBundle I M))
      (Set.univ ×ˢ (extChartAt I p).source)) :
    ContDiffOn ℝ n (fun r : ℝ × E => chartPushforwardField I X p r.1 r.2)
      (Set.univ ×ˢ (extChartAt I p).target) := by
  have hmaps : Set.MapsTo (fun r : ℝ × M => (⟨r.2, X r.1 r.2⟩ : TangentBundle I M))
      (Set.univ ×ˢ (extChartAt I p).source)
      (trivializationAt E (TangentSpace I) p).source := by
    intro r hr
    rw [TangentBundle.trivializationAt_source]
    have hr2 := hr.2
    rw [extChartAt_source] at hr2
    exact hr2
  have hsnd : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) n
      (fun r : ℝ × M => (trivializationAt E (TangentSpace I) p
        (⟨r.2, X r.1 r.2⟩ : TangentBundle I M)).2)
      (Set.univ ×ˢ (extChartAt I p).source) :=
    (((trivializationAt E (TangentSpace I) p).contMDiffOn_iff hmaps).mp hX).2
  have hΦ : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ).prod I) n
      (fun r : ℝ × E => ((r.1 : ℝ), (extChartAt I p).symm r.2))
      (Set.univ ×ˢ (extChartAt I p).target) :=
    ((ContinuousLinearMap.fst ℝ ℝ E).contMDiff.contMDiffOn).prodMk
      ((contMDiffOn_extChartAt_symm p).comp
        ((ContinuousLinearMap.snd ℝ ℝ E).contMDiff.contMDiffOn)
        (fun r hr => hr.2))
  have hcomp :=
    hsnd.comp hΦ (fun r hr => ⟨Set.mem_univ _, (extChartAt I p).map_target hr.2⟩)
  rw [← contMDiffOn_iff_contDiffOn]
  refine hcomp.congr (fun r hr => ?_)
  simp only [Function.comp_apply]
  have hq : r.2 ∈ (extChartAt I p).target := hr.2
  have hy : (extChartAt I p).symm r.2 ∈ (extChartAt I p).source := (extChartAt I p).map_target hq
  have hqe : extChartAt I p ((extChartAt I p).symm r.2) = r.2 := (extChartAt I p).right_inv hq
  have hL : chartPushforwardField I X p r.1 r.2
      = tangentCoordChange I ((extChartAt I p).symm r.2) p ((extChartAt I p).symm r.2)
          (X r.1 ((extChartAt I p).symm r.2)) := by
    conv_lhs => rw [← hqe]
    exact chartPushforwardField_extChartAt X r.1 hy
  rw [hL, TangentBundle.trivializationAt_apply, tangentCoordChange_def]
  rfl

/-- **Time-uniform `LipschitzOnWith` of the chart pushforward field on a convex compact tube.**  The
time-independent (`hlip`) datum consumed by `extChartAt_comp_eqOn_of_lipschitzOnWith`: a *single*
Lipschitz constant `K` valid for **every** time slice `chartPushforwardField I X p t`
(`t ∈ Set.Icc a b`), obtained from the joint-in-time field regularity
`contDiffOn_prod_chartPushforwardField` on the compact convex product tube `Set.Icc a b ×ˢ s`
(`ContDiffOn.exists_lipschitzOnWith`), then restricting the joint Lipschitz bound to each time slice:
for a fixed time `t` the two product points `(t, q)`, `(t, q')` share their first coordinate, so their
sup-metric distance `edist (t, q) (t, q')` collapses to `edist q q'` (`Prod.edist_eq`, `edist_self`),
turning the joint bound into the slice bound with the *same* constant.

This is exactly the uniform-`K` shape the temporal integral-curve uniqueness comparison requires for its
`hlip : ∀ t ∈ Set.Ioo a b, LipschitzOnWith K (chartPushforwardField I X p t) (state t)` hypothesis with
a constant state tube `state t := s` (and `Set.Ioo a b ⊆ Set.Icc a b`), strengthening the
per-fixed-time `exists_lipschitzOnWith_chartPushforwardField` to a bound uniform over the whole compact
time interval — the field-Lipschitz input of the step-(v) GAP-1 glue that no longer varies with `t`. -/
theorem exists_lipschitzOnWith_forall_mem_Icc_chartPushforwardField {n : WithTop ℕ∞}
    [IsManifold I n M] [ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I]
    {X : ℝ → M → E} {p : M}
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) n
      (fun r : ℝ × M => (⟨r.2, X r.1 r.2⟩ : TangentBundle I M))
      (Set.univ ×ˢ (extChartAt I p).source))
    (hn : n ≠ 0) {a b : ℝ} {s : Set E} (hs_sub : s ⊆ (extChartAt I p).target)
    (hs_conv : Convex ℝ s) (hs_comp : IsCompact s) :
    ∃ K, ∀ t ∈ Set.Icc a b, LipschitzOnWith K (chartPushforwardField I X p t) s := by
  have hsub : Set.Icc a b ×ˢ s ⊆ Set.univ ×ˢ (extChartAt I p).target :=
    Set.prod_mono (Set.subset_univ _) hs_sub
  have hconv : Convex ℝ (Set.Icc a b ×ˢ s) := (convex_Icc a b).prod hs_conv
  have hcomp : IsCompact (Set.Icc a b ×ˢ s) := isCompact_Icc.prod hs_comp
  obtain ⟨K, hK⟩ :=
    ((contDiffOn_prod_chartPushforwardField hX).mono hsub).exists_lipschitzOnWith hn hconv hcomp
  refine ⟨K, fun t ht => ?_⟩
  intro q hq q' hq'
  have hedist : edist ((t, q) : ℝ × E) (t, q') = edist q q' := by
    rw [Prod.edist_eq]
    dsimp only
    rw [edist_self]
    exact max_eq_right (by positivity)
  have hlip := hK (⟨ht, hq⟩ : ((t, q) : ℝ × E) ∈ Set.Icc a b ×ˢ s)
    (⟨ht, hq'⟩ : ((t, q') : ℝ × E) ∈ Set.Icc a b ×ˢ s)
  rw [hedist] at hlip
  exact hlip

/-- **Field-Lipschitz bound on an open ball tube from a closed-ball chart containment.**  Specialises
`exists_lipschitzOnWith_forall_mem_Icc_chartPushforwardField` to a metric ball `state₀ := Metric.ball c ρ`
whose closure `Metric.closedBall c ρ` lies in the chart target.  The closed ball is compact (finite
dimension gives `ProperSpace E`) and convex, so the base lemma yields a uniform Lipschitz constant for
`chartPushforwardField I X p t` on it over the whole time interval `Set.Icc a b`, and that restricts to
the open ball `Metric.ball c ρ ⊆ Metric.closedBall c ρ`.  This is exactly the open, convex Lipschitz tube
`state₀` datum (with its `hlip`) consumed by the step-(v) globalisation capstone
(`exists_flow_Ioo_forall_contMDiff_of_field_jets_finite_cover_windowLip`), discharged directly from the
per-patch chart field jet — no global-in-time Lipschitz hypothesis needed. -/
theorem exists_lipschitzOnWith_forall_mem_Icc_chartPushforwardField_ball {n : WithTop ℕ∞}
    [IsManifold I n M] [ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I]
    {X : ℝ → M → E} {p : M}
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) n
      (fun r : ℝ × M => (⟨r.2, X r.1 r.2⟩ : TangentBundle I M))
      (Set.univ ×ˢ (extChartAt I p).source))
    (hn : n ≠ 0) {a b : ℝ} {c : E} {ρ : ℝ}
    (hball : Metric.closedBall c ρ ⊆ (extChartAt I p).target) :
    ∃ K, ∀ t ∈ Set.Icc a b, LipschitzOnWith K
      (chartPushforwardField I X p t) (Metric.ball c ρ) := by
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_forall_mem_Icc_chartPushforwardField hX hn
    hball (convex_closedBall c ρ) (isCompact_closedBall c ρ)
  exact ⟨K, fun t ht => (hK t ht).mono Metric.ball_subset_closedBall⟩

/-- **Global single-chart-conjugation `C³` gluer.**  The primed (single fixed chart `x₀`, i.e.
`y₀ = x₀`) analogue of `contMDiff_of_forall_extChartAt_conjugation`: a map `F : M → M` that, near every
point, agrees in ONE preferred extended chart `extChartAt I x₀` with a globally-`C³` model map `Ψ` — the
target read in the SAME chart `x₀` as the source, `extChartAt I x₀ (F y) = Ψ (extChartAt I x₀ y)` — is
globally `ContMDiff I I 3`.  Each local witness is discharged by the fixed-chart transfer
`contMDiffOn_of_extChartAt_conjugation'` and upgraded to `ContMDiffAt` on the neighbourhood.

This is the gluer matching the single-fixed-chart conjugation produced by the *temporal* integral-curve
identification (`contMDiffOn_flowSlice_of_rawFlow_modelFlow_eqOn` below), whose spatial conjugation
`extChartAt I p (Φ t x) = Ψ t (extChartAt I p x)` uses one chart `p` for both source and target — hence
it feeds THIS gluer (not the image-centred `contMDiff_of_forall_extChartAt_conjugation`) to assemble the
global slice `C³` (`hslicesC3`) obligation of `exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3`. -/
theorem contMDiff_of_forall_extChartAt_conjugation'
    {F : M → M}
    (h : ∀ x : M, ∃ (x₀ : M) (U : Set M) (Ψ : E → E),
      U ∈ 𝓝 x ∧ U ⊆ (chartAt H x₀).source ∧ ContDiff ℝ 3 Ψ ∧
      Set.MapsTo F U (chartAt H x₀).source ∧
      (∀ y ∈ U, extChartAt I x₀ (F y) = Ψ (extChartAt I x₀ y))) :
    ContMDiff I I 3 F := by
  intro x
  obtain ⟨x₀, U, Ψ, hUmem, hU, hΨ, hFU, hconj⟩ := h x
  exact (contMDiffOn_of_extChartAt_conjugation' hU hΨ hFU hconj).contMDiffAt hUmem

/-- **Fixed-time flow-slice `C³` regularity from temporal integral-curve uniqueness against a
model-`C³` flow.**  The genuine GAP-1 assembly step joining the two halves of the chart-transfer
programme: temporal integral-curve uniqueness (`extChartAt_comp_eqOn_of_lipschitzOnWith`) and the
fixed-chart `C³` conjugation transfer (`contMDiffOn_of_extChartAt_conjugation'`).

For a raw manifold flow `Φ : ℝ → M → M` whose trajectories `τ ↦ Φ τ x` solve the bare gauge ODE
`HasMFDerivWithinAt … ((1).smulRight (X τ (Φ τ x)))` on an open window `Ioo a b` and stay in the
preferred chart `extChartAt I p`, and a model flow `Ψ : ℝ → E → E` whose orbits
`τ ↦ Ψ τ (extChartAt I p x)` are integral curves of the chart pushforward field
`chartPushforwardField I X p` agreeing with the raw chart representation at an interior anchor time
`t₀`, the (uniform-in-time, tube-local) Lipschitz control on the pushforward field forces, at every
window time `t`, the *spatial* conjugation identity `extChartAt I p (Φ t x) = Ψ t (extChartAt I p x)`
on `U`.  Feeding that fixed-`t` identity (with the `C³` spatial slice `Ψ t`) to
`contMDiffOn_of_extChartAt_conjugation'` (single fixed chart `p` for source and target) discharges
`ContMDiffOn I I 3 (Φ t) U` on the chart-confined patch — the per-patch content that
`contMDiff_of_forall_extChartAt_conjugation` glues into the global slice `C³` (`hslicesC3`) obligation
of `exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3`.  No spatial regularity of `Φ`
itself is assumed: it is *produced* from the raw ODE by comparison with the model-`C³` flow. -/
theorem contMDiffOn_flowSlice_of_rawFlow_modelFlow_eqOn
    {Φ : ℝ → M → M} {Ψ : ℝ → E → E} {p : M} {X : ℝ → M → E}
    {a b t₀ t : ℝ} {K : NNReal} {state : ℝ → Set E} {U : Set M}
    (hU : U ⊆ (chartAt H p).source)
    (hΨ : ContDiff ℝ 3 (Ψ t))
    (hΦU : Set.MapsTo (Φ t) U (chartAt H p).source)
    (ht : t ∈ Set.Ioo a b)
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hlip : ∀ τ ∈ Set.Ioo a b, LipschitzOnWith K (chartPushforwardField I X p τ) (state τ))
    (hraw : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b,
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ : ℝ ↦ Φ τ x) (Set.Ioo a b) τ
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (Φ τ x))))
    (hsrc : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b, Φ τ x ∈ (extChartAt I p).source)
    (hg' : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b,
      HasDerivAt (fun τ : ℝ ↦ Ψ τ (extChartAt I p x))
        (chartPushforwardField I X p τ (Ψ τ (extChartAt I p x))) τ)
    (hγ_mem : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b, extChartAt I p (Φ τ x) ∈ state τ)
    (hg_mem : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b, Ψ τ (extChartAt I p x) ∈ state τ)
    (heq₀ : ∀ x ∈ U, extChartAt I p (Φ t₀ x) = Ψ t₀ (extChartAt I p x)) :
    ContMDiffOn I I 3 (Φ t) U := by
  refine contMDiffOn_of_extChartAt_conjugation' hU hΨ hΦU (fun x hx => ?_)
  exact extChartAt_comp_eqOn_of_lipschitzOnWith
    (fun τ hτ => hraw x hx τ hτ) (fun τ hτ => hsrc x hx τ hτ) ht₀ hlip
    (fun τ hτ => hg' x hx τ hτ) (fun τ hτ => hγ_mem x hx τ hτ)
    (fun τ hτ => hg_mem x hx τ hτ) (heq₀ x hx) ht

/-- **Backward per-patch flow-slice `C³` in the raw-flow / model-diffeomorph setting.**  The
inverse-map companion of `contMDiffOn_flowSlice_of_rawFlow_modelFlow_eqOn`: with the model comparison
flow supplied as a genuine family of `C³` self-diffeomorphs `Ψ : ℝ → (E ≃ₘ^3 E)` (the shape of the
model gauge-flow slice `τ ↦ G.maps3 τ`), the *same* temporal integral-curve comparison data that yields
the forward slice `C³` also yields, for any `Gt` left-inverting `Φ t` on `U`,
`ContMDiffOn I I 3 Gt (Φ t '' U)`.  The forward single-fixed-chart conjugation
`extChartAt I p (Φ t x) = Ψ t (extChartAt I p x)` on `U` is produced exactly as in the forward lemma
(via the temporal integral-curve uniqueness core `extChartAt_comp_eqOn_of_lipschitzOnWith`), then fed —
with the diffeomorph `Ψ t` (whose `C³` inverse discharges the backward transfer) and the left-inverse
datum — to `contMDiffOn_symm_of_extChartAt_conjugation_diffeomorph'`.  This is the backward per-patch
brick of the `hslicesC3` inverse-slice obligation, produced from the raw flow ODE, tube-Lipschitz
control, and model comparison alone — no spatial regularity of `Φ` or backward orbit confinement
assumed. -/
theorem contMDiffOn_symm_flowSlice_of_rawFlow_modelFlow_eqOn
    {Φ : ℝ → M → M} {Ψ : ℝ → (E ≃ₘ^3⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E)} {Gt : M → M} {p : M} {X : ℝ → M → E}
    {a b t₀ t : ℝ} {K : NNReal} {state : ℝ → Set E} {U : Set M}
    (hU : U ⊆ (chartAt H p).source)
    (hΦU : Set.MapsTo (Φ t) U (chartAt H p).source)
    (ht : t ∈ Set.Ioo a b)
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hlip : ∀ τ ∈ Set.Ioo a b, LipschitzOnWith K (chartPushforwardField I X p τ) (state τ))
    (hraw : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b,
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ : ℝ ↦ Φ τ x) (Set.Ioo a b) τ
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (Φ τ x))))
    (hsrc : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b, Φ τ x ∈ (extChartAt I p).source)
    (hg' : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b,
      HasDerivAt (fun τ : ℝ ↦ (Ψ τ : E → E) (extChartAt I p x))
        (chartPushforwardField I X p τ ((Ψ τ : E → E) (extChartAt I p x))) τ)
    (hγ_mem : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b, extChartAt I p (Φ τ x) ∈ state τ)
    (hg_mem : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b, (Ψ τ : E → E) (extChartAt I p x) ∈ state τ)
    (heq₀ : ∀ x ∈ U, extChartAt I p (Φ t₀ x) = (Ψ t₀ : E → E) (extChartAt I p x))
    (hGleft : ∀ x ∈ U, Gt (Φ t x) = x) :
    ContMDiffOn I I 3 Gt (Φ t '' U) := by
  refine contMDiffOn_symm_of_extChartAt_conjugation_diffeomorph' (Ψ := Ψ t) hΦU hU
    (fun x hx => ?_) hGleft
  exact extChartAt_comp_eqOn_of_lipschitzOnWith
    (fun τ hτ => hraw x hx τ hτ) (fun τ hτ => hsrc x hx τ hτ) ht₀ hlip
    (fun τ hτ => hg' x hx τ hτ) (fun τ hτ => hγ_mem x hx τ hτ)
    (fun τ hτ => hg_mem x hx τ hτ) (heq₀ x hx) ht

/-- **Global flow-slice `C³` (Route-A `hslicesC3`) from a per-point family of temporal integral-curve
comparisons.**  The GAP-1 capstone: for the fixed time `t`, `ContMDiff I I 3 (Φ t)` — exactly the
`hslicesC3` datum of `exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3` (Route A) — provided
that around EVERY base point `x` there is a preferred chart `p`, a model-`C³` comparison flow `Ψ`, an
open window `Ioo a b ∋ t, t₀`, a uniform tube-Lipschitz constant `K` for the chart pushforward field, and
a neighbourhood `U ∋ x` on which the raw flow trajectories solve the bare gauge ODE, stay in the chart,
and are compared (integral-curve co-solution + anchor agreement) with the model flow's orbits.

Each local package yields, via the temporal integral-curve uniqueness core
`extChartAt_comp_eqOn_of_lipschitzOnWith`, the single-fixed-chart spatial conjugation
`extChartAt I p (Φ t y) = Ψ t (extChartAt I p y)` on `U`; the primed global gluer
`contMDiff_of_forall_extChartAt_conjugation'` then assembles those into global `C³`.  This is the direct
bridge from "raw compact flow + model-`C³` comparison data, locally everywhere" to the Route-A slice-`C³`
obligation — no spatial regularity of `Φ` assumed anywhere. -/
theorem contMDiff_flowSlice_of_forall_rawFlow_modelFlow_eqOn
    {Φ : ℝ → M → M} {X : ℝ → M → E} {t : ℝ}
    (h : ∀ x : M, ∃ (p : M) (Ψ : ℝ → E → E) (a b t₀ : ℝ) (K : NNReal)
        (state : ℝ → Set E) (U : Set M),
      U ∈ nhds x ∧ U ⊆ (chartAt H p).source ∧ ContDiff ℝ 3 (Ψ t) ∧
      Set.MapsTo (Φ t) U (chartAt H p).source ∧ t ∈ Set.Ioo a b ∧ t₀ ∈ Set.Ioo a b ∧
      (∀ τ ∈ Set.Ioo a b, LipschitzOnWith K (chartPushforwardField I X p τ) (state τ)) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
        HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ : ℝ ↦ Φ τ y) (Set.Ioo a b) τ
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (Φ τ y)))) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, Φ τ y ∈ (extChartAt I p).source) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
        HasDerivAt (fun τ : ℝ ↦ Ψ τ (extChartAt I p y))
          (chartPushforwardField I X p τ (Ψ τ (extChartAt I p y))) τ) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, extChartAt I p (Φ τ y) ∈ state τ) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, Ψ τ (extChartAt I p y) ∈ state τ) ∧
      (∀ y ∈ U, extChartAt I p (Φ t₀ y) = Ψ t₀ (extChartAt I p y))) :
    ContMDiff I I 3 (Φ t) := by
  refine contMDiff_of_forall_extChartAt_conjugation' (fun x => ?_)
  obtain ⟨p, Ψ, a, b, t₀, K, state, U, hUmem, hU, hΨ, hΦU, ht, ht₀, hlip,
    hraw, hsrc, hg', hγ_mem, hg_mem, heq₀⟩ := h x
  refine ⟨p, U, Ψ t, hUmem, hU, hΨ, hΦU, fun y hy => ?_⟩
  exact extChartAt_comp_eqOn_of_lipschitzOnWith
    (fun τ hτ => hraw y hy τ hτ) (fun τ hτ => hsrc y hy τ hτ) ht₀ hlip
    (fun τ hτ => hg' y hy τ hτ) (fun τ hτ => hγ_mem y hy τ hτ)
    (fun τ hτ => hg_mem y hy τ hτ) (heq₀ y hy) ht

/-- **Global inverse-slice `C³` from per-point backward per-patch data against an open-map slice.**  The
backward-slice globaliser, dual to `contMDiff_of_forall_extChartAt_conjugation'`: at a fixed time, if the
forward slice `Φt` is an open map (its compact-manifold time-slices are diffeomorphisms, hence open) and
surjective, and around every base point `x` there is an open neighbourhood `U ∋ x` on which the inverse
slice `Gt` is `ContMDiffOn I I 3` on the forward image `Φt '' U` — precisely the datum produced by
`contMDiffOn_symm_flowSlice_of_rawFlow_modelFlow_eqOn` — then `Gt` is globally `ContMDiff I I 3`.

Every point `y = Φt x` (surjectivity) has the open neighbourhood `Φt '' U` (open by the open-map
hypothesis) on which `Gt` is `ContMDiffOn`; `contMDiff_of_locally_contMDiffOn` glues these into global
`ContMDiff`.  Composed with the per-patch backward lemma this discharges the inverse-slice (`G t`) `C³`
half of the `hslicesC3` obligation of `exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3`
(the forward half being handled by the primed forward gluer). -/
theorem contMDiff_symm_flowSlice_of_forall_openImage
    {Φt Gt : M → M}
    (hopen : IsOpenMap Φt)
    (hsurj : Function.Surjective Φt)
    (h : ∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ContMDiffOn I I 3 Gt (Φt '' U)) :
    ContMDiff I I 3 Gt := by
  refine contMDiff_of_locally_contMDiffOn (fun y => ?_)
  obtain ⟨x, rfl⟩ := hsurj y
  obtain ⟨U, hUopen, hxU, hGU⟩ := h x
  exact ⟨Φt '' U, hopen U hUopen, ⟨x, hxU, rfl⟩, hGU⟩

/-- **Global inverse-slice `C³` (Route-A `hslicesC3`, backward half) from a per-point family of
temporal integral-curve comparisons.**  The inverse-slice mirror of the forward capstone
`contMDiff_flowSlice_of_forall_rawFlow_modelFlow_eqOn`: for a fixed time `t`, `ContMDiff I I 3 Gt`
for the spatial inverse `Gt` of the forward slice `Φ t` — exactly the inverse-slice `hslicesC3` datum
of `exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3` (Route A) — provided:

* the forward slice `Φ t` is *continuous* and *surjective*, and `Gt` left-inverts it globally (on a
  compact `T2` manifold these package `Φ t` as a homeomorphism, so it is an open map — the topological
  input the backward globaliser `contMDiff_symm_flowSlice_of_forall_openImage` consumes); and
* around EVERY base point `x` there is a preferred chart `p`, a *diffeomorph* model comparison flow
  `Ψ : ℝ → (E ≃ₘ^3 E)` (the shape `τ ↦ G.maps3 τ` of the model gauge-flow slice), an open window
  `Ioo a b ∋ t, t₀`, a uniform tube-Lipschitz constant `K` for the chart pushforward field, and a
  neighbourhood `U ∋ x` on which the raw flow trajectories solve the bare gauge ODE, stay in the chart,
  and are compared (integral-curve co-solution + anchor agreement) with the model flow's orbits.

Each local package yields, via the backward per-patch brick
`contMDiffOn_symm_flowSlice_of_rawFlow_modelFlow_eqOn` (whose spatial conjugation comes from the
temporal integral-curve uniqueness core `extChartAt_comp_eqOn_of_lipschitzOnWith`), the local
`ContMDiffOn I I 3 Gt (Φ t '' U)`; the open-map surjective slice `Φ t` — obtained from
`Continuous.homeoOfEquivCompactToT2` applied to the continuous bijection `Φ t` on compact `T2` `M` —
then feeds `contMDiff_symm_flowSlice_of_forall_openImage` to glue those into global `C³`.  This is the
direct bridge from "raw compact flow + model-`C³` comparison data, locally everywhere" to the
inverse-slice `C³` obligation; paired with the forward capstone it discharges both halves of
`hslicesC3`, no spatial regularity of `Φ` assumed anywhere. -/
theorem contMDiff_symm_flowSlice_of_forall_rawFlow_modelFlow_eqOn
    [CompactSpace M]
    {Φ : ℝ → M → M} {Gt : M → M} {X : ℝ → M → E} {t : ℝ}
    (hΦcont : Continuous (Φ t))
    (hΦsurj : Function.Surjective (Φ t))
    (hGleft : Function.LeftInverse Gt (Φ t))
    (h : ∀ x : M, ∃ (p : M) (Ψ : ℝ → (E ≃ₘ^3⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E)) (a b t₀ : ℝ) (K : NNReal)
        (state : ℝ → Set E) (U : Set M),
      U ∈ nhds x ∧ U ⊆ (chartAt H p).source ∧
      Set.MapsTo (Φ t) U (chartAt H p).source ∧ t ∈ Set.Ioo a b ∧ t₀ ∈ Set.Ioo a b ∧
      (∀ τ ∈ Set.Ioo a b, LipschitzOnWith K (chartPushforwardField I X p τ) (state τ)) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
        HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ : ℝ ↦ Φ τ y) (Set.Ioo a b) τ
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (Φ τ y)))) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, Φ τ y ∈ (extChartAt I p).source) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
        HasDerivAt (fun τ : ℝ ↦ (Ψ τ : E → E) (extChartAt I p y))
          (chartPushforwardField I X p τ ((Ψ τ : E → E) (extChartAt I p y))) τ) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, extChartAt I p (Φ τ y) ∈ state τ) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, (Ψ τ : E → E) (extChartAt I p y) ∈ state τ) ∧
      (∀ y ∈ U, extChartAt I p (Φ t₀ y) = (Ψ t₀ : E → E) (extChartAt I p y))) :
    ContMDiff I I 3 Gt := by
  have hbij : Function.Bijective (Φ t) := ⟨hGleft.injective, hΦsurj⟩
  have hopen : IsOpenMap (Φ t) :=
    (Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective (Φ t) hbij) hΦcont).isOpenMap
  refine contMDiff_symm_flowSlice_of_forall_openImage hopen hΦsurj (fun x => ?_)
  obtain ⟨p, Ψ, a, b, t₀, K, state, U, hUmem, hU, hΦU, ht, ht₀, hlip,
    hraw, hsrc, hg', hγ_mem, hg_mem, heq₀⟩ := h x
  refine ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.mpr hUmem, ?_⟩
  have key : ContMDiffOn I I 3 Gt (Φ t '' U) :=
    contMDiffOn_symm_flowSlice_of_rawFlow_modelFlow_eqOn
      (Φ := Φ) (Ψ := Ψ) (Gt := Gt) (p := p) (X := X) (a := a) (b := b) (t₀ := t₀) (t := t)
      (K := K) (state := state) (U := U)
      hU hΦU ht ht₀ hlip hraw hsrc hg' hγ_mem hg_mem heq₀ (fun y _ => hGleft y)
  exact key.mono (Set.image_mono interior_subset)

/-- **Both slices `C³` (Route-A `hslicesC3` conclusion, fixed time) from one per-point diffeomorph
comparison family.**  Consolidates the forward capstone
`contMDiff_flowSlice_of_forall_rawFlow_modelFlow_eqOn` and the backward capstone
`contMDiff_symm_flowSlice_of_forall_rawFlow_modelFlow_eqOn` into the exact
`ContMDiff I I 3 (Φ t) ∧ ContMDiff I I 3 Gt` shape of the `hslicesC3` conclusion of
`exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3` at a fixed time `t`.

A *single* per-base-point comparison package — carrying a genuine `C³` *diffeomorph* model flow
`Ψ : ℝ → (E ≃ₘ^3 E)` (so its underlying map is `C³` and its inverse is `C³`), together with the raw
gauge ODE, tube-Lipschitz control, integral-curve co-solution, and anchor agreement — feeds *both*
directions: the forward slice `C³` extracts `ContDiff ℝ 3 (Ψ t)` from `(Ψ t).contMDiff` and applies
the forward gluer; the inverse slice `C³` passes the same diffeomorph package (plus the compact-`T2`
homeomorphism data `Continuous`/`Surjective`/left-inverse of `Φ t`) to the backward capstone.  This is
the single-time `hslicesC3` datum; quantifying `t` over the flow window discharges both conjuncts of
`hslicesC3` from one uniform supply of per-point comparison packages. -/
theorem contMDiff_flowSlice_and_symm_of_forall_rawFlow_modelFlow_eqOn
    [CompactSpace M]
    {Φ : ℝ → M → M} {Gt : M → M} {X : ℝ → M → E} {t : ℝ}
    (hΦcont : Continuous (Φ t))
    (hΦsurj : Function.Surjective (Φ t))
    (hGleft : Function.LeftInverse Gt (Φ t))
    (h : ∀ x : M, ∃ (p : M) (Ψ : ℝ → (E ≃ₘ^3⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E)) (a b t₀ : ℝ) (K : NNReal)
        (state : ℝ → Set E) (U : Set M),
      U ∈ nhds x ∧ U ⊆ (chartAt H p).source ∧
      Set.MapsTo (Φ t) U (chartAt H p).source ∧ t ∈ Set.Ioo a b ∧ t₀ ∈ Set.Ioo a b ∧
      (∀ τ ∈ Set.Ioo a b, LipschitzOnWith K (chartPushforwardField I X p τ) (state τ)) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
        HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ : ℝ ↦ Φ τ y) (Set.Ioo a b) τ
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (Φ τ y)))) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, Φ τ y ∈ (extChartAt I p).source) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
        HasDerivAt (fun τ : ℝ ↦ (Ψ τ : E → E) (extChartAt I p y))
          (chartPushforwardField I X p τ ((Ψ τ : E → E) (extChartAt I p y))) τ) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, extChartAt I p (Φ τ y) ∈ state τ) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, (Ψ τ : E → E) (extChartAt I p y) ∈ state τ) ∧
      (∀ y ∈ U, extChartAt I p (Φ t₀ y) = (Ψ t₀ : E → E) (extChartAt I p y))) :
    ContMDiff I I 3 (Φ t) ∧ ContMDiff I I 3 Gt := by
  refine ⟨contMDiff_flowSlice_of_forall_rawFlow_modelFlow_eqOn (X := X) (Φ := Φ) (t := t)
      (fun x => ?_),
    contMDiff_symm_flowSlice_of_forall_rawFlow_modelFlow_eqOn hΦcont hΦsurj hGleft h⟩
  obtain ⟨p, Ψ, a, b, t₀, K, state, U, hUmem, hU, hΦU, ht, ht₀, hlip,
    hraw, hsrc, hg', hγ_mem, hg_mem, heq₀⟩ := h x
  exact ⟨p, fun τ => (Ψ τ : E → E), a, b, t₀, K, state, U, hUmem, hU,
    contMDiff_iff_contDiff.mp (Ψ t).contMDiff, hΦU, ht, ht₀, hlip,
    hraw, hsrc, hg', hγ_mem, hg_mem, heq₀⟩

end PoincareCurvature.GaugeFlowAssembly
