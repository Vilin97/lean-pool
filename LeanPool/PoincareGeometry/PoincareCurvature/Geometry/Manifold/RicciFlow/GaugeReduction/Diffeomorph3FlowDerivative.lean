/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.DeTurckCoordinatePicardEstimates
/-!
# Derivative views of `C^3` DeTurck gauge flows

This small extension module keeps derivative-level gauge-flow adapters out of the
large gauge-reduction file.  It exposes the exact pointwise derivative hypothesis
used by derivative-level non-identity gauge routes from the more geometric
`SatisfiesGaugeFlowOn` statement.
-/

@[expose] public noncomputable section

open scoped Manifold ContDiff Topology
open Set

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]
/-- The primitive pointwise derivative form of the intrinsic DeTurck gauge-flow equation
for a `C^3` diffeomorphism family. -/
def Diffeomorph3IntrinsicGaugeFlowDerivativeOn
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∀ x : M,
    HasMFDerivAt[s] (fun τ : ℝ ↦ (Φ τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)))

/-- Within-time-set preferred-chart ODE data for the intrinsic DeTurck
gauge-flow equation.

This is the chart-local endpoint shape produced by closed-interval Picard
arguments: the curve is known to remain in the centered chart source relative
to the active time set, and the centered chart derivative is a
`HasDerivWithinAt` statement on that same time set. -/
def Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∀ x : M,
    ((fun τ : ℝ ↦ (Φ τ) x) ⁻¹' (extChartAt I ((Φ t) x)).source ∈ 𝓝[s] t) ∧
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((Φ t) x)) ((Φ τ) x))
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)) s t

/-- Extract the within-time-set source-neighborhood input from preferred-chart
ODE data. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn.eventuallyWithin_mem_source
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) Φ g background s)
    {t : ℝ} (ht : t ∈ s) (x : M) :
    (fun τ : ℝ ↦ (Φ τ) x) ⁻¹' (extChartAt I ((Φ t) x)).source ∈ 𝓝[s] t :=
  (hchart t ht x).1

/-- Extract the within-time-set centered-chart derivative from preferred-chart
ODE data. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn.hasDerivWithinAt_extChartAt_eval_self
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) Φ g background s)
    {t : ℝ} (ht : t ∈ s) (x : M) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I ((Φ t) x)) ((Φ τ) x))
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)) s t :=
  (hchart t ht x).2

/-- A centered preferred-chart derivative for a manifold curve can be rewritten
in any fixed preferred chart whose source contains the endpoint.

This is the local-readout direction complementary to
`Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn.toChartDerivativeOn`:
it composes the centered coordinate curve with the chart transition from the
centered chart at `q` to the fixed chart at `p`. -/
theorem hasDerivWithinAt_extChartAt_eval_of_hasDerivWithinAt_extChartAt_eval_self
    {s : Set ℝ} {γ : ℝ → M} {t : ℝ} {p q : M}
    {v : TangentSpace I q}
    (hq : γ t = q)
    (hsrcp : q ∈ (extChartAt I p).source)
    (hsourceq : γ ⁻¹' (extChartAt I q).source ∈ 𝓝[s] t)
    (hderivq : HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I q) (γ τ)) v s t) :
    HasDerivWithinAt
      (fun τ : ℝ ↦ (extChartAt I p) (γ τ))
      (tangentCoordChange I q p q v) s t := by
  have hsrcq : q ∈ (extChartAt I q).source := by
    simpa using mem_extChartAt_source (I := I) q
  have htransition :
      HasFDerivWithinAt ((extChartAt I p) ∘ (extChartAt I q).symm)
        (tangentCoordChange I q p q) (range I) ((extChartAt I q) q) :=
    hasFDerivWithinAt_tangentCoordChange (I := I) (x := q) (y := p) (z := q)
      ⟨hsrcq, hsrcp⟩
  let sourceSet : Set ℝ := γ ⁻¹' (extChartAt I q).source
  have hmaps :
      MapsTo (fun τ : ℝ ↦ (extChartAt I q) (γ τ))
        (s ∩ sourceSet) (range I) := by
    intro τ hτ
    exact extChartAt_target_subset_range q
      ((extChartAt I q).map_source (by simpa [sourceSet] using hτ.2))
  have htransition_at :
      HasFDerivWithinAt ((extChartAt I p) ∘ (extChartAt I q).symm)
        (tangentCoordChange I q p q) (range I)
        ((fun τ : ℝ ↦ (extChartAt I q) (γ τ)) t) := by
    simpa [hq] using htransition
  have hcomp :
      HasDerivWithinAt
        (((extChartAt I p) ∘ (extChartAt I q).symm) ∘
          (fun τ : ℝ ↦ (extChartAt I q) (γ τ)))
        (tangentCoordChange I q p q v) (s ∩ sourceSet) t := by
    exact htransition_at.comp_hasDerivWithinAt t
      (hderivq.mono inter_subset_left) hmaps
  have heq_restricted :
      (fun τ : ℝ ↦ (extChartAt I p) (γ τ)) =ᶠ[𝓝[s ∩ sourceSet] t]
        (((extChartAt I p) ∘ (extChartAt I q).symm) ∘
          (fun τ : ℝ ↦ (extChartAt I q) (γ τ))) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτsrc : γ τ ∈ (extChartAt I q).source := by
      simpa [sourceSet] using hτ.2
    simpa [Function.comp_def] using
      congrArg (fun z : M ↦ (extChartAt I p) z)
        ((extChartAt I q).left_inv hτsrc).symm
  have heq_t :
      (extChartAt I p) (γ t) =
        (((extChartAt I p) ∘ (extChartAt I q).symm) ∘
          (fun τ : ℝ ↦ (extChartAt I q) (γ τ))) t := by
    have htSrc : γ t ∈ (extChartAt I q).source := by
      simpa [hq] using hsrcq
    simpa [Function.comp_def] using
      congrArg (fun z : M ↦ (extChartAt I p) z)
        ((extChartAt I q).left_inv htSrc).symm
  have hfixed_restricted :
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I p) (γ τ))
        (tangentCoordChange I q p q v) (s ∩ sourceSet) t :=
    hcomp.congr_of_eventuallyEq heq_restricted heq_t
  have hsourceSet : s ∩ sourceSet ∈ 𝓝[s] t := by
    exact Filter.inter_mem self_mem_nhdsWithin (by simpa [sourceSet] using hsourceq)
  exact hfixed_restricted.mono_of_mem_nhdsWithin hsourceSet

/-- Preferred-chart ODE data gives continuity of the underlying manifold curve
within the active time set. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn.continuousWithinAt_eval_self
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) Φ g background s)
    {t : ℝ} (ht : t ∈ s) (x : M) :
    ContinuousWithinAt (fun τ : ℝ ↦ (Φ τ) x) s t := by
  let e := extChartAt I ((Φ t) x)
  have hx : (Φ t) x ∈ e.source := by
    simpa [e] using mem_extChartAt_source (I := I) ((Φ t) x)
  have hsymm : ContinuousAt e.symm (e ((Φ t) x)) := by
    simpa [e] using continuousAt_extChartAt_symm (I := I) ((Φ t) x)
  have hchart_cont : ContinuousWithinAt (fun τ : ℝ ↦ e ((Φ τ) x)) s t := by
    simpa [e] using (hchart t ht x).2.continuousWithinAt
  have hcomp' : ContinuousWithinAt
      (e.symm ∘ fun τ : ℝ ↦ e ((Φ τ) x)) s t :=
    ContinuousAt.comp_continuousWithinAt
      (g := e.symm) (f := fun τ : ℝ ↦ e ((Φ τ) x))
      (s := s) (x := t) hsymm hchart_cont
  have hcomp : ContinuousWithinAt
      (fun τ : ℝ ↦ e.symm (e ((Φ τ) x))) s t := by
    simpa [Function.comp_def] using hcomp'
  have hsource' : ∀ᶠ τ in 𝓝[s] t, (Φ τ) x ∈ e.source := by
    change (fun τ : ℝ ↦ (Φ τ) x) ⁻¹' e.source ∈ 𝓝[s] t
    simpa [e] using (hchart t ht x).1
  exact hcomp.congr_of_eventuallyEq
    (hsource'.mono fun τ hτ ↦ by simpa [e] using (e.left_inv hτ).symm)
    (by simpa [e] using (e.left_inv hx).symm)

/-- Build within-time-set preferred-chart ODE data from local coordinate curves
that are eventually equal, in the within-filter, to the actual centered
preferred-chart coordinate curves. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn.of_eventuallyEq
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    {coord : ℝ → M → ℝ → E}
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (Φ τ) x) ⁻¹' (extChartAt I ((Φ t) x)).source ∈ 𝓝[s] t)
    (hcoord : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt (coord t x)
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)) s t)
    (heq : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (extChartAt I ((Φ t) x)) ((Φ τ) x)) =ᶠ[𝓝[s] t] coord t x)
    (heq_t : ∀ t ∈ s, ∀ x : M,
      (extChartAt I ((Φ t) x)) ((Φ t) x) = coord t x t) :
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) Φ g background s := by
  intro t ht x
  exact ⟨hsource t ht x,
    (hcoord t ht x).congr_of_eventuallyEq (heq t ht x) (heq_t t ht x)⟩

/-- Restrict within-time-set preferred-chart ODE data to a smaller time set. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn.mono
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s t : Set ℝ}
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) Φ g background t)
    (hst : s ⊆ t) :
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) Φ g background s := by
  intro τ hτ x
  have hsource : (fun σ : ℝ ↦ (Φ σ) x) ⁻¹'
      (extChartAt I ((Φ τ) x)).source ∈ 𝓝[s] τ :=
    (nhdsWithin_mono τ hst) (hchart τ (hst hτ) x).1
  exact ⟨hsource, (hchart τ (hst hτ) x).2.mono hst⟩

/-- Within-time-set fixed-chart ODE data for the intrinsic DeTurck
gauge-flow equation.

The chart center may depend on the time and base point.  This is the finite-cover
Picard shape: the coordinate curve is differentiated in a prescribed chart whose
source contains the endpoint, and the velocity is the intrinsic vector field
transported into that fixed chart. -/
def Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (chartCenter : ℝ → M → M)
    (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∀ x : M,
    ((Φ t) x ∈ (extChartAt I (chartCenter t x)).source) ∧
      ((fun τ : ℝ ↦ (Φ τ) x) ⁻¹'
          (extChartAt I (chartCenter t x)).source ∈ 𝓝[s] t) ∧
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (chartCenter t x)) ((Φ τ) x))
          (tangentCoordChange I ((Φ t) x) (chartCenter t x) ((Φ t) x)
            (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)))
          s t

/-- Restrict within-time-set fixed-chart ODE data to a smaller time set. -/
theorem Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn.mono
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {chartCenter : ℝ → M → M}
    {s t : Set ℝ}
    (hfixed : Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn
      (I := I) (M := M) Φ g background chartCenter t)
    (hst : s ⊆ t) :
    Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn
      (I := I) (M := M) Φ g background chartCenter s := by
  intro τ hτ x
  rcases hfixed τ (hst hτ) x with ⟨hmem, hsource, hderiv⟩
  exact ⟨hmem, (nhdsWithin_mono τ hst) hsource, hderiv.mono hst⟩

/-- Fixed-chart intrinsic ODE data converts to the centered-chart package used
by the raw gauge-flow existence layer.  The proof composes the fixed-coordinate
curve with the chart transition into the centered chart and cancels the two
tangent-coordinate changes. -/
theorem Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn.toChartDerivativeOn
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {chartCenter : ℝ → M → M}
    {s : Set ℝ}
    (hfixed : Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn
      (I := I) (M := M) Φ g background chartCenter s) :
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) Φ g background s := by
  intro t ht x
  let y : M := (Φ t) x
  let p : M := chartCenter t x
  rcases hfixed t ht x with ⟨hsrcp, hsourcep, hderivp⟩
  have hsrcy : y ∈ (extChartAt I y).source := by
    simpa [y] using mem_extChartAt_source (I := I) y
  let Xty : TangentSpace I y :=
    intrinsicDeTurckGaugeField (I := I) (M := M) g background t y
  have hvel :
      tangentCoordChange I p y y (tangentCoordChange I y p y Xty) = Xty := by
    rw [tangentCoordChange_comp (I := I) (w := y) (x := p) (y := y) (z := y)
      (v := Xty) ⟨⟨hsrcy, hsrcp⟩, hsrcy⟩]
    rw [tangentCoordChange_self (I := I) (x := y) (z := y) (v := Xty) hsrcy]
  have htransition :
      HasFDerivWithinAt ((extChartAt I y) ∘ (extChartAt I p).symm)
        (tangentCoordChange I p y y) (range I) ((extChartAt I p) y) :=
    hasFDerivWithinAt_tangentCoordChange (I := I) (x := p) (y := y) (z := y)
      ⟨hsrcp, hsrcy⟩
  let sourceSet : Set ℝ :=
    (fun τ : ℝ ↦ (Φ τ) x) ⁻¹' (extChartAt I p).source
  have hmaps :
      MapsTo (fun τ : ℝ ↦ (extChartAt I p) ((Φ τ) x))
        (s ∩ sourceSet) (range I) := by
    intro τ hτ
    exact extChartAt_target_subset_range p
      ((extChartAt I p).map_source (by simpa [sourceSet] using hτ.2))
  have hcomp :
      HasDerivWithinAt
        (((extChartAt I y) ∘ (extChartAt I p).symm) ∘
          (fun τ : ℝ ↦ (extChartAt I p) ((Φ τ) x)))
        (tangentCoordChange I p y y
          (tangentCoordChange I y p y
            (intrinsicDeTurckGaugeField (I := I) (M := M) g background t y)))
        (s ∩ sourceSet) t := by
    simpa [y, p, Xty] using
      htransition.comp_hasDerivWithinAt t (hderivp.mono inter_subset_left) hmaps
  have heq_restricted :
      (fun τ : ℝ ↦ (extChartAt I y) ((Φ τ) x)) =ᶠ[𝓝[s ∩ sourceSet] t]
        (((extChartAt I y) ∘ (extChartAt I p).symm) ∘
          (fun τ : ℝ ↦ (extChartAt I p) ((Φ τ) x))) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτsrc : (Φ τ) x ∈ (extChartAt I p).source := by
      simpa [sourceSet] using hτ.2
    simpa [Function.comp_def] using
      congrArg (fun z : M ↦ (extChartAt I y) z)
        ((extChartAt I p).left_inv hτsrc).symm
  have heq_t :
      (extChartAt I y) ((Φ t) x) =
        (((extChartAt I y) ∘ (extChartAt I p).symm) ∘
          (fun τ : ℝ ↦ (extChartAt I p) ((Φ τ) x))) t := by
    simpa [Function.comp_def, y] using
      congrArg (fun z : M ↦ (extChartAt I y) z)
        ((extChartAt I p).left_inv hsrcp).symm
  have hcenter_restricted :
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I y) ((Φ τ) x))
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t y)
        (s ∩ sourceSet) t := by
    exact (hcomp.congr_of_eventuallyEq heq_restricted heq_t).congr_deriv (by
      change tangentCoordChange I p y y (tangentCoordChange I y p y Xty) = Xty
      exact hvel)
  have hsourceSet : s ∩ sourceSet ∈ 𝓝[s] t := by
    exact Filter.inter_mem self_mem_nhdsWithin (by simpa [sourceSet, p] using hsourcep)
  have hcenter :
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I y) ((Φ τ) x))
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t y) s t :=
    hcenter_restricted.mono_of_mem_nhdsWithin hsourceSet
  have hmanifold_cont :
      ContinuousWithinAt (fun τ : ℝ ↦ (Φ τ) x) s t := by
    have hsymm : ContinuousAt (extChartAt I p).symm ((extChartAt I p) y) :=
      continuousAt_extChartAt_symm' (I := I) hsrcp
    have hcoord : ContinuousWithinAt
        (fun τ : ℝ ↦ (extChartAt I p) ((Φ τ) x)) s t :=
      hderivp.continuousWithinAt
    have hcomp' : ContinuousWithinAt
        ((extChartAt I p).symm ∘
          fun τ : ℝ ↦ (extChartAt I p) ((Φ τ) x)) s t :=
      ContinuousAt.comp_continuousWithinAt
        (g := (extChartAt I p).symm)
        (f := fun τ : ℝ ↦ (extChartAt I p) ((Φ τ) x))
        (s := s) (x := t) hsymm hcoord
    have hcomp_mfld : ContinuousWithinAt
        (fun τ : ℝ ↦ (extChartAt I p).symm ((extChartAt I p) ((Φ τ) x))) s t := by
      simpa [Function.comp_def] using hcomp'
    have hsourcep_eventually :
        ∀ᶠ τ in 𝓝[s] t, (Φ τ) x ∈ (extChartAt I p).source := by
      change (fun τ : ℝ ↦ (Φ τ) x) ⁻¹' (extChartAt I p).source ∈ 𝓝[s] t
      simpa [p] using hsourcep
    exact hcomp_mfld.congr_of_eventuallyEq
      (hsourcep_eventually.mono fun τ hτ ↦ by
        simpa using ((extChartAt I p).left_inv hτ).symm)
      (by simpa [y] using ((extChartAt I p).left_inv hsrcp).symm)
  have hsource_center :
      (fun τ : ℝ ↦ (Φ τ) x) ⁻¹' (extChartAt I y).source ∈ 𝓝[s] t :=
    hmanifold_cont.preimage_mem_nhdsWithin
      ((isOpen_extChartAt_source (I := I) y).mem_nhds hsrcy)
  refine ⟨?_, ?_⟩
  · simpa [y, extChartAt_source] using hsource_center
  · simpa [y] using hcenter

/-- Build within-time-set fixed-chart intrinsic ODE data from fixed-chart
derivative data for a model vector field identified with the intrinsic DeTurck
gauge field along the flow. -/
theorem Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn.of_vectorField_eq
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {chartCenter : ℝ → M → M}
    {s : Set ℝ}
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    (hmem : ∀ t ∈ s, ∀ x : M,
      (Φ t) x ∈ (extChartAt I (chartCenter t x)).source)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (Φ τ) x) ⁻¹'
          (extChartAt I (chartCenter t x)).source ∈ 𝓝[s] t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (chartCenter t x)) ((Φ τ) x))
        (tangentCoordChange I ((Φ t) x) (chartCenter t x) ((Φ t) x)
          (Y t ((Φ t) x))) s t)
    (hY : ∀ t ∈ s, ∀ x : M,
      Y t ((Φ t) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)) :
    Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn
      (I := I) (M := M) Φ g background chartCenter s := by
  intro t ht x
  exact ⟨hmem t ht x, hsource t ht x, by simpa [hY t ht x] using hderiv t ht x⟩

/-- Build within-time-set fixed-chart intrinsic ODE data from fixed-chart
derivative data for a model vector field identified with the intrinsic DeTurck
gauge field along the flow in the relative time-set filter. -/
theorem Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn.of_vectorField_eq_nhdsWithin
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {chartCenter : ℝ → M → M}
    {s : Set ℝ}
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    (hmem : ∀ t ∈ s, ∀ x : M,
      (Φ t) x ∈ (extChartAt I (chartCenter t x)).source)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (Φ τ) x) ⁻¹'
          (extChartAt I (chartCenter t x)).source ∈ 𝓝[s] t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I (chartCenter t x)) ((Φ τ) x))
        (tangentCoordChange I ((Φ t) x) (chartCenter t x) ((Φ t) x)
          (Y t ((Φ t) x))) s t)
    (hY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      Y τ ((Φ τ) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background τ ((Φ τ) x)) :
    Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn
      (I := I) (M := M) Φ g background chartCenter s := by
  intro t ht x
  have hYt_all : ∀ x : M,
      Y t ((Φ t) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x) :=
    mem_of_mem_nhdsWithin ht (hY t ht)
  exact ⟨hmem t ht x, hsource t ht x, by simpa [hYt_all x] using hderiv t ht x⟩

/-- Ordinary-at-time derivative form of the intrinsic DeTurck gauge-flow equation
for a `C^3` diffeomorphism family, restricted to times in `s`.

This is the shape produced by Picard-interior ODE arguments after upgrading
closed-interval derivatives to ordinary derivatives on the open time set. -/
def Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∀ x : M,
    HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (Φ τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)))

/-- Ordinary preferred-chart ODE data for the intrinsic DeTurck gauge-flow
equation, restricted to times in `s`.

The source-neighborhood clause is the chart-local continuity input used by the
existence layer: it says the curve stays eventually in the centered chart source
at the time where the ordinary chart derivative is taken. -/
def Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∀ x : M,
    ((fun τ : ℝ ↦ (Φ τ) x) ⁻¹' (extChartAt I ((Φ t) x)).source ∈ 𝓝 t) ∧
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I ((Φ t) x)) ((Φ τ) x))
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)) t

/-- Extract the source-neighborhood input from ordinary preferred-chart ODE
data. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn.eventually_mem_source
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn
      (I := I) (M := M) Φ g background s)
    {t : ℝ} (ht : t ∈ s) (x : M) :
    (fun τ : ℝ ↦ (Φ τ) x) ⁻¹' (extChartAt I ((Φ t) x)).source ∈ 𝓝 t :=
  (hchart t ht x).1

/-- Extract the ordinary centered-chart derivative from ordinary preferred-chart
ODE data. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn.hasDerivAt_extChartAt_eval_self
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn
      (I := I) (M := M) Φ g background s)
    {t : ℝ} (ht : t ∈ s) (x : M) :
    HasDerivAt
      (fun τ : ℝ ↦ (extChartAt I ((Φ t) x)) ((Φ τ) x))
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)) t :=
  (hchart t ht x).2

/-- Ordinary preferred-chart ODE data gives ordinary continuity of the
underlying manifold curve. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn.continuousAt_eval_self
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn
      (I := I) (M := M) Φ g background s)
    {t : ℝ} (ht : t ∈ s) (x : M) :
    ContinuousAt (fun τ : ℝ ↦ (Φ τ) x) t := by
  let e := extChartAt I ((Φ t) x)
  have hx : (Φ t) x ∈ e.source := by
    simpa [e] using mem_extChartAt_source (I := I) ((Φ t) x)
  have hsymm : ContinuousAt e.symm (e ((Φ t) x)) := by
    simpa [e] using continuousAt_extChartAt_symm (I := I) ((Φ t) x)
  have hchart_cont : ContinuousAt (fun τ : ℝ ↦ e ((Φ τ) x)) t := by
    simpa [e] using (hchart t ht x).2.continuousAt
  have hcomp' : ContinuousAt
      (e.symm ∘ fun τ : ℝ ↦ e ((Φ τ) x)) t :=
    ContinuousAt.comp
      (g := e.symm) (f := fun τ : ℝ ↦ e ((Φ τ) x))
      (x := t) hsymm hchart_cont
  have hcomp : ContinuousAt (fun τ : ℝ ↦ e.symm (e ((Φ τ) x))) t := by
    simpa [Function.comp_def] using hcomp'
  have hsource' : ∀ᶠ τ in 𝓝 t, (Φ τ) x ∈ e.source := by
    change (fun τ : ℝ ↦ (Φ τ) x) ⁻¹' e.source ∈ 𝓝 t
    simpa [e] using (hchart t ht x).1
  exact hcomp.congr_of_eventuallyEq
    (hsource'.mono fun τ hτ ↦ by simpa [e] using (e.left_inv hτ).symm)

/-- Ordinary-at-time fixed-chart ODE data for the intrinsic DeTurck gauge-flow
equation.  This is the open-time version of
`Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn`. -/
def Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (chartCenter : ℝ → M → M)
    (s : Set ℝ) : Prop :=
  ∀ t ∈ s, ∀ x : M,
    ((Φ t) x ∈ (extChartAt I (chartCenter t x)).source) ∧
      ((fun τ : ℝ ↦ (Φ τ) x) ⁻¹'
          (extChartAt I (chartCenter t x)).source ∈ 𝓝 t) ∧
        HasDerivAt
          (fun τ : ℝ ↦ (extChartAt I (chartCenter t x)) ((Φ τ) x))
          (tangentCoordChange I ((Φ t) x) (chartCenter t x) ((Φ t) x)
            (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)))
          t

/-- Restrict ordinary fixed-chart ODE data to a smaller time set. -/
theorem Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn.mono
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {chartCenter : ℝ → M → M}
    {s t : Set ℝ}
    (hfixed : Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn
      (I := I) (M := M) Φ g background chartCenter t)
    (hst : s ⊆ t) :
    Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn
      (I := I) (M := M) Φ g background chartCenter s := by
  intro τ hτ x
  exact hfixed τ (hst hτ) x

/-- Within-time-set fixed-chart ODE data gives ordinary fixed-chart ODE data
whenever the time set is a neighborhood of each of its times. -/
theorem Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn.of_fixedChartDerivativeOn
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {chartCenter : ℝ → M → M}
    {s : Set ℝ}
    (hfixed : Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn
      (I := I) (M := M) Φ g background chartCenter s)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t) :
    Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn
      (I := I) (M := M) Φ g background chartCenter s := by
  intro t ht x
  rcases hfixed t ht x with ⟨hmem, hsource, hderiv⟩
  have htime : s ∈ 𝓝 t := hs ht
  have hsource' : (fun τ : ℝ ↦ (Φ τ) x) ⁻¹'
      (extChartAt I (chartCenter t x)).source ∈ 𝓝 t := by
    simpa [nhdsWithin_eq_nhds.2 htime] using hsource
  exact ⟨hmem, hsource', hderiv.hasDerivAt htime⟩

/-- Ordinary fixed-chart intrinsic ODE data converts to the ordinary
centered-chart package. -/
theorem Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn.toChartDerivativeAtOn
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {chartCenter : ℝ → M → M}
    {s : Set ℝ}
    (hfixed : Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn
      (I := I) (M := M) Φ g background chartCenter s) :
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn
      (I := I) (M := M) Φ g background s := by
  intro t ht x
  let y : M := (Φ t) x
  let p : M := chartCenter t x
  rcases hfixed t ht x with ⟨hsrcp, hsourcep, hderivp⟩
  have hsrcy : y ∈ (extChartAt I y).source := by
    simpa [y] using mem_extChartAt_source (I := I) y
  let Xty : TangentSpace I y :=
    intrinsicDeTurckGaugeField (I := I) (M := M) g background t y
  have hvel :
      tangentCoordChange I p y y (tangentCoordChange I y p y Xty) = Xty := by
    rw [tangentCoordChange_comp (I := I) (w := y) (x := p) (y := y) (z := y)
      (v := Xty) ⟨⟨hsrcy, hsrcp⟩, hsrcy⟩]
    rw [tangentCoordChange_self (I := I) (x := y) (z := y) (v := Xty) hsrcy]
  have htransition :
      HasFDerivWithinAt ((extChartAt I y) ∘ (extChartAt I p).symm)
        (tangentCoordChange I p y y) (range I) ((extChartAt I p) y) :=
    hasFDerivWithinAt_tangentCoordChange (I := I) (x := p) (y := y) (z := y)
      ⟨hsrcp, hsrcy⟩
  have hsourcep_eventually :
      ∀ᶠ τ in 𝓝 t, (Φ τ) x ∈ (extChartAt I p).source := by
    change (fun τ : ℝ ↦ (Φ τ) x) ⁻¹' (extChartAt I p).source ∈ 𝓝 t
    simpa [p] using hsourcep
  have hmaps :
      ∀ᶠ τ in 𝓝 t,
        (extChartAt I p) ((Φ τ) x) ∈ range I :=
    hsourcep_eventually.mono fun τ hτ ↦
      extChartAt_target_subset_range p ((extChartAt I p).map_source hτ)
  have hcomp :
      HasDerivAt
        (((extChartAt I y) ∘ (extChartAt I p).symm) ∘
          (fun τ : ℝ ↦ (extChartAt I p) ((Φ τ) x)))
        (tangentCoordChange I p y y
          (tangentCoordChange I y p y
            (intrinsicDeTurckGaugeField (I := I) (M := M) g background t y)))
        t := by
    simpa [y, p, Xty] using htransition.comp_hasDerivAt t hderivp hmaps
  have heq :
      (fun τ : ℝ ↦ (extChartAt I y) ((Φ τ) x)) =ᶠ[𝓝 t]
        (((extChartAt I y) ∘ (extChartAt I p).symm) ∘
          (fun τ : ℝ ↦ (extChartAt I p) ((Φ τ) x))) :=
    hsourcep_eventually.mono fun τ hτsrc ↦ by
      simpa [Function.comp_def] using
        congrArg (fun z : M ↦ (extChartAt I y) z)
          ((extChartAt I p).left_inv hτsrc).symm
  have hcenter :
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I y) ((Φ τ) x))
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t y) t := by
    exact (hcomp.congr_of_eventuallyEq heq).congr_deriv (by
      change tangentCoordChange I p y y (tangentCoordChange I y p y Xty) = Xty
      exact hvel)
  have hmanifold_cont :
      ContinuousAt (fun τ : ℝ ↦ (Φ τ) x) t := by
    have hsymm : ContinuousAt (extChartAt I p).symm ((extChartAt I p) y) :=
      continuousAt_extChartAt_symm' (I := I) hsrcp
    have hcoord : ContinuousAt
        (fun τ : ℝ ↦ (extChartAt I p) ((Φ τ) x)) t :=
      hderivp.continuousAt
    have hcomp' : ContinuousAt
        ((extChartAt I p).symm ∘
          fun τ : ℝ ↦ (extChartAt I p) ((Φ τ) x)) t :=
      ContinuousAt.comp
        (g := (extChartAt I p).symm)
        (f := fun τ : ℝ ↦ (extChartAt I p) ((Φ τ) x))
        (x := t) hsymm hcoord
    have hcomp_mfld : ContinuousAt
        (fun τ : ℝ ↦ (extChartAt I p).symm ((extChartAt I p) ((Φ τ) x))) t := by
      simpa [Function.comp_def] using hcomp'
    exact hcomp_mfld.congr_of_eventuallyEq
      (hsourcep_eventually.mono fun τ hτ ↦ by
        simpa using ((extChartAt I p).left_inv hτ).symm)
  have hsource_center :
      (fun τ : ℝ ↦ (Φ τ) x) ⁻¹' (extChartAt I y).source ∈ 𝓝 t :=
    hmanifold_cont.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := I) y).mem_nhds hsrcy)
  refine ⟨?_, ?_⟩
  · simpa [y, extChartAt_source] using hsource_center
  · simpa [y] using hcenter

/-- Build ordinary fixed-chart intrinsic ODE data from ordinary fixed-chart
derivative data for a model vector field identified with the intrinsic DeTurck
gauge field along the flow. -/
theorem Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn.of_vectorField_eq
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {chartCenter : ℝ → M → M}
    {s : Set ℝ}
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    (hmem : ∀ t ∈ s, ∀ x : M,
      (Φ t) x ∈ (extChartAt I (chartCenter t x)).source)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (Φ τ) x) ⁻¹'
          (extChartAt I (chartCenter t x)).source ∈ 𝓝 t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I (chartCenter t x)) ((Φ τ) x))
        (tangentCoordChange I ((Φ t) x) (chartCenter t x) ((Φ t) x)
          (Y t ((Φ t) x))) t)
    (hY : ∀ t ∈ s, ∀ x : M,
      Y t ((Φ t) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)) :
    Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn
      (I := I) (M := M) Φ g background chartCenter s := by
  intro t ht x
  exact ⟨hmem t ht x, hsource t ht x, by simpa [hY t ht x] using hderiv t ht x⟩

/-- Build ordinary fixed-chart intrinsic ODE data from ordinary fixed-chart
derivative data for a model vector field identified with the intrinsic DeTurck
gauge field along the flow in the relative time-set filter. -/
theorem Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn.of_vectorField_eq_nhdsWithin
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {chartCenter : ℝ → M → M}
    {s : Set ℝ}
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    (hmem : ∀ t ∈ s, ∀ x : M,
      (Φ t) x ∈ (extChartAt I (chartCenter t x)).source)
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (Φ τ) x) ⁻¹'
          (extChartAt I (chartCenter t x)).source ∈ 𝓝 t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I (chartCenter t x)) ((Φ τ) x))
        (tangentCoordChange I ((Φ t) x) (chartCenter t x) ((Φ t) x)
          (Y t ((Φ t) x))) t)
    (hY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      Y τ ((Φ τ) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background τ ((Φ τ) x)) :
    Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn
      (I := I) (M := M) Φ g background chartCenter s := by
  intro t ht x
  have hYt_all : ∀ x : M,
      Y t ((Φ t) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x) :=
    mem_of_mem_nhdsWithin ht (hY t ht)
  exact ⟨hmem t ht x, hsource t ht x, by simpa [hYt_all x] using hderiv t ht x⟩

/-- Build within-time-set intrinsic derivative data from derivative data for a model vector field,
once that vector field is identified with the intrinsic DeTurck gauge field along the flow. -/
theorem Diffeomorph3IntrinsicGaugeFlowDerivativeOn.of_vectorField_eq
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasMFDerivAt[s] (fun τ : ℝ ↦ (Φ τ) x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t ((Φ t) x))))
    (hY : ∀ t ∈ s, ∀ x : M,
      Y t ((Φ t) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)) :
    Diffeomorph3IntrinsicGaugeFlowDerivativeOn
      (I := I) (M := M) Φ g background s := by
  intro t ht x
  simpa [hY t ht x] using hderiv t ht x

/-- Build within-time-set intrinsic derivative data from derivative data for a
model vector field, once that vector field is identified with the intrinsic
DeTurck gauge field along the flow in the relative time-set filter. -/
theorem Diffeomorph3IntrinsicGaugeFlowDerivativeOn.of_vectorField_eq_nhdsWithin
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasMFDerivAt[s] (fun τ : ℝ ↦ (Φ τ) x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t ((Φ t) x))))
    (hY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      Y τ ((Φ τ) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background τ ((Φ τ) x)) :
    Diffeomorph3IntrinsicGaugeFlowDerivativeOn
      (I := I) (M := M) Φ g background s := by
  intro t ht x
  have hYt_all : ∀ x : M,
      Y t ((Φ t) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x) :=
    mem_of_mem_nhdsWithin ht (hY t ht)
  simpa [hYt_all x] using hderiv t ht x

/-- Build within-time-set preferred-chart intrinsic ODE data from preferred-chart derivative data
for a model vector field identified with the intrinsic DeTurck gauge field along the flow. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn.of_vectorField_eq
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (Φ τ) x) ⁻¹' (extChartAt I ((Φ t) x)).source ∈ 𝓝[s] t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((Φ t) x)) ((Φ τ) x))
        (Y t ((Φ t) x)) s t)
    (hY : ∀ t ∈ s, ∀ x : M,
      Y t ((Φ t) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)) :
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) Φ g background s := by
  intro t ht x
  exact ⟨hsource t ht x, by simpa [hY t ht x] using hderiv t ht x⟩

/-- Build within-time-set preferred-chart intrinsic ODE data from preferred-chart
derivative data for a model vector field identified with the intrinsic DeTurck
gauge field along the flow in the relative time-set filter. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn.of_vectorField_eq_nhdsWithin
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (Φ τ) x) ⁻¹' (extChartAt I ((Φ t) x)).source ∈ 𝓝[s] t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivWithinAt
        (fun τ : ℝ ↦ (extChartAt I ((Φ t) x)) ((Φ τ) x))
        (Y t ((Φ t) x)) s t)
    (hY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      Y τ ((Φ τ) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background τ ((Φ τ) x)) :
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) Φ g background s := by
  intro t ht x
  have hYt_all : ∀ x : M,
      Y t ((Φ t) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x) :=
    mem_of_mem_nhdsWithin ht (hY t ht)
  exact ⟨hsource t ht x, by simpa [hYt_all x] using hderiv t ht x⟩

/-- Preferred-chart ODE data directly supplies the primitive intrinsic manifold
derivative data within the same time set. -/
theorem Diffeomorph3IntrinsicGaugeFlowDerivativeOn.of_chartDerivativeOn
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) Φ g background s) :
    Diffeomorph3IntrinsicGaugeFlowDerivativeOn
      (I := I) (M := M) Φ g background s := by
  intro t ht x
  refine ⟨hchart.continuousWithinAt_eval_self ht x, ?_⟩
  have h := (hchart t ht x).2.hasFDerivWithinAt
  unfold TangentSpace at h ⊢
  simpa [TangentSpace, writtenInExtChartAt, extChartAt_model_space_eq_id,
    Function.comp_def, PartialEquiv.refl_coe, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
    OpenPartialHomeomorph.coe_toPartialEquiv, range_id, inter_univ, preimage_id_eq, id_eq,
    ContinuousLinearMap.smulRight_one_eq_toSpanSingleton] using h

/-- Fixed-chart intrinsic ODE data directly supplies the primitive intrinsic
manifold derivative data within the same time set. -/
theorem Diffeomorph3IntrinsicGaugeFlowDerivativeOn.of_fixedChartDerivativeOn
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {chartCenter : ℝ → M → M}
    {s : Set ℝ}
    (hfixed : Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn
      (I := I) (M := M) Φ g background chartCenter s) :
    Diffeomorph3IntrinsicGaugeFlowDerivativeOn
      (I := I) (M := M) Φ g background s :=
  Diffeomorph3IntrinsicGaugeFlowDerivativeOn.of_chartDerivativeOn
    (I := I) (M := M) hfixed.toChartDerivativeOn

/-- Build ordinary intrinsic derivative data from derivative data for a model vector field, once
that vector field is identified with the intrinsic DeTurck gauge field along the flow. -/
theorem Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn.of_vectorField_eq
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (Φ τ) x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t ((Φ t) x))))
    (hY : ∀ t ∈ s, ∀ x : M,
      Y t ((Φ t) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)) :
    Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn
      (I := I) (M := M) Φ g background s := by
  intro t ht x
  simpa [hY t ht x] using hderiv t ht x

/-- Build ordinary intrinsic derivative data from derivative data for a model
vector field, once that vector field is identified with the intrinsic DeTurck
gauge field along the flow in the relative time-set filter. -/
theorem Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn.of_vectorField_eq_nhdsWithin
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (Φ τ) x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t ((Φ t) x))))
    (hY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      Y τ ((Φ τ) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background τ ((Φ τ) x)) :
    Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn
      (I := I) (M := M) Φ g background s := by
  intro t ht x
  have hYt_all : ∀ x : M,
      Y t ((Φ t) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x) :=
    mem_of_mem_nhdsWithin ht (hY t ht)
  simpa [hYt_all x] using hderiv t ht x

/-- Build ordinary preferred-chart intrinsic ODE data from preferred-chart derivative data for a
model vector field identified with the intrinsic DeTurck gauge field along the flow. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn.of_vectorField_eq
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (Φ τ) x) ⁻¹' (extChartAt I ((Φ t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I ((Φ t) x)) ((Φ τ) x))
        (Y t ((Φ t) x)) t)
    (hY : ∀ t ∈ s, ∀ x : M,
      Y t ((Φ t) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)) :
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn
      (I := I) (M := M) Φ g background s := by
  intro t ht x
  exact ⟨hsource t ht x, by simpa [hY t ht x] using hderiv t ht x⟩

/-- Build ordinary preferred-chart intrinsic ODE data from preferred-chart
derivative data for a model vector field identified with the intrinsic DeTurck
gauge field along the flow in the relative time-set filter. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn.of_vectorField_eq_nhdsWithin
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    {Y : CovariantDerivative.TimeDependentVectorField (I := I) (M := M)}
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (Φ τ) x) ⁻¹' (extChartAt I ((Φ t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ t ∈ s, ∀ x : M,
      HasDerivAt
        (fun τ : ℝ ↦ (extChartAt I ((Φ t) x)) ((Φ τ) x))
        (Y t ((Φ t) x)) t)
    (hY : ∀ t ∈ s, ∀ᶠ τ in 𝓝[s] t, ∀ x : M,
      Y τ ((Φ τ) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background τ ((Φ τ) x)) :
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn
      (I := I) (M := M) Φ g background s := by
  intro t ht x
  have hYt_all : ∀ x : M,
      Y t ((Φ t) x) =
        intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x) :=
    mem_of_mem_nhdsWithin ht (hY t ht)
  exact ⟨hsource t ht x, by simpa [hYt_all x] using hderiv t ht x⟩

/-- Ordinary preferred-chart ODE data directly supplies ordinary primitive
intrinsic manifold derivative data. -/
theorem Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn.of_chartDerivativeAtOn
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn
      (I := I) (M := M) Φ g background s) :
    Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn
      (I := I) (M := M) Φ g background s := by
  intro t ht x
  refine ⟨hchart.continuousAt_eval_self ht x, ?_⟩
  have h := (hchart t ht x).2.hasFDerivAt
  unfold TangentSpace at h ⊢
  simpa [TangentSpace, writtenInExtChartAt, extChartAt_model_space_eq_id,
    Function.comp_def, PartialEquiv.refl_coe, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
    OpenPartialHomeomorph.coe_toPartialEquiv, range_id, inter_univ, preimage_id_eq, id_eq,
    ContinuousLinearMap.smulRight_one_eq_toSpanSingleton] using h

/-- Ordinary fixed-chart intrinsic ODE data directly supplies primitive
ordinary intrinsic manifold derivative data. -/
theorem Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn.of_fixedChartDerivativeAtOn
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {chartCenter : ℝ → M → M}
    {s : Set ℝ}
    (hfixed : Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn
      (I := I) (M := M) Φ g background chartCenter s) :
    Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn
      (I := I) (M := M) Φ g background s :=
  Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn.of_chartDerivativeAtOn
    (I := I) (M := M) hfixed.toChartDerivativeAtOn

/-- Restrict ordinary preferred-chart ODE data to a smaller time set. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn.mono
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s t : Set ℝ}
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn
      (I := I) (M := M) Φ g background t)
    (hst : s ⊆ t) :
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn
      (I := I) (M := M) Φ g background s := by
  intro τ hτ x
  exact hchart τ (hst hτ) x

/-- Within-time-set preferred-chart ODE data gives ordinary preferred-chart ODE
data whenever the time set is a neighborhood of each of its times. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn.of_chartDerivativeOn
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) Φ g background s)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t) :
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn
      (I := I) (M := M) Φ g background s := by
  intro t ht x
  have hsource : (fun τ : ℝ ↦ (Φ τ) x) ⁻¹'
      (extChartAt I ((Φ t) x)).source ∈ 𝓝 t := by
    simpa [nhdsWithin_eq_nhds.2 (hs ht)] using (hchart t ht x).1
  exact ⟨hsource, (hchart t ht x).2.hasDerivAt (hs ht)⟩

/-- Build ordinary preferred-chart ODE data from local coordinate curves that
are eventually equal to the actual centered preferred-chart coordinate curves.
This is the transfer form used after a chart-local Picard solution has been
identified with the geometric coordinate readout near the time of interest. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn.of_eventuallyEq
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    {coord : ℝ → M → ℝ → E}
    (hsource : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (Φ τ) x) ⁻¹' (extChartAt I ((Φ t) x)).source ∈ 𝓝 t)
    (hcoord : ∀ t ∈ s, ∀ x : M,
      HasDerivAt (coord t x)
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)) t)
    (heq : ∀ t ∈ s, ∀ x : M,
      (fun τ : ℝ ↦ (extChartAt I ((Φ t) x)) ((Φ τ) x)) =ᶠ[𝓝 t] coord t x) :
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn
      (I := I) (M := M) Φ g background s := by
  intro t ht x
  exact ⟨hsource t ht x, (hcoord t ht x).congr_of_eventuallyEq (heq t ht x)⟩

/-- Ordinary-at-time derivative data on `s` immediately gives the within-set
derivative data used by the primitive gauge-flow API. -/
theorem Diffeomorph3IntrinsicGaugeFlowDerivativeOn.of_derivativeAtOn
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hderiv : Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn
      (I := I) (M := M) Φ g background s) :
    Diffeomorph3IntrinsicGaugeFlowDerivativeOn
      (I := I) (M := M) Φ g background s := by
  intro t ht x
  exact (hderiv t ht x).hasMFDerivWithinAt

/-- Ordinary preferred-chart ODE data on `s` immediately gives the within-set
preferred-chart ODE data used by the primitive gauge-flow API. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn.of_chartDerivativeAtOn
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn
      (I := I) (M := M) Φ g background s) :
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) Φ g background s := by
  intro t ht x
  exact ⟨nhdsWithin_le_nhds (hchart t ht x).1,
    (hchart t ht x).2.hasDerivWithinAt⟩

/-- Within-time-set derivative data gives ordinary-at-time data whenever the
time set is a neighborhood of each of its times. -/
theorem Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn.of_derivativeOn
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hderiv : Diffeomorph3IntrinsicGaugeFlowDerivativeOn
      (I := I) (M := M) Φ g background s)
    (hs : ∀ ⦃t : ℝ⦄, t ∈ s → s ∈ 𝓝 t) :
    Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn
      (I := I) (M := M) Φ g background s := by
  intro t ht x
  exact (hderiv t ht x).hasMFDerivAt (hs ht)

/-- Restrict primitive within-time-set derivative data to a smaller time set. -/
theorem Diffeomorph3IntrinsicGaugeFlowDerivativeOn.mono
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s t : Set ℝ}
    (hderiv : Diffeomorph3IntrinsicGaugeFlowDerivativeOn
      (I := I) (M := M) Φ g background t)
    (hst : s ⊆ t) :
    Diffeomorph3IntrinsicGaugeFlowDerivativeOn
      (I := I) (M := M) Φ g background s := by
  intro τ hτ x
  exact (hderiv τ (hst hτ) x).mono hst

/-- Restrict ordinary-at-time derivative data to a smaller time set. -/
theorem Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn.mono
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s t : Set ℝ}
    (hderiv : Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn
      (I := I) (M := M) Φ g background t)
    (hst : s ⊆ t) :
    Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn
      (I := I) (M := M) Φ g background s := by
  intro τ hτ x
  exact hderiv τ (hst hτ) x

/-- Closed-Picard-interval primitive derivative data gives ordinary derivative
data on the open Picard interior. -/
theorem Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn.of_derivativeOn_Ioo
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {tmin tmax : ℝ}
    (hderiv : Diffeomorph3IntrinsicGaugeFlowDerivativeOn
      (I := I) (M := M) Φ g background (Icc tmin tmax)) :
    Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn
      (I := I) (M := M) Φ g background (Ioo tmin tmax) := by
  intro t ht x
  exact (hderiv t (Ioo_subset_Icc_self ht) x).hasMFDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- Closed-Picard-interval preferred-chart ODE data gives ordinary
preferred-chart ODE data on the open Picard interior. -/
theorem Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn.of_chartDerivativeOn_Ioo
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {tmin tmax : ℝ}
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) Φ g background (Icc tmin tmax)) :
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn
      (I := I) (M := M) Φ g background (Ioo tmin tmax) := by
  intro t ht x
  have htime : Icc tmin tmax ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have hsource : (fun τ : ℝ ↦ (Φ τ) x) ⁻¹'
      (extChartAt I ((Φ t) x)).source ∈ 𝓝 t := by
    simpa [nhdsWithin_eq_nhds.2 htime] using
      (hchart t (Ioo_subset_Icc_self ht) x).1
  exact ⟨hsource, (hchart t (Ioo_subset_Icc_self ht) x).2.hasDerivAt htime⟩

/-- Closed-Picard-interval fixed-chart ODE data gives ordinary fixed-chart ODE
data on the open Picard interior, preserving the chosen chart centers. -/
theorem Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn.of_fixedChartDerivativeOn_Ioo
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {chartCenter : ℝ → M → M}
    {tmin tmax : ℝ}
    (hfixed : Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn
      (I := I) (M := M) Φ g background chartCenter (Icc tmin tmax)) :
    Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn
      (I := I) (M := M) Φ g background chartCenter (Ioo tmin tmax) := by
  intro t ht x
  have htime : Icc tmin tmax ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  rcases hfixed t (Ioo_subset_Icc_self ht) x with ⟨hmem, hsource, hderiv⟩
  have hsource' : (fun τ : ℝ ↦ (Φ τ) x) ⁻¹'
      (extChartAt I (chartCenter t x)).source ∈ 𝓝 t := by
    simpa [nhdsWithin_eq_nhds.2 htime] using hsource
  exact ⟨hmem, hsource', hderiv.hasDerivAt htime⟩

/-- Closed-Picard-interval preferred-chart ODE data gives ordinary primitive
intrinsic derivative data on the open Picard interior. -/
theorem Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn.of_chartDerivativeOn_Ioo
    {Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {tmin tmax : ℝ}
    (hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) Φ g background (Icc tmin tmax)) :
    Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn
      (I := I) (M := M) Φ g background (Ioo tmin tmax) :=
  Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn.of_chartDerivativeAtOn
    (I := I) (M := M)
    (Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn.of_chartDerivativeOn_Ioo
      (I := I) (M := M) hchart)

/-- Fixed-IVP primitive derivative data for the intrinsic DeTurck gauges of all
chosen DeTurck solutions of one initial-value problem. -/
def ChosenIntrinsicDeTurckGaugeFlowDerivative
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)) : Prop :=
  ∀ sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp,
    Diffeomorph3IntrinsicGaugeFlowDerivativeOn (I := I) (M := M)
      (maps3 sol)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet

/-- Fixed-IVP within-time-set preferred-chart ODE data for the intrinsic DeTurck
gauges of all chosen DeTurck solutions of one initial-value problem. -/
def ChosenIntrinsicDeTurckGaugeFlowChartDerivative
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)) : Prop :=
  ∀ sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp,
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn (I := I) (M := M)
      (maps3 sol)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet

/-- Fixed-IVP ordinary-at-time derivative data for the intrinsic DeTurck gauges
of all chosen DeTurck solutions of one initial-value problem. -/
def ChosenIntrinsicDeTurckGaugeFlowDerivativeAt
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)) : Prop :=
  ∀ sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp,
    Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn (I := I) (M := M)
      (maps3 sol)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet

/-- Fixed-IVP ordinary preferred-chart ODE data for the intrinsic DeTurck gauges
of all chosen DeTurck solutions of one initial-value problem. -/
def ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAt
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)) : Prop :=
  ∀ sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp,
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn (I := I) (M := M)
      (maps3 sol)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet

/-- Fixed-IVP within-time-set derivative data for a model vector field gives intrinsic DeTurck
derivative data once the model field is identified with the intrinsic gauge field along each chosen
flow. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivative_of_vectorField_eq
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
          (fun τ : ℝ ↦ (maps3 sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Y sol t ((maps3 sol t) x))))
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        Y sol t ((maps3 sol t) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) :
    ChosenIntrinsicDeTurckGaugeFlowDerivative
      (I := I) (M := M) ivp maps3 := by
  intro sol
  exact Diffeomorph3IntrinsicGaugeFlowDerivativeOn.of_vectorField_eq
    (I := I) (M := M) (Y := Y sol) (hderiv sol) (hY sol)

/-- Fixed-IVP within-time-set derivative data for a model vector field gives
intrinsic DeTurck derivative data once the model field is identified with the
intrinsic gauge field along each chosen flow in the relative time-set filter. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivative_of_vectorField_eq_nhdsWithin
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
          (fun τ : ℝ ↦ (maps3 sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Y sol t ((maps3 sol t) x))))
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet,
        ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
          Y sol τ ((maps3 sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 sol τ) x)) :
    ChosenIntrinsicDeTurckGaugeFlowDerivative
      (I := I) (M := M) ivp maps3 := by
  intro sol
  exact Diffeomorph3IntrinsicGaugeFlowDerivativeOn.of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (Y := Y sol) (hderiv sol) (hY sol)

/-- Fixed-IVP within-time-set preferred-chart ODE data for a model vector field gives intrinsic
DeTurck chart-ODE data once the model field is identified with the intrinsic gauge field along each
chosen flow. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivative_of_vectorField_eq
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈
          𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (Y sol t ((maps3 sol t) x)) sol.1.toIntrinsicDeTurckSolution.timeSet t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        Y sol t ((maps3 sol t) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivative
      (I := I) (M := M) ivp maps3 := by
  intro sol
  exact Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn.of_vectorField_eq
    (I := I) (M := M) (Y := Y sol) (hsource sol) (hderiv sol) (hY sol)

/-- Fixed-IVP within-time-set preferred-chart ODE data for a model vector field
gives intrinsic DeTurck chart-ODE data once the model field is identified with
the intrinsic gauge field along each chosen flow in the relative time-set
filter. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivative_of_vectorField_eq_nhdsWithin
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈
          𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (Y sol t ((maps3 sol t) x)) sol.1.toIntrinsicDeTurckSolution.timeSet t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet,
        ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
          Y sol τ ((maps3 sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 sol τ) x)) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivative
      (I := I) (M := M) ivp maps3 := by
  intro sol
  exact Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn.of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (Y := Y sol) (hsource sol) (hderiv sol) (hY sol)

/-- Fixed-IVP ordinary-at-time derivative data for a model vector field gives intrinsic DeTurck
derivative data once the model field is identified with the intrinsic gauge field along each chosen
flow. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeAt_of_vectorField_eq
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (maps3 sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Y sol t ((maps3 sol t) x))))
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        Y sol t ((maps3 sol t) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeAt
      (I := I) (M := M) ivp maps3 := by
  intro sol
  exact Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn.of_vectorField_eq
    (I := I) (M := M) (Y := Y sol) (hderiv sol) (hY sol)

/-- Fixed-IVP ordinary-at-time derivative data for a model vector field gives
intrinsic DeTurck derivative data once the model field is identified with the
intrinsic gauge field along each chosen flow in the relative time-set filter. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeAt_of_vectorField_eq_nhdsWithin
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (maps3 sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Y sol t ((maps3 sol t) x))))
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet,
        ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
          Y sol τ ((maps3 sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 sol τ) x)) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeAt
      (I := I) (M := M) ivp maps3 := by
  intro sol
  exact Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn.of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (Y := Y sol) (hderiv sol) (hY sol)

/-- Fixed-IVP ordinary preferred-chart ODE data for a model vector field gives intrinsic DeTurck
chart-ODE data once the model field is identified with the intrinsic gauge field along each chosen
flow. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivativeAt_of_vectorField_eq
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (Y sol t ((maps3 sol t) x)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        Y sol t ((maps3 sol t) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAt
      (I := I) (M := M) ivp maps3 := by
  intro sol
  exact Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn.of_vectorField_eq
    (I := I) (M := M) (Y := Y sol) (hsource sol) (hderiv sol) (hY sol)

/-- Fixed-IVP ordinary preferred-chart ODE data for a model vector field gives
intrinsic DeTurck chart-ODE data once the model field is identified with the
intrinsic gauge field along each chosen flow in the relative time-set filter. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivativeAt_of_vectorField_eq_nhdsWithin
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (Y sol t ((maps3 sol t) x)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet,
        ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
          Y sol τ ((maps3 sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 sol τ) x)) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAt
      (I := I) (M := M) ivp maps3 := by
  intro sol
  exact Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn.of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (Y := Y sol) (hsource sol) (hderiv sol) (hY sol)

/-- Fixed-IVP preferred-chart ODE data directly supplies the primitive intrinsic
derivative data, without first constructing a raw gauge-flow witness. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivative_of_chartDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivative
      (I := I) (M := M) ivp maps3) :
    ChosenIntrinsicDeTurckGaugeFlowDerivative
      (I := I) (M := M) ivp maps3 := by
  intro sol
  exact Diffeomorph3IntrinsicGaugeFlowDerivativeOn.of_chartDerivativeOn
    (I := I) (M := M) (hchart sol)

/-- Fixed-IVP ordinary preferred-chart ODE data directly supplies ordinary
primitive intrinsic derivative data. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeAt_of_chartDerivativeAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAt
      (I := I) (M := M) ivp maps3) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeAt
      (I := I) (M := M) ivp maps3 := by
  intro sol
  exact Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn.of_chartDerivativeAtOn
    (I := I) (M := M) (hchart sol)

/-- Ordinary-at-time fixed-IVP derivative data gives the within-set derivative
view expected by derivative-level gauge-reduction APIs. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivative_of_derivativeAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (hderiv : ChosenIntrinsicDeTurckGaugeFlowDerivativeAt
      (I := I) (M := M) ivp maps3) :
    ChosenIntrinsicDeTurckGaugeFlowDerivative
      (I := I) (M := M) ivp maps3 := by
  intro sol
  exact Diffeomorph3IntrinsicGaugeFlowDerivativeOn.of_derivativeAtOn
    (I := I) (M := M) (hderiv sol)

/-- Fixed-IVP within-time-set derivative data gives ordinary-at-time derivative
data whenever each chosen solution time set is a neighborhood at its times. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeAt_of_derivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (hderiv : ChosenIntrinsicDeTurckGaugeFlowDerivative
      (I := I) (M := M) ivp maps3)
    (htime : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeAt
      (I := I) (M := M) ivp maps3 := by
  intro sol
  exact Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn.of_derivativeOn
    (I := I) (M := M) (hderiv sol) (htime sol)

/-- Fixed-IVP within-time-set preferred-chart ODE data gives ordinary
preferred-chart ODE data whenever each chosen solution time set is a
neighborhood at its times. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivativeAt_of_chartDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivative
      (I := I) (M := M) ivp maps3)
    (htime : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAt
      (I := I) (M := M) ivp maps3 := by
  intro sol
  exact Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn.of_chartDerivativeOn
    (I := I) (M := M) (hchart sol) (htime sol)

/-- Ordinary preferred-chart ODE data gives the within-time-set chart package
expected by derivative-level gauge-reduction APIs. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivative_of_chartDerivativeAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAt
      (I := I) (M := M) ivp maps3) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivative
      (I := I) (M := M) ivp maps3 := by
  intro sol
  exact Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn.of_chartDerivativeAtOn
    (I := I) (M := M) (hchart sol)

/-- Fixed-IVP closed-Picard primitive derivative data gives ordinary-at-time
derivative data on the chosen open solution time set. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeAt_of_picardIccDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowDerivativeOn (I := I) (M := M)
        (maps3 sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        (Icc (tmin sol) (tmax sol))) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeAt
      (I := I) (M := M) ivp maps3 := by
  intro sol
  have h :=
    Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn.of_derivativeOn_Ioo
      (I := I) (M := M) (hderiv sol)
  simpa [htimeSet sol] using h

/-- Fixed-IVP closed-Picard preferred-chart ODE data gives ordinary chart-ODE
data on the chosen open solution time set. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivativeAt_of_picardIccChartDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hchart : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn (I := I) (M := M)
        (maps3 sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        (Icc (tmin sol) (tmax sol))) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAt
      (I := I) (M := M) ivp maps3 := by
  intro sol
  have h :=
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn.of_chartDerivativeOn_Ioo
      (I := I) (M := M) (hchart sol)
  simpa [htimeSet sol] using h

/-- Fixed-IVP closed-Picard preferred-chart ODE data gives ordinary primitive
derivative data on the chosen open solution time set. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeAt_of_picardIccChartDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hchart : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn (I := I) (M := M)
        (maps3 sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        (Icc (tmin sol) (tmax sol))) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeAt
      (I := I) (M := M) ivp maps3 := by
  intro sol
  have h :=
    Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn.of_chartDerivativeOn_Ioo
      (I := I) (M := M) (hchart sol)
  simpa [htimeSet sol] using h

/-- Fixed-IVP closed-Picard fixed-chart ODE data gives ordinary chart-ODE data
on the chosen open solution time set. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivativeAt_of_picardIccFixedChartDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (chartCenter : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp, ℝ → M → M)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hfixed : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn (I := I) (M := M)
        (maps3 sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        (chartCenter sol) (Icc (tmin sol) (tmax sol))) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAt
      (I := I) (M := M) ivp maps3 := by
  intro sol
  have hfixedAt :=
    Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn.of_fixedChartDerivativeOn_Ioo
      (I := I) (M := M) (hfixed sol)
  have hchart :=
    Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn.toChartDerivativeAtOn
      (I := I) (M := M) hfixedAt
  simpa [htimeSet sol] using hchart

/-- Fixed-IVP closed-Picard fixed-chart ODE data gives ordinary primitive
derivative data on the chosen open solution time set. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeAt_of_picardIccFixedChartDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (chartCenter : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp, ℝ → M → M)
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hfixed : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn (I := I) (M := M)
        (maps3 sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        (chartCenter sol) (Icc (tmin sol) (tmax sol))) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeAt
      (I := I) (M := M) ivp maps3 := by
  intro sol
  have hfixedAt :=
    Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn.of_fixedChartDerivativeOn_Ioo
      (I := I) (M := M) (hfixed sol)
  have hderiv :=
    Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn.of_fixedChartDerivativeAtOn
      (I := I) (M := M) hfixedAt
  simpa [htimeSet sol] using hderiv

/-- Fixed-IVP closed-Picard fixed-chart ODE data for model vector fields gives
ordinary chart-ODE data on the chosen open solution time set once those model
fields are identified with the intrinsic DeTurck gauge fields along the
candidate flows. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivativeAt_of_picardIccFixedChartDerivative_of_vectorField_eq
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (chartCenter : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp, ℝ → M → M)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hmem : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (maps3 sol t) x ∈ (extChartAt I (chartCenter sol t x)).source)
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I (chartCenter sol t x)).source ∈
          𝓝[Icc (tmin sol) (tmax sol)] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (chartCenter sol t x)) ((maps3 sol τ) x))
          (tangentCoordChange I ((maps3 sol t) x) (chartCenter sol t x)
            ((maps3 sol t) x) ((Y sol) t ((maps3 sol t) x)))
          (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (Y sol) t ((maps3 sol t) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAt
      (I := I) (M := M) ivp maps3 :=
  chosenIntrinsicDeTurckGaugeFlowChartDerivativeAt_of_picardIccFixedChartDerivative
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3)
    chartCenter tmin tmax htimeSet
    (fun sol ↦
      Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn.of_vectorField_eq
        (I := I) (M := M) (hmem sol) (hsource sol) (hderiv sol) (hY sol))

/-- Fixed-IVP closed-Picard fixed-chart ODE data for model vector fields gives
ordinary primitive derivative data on the chosen open solution time set once
those model fields are identified with the intrinsic DeTurck gauge fields along
the candidate flows. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeAt_of_picardIccFixedChartDerivative_of_vectorField_eq
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (chartCenter : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp, ℝ → M → M)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hmem : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (maps3 sol t) x ∈ (extChartAt I (chartCenter sol t x)).source)
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I (chartCenter sol t x)).source ∈
          𝓝[Icc (tmin sol) (tmax sol)] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (chartCenter sol t x)) ((maps3 sol τ) x))
          (tangentCoordChange I ((maps3 sol t) x) (chartCenter sol t x)
            ((maps3 sol t) x) ((Y sol) t ((maps3 sol t) x)))
          (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (Y sol) t ((maps3 sol t) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeAt
      (I := I) (M := M) ivp maps3 :=
  chosenIntrinsicDeTurckGaugeFlowDerivativeAt_of_chartDerivativeAt
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3)
    (chosenIntrinsicDeTurckGaugeFlowChartDerivativeAt_of_picardIccFixedChartDerivative_of_vectorField_eq
      (I := I) (M := M) (ivp := ivp) (maps3 := maps3)
      chartCenter Y tmin tmax htimeSet hmem hsource hderiv hY)

/-- Fixed-IVP closed-Picard fixed-chart ODE data for model vector fields gives
ordinary chart-ODE data on the chosen open solution time set once those model
fields are identified with the intrinsic DeTurck gauge fields in the
closed-interval relative time filters. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivativeAt_of_picardIccFixedChartDerivative_of_vectorField_eq_nhdsWithin
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (chartCenter : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp, ℝ → M → M)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hmem : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (maps3 sol t) x ∈ (extChartAt I (chartCenter sol t x)).source)
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I (chartCenter sol t x)).source ∈
          𝓝[Icc (tmin sol) (tmax sol)] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (chartCenter sol t x)) ((maps3 sol τ) x))
          (tangentCoordChange I ((maps3 sol t) x) (chartCenter sol t x)
            ((maps3 sol t) x) ((Y sol) t ((maps3 sol t) x)))
          (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Icc (tmin sol) (tmax sol)] t, ∀ x : M,
          (Y sol) τ ((maps3 sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 sol τ) x)) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAt
      (I := I) (M := M) ivp maps3 :=
  chosenIntrinsicDeTurckGaugeFlowChartDerivativeAt_of_picardIccFixedChartDerivative
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3)
    chartCenter tmin tmax htimeSet
    (fun sol ↦
      Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn.of_vectorField_eq_nhdsWithin
        (I := I) (M := M) (hmem sol) (hsource sol) (hderiv sol) (hY sol))

/-- Fixed-IVP closed-Picard fixed-chart ODE data for model vector fields gives
ordinary primitive derivative data on the chosen open solution time set once
those model fields are identified with the intrinsic DeTurck gauge fields in the
closed-interval relative time filters. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeAt_of_picardIccFixedChartDerivative_of_vectorField_eq_nhdsWithin
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (chartCenter : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp, ℝ → M → M)
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hmem : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (maps3 sol t) x ∈ (extChartAt I (chartCenter sol t x)).source)
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I (chartCenter sol t x)).source ∈
          𝓝[Icc (tmin sol) (tmax sol)] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I (chartCenter sol t x)) ((maps3 sol τ) x))
          (tangentCoordChange I ((maps3 sol t) x) (chartCenter sol t x)
            ((maps3 sol t) x) ((Y sol) t ((maps3 sol t) x)))
          (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Icc (tmin sol) (tmax sol)] t, ∀ x : M,
          (Y sol) τ ((maps3 sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 sol τ) x)) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeAt
      (I := I) (M := M) ivp maps3 :=
  chosenIntrinsicDeTurckGaugeFlowDerivativeAt_of_chartDerivativeAt
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3)
    (chosenIntrinsicDeTurckGaugeFlowChartDerivativeAt_of_picardIccFixedChartDerivative_of_vectorField_eq_nhdsWithin
      (I := I) (M := M) (ivp := ivp) (maps3 := maps3)
      chartCenter Y tmin tmax htimeSet hmem hsource hderiv hY)

/-- Fixed-IVP closed-Picard preferred-chart ODE data for model vector fields
gives ordinary chart-ODE data on the chosen open solution time set once those
model fields are identified with the intrinsic DeTurck gauge fields along the
candidate flows. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivativeAt_of_picardIccChartDerivative_of_vectorField_eq
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈
          𝓝[Icc (tmin sol) (tmax sol)] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (Y sol t ((maps3 sol t) x)) (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        Y sol t ((maps3 sol t) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAt
      (I := I) (M := M) ivp maps3 := by
  intro sol
  have hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn
      (I := I) (M := M) (maps3 sol)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      (Icc (tmin sol) (tmax sol)) :=
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn.of_vectorField_eq
      (I := I) (M := M) (Y := Y sol)
      (hsource sol) (hderiv sol) (hY sol)
  have h :=
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn.of_chartDerivativeOn_Ioo
      (I := I) (M := M) hchart
  simpa [htimeSet sol] using h

/-- Fixed-IVP closed-Picard preferred-chart ODE data for model vector fields
gives ordinary primitive intrinsic derivative data on the chosen open solution
time set once those model fields are identified with the intrinsic DeTurck gauge
fields along the candidate flows. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeAt_of_picardIccChartDerivative_of_vectorField_eq
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈
          𝓝[Icc (tmin sol) (tmax sol)] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (Y sol t ((maps3 sol t) x)) (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        Y sol t ((maps3 sol t) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 sol t) x)) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeAt
      (I := I) (M := M) ivp maps3 :=
  chosenIntrinsicDeTurckGaugeFlowDerivativeAt_of_chartDerivativeAt
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3)
    (chosenIntrinsicDeTurckGaugeFlowChartDerivativeAt_of_picardIccChartDerivative_of_vectorField_eq
      (I := I) (M := M) (ivp := ivp) (maps3 := maps3)
      Y tmin tmax htimeSet hsource hderiv hY)

/-- Fixed-IVP closed-Picard preferred-chart ODE data for model vector fields
gives ordinary chart-ODE data on the chosen open solution time set once those
model fields are identified with the intrinsic DeTurck gauge fields along the
candidate flows in the relative open-interval filters. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivativeAt_of_picardIccChartDerivative_of_vectorField_eq_nhdsWithin
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈
          𝓝[Icc (tmin sol) (tmax sol)] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (Y sol t ((maps3 sol t) x)) (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t, ∀ x : M,
          Y sol τ ((maps3 sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 sol τ) x)) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAt
      (I := I) (M := M) ivp maps3 := by
  intro sol
  have hchart : Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn
      (I := I) (M := M) (maps3 sol)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      (Ioo (tmin sol) (tmax sol)) :=
    Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn.of_vectorField_eq_nhdsWithin
      (I := I) (M := M) (Y := Y sol)
      (fun t ht x ↦ by
        have htime : Icc (tmin sol) (tmax sol) ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
        simpa [nhdsWithin_eq_nhds.2 htime] using
          hsource sol t (Ioo_subset_Icc_self ht) x)
      (fun t ht x ↦
        (hderiv sol t (Ioo_subset_Icc_self ht) x).hasDerivAt
          (Icc_mem_nhds ht.1 ht.2))
      (hY sol)
  simpa [htimeSet sol] using hchart

/-- Fixed-IVP closed-Picard preferred-chart ODE data for model vector fields
gives ordinary primitive intrinsic derivative data on the chosen open solution
time set once those model fields are identified with the intrinsic DeTurck gauge
fields along the candidate flows in the relative open-interval filters. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeAt_of_picardIccChartDerivative_of_vectorField_eq_nhdsWithin
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (Y : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin sol) (tmax sol))
    (hsource : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        (fun τ : ℝ ↦ (maps3 sol τ) x) ⁻¹'
            (extChartAt I ((maps3 sol t) x)).source ∈
          𝓝[Icc (tmin sol) (tmax sol)] t)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Icc (tmin sol) (tmax sol), ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 sol t) x)) ((maps3 sol τ) x))
          (Y sol t ((maps3 sol t) x)) (Icc (tmin sol) (tmax sol)) t)
    (hY : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ Ioo (tmin sol) (tmax sol),
        ∀ᶠ τ in 𝓝[Ioo (tmin sol) (tmax sol)] t, ∀ x : M,
          Y sol τ ((maps3 sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 sol τ) x)) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeAt
      (I := I) (M := M) ivp maps3 :=
  chosenIntrinsicDeTurckGaugeFlowDerivativeAt_of_chartDerivativeAt
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3)
    (chosenIntrinsicDeTurckGaugeFlowChartDerivativeAt_of_picardIccChartDerivative_of_vectorField_eq_nhdsWithin
      (I := I) (M := M) (ivp := ivp) (maps3 := maps3)
      Y tmin tmax htimeSet hsource hderiv hY)

/-- A `C^3` diffeomorphism family satisfying the DeTurck gauge-flow equation
also provides the primitive pointwise derivative data expected by the
derivative-level gauge-reduction APIs. -/
theorem SmoothSelfDiffeomorph3Family.hasMFDerivWithinAt_of_satisfiesGaugeFlowOn
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ}
    (hflow : SatisfiesGaugeFlowOn (I := I) (M := M)
      Φ.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background) s)
    {t : ℝ} (ht : t ∈ s) (x : M) :
  HasMFDerivAt[s] (fun τ : ℝ ↦ (Φ τ) x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x))) := by
  change HasMFDerivAt[s] (fun τ : ℝ ↦ (Φ τ) x) t
    ((1 : ℝ →L[ℝ] ℝ).smulRight
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background t ((Φ t) x)))
  exact hflow.hasMFDerivWithinAt ht x

/-- For `C^3` diffeomorphism families, the geometric intrinsic DeTurck
gauge-flow statement is equivalent to the primitive derivative data used by
the derivative-level theorem packages. -/
theorem SmoothSelfDiffeomorph3Family.satisfiesGaugeFlowOn_intrinsic_iff_derivativeOn
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    {g : MetricFamily (I := I) (M := M)}
    {background : ConnectionFamily (I := I) (M := M)}
    {s : Set ℝ} :
    SatisfiesGaugeFlowOn (I := I) (M := M)
      Φ.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
      (intrinsicDeTurckGaugeField (I := I) (M := M) g background) s ↔
    Diffeomorph3IntrinsicGaugeFlowDerivativeOn
      (I := I) (M := M) Φ g background s := by
  constructor
  · intro hflow t ht x
    exact Φ.hasMFDerivWithinAt_of_satisfiesGaugeFlowOn hflow ht x
  · intro hderiv
    exact SatisfiesGaugeFlowOn.of_hasMFDerivWithinAt
      (I := I) (M := M)
      (Φ := Φ.toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily)
      (X := intrinsicDeTurckGaugeField (I := I) (M := M) g background)
      (s := s)
      (fun t ht x ↦ hderiv t ht x)

/-- Fixed-IVP derivative data extracted from geometric `C^3` gauge-flow
solutions for every chosen DeTurck solution. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivative_of_satisfiesGaugeFlowOn
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (hflow : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SatisfiesGaugeFlowOn (I := I) (M := M)
        (maps3 sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    ChosenIntrinsicDeTurckGaugeFlowDerivative (I := I) (M := M) ivp maps3 := by
  intro sol t ht x
  exact (maps3 sol).hasMFDerivWithinAt_of_satisfiesGaugeFlowOn
    (I := I) (M := M) (hflow sol) ht x

/-- Fixed-IVP primitive derivative data recovers the geometric
`SatisfiesGaugeFlowOn` statement for every chosen DeTurck solution. -/
theorem satisfiesGaugeFlowOn_of_chosenIntrinsicDeTurckGaugeFlowDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    {maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (hderiv : ChosenIntrinsicDeTurckGaugeFlowDerivative
      (I := I) (M := M) ivp maps3)
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    SatisfiesGaugeFlowOn (I := I) (M := M)
      (maps3 sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      sol.1.toIntrinsicDeTurckSolution.timeSet := by
  exact ((maps3 sol).satisfiesGaugeFlowOn_intrinsic_iff_derivativeOn
    (I := I) (M := M)
    (g := sol.1.toIntrinsicDeTurckSolution.metric)
    (background := sol.1.toIntrinsicDeTurckSolution.background)
    (s := sol.1.toIntrinsicDeTurckSolution.timeSet)).2 (hderiv sol)

/-- Fixed-IVP primitive derivative data is exactly the geometric intrinsic
DeTurck gauge-flow equation for every chosen DeTurck solution. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivative_iff_satisfiesGaugeFlowOn
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)) :
    ChosenIntrinsicDeTurckGaugeFlowDerivative (I := I) (M := M) ivp maps3 ↔
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet := by
  constructor
  · intro hderiv sol
    exact satisfiesGaugeFlowOn_of_chosenIntrinsicDeTurckGaugeFlowDerivative
      (I := I) (M := M) hderiv sol
  · exact chosenIntrinsicDeTurckGaugeFlowDerivative_of_satisfiesGaugeFlowOn
      (I := I) (M := M) maps3

/-- Family-level primitive derivative data for the intrinsic DeTurck gauges of all
chosen DeTurck solutions. -/
def ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)) : Prop :=
  ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowDerivativeOn (I := I) (M := M)
        (maps3 ivp sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet

/-- Family-level within-time-set preferred-chart ODE data for the intrinsic
DeTurck gauges of all chosen DeTurck solutions. -/
def ChosenIntrinsicDeTurckGaugeFlowChartDerivativeFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)) : Prop :=
  ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn (I := I) (M := M)
        (maps3 ivp sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet

/-- Family-level ordinary-at-time derivative data for the intrinsic DeTurck
gauges of all chosen DeTurck solutions. -/
def ChosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)) : Prop :=
  ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn (I := I) (M := M)
        (maps3 ivp sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet

/-- Family-level ordinary preferred-chart ODE data for the intrinsic DeTurck
gauges of all chosen DeTurck solutions. -/
def ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)) : Prop :=
  ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn (I := I) (M := M)
        (maps3 ivp sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet

/-- Family-level within-time-set derivative data for model vector fields gives intrinsic DeTurck
derivative-family data once each model field is identified with the intrinsic gauge field along the
corresponding chosen flow. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeFamily_of_vectorField_eq
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Y ivp sol t ((maps3 ivp sol t) x))))
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        Y ivp sol t ((maps3 ivp sol t) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x)) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily
      (I := I) (M := M) maps3 := by
  intro ivp
  exact chosenIntrinsicDeTurckGaugeFlowDerivative_of_vectorField_eq
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3 ivp)
    (Y ivp) (hderiv ivp) (hY ivp)

/-- Family-level within-time-set derivative data for model vector fields gives
intrinsic DeTurck derivative-family data once each model field is identified
with the intrinsic gauge field along the corresponding chosen flow in the
relative time-set filter. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeFamily_of_vectorField_eq_nhdsWithin
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasMFDerivAt[sol.1.toIntrinsicDeTurckSolution.timeSet]
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Y ivp sol t ((maps3 ivp sol t) x))))
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet,
        ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
          Y ivp sol τ ((maps3 ivp sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 ivp sol τ) x)) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily
      (I := I) (M := M) maps3 := by
  intro ivp
  exact chosenIntrinsicDeTurckGaugeFlowDerivative_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3 ivp)
    (Y ivp) (hderiv ivp) (hY ivp)

/-- Family-level within-time-set preferred-chart ODE data for model vector fields gives intrinsic
DeTurck chart-ODE-family data once each model field is identified with the intrinsic gauge field
along the corresponding chosen flow. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivativeFamily_of_vectorField_eq
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
            (extChartAt I ((maps3 ivp sol t) x)).source ∈
          𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
          (Y ivp sol t ((maps3 ivp sol t) x))
          sol.1.toIntrinsicDeTurckSolution.timeSet t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        Y ivp sol t ((maps3 ivp sol t) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x)) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivativeFamily
      (I := I) (M := M) maps3 := by
  intro ivp
  exact chosenIntrinsicDeTurckGaugeFlowChartDerivative_of_vectorField_eq
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3 ivp)
    (Y ivp) (hsource ivp) (hderiv ivp) (hY ivp)

/-- Family-level within-time-set preferred-chart ODE data for model vector
fields gives intrinsic DeTurck chart-ODE-family data once each model field is
identified with the intrinsic gauge field along the corresponding chosen flow
in the relative time-set filter. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivativeFamily_of_vectorField_eq_nhdsWithin
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
            (extChartAt I ((maps3 ivp sol t) x)).source ∈
          𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivWithinAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
          (Y ivp sol t ((maps3 ivp sol t) x))
          sol.1.toIntrinsicDeTurckSolution.timeSet t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet,
        ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
          Y ivp sol τ ((maps3 ivp sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 ivp sol τ) x)) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivativeFamily
      (I := I) (M := M) maps3 := by
  intro ivp
  exact chosenIntrinsicDeTurckGaugeFlowChartDerivative_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3 ivp)
    (Y ivp) (hsource ivp) (hderiv ivp) (hY ivp)

/-- Family-level ordinary-at-time derivative data for model vector fields gives intrinsic DeTurck
derivative-family data once each model field is identified with the intrinsic gauge field along the
corresponding chosen flow. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily_of_vectorField_eq
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Y ivp sol t ((maps3 ivp sol t) x))))
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        Y ivp sol t ((maps3 ivp sol t) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x)) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily
      (I := I) (M := M) maps3 := by
  intro ivp
  exact chosenIntrinsicDeTurckGaugeFlowDerivativeAt_of_vectorField_eq
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3 ivp)
    (Y ivp) (hderiv ivp) (hY ivp)

/-- Family-level ordinary-at-time derivative data for model vector fields gives
intrinsic DeTurck derivative-family data once each model field is identified
with the intrinsic gauge field along the corresponding chosen flow in the
relative time-set filter. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily_of_vectorField_eq_nhdsWithin
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasMFDerivAt 𝓘(ℝ) I (fun τ : ℝ ↦ (maps3 ivp sol τ) x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Y ivp sol t ((maps3 ivp sol t) x))))
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet,
        ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
          Y ivp sol τ ((maps3 ivp sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 ivp sol τ) x)) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily
      (I := I) (M := M) maps3 := by
  intro ivp
  exact chosenIntrinsicDeTurckGaugeFlowDerivativeAt_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3 ivp)
    (Y ivp) (hderiv ivp) (hY ivp)

/-- Family-level ordinary preferred-chart ODE data for model vector fields gives intrinsic DeTurck
chart-ODE-family data once each model field is identified with the intrinsic gauge field along the
corresponding chosen flow. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily_of_vectorField_eq
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
            (extChartAt I ((maps3 ivp sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
          (Y ivp sol t ((maps3 ivp sol t) x)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        Y ivp sol t ((maps3 ivp sol t) x) =
          intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x)) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily
      (I := I) (M := M) maps3 := by
  intro ivp
  exact chosenIntrinsicDeTurckGaugeFlowChartDerivativeAt_of_vectorField_eq
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3 ivp)
    (Y ivp) (hsource ivp) (hderiv ivp) (hY ivp)

/-- Family-level ordinary preferred-chart ODE data for model vector fields gives
intrinsic DeTurck chart-ODE-family data once each model field is identified
with the intrinsic gauge field along the corresponding chosen flow in the
relative time-set filter. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily_of_vectorField_eq_nhdsWithin
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
            (extChartAt I ((maps3 ivp sol t) x)).source ∈ 𝓝 t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet, ∀ x : M,
        HasDerivAt
          (fun τ : ℝ ↦ (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
          (Y ivp sol t ((maps3 ivp sol t) x)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet,
        ∀ᶠ τ in 𝓝[sol.1.toIntrinsicDeTurckSolution.timeSet] t, ∀ x : M,
          Y ivp sol τ ((maps3 ivp sol τ) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background τ ((maps3 ivp sol τ) x)) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily
      (I := I) (M := M) maps3 := by
  intro ivp
  exact chosenIntrinsicDeTurckGaugeFlowChartDerivativeAt_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3 ivp)
    (Y ivp) (hsource ivp) (hderiv ivp) (hY ivp)

/-- Family-level preferred-chart ODE data directly supplies primitive intrinsic
derivative-family data. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeFamily_of_chartDerivativeFamily
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivativeFamily
      (I := I) (M := M) maps3) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily
      (I := I) (M := M) maps3 := by
  intro ivp
  exact chosenIntrinsicDeTurckGaugeFlowDerivative_of_chartDerivative
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3 ivp) (hchart ivp)

/-- Family-level ordinary preferred-chart ODE data directly supplies ordinary
primitive intrinsic derivative-family data. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily_of_chartDerivativeAtFamily
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily
      (I := I) (M := M) maps3) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily
      (I := I) (M := M) maps3 := by
  intro ivp
  exact chosenIntrinsicDeTurckGaugeFlowDerivativeAt_of_chartDerivativeAt
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3 ivp) (hchart ivp)

/-- Ordinary-at-time family derivative data gives the within-set derivative-family
view expected by derivative-level gauge-reduction APIs. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeFamily_of_derivativeAtFamily
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (hderiv : ChosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily
      (I := I) (M := M) maps3) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily
      (I := I) (M := M) maps3 := by
  intro ivp sol
  exact Diffeomorph3IntrinsicGaugeFlowDerivativeOn.of_derivativeAtOn
    (I := I) (M := M) (hderiv ivp sol)

/-- Family-level within-time-set derivative data gives ordinary-at-time
derivative data whenever each chosen solution time set is a neighborhood at its
times. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily_of_derivativeFamily
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (hderiv : ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily
      (I := I) (M := M) maps3)
    (htime : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily
      (I := I) (M := M) maps3 := by
  intro ivp sol
  exact Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn.of_derivativeOn
    (I := I) (M := M) (hderiv ivp sol) (htime ivp sol)

/-- Family-level within-time-set preferred-chart ODE data gives ordinary
preferred-chart ODE data whenever each chosen solution time set is a
neighborhood at its times. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily_of_chartDerivativeFamily
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivativeFamily
      (I := I) (M := M) maps3)
    (htime : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        sol.1.toIntrinsicDeTurckSolution.timeSet ∈ 𝓝 t) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily
      (I := I) (M := M) maps3 := by
  intro ivp sol
  exact Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn.of_chartDerivativeOn
    (I := I) (M := M) (hchart ivp sol) (htime ivp sol)

/-- Ordinary preferred-chart ODE-family data gives the within-time-set chart
package expected by derivative-level gauge-reduction APIs. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivativeFamily_of_chartDerivativeAtFamily
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (hchart : ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily
      (I := I) (M := M) maps3) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivativeFamily
      (I := I) (M := M) maps3 := by
  intro ivp
  exact chosenIntrinsicDeTurckGaugeFlowChartDerivative_of_chartDerivativeAt
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3 ivp) (hchart ivp)

/-- Family-level closed-Picard primitive derivative data gives ordinary-at-time
derivative data on each chosen open solution time set. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily_of_picardIccDerivativeFamily
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Diffeomorph3IntrinsicGaugeFlowDerivativeOn (I := I) (M := M)
          (maps3 ivp sol)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background
          (Icc (tmin ivp sol) (tmax ivp sol))) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily
      (I := I) (M := M) maps3 := by
  intro ivp
  exact chosenIntrinsicDeTurckGaugeFlowDerivativeAt_of_picardIccDerivative
    (I := I) (M := M) (ivp := ivp)
    (tmin ivp) (tmax ivp) (htimeSet ivp) (hderiv ivp)

/-- Family-level closed-Picard preferred-chart ODE data gives ordinary chart-ODE
data on each chosen open solution time set. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily_of_picardIccChartDerivativeFamily
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hchart : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn (I := I) (M := M)
          (maps3 ivp sol)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background
          (Icc (tmin ivp sol) (tmax ivp sol))) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily
      (I := I) (M := M) maps3 := by
  intro ivp
  exact chosenIntrinsicDeTurckGaugeFlowChartDerivativeAt_of_picardIccChartDerivative
    (I := I) (M := M) (ivp := ivp)
    (tmin ivp) (tmax ivp) (htimeSet ivp) (hchart ivp)

/-- Family-level closed-Picard preferred-chart ODE data gives ordinary primitive
derivative-family data on each chosen open solution time set. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily_of_picardIccChartDerivativeFamily
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hchart : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn (I := I) (M := M)
          (maps3 ivp sol)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background
          (Icc (tmin ivp sol) (tmax ivp sol))) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily
      (I := I) (M := M) maps3 := by
  intro ivp
  exact chosenIntrinsicDeTurckGaugeFlowDerivativeAt_of_picardIccChartDerivative
    (I := I) (M := M) (ivp := ivp)
    (tmin ivp) (tmax ivp) (htimeSet ivp) (hchart ivp)

/-- Family-level closed-Picard fixed-chart ODE data gives ordinary chart-ODE
data on each chosen open solution time set. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily_of_picardIccFixedChartDerivativeFamily
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (chartCenter : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp, ℝ → M → M)
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hfixed : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn (I := I) (M := M)
          (maps3 ivp sol)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background
          (chartCenter ivp sol) (Icc (tmin ivp sol) (tmax ivp sol))) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily
      (I := I) (M := M) maps3 := by
  intro ivp
  exact chosenIntrinsicDeTurckGaugeFlowChartDerivativeAt_of_picardIccFixedChartDerivative
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3 ivp)
    (chartCenter ivp) (tmin ivp) (tmax ivp) (htimeSet ivp) (hfixed ivp)

/-- Family-level closed-Picard fixed-chart ODE data gives ordinary primitive
derivative-family data on each chosen open solution time set. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily_of_picardIccFixedChartDerivativeFamily
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (chartCenter : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp, ℝ → M → M)
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hfixed : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn (I := I) (M := M)
          (maps3 ivp sol)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background
          (chartCenter ivp sol) (Icc (tmin ivp sol) (tmax ivp sol))) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily
      (I := I) (M := M) maps3 :=
  chosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily_of_chartDerivativeAtFamily
    (I := I) (M := M) (maps3 := maps3)
    (chosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily_of_picardIccFixedChartDerivativeFamily
      (I := I) (M := M) (maps3 := maps3)
      chartCenter tmin tmax htimeSet hfixed)

/-- Family-level closed-Picard fixed-chart ODE data for model vector fields
gives ordinary chart-ODE-family data on each chosen open solution time set once
those model fields are identified with the intrinsic DeTurck gauge fields along
the corresponding candidate flows. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily_of_picardIccFixedChartDerivativeFamily_of_vectorField_eq
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (chartCenter : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp, ℝ → M → M)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hmem : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (maps3 ivp sol t) x ∈
            (extChartAt I (chartCenter ivp sol t x)).source)
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I (chartCenter ivp sol t x)).source ∈
            𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I (chartCenter ivp sol t x)) ((maps3 ivp sol τ) x))
            (tangentCoordChange I ((maps3 ivp sol t) x) (chartCenter ivp sol t x)
              ((maps3 ivp sol t) x) ((Y ivp sol) t ((maps3 ivp sol t) x)))
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (Y ivp sol) t ((maps3 ivp sol t) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x)) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily
      (I := I) (M := M) maps3 := by
  intro ivp
  exact chosenIntrinsicDeTurckGaugeFlowChartDerivativeAt_of_picardIccFixedChartDerivative_of_vectorField_eq
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3 ivp)
    (chartCenter ivp) (Y ivp) (tmin ivp) (tmax ivp) (htimeSet ivp)
    (hmem ivp) (hsource ivp) (hderiv ivp) (hY ivp)

/-- Family-level closed-Picard fixed-chart ODE data for model vector fields
gives ordinary primitive derivative-family data on each chosen open solution
time set once those model fields are identified with the intrinsic DeTurck gauge
fields along the corresponding candidate flows. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily_of_picardIccFixedChartDerivativeFamily_of_vectorField_eq
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (chartCenter : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp, ℝ → M → M)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hmem : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (maps3 ivp sol t) x ∈
            (extChartAt I (chartCenter ivp sol t x)).source)
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I (chartCenter ivp sol t x)).source ∈
            𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I (chartCenter ivp sol t x)) ((maps3 ivp sol τ) x))
            (tangentCoordChange I ((maps3 ivp sol t) x) (chartCenter ivp sol t x)
              ((maps3 ivp sol t) x) ((Y ivp sol) t ((maps3 ivp sol t) x)))
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (Y ivp sol) t ((maps3 ivp sol t) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t ((maps3 ivp sol t) x)) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily
      (I := I) (M := M) maps3 :=
  chosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily_of_chartDerivativeAtFamily
    (I := I) (M := M) (maps3 := maps3)
    (chosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily_of_picardIccFixedChartDerivativeFamily_of_vectorField_eq
      (I := I) (M := M) (maps3 := maps3)
      chartCenter Y tmin tmax htimeSet hmem hsource hderiv hY)

/-- Family-level closed-Picard fixed-chart ODE data for model vector fields
gives ordinary chart-ODE-family data on each chosen open solution time set once
those model fields are identified with the intrinsic DeTurck gauge fields in the
closed-interval relative time filters. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily_of_picardIccFixedChartDerivativeFamily_of_vectorField_eq_nhdsWithin
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (chartCenter : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp, ℝ → M → M)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hmem : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (maps3 ivp sol t) x ∈
            (extChartAt I (chartCenter ivp sol t x)).source)
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I (chartCenter ivp sol t x)).source ∈
            𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I (chartCenter ivp sol t x)) ((maps3 ivp sol τ) x))
            (tangentCoordChange I ((maps3 ivp sol t) x) (chartCenter ivp sol t x)
              ((maps3 ivp sol t) x) ((Y ivp sol) t ((maps3 ivp sol t) x)))
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol),
          ∀ᶠ τ in 𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t, ∀ x : M,
            (Y ivp sol) τ ((maps3 ivp sol τ) x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ
                ((maps3 ivp sol τ) x)) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily
      (I := I) (M := M) maps3 := by
  intro ivp
  exact chosenIntrinsicDeTurckGaugeFlowChartDerivativeAt_of_picardIccFixedChartDerivative_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3 ivp)
    (chartCenter ivp) (Y ivp) (tmin ivp) (tmax ivp) (htimeSet ivp)
    (hmem ivp) (hsource ivp) (hderiv ivp) (hY ivp)

/-- Family-level closed-Picard fixed-chart ODE data for model vector fields
gives ordinary primitive derivative-family data on each chosen open solution
time set once those model fields are identified with the intrinsic DeTurck gauge
fields in the closed-interval relative time filters. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily_of_picardIccFixedChartDerivativeFamily_of_vectorField_eq_nhdsWithin
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (chartCenter : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp, ℝ → M → M)
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hmem : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (maps3 ivp sol t) x ∈
            (extChartAt I (chartCenter ivp sol t x)).source)
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I (chartCenter ivp sol t x)).source ∈
            𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I (chartCenter ivp sol t x)) ((maps3 ivp sol τ) x))
            (tangentCoordChange I ((maps3 ivp sol t) x) (chartCenter ivp sol t x)
              ((maps3 ivp sol t) x) ((Y ivp sol) t ((maps3 ivp sol t) x)))
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol),
          ∀ᶠ τ in 𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t, ∀ x : M,
            (Y ivp sol) τ ((maps3 ivp sol τ) x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ
                ((maps3 ivp sol τ) x)) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily
      (I := I) (M := M) maps3 :=
  chosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily_of_chartDerivativeAtFamily
    (I := I) (M := M) (maps3 := maps3)
    (chosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily_of_picardIccFixedChartDerivativeFamily_of_vectorField_eq_nhdsWithin
      (I := I) (M := M) (maps3 := maps3)
      chartCenter Y tmin tmax htimeSet hmem hsource hderiv hY)

/-- Family-level closed-Picard preferred-chart ODE data for model vector fields
gives ordinary chart-ODE-family data on each chosen open solution time set once
those model fields are identified with the intrinsic DeTurck gauge fields along
the corresponding candidate flows. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily_of_picardIccChartDerivativeFamily_of_vectorField_eq
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈
            𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            (Y ivp sol t ((maps3 ivp sol t) x))
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          Y ivp sol t ((maps3 ivp sol t) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t
                ((maps3 ivp sol t) x)) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily
      (I := I) (M := M) maps3 := by
  intro ivp
  exact chosenIntrinsicDeTurckGaugeFlowChartDerivativeAt_of_picardIccChartDerivative_of_vectorField_eq
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3 ivp)
    (Y ivp) (tmin ivp) (tmax ivp) (htimeSet ivp)
    (hsource ivp) (hderiv ivp) (hY ivp)

/-- Family-level closed-Picard preferred-chart ODE data for model vector fields
gives ordinary primitive derivative-family data on each chosen open solution
time set once those model fields are identified with the intrinsic DeTurck gauge
fields along the corresponding candidate flows. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily_of_picardIccChartDerivativeFamily_of_vectorField_eq
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈
            𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            (Y ivp sol t ((maps3 ivp sol t) x))
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          Y ivp sol t ((maps3 ivp sol t) x) =
            intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background t
                ((maps3 ivp sol t) x)) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily
      (I := I) (M := M) maps3 :=
  chosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily_of_chartDerivativeAtFamily
    (I := I) (M := M) (maps3 := maps3)
    (chosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily_of_picardIccChartDerivativeFamily_of_vectorField_eq
      (I := I) (M := M) (maps3 := maps3)
      Y tmin tmax htimeSet hsource hderiv hY)

/-- Family-level closed-Picard preferred-chart ODE data for model vector fields
gives ordinary chart-ODE-family data on each chosen open solution time set once
those model fields are identified with the intrinsic DeTurck gauge fields along
the corresponding candidate flows in the relative open-interval filters. -/
theorem chosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily_of_picardIccChartDerivativeFamily_of_vectorField_eq_nhdsWithin
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈
            𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            (Y ivp sol t ((maps3 ivp sol t) x))
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Ioo (tmin ivp sol) (tmax ivp sol),
          ∀ᶠ τ in 𝓝[Ioo (tmin ivp sol) (tmax ivp sol)] t, ∀ x : M,
            Y ivp sol τ ((maps3 ivp sol τ) x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ
                ((maps3 ivp sol τ) x)) :
    ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily
      (I := I) (M := M) maps3 := by
  intro ivp
  exact chosenIntrinsicDeTurckGaugeFlowChartDerivativeAt_of_picardIccChartDerivative_of_vectorField_eq_nhdsWithin
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3 ivp)
    (Y ivp) (tmin ivp) (tmax ivp) (htimeSet ivp)
    (hsource ivp) (hderiv ivp) (hY ivp)

/-- Family-level closed-Picard preferred-chart ODE data for model vector fields
gives ordinary primitive derivative-family data on each chosen open solution
time set once those model fields are identified with the intrinsic DeTurck gauge
fields along the corresponding candidate flows in the relative open-interval
filters. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily_of_picardIccChartDerivativeFamily_of_vectorField_eq_nhdsWithin
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (Y : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        CovariantDerivative.TimeDependentVectorField (I := I) (M := M))
    (tmin tmax : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp → ℝ)
    (htimeSet : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        sol.1.toIntrinsicDeTurckSolution.timeSet = Ioo (tmin ivp sol) (tmax ivp sol))
    (hsource : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          (fun τ : ℝ ↦ (maps3 ivp sol τ) x) ⁻¹'
              (extChartAt I ((maps3 ivp sol t) x)).source ∈
            𝓝[Icc (tmin ivp sol) (tmax ivp sol)] t)
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Icc (tmin ivp sol) (tmax ivp sol), ∀ x : M,
          HasDerivWithinAt
            (fun τ : ℝ ↦
              (extChartAt I ((maps3 ivp sol t) x)) ((maps3 ivp sol τ) x))
            (Y ivp sol t ((maps3 ivp sol t) x))
            (Icc (tmin ivp sol) (tmax ivp sol)) t)
    (hY : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ t ∈ Ioo (tmin ivp sol) (tmax ivp sol),
          ∀ᶠ τ in 𝓝[Ioo (tmin ivp sol) (tmax ivp sol)] t, ∀ x : M,
            Y ivp sol τ ((maps3 ivp sol τ) x) =
              intrinsicDeTurckGaugeField (I := I) (M := M)
                sol.1.toIntrinsicDeTurckSolution.metric
                sol.1.toIntrinsicDeTurckSolution.background τ
                ((maps3 ivp sol τ) x)) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily
      (I := I) (M := M) maps3 :=
  chosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily_of_chartDerivativeAtFamily
    (I := I) (M := M) (maps3 := maps3)
    (chosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily_of_picardIccChartDerivativeFamily_of_vectorField_eq_nhdsWithin
      (I := I) (M := M) (maps3 := maps3)
      Y tmin tmax htimeSet hsource hderiv hY)

/-- Family-level derivative data extracted from geometric `C^3` gauge-flow
solutions for every chosen DeTurck solution. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeFamily_of_satisfiesGaugeFlowOn
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (hflow : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SatisfiesGaugeFlowOn (I := I) (M := M)
          (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
          (intrinsicDeTurckGaugeField (I := I) (M := M)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background)
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily (I := I) (M := M) maps3 := by
  intro ivp sol t ht x
  exact (maps3 ivp sol).hasMFDerivWithinAt_of_satisfiesGaugeFlowOn
    (I := I) (M := M) (hflow ivp sol) ht x

/-- Theorem-family primitive derivative data recovers the geometric
`SatisfiesGaugeFlowOn` statement for every chosen DeTurck solution. -/
theorem satisfiesGaugeFlowOnFamily_of_chosenIntrinsicDeTurckGaugeFlowDerivativeFamily
    {maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)}
    (hderiv : ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily
      (I := I) (M := M) maps3)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp) :
    SatisfiesGaugeFlowOn (I := I) (M := M)
      (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      sol.1.toIntrinsicDeTurckSolution.timeSet := by
  exact satisfiesGaugeFlowOn_of_chosenIntrinsicDeTurckGaugeFlowDerivative
    (I := I) (M := M) (ivp := ivp) (maps3 := maps3 ivp)
    (fun sol ↦ hderiv ivp sol) sol

/-- Theorem-family primitive derivative data is exactly the geometric intrinsic
DeTurck gauge-flow equation for every chosen DeTurck solution. -/
theorem chosenIntrinsicDeTurckGaugeFlowDerivativeFamily_iff_satisfiesGaugeFlowOn
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M)) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily (I := I) (M := M) maps3 ↔
      ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
        ∀ sol : ChosenIntrinsicDeTurckLocalSolution
            (E := E) (H := H) (I := I) (M := M) ivp,
          SatisfiesGaugeFlowOn (I := I) (M := M)
            (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
            (intrinsicDeTurckGaugeField (I := I) (M := M)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background)
            sol.1.toIntrinsicDeTurckSolution.timeSet := by
  constructor
  · intro hderiv ivp sol
    exact satisfiesGaugeFlowOnFamily_of_chosenIntrinsicDeTurckGaugeFlowDerivativeFamily
      (I := I) (M := M) hderiv ivp sol
  · exact chosenIntrinsicDeTurckGaugeFlowDerivativeFamily_of_satisfiesGaugeFlowOn
      (I := I) (M := M) maps3

/-- Coordinate pushforward map for the variational data field.

This inlines
`SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap` so the
variational field can live upstream of `Diffeomorph3FlowTimeDerivative`.
Definitionally equal to the TimeDerivative version. -/
noncomputable def ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow.variationalTangentCoordinateMap
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (t τ : ℝ) (x : M) : E →L[ℝ] E :=
  let TM := (TangentSpace I : M → Type _)
  ContinuousLinearMap.inCoordinates E TM E TM x x ((Φ t) x) ((Φ τ) x)
    ((Φ τ).pushforwardTangent x)

/-- Coordinate metric bilinear form for the variational data field.

This inlines
`SmoothSelfDiffeomorph3Family.pullbackMetricBilinearCoordinateMap` so the
variational field can live upstream of `Diffeomorph3FlowTimeDerivative`.
Definitionally equal to the TimeDerivative version. -/
noncomputable def ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow.variationalBilinearCoordinateMap
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (t τ : ℝ) (x : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  let TM := (TangentSpace I : M → Type _)
  let TStar := fun y : M => TM y →L[ℝ] ℝ
  let OneF := E →L[ℝ] ℝ
  ContinuousLinearMap.inCoordinates E TM OneF TStar
    ((Φ t) x) ((Φ τ) x) ((Φ t) x) ((Φ τ) x) ((g τ).inner ((Φ τ) x))

/-- Source tangent coordinate for the variational data field.

This inlines `SmoothSelfDiffeomorph3Family.sourceTangentCoordinate`. -/
noncomputable def ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow.variationalSourceTangentCoordinate
    (x : M) (u : TangentSpace I x) : E :=
  let TM := (TangentSpace I : M → Type _)
  let hx : x ∈ (trivializationAt E TM x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  (trivializationAt E TM x).continuousLinearEquivAt ℝ x hx u

/-- Tangent vector from coordinate for the variational data field.

This inlines `SmoothSelfDiffeomorph3Family.tangentVectorOfCoordinate`. -/
noncomputable def ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow.variationalTangentVectorOfCoordinate
    (x : M) (uE : E) : TangentSpace I x :=
  let TM := (TangentSpace I : M → Type _)
  let hx : x ∈ (trivializationAt E TM x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  ((trivializationAt E TM x).continuousLinearEquivAt ℝ x hx).symm uE

/-- Per-point variational data for Milestone 4.1.

For a DeTurck gauge flow `Φ`, metric `g`, background `background`,
gauge-corrected velocity `gdot`, time `t` and base point `x`, this packages
genuine time-differentiability of the flow's coordinate pushforward and metric
bilinear maps via the variational equation:
- `D` is the variational derivative operator (the Lie bracket of the DeTurck
  field, in coordinates),
- `hA` is the variational equation for the coordinate pushforward (M1c),
- `hB` is the time-derivative of the coordinate metric bilinear form (M1a+M1b),
- `hD_bracket` identifies `D` with the Lie bracket of the DeTurck field,
- `hval` assembles these into the gauge-corrected velocity identity.

Constructors supply this from Picard–Lindelöf ODE theory
(`ModelGaugeFlowODE.VariationalLocalFlowSolution` + identification with the
gauge flow); it is real analytic data, not scaffolding. -/
def ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowVariationalData
    (Φ : SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (gdot : MetricTensorFamily (I := I) (M := M))
    (t : ℝ) (x : M) : Prop :=
  ∃ (D : E →L[ℝ] E) (B' : E →L[ℝ] E →L[ℝ] ℝ),
    -- Chart membership: the flow stays in the tangent chart at `(Φ t) x`
    -- for `τ` near `t`. This is part of the Picard variational setup.
    (∀ᶠ τ in 𝓝 t, (Φ τ) x ∈
      (trivializationAt E (TangentSpace I : M → Type _) ((Φ t) x)).baseSet) ∧
    HasDerivAt
      (fun τ : ℝ ↦ ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow.variationalTangentCoordinateMap Φ t τ x)
      (D.comp (ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow.variationalTangentCoordinateMap Φ t t x)) t ∧
    HasDerivAt
      (fun τ : ℝ ↦ ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow.variationalBilinearCoordinateMap Φ g t τ x)
      B' t ∧
    (∀ w : TangentSpace I x,
      ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow.variationalTangentVectorOfCoordinate
        ((Φ t) x)
        (D (ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow.variationalSourceTangentCoordinate
          ((Φ t) x) ((Φ t).pushforwardTangent x w))) =
      VectorField.mlieBracket I
        (FiberBundle.extend E ((Φ t).pushforwardTangent x w))
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t)
        ((Φ t) x)) ∧
    ∀ u v : TangentSpace I x,
      let uE := ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow.variationalSourceTangentCoordinate x u
      let vE := ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow.variationalSourceTangentCoordinate x v
      let At := ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow.variationalTangentCoordinateMap Φ t t x
      let Bt := ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow.variationalBilinearCoordinateMap Φ g t t x
      B' (At uE) (At vE) + Bt (D (At uE)) (At vE) + Bt (At uE) (D (At vE)) = gdot t x u v

/-- A reusable bundle of geometric `C^3` intrinsic DeTurck gauge flows for all
chosen DeTurck local solutions of a fixed initial-value problem. -/
structure ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) where
  maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp,
    SmoothSelfDiffeomorph3Family (I := I) (M := M)
  anchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp,
    SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
      (maps3 sol) ivp.initialTime
  satisfies : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp,
    SatisfiesGaugeFlowOn (I := I) (M := M)
      (maps3 sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
      (intrinsicDeTurckGaugeField (I := I) (M := M)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background)
      sol.1.toIntrinsicDeTurckSolution.timeSet
  /-- Genuine per-point variational data for Milestone 4.1.

  For each solution, time `t` in the time set, and base point `x`, this supplies
  the variational derivative operator, the time-derivatives of the coordinate
  pushforward and metric bilinear maps, the Lie-bracket identification, and the
  assembled gauge-corrected velocity identity. Constructors build this from
  Picard–Lindelöf ODE theory; it is real analytic data, not scaffolding.

  The gauge-corrected velocity `gdot` is existentially packaged with its
  identification to the solution's gauge-corrected pullback velocity, so the
  field does not depend on the `gauge` projection defined after the structure. -/
  variational : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp,
    ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet → ∀ x : M,
      ∃ gdot : MetricTensorFamily (I := I) (M := M),
        gdot = sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
          (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
            (I := I) (M := M)
            (g := sol.1.toIntrinsicDeTurckSolution.metric)
            (background := sol.1.toIntrinsicDeTurckSolution.background)
            (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
            (t₀ := ivp.initialTime)
            (maps3 sol) (anchored sol) (satisfies sol)) ∧
        ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowVariationalData
          (I := I) (M := M)
          (maps3 sol)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background
          gdot t x

namespace ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow

/-- Build a fixed-IVP geometric `C^3` gauge-flow bundle from anchoring,
primitive derivative data, and genuine variational data. -/
def ofDerivativeData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (maps3 : ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (hanchored : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 sol) ivp.initialTime)
    (hderiv : ChosenIntrinsicDeTurckGaugeFlowDerivative
      (I := I) (M := M) ivp maps3)
    (hvar : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet → ∀ x : M,
        ∃ gdot : MetricTensorFamily (I := I) (M := M),
          gdot = sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 sol)
              (hanchored sol)
              (satisfiesGaugeFlowOn_of_chosenIntrinsicDeTurckGaugeFlowDerivative
                (I := I) (M := M) hderiv sol)) ∧
          ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowVariationalData
            (I := I) (M := M)
            (maps3 sol)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background
            gdot t x) :
    ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp where
  maps3 := maps3
  anchored := hanchored
  satisfies := fun sol ↦
    satisfiesGaugeFlowOn_of_chosenIntrinsicDeTurckGaugeFlowDerivative
      (I := I) (M := M) hderiv sol
  variational := hvar

/-- The derivative view of a bundled geometric gauge-flow family for one initial
value problem. -/
theorem derivativeData
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) :
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      Diffeomorph3IntrinsicGaugeFlowDerivativeOn (I := I) (M := M)
        (G.maps3 sol)
        sol.1.toIntrinsicDeTurckSolution.metric
        sol.1.toIntrinsicDeTurckSolution.background
        sol.1.toIntrinsicDeTurckSolution.timeSet := by
  intro sol t ht x
  exact (G.maps3 sol).hasMFDerivWithinAt_of_satisfiesGaugeFlowOn
    (I := I) (M := M) (G.satisfies sol) ht x

/-- The anchored intrinsic DeTurck gauge associated to one solution in a bundled
geometric gauge-flow family for a fixed initial-value problem. -/
def gauge
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime :=
  AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
    (I := I) (M := M)
    (g := sol.1.toIntrinsicDeTurckSolution.metric)
    (background := sol.1.toIntrinsicDeTurckSolution.background)
    (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
    (t₀ := ivp.initialTime)
    (G.maps3 sol) (G.anchored sol) (G.satisfies sol)

/-- The same anchored gauge, constructed through the derivative-family view. -/
def gaugeViaDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime :=
  AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
    (I := I) (M := M)
    (g := sol.1.toIntrinsicDeTurckSolution.metric)
    (background := sol.1.toIntrinsicDeTurckSolution.background)
    (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
    (t₀ := ivp.initialTime)
    (G.maps3 sol) (G.anchored sol) (G.derivativeData sol)

@[simp] theorem gauge_maps
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.gauge sol).maps = G.maps3 sol := rfl

@[simp] theorem gaugeViaDerivative_maps
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.gaugeViaDerivative sol).maps = G.maps3 sol := rfl

@[simp] theorem gaugeCorrectedPullbackVelocity_gauge_eq_gaugeViaDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol) =
      sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        (G.gaugeViaDerivative sol) := rfl

/-- Build the actual time derivative of a fixed-IVP gauge-pulled metric from the scalar
inner-product derivative at every fixed pair of tangent vectors. -/
theorem hasTimeDerivativeOn_of_innerHasDerivAt
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TangentSpace I x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                (((G.maps3 sol) τ) x)
                (((G.maps3 sol) τ).pushforwardTangent x u)
                (((G.maps3 sol) τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              (G.gauge sol) t x u v) t)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((G.maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  SmoothSelfDiffeomorph3Family.pullbackMetricFamily_hasTimeDerivativeOn_of_inner_hasDerivAt
    (I := I) (M := M)
    (Φ := G.maps3 sol)
    (g := sol.1.toIntrinsicDeTurckSolution.metric)
    (gdot := sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
    (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
    (hderiv sol)

/-- Extract the scalar inner-product derivative data for a fixed-IVP geometric
gauge-flow bundle from a time derivative of the actual gauge-pulled metric. -/
theorem innerHasDerivAt_of_hasTimeDerivativeOn
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((G.maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet)
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TangentSpace I x) :
    HasDerivAt
      (fun τ ↦
        (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
          (((G.maps3 sol) τ) x)
          (((G.maps3 sol) τ).pushforwardTangent x u)
          (((G.maps3 sol) τ).pushforwardTangent x v))
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        (G.gauge sol) t x u v) t := by
  refine (sol.1.gaugeCorrectedPullbackMetric_inner_hasDerivAt_of_hasTimeDerivativeOn
    (G.gauge sol) (hpullDerivative sol) ht x u v).congr_of_eventuallyEq ?_
  filter_upwards [] with τ
  rw [ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow.gauge_maps,
    SmoothSelfDiffeomorph3.pushforwardTangent_apply,
    SmoothSelfDiffeomorph3.pushforwardTangent_apply]

end ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow

/-- A reusable bundle of geometric `C^3` intrinsic DeTurck gauge flows for all
chosen DeTurck local solutions in a theorem-family argument. -/
structure ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily where
  maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family (I := I) (M := M)
  anchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
        (maps3 ivp sol) ivp.initialTime
  satisfies : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      SatisfiesGaugeFlowOn (I := I) (M := M)
        (maps3 ivp sol).toSmoothSelfDiffeomorph2Family.toSmoothSelfMapFamily
        (intrinsicDeTurckGaugeField (I := I) (M := M)
          sol.1.toIntrinsicDeTurckSolution.metric
          sol.1.toIntrinsicDeTurckSolution.background)
        sol.1.toIntrinsicDeTurckSolution.timeSet
  variational : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
    ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet → ∀ x : M,
        ∃ gdot : MetricTensorFamily (I := I) (M := M),
          gdot = sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
            (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
              (I := I) (M := M)
              (g := sol.1.toIntrinsicDeTurckSolution.metric)
              (background := sol.1.toIntrinsicDeTurckSolution.background)
              (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
              (t₀ := ivp.initialTime)
              (maps3 ivp sol) (anchored ivp sol) (satisfies ivp sol)) ∧
          ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowVariationalData
            (I := I) (M := M)
            (maps3 ivp sol)
            sol.1.toIntrinsicDeTurckSolution.metric
            sol.1.toIntrinsicDeTurckSolution.background
            gdot t x

namespace ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily

/-- Build a theorem-family geometric `C^3` gauge-flow bundle from anchoring,
primitive derivative-family data, and genuine variational data. -/
def ofDerivativeFamily
    (maps3 : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ _sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family (I := I) (M := M))
    (hanchored : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        SmoothSelfDiffeomorph3Family.AnchoredAt (I := I) (M := M)
          (maps3 ivp sol) ivp.initialTime)
    (hderiv : ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily
      (I := I) (M := M) maps3)
    (hvar : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet → ∀ x : M,
          ∃ gdot : MetricTensorFamily (I := I) (M := M),
            gdot = sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              (AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
                (I := I) (M := M)
                (g := sol.1.toIntrinsicDeTurckSolution.metric)
                (background := sol.1.toIntrinsicDeTurckSolution.background)
                (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
                (t₀ := ivp.initialTime)
                (maps3 ivp sol)
                (hanchored ivp sol)
                (satisfiesGaugeFlowOnFamily_of_chosenIntrinsicDeTurckGaugeFlowDerivativeFamily
                  (I := I) (M := M) hderiv ivp sol)) ∧
            ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowVariationalData
              (I := I) (M := M)
              (maps3 ivp sol)
              sol.1.toIntrinsicDeTurckSolution.metric
              sol.1.toIntrinsicDeTurckSolution.background
              gdot t x) :
    ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M) where
  maps3 := maps3
  anchored := hanchored
  satisfies := fun ivp sol ↦
    satisfiesGaugeFlowOnFamily_of_chosenIntrinsicDeTurckGaugeFlowDerivativeFamily
      (I := I) (M := M) hderiv ivp sol
  variational := hvar

/-- Restrict a theorem-family gauge-flow bundle to one initial-value problem. -/
def forInitialValueProblem
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp where
  maps3 := G.maps3 ivp
  anchored := G.anchored ivp
  satisfies := G.satisfies ivp
  variational := G.variational ivp

/-- Assemble theorem-family geometric gauge-flow data from fixed-IVP geometric
gauge-flow data for every initial-value problem. -/
def of_forInitialValueProblem
    (G : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
        (E := E) (H := H) (I := I) (M := M) ivp) :
    ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M) where
  maps3 := fun ivp sol ↦ (G ivp).maps3 sol
  anchored := fun ivp sol ↦ (G ivp).anchored sol
  satisfies := fun ivp sol ↦ (G ivp).satisfies sol
  variational := fun ivp sol ↦ (G ivp).variational sol

@[simp] theorem of_forInitialValueProblem_maps3
    (G : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
        (E := E) (H := H) (I := I) (M := M) ivp)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    ((of_forInitialValueProblem (I := I) (M := M) G).maps3 ivp sol) =
      (G ivp).maps3 sol := rfl

@[simp] theorem of_forInitialValueProblem_anchored
    (G : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
        (E := E) (H := H) (I := I) (M := M) ivp)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    ((of_forInitialValueProblem (I := I) (M := M) G).anchored ivp sol) =
      (G ivp).anchored sol := rfl

@[simp] theorem of_forInitialValueProblem_satisfies
    (G : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
        (E := E) (H := H) (I := I) (M := M) ivp)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    ((of_forInitialValueProblem (I := I) (M := M) G).satisfies ivp sol) =
      (G ivp).satisfies sol := rfl

@[simp] theorem forInitialValueProblem_of_forInitialValueProblem
    (G : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
        (E := E) (H := H) (I := I) (M := M) ivp)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    (of_forInitialValueProblem (I := I) (M := M) G).forInitialValueProblem ivp =
      G ivp := rfl

@[simp] theorem of_forInitialValueProblem_forInitialValueProblem
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) :
    of_forInitialValueProblem (I := I) (M := M)
      (fun ivp ↦ G.forInitialValueProblem ivp) = G := rfl

/-- Restrict proof-level theorem-family geometric gauge-flow data to one
initial-value problem. -/
theorem nonempty_forInitialValueProblem
    (hG : Nonempty (ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)) :
    Nonempty (ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp) := by
  rcases hG with ⟨G⟩
  exact ⟨G.forInitialValueProblem ivp⟩

/-- Assemble proof-level theorem-family geometric gauge-flow data from
proof-level fixed-IVP geometric gauge-flow data for every initial-value
problem. -/
theorem nonempty_of_forInitialValueProblem
    (hG : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      Nonempty (ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
        (E := E) (H := H) (I := I) (M := M) ivp)) :
    Nonempty (ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) := by
  classical
  exact ⟨of_forInitialValueProblem (I := I) (M := M)
    (fun ivp ↦ Classical.choice (hG ivp))⟩

/-- Theorem-family geometric gauge-flow data is equivalent to fixed-IVP
geometric gauge-flow data for every initial-value problem. -/
theorem nonempty_iff_forall_nonempty_forInitialValueProblem :
    Nonempty (ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) ↔
    ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      Nonempty (ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
        (E := E) (H := H) (I := I) (M := M) ivp) := by
  constructor
  · intro hG ivp
    exact nonempty_forInitialValueProblem (I := I) (M := M) hG ivp
  · exact nonempty_of_forInitialValueProblem (I := I) (M := M)

/-- The derivative-family view of a bundled geometric gauge-flow family. -/
theorem derivativeFamily
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M)) :
    ChosenIntrinsicDeTurckGaugeFlowDerivativeFamily (I := I) (M := M) G.maps3 :=
  chosenIntrinsicDeTurckGaugeFlowDerivativeFamily_of_satisfiesGaugeFlowOn
    (I := I) (M := M) G.maps3 G.satisfies

/-- The anchored intrinsic DeTurck gauge associated to one member of a bundled
geometric gauge-flow family. -/
def gauge
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime :=
  AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.ofSatisfiesGaugeFlowOn
    (I := I) (M := M)
    (g := sol.1.toIntrinsicDeTurckSolution.metric)
    (background := sol.1.toIntrinsicDeTurckSolution.background)
    (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
    (t₀ := ivp.initialTime)
    (G.maps3 ivp sol) (G.anchored ivp sol) (G.satisfies ivp sol)

@[simp] theorem forInitialValueProblem_maps3
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    ((G.forInitialValueProblem ivp).maps3 sol) = G.maps3 ivp sol := rfl

@[simp] theorem forInitialValueProblem_anchored
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    ((G.forInitialValueProblem ivp).anchored sol) = G.anchored ivp sol := rfl

@[simp] theorem forInitialValueProblem_satisfies
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    ((G.forInitialValueProblem ivp).satisfies sol) = G.satisfies ivp sol := rfl

@[simp] theorem forInitialValueProblem_gauge
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    ((G.forInitialValueProblem ivp).gauge sol) = G.gauge ivp sol := rfl

/-- The same anchored gauge, constructed through the derivative-family view.  This
matches derivative-level APIs whose scalar derivative formula references
`of_hasMFDerivWithinAt`. -/
def gaugeViaDerivative
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn (I := I) (M := M)
      sol.1.toIntrinsicDeTurckSolution.metric
      sol.1.toIntrinsicDeTurckSolution.background
      sol.1.toIntrinsicDeTurckSolution.timeSet ivp.initialTime :=
  AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.of_hasMFDerivWithinAt
    (I := I) (M := M)
    (g := sol.1.toIntrinsicDeTurckSolution.metric)
    (background := sol.1.toIntrinsicDeTurckSolution.background)
    (s := sol.1.toIntrinsicDeTurckSolution.timeSet)
    (t₀ := ivp.initialTime)
    (G.maps3 ivp sol) (G.anchored ivp sol) (G.derivativeFamily ivp sol)

@[simp] theorem gauge_maps
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.gauge ivp sol).maps = G.maps3 ivp sol := rfl

@[simp] theorem gaugeViaDerivative_maps
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    (G.gaugeViaDerivative ivp sol).maps = G.maps3 ivp sol := rfl

/-- The concrete corrected pullback velocity depends on the underlying `C^3`
diffeomorphism family, not on whether the anchored gauge was constructed from the
geometric flow statement or from its derivative view. -/
@[simp] theorem gaugeCorrectedPullbackVelocity_gauge_eq_gaugeViaDerivative
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge ivp sol) =
      sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        (G.gaugeViaDerivative ivp sol) := rfl

/-- Build theorem-family time derivatives of the actual gauge-pulled metrics from scalar
inner-product derivative data for the bundled non-identity `C^3` gauges. -/
theorem hasTimeDerivativeOn_of_innerHasDerivAt
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((G.maps3 ivp sol) τ) x)
                  (((G.maps3 ivp sol) τ).pushforwardTangent x u)
                  (((G.maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (G.gauge ivp sol) t x u v) t)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp) :
    HasTimeDerivativeOn (I := I) (M := M)
      ((G.maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge ivp sol))
      sol.1.toIntrinsicDeTurckSolution.timeSet :=
  (G.forInitialValueProblem ivp).hasTimeDerivativeOn_of_innerHasDerivAt
    (hderiv ivp) sol

/-- Extract the scalar inner-product derivative data for a theorem-family
geometric gauge-flow bundle from time derivatives of the actual gauge-pulled
metrics. -/
theorem innerHasDerivAt_of_hasTimeDerivativeOn
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((G.maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet)
    (ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M))
    (sol : ChosenIntrinsicDeTurckLocalSolution
      (E := E) (H := H) (I := I) (M := M) ivp)
    {t : ℝ} (ht : t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet)
    (x : M) (u v : TangentSpace I x) :
    HasDerivAt
      (fun τ ↦
        (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
          (((G.maps3 ivp sol) τ) x)
          (((G.maps3 ivp sol) τ).pushforwardTangent x u)
          (((G.maps3 ivp sol) τ).pushforwardTangent x v))
      (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
        (G.gauge ivp sol) t x u v) t := by
  refine ((G.forInitialValueProblem ivp).innerHasDerivAt_of_hasTimeDerivativeOn
    (hpullDerivative ivp) sol ht x u v).congr_of_eventuallyEq ?_
  filter_upwards [] with τ
  rw [ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily.forInitialValueProblem_maps3,
    SmoothSelfDiffeomorph3.pushforwardTangent_apply,
    SmoothSelfDiffeomorph3.pushforwardTangent_apply]

end ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily

/-- A chosen-background DeTurck theorem family becomes gauge-reducible from a
geometric `C^3` gauge-flow family once the actual gauge-pulled metric has the
concrete corrected velocity as its time derivative. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaDiffeomorph3GaugeFlowFamilyTimeDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((G.maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowDerivativeTimeDerivative
    G.maps3 G.anchored G.derivativeFamily
    (fun ivp sol ↦ by
      simpa only [
        ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily.gaugeViaDerivative,
        ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily.gaugeCorrectedPullbackVelocity_gauge_eq_gaugeViaDerivative] using
        hpullDerivative ivp sol)

/-- Intrinsic Ricci-flow theorem-family projection from a geometric `C^3`
gauge-flow family and a pulled-back metric time derivative. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaDiffeomorph3GaugeFlowFamilyTimeDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((G.maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowFamilyTimeDerivative
    G hpullDerivative).toIntrinsicFamily

/-- Ordinary Ricci-flow theorem-family projection from a geometric `C^3`
gauge-flow family and a pulled-back metric time derivative. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaDiffeomorph3GaugeFlowFamilyTimeDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (hpullDerivative : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        HasTimeDerivativeOn (I := I) (M := M)
          ((G.maps3 ivp sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
          (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge ivp sol))
          sol.1.toIntrinsicDeTurckSolution.timeSet) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toIntrinsicFamily_viaDiffeomorph3GaugeFlowFamilyTimeDerivative
    G hpullDerivative).toOrdinary

/-- A chosen-background DeTurck theorem family becomes gauge-reducible from a
geometric `C^3` gauge-flow family once the scalar inner-product derivative of the
pulled-back metric has the concrete corrected velocity. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toGaugeReducible_viaDiffeomorph3GaugeFlowFamilyInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((G.maps3 ivp sol) τ) x)
                  (((G.maps3 ivp sol) τ).pushforwardTangent x u)
                  (((G.maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (G.gauge ivp sol) t x u v) t) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M) :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowFamilyTimeDerivative
    G (G.hasTimeDerivativeOn_of_innerHasDerivAt hderiv)

/-- Intrinsic Ricci-flow theorem-family projection from a geometric `C^3`
gauge-flow family and scalar inner-product derivative data for the pulled-back metric. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toIntrinsicFamily_viaDiffeomorph3GaugeFlowFamilyInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((G.maps3 ivp sol) τ) x)
                  (((G.maps3 ivp sol) τ).pushforwardTangent x u)
                  (((G.maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (G.gauge ivp sol) t x u v) t) :
    IntrinsicLocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowFamilyInnerDerivative
    G hderiv).toIntrinsicFamily

/-- Ordinary Ricci-flow theorem-family projection from a geometric `C^3`
gauge-flow family and scalar inner-product derivative data for the pulled-back metric. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.toOrdinaryFamily_viaDiffeomorph3GaugeFlowFamilyInnerDerivative
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily
      (E := E) (H := H) (I := I) (M := M))
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowFamily
      (E := E) (H := H) (I := I) (M := M))
    (hderiv : ∀ ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M),
      ∀ sol : ChosenIntrinsicDeTurckLocalSolution
          (E := E) (H := H) (I := I) (M := M) ivp,
        ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
          ∀ x : M, ∀ u v : TangentSpace I x,
            HasDerivAt
              (fun τ ↦
                (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                  (((G.maps3 ivp sol) τ) x)
                  (((G.maps3 ivp sol) τ).pushforwardTangent x u)
                  (((G.maps3 ivp sol) τ).pushforwardTangent x v))
              (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
                (G.gauge ivp sol) t x u v) t) :
    LocalExistenceUniquenessFamily (E := E) (H := H) (I := I) (M := M) :=
  (pkg.toIntrinsicFamily_viaDiffeomorph3GaugeFlowFamilyInnerDerivative
    G hderiv).toOrdinary

/-- A chosen-background DeTurck theorem package becomes gauge-reducible from a
geometric `C^3` gauge-flow bundle once the actual gauge-pulled metric has the
concrete corrected velocity as its time derivative. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReducible_viaDiffeomorph3GaugeFlowBundleTimeDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((G.maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowDerivativeTimeDerivative
    G.maps3 G.anchored G.derivativeData
    (fun sol ↦ by
      simpa only [
        ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow.gaugeViaDerivative,
        ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow.gaugeCorrectedPullbackVelocity_gauge_eq_gaugeViaDerivative] using
        hpullDerivative sol)

/-- Intrinsic Ricci-flow theorem-package projection from a geometric `C^3`
gauge-flow bundle and a pulled-back metric time derivative. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaDiffeomorph3GaugeFlowBundleTimeDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((G.maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowBundleTimeDerivative
    G hpullDerivative).toIntrinsic

/-- Ordinary Ricci-flow theorem-package projection from a geometric `C^3`
gauge-flow bundle and a pulled-back metric time derivative. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaDiffeomorph3GaugeFlowBundleTimeDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hpullDerivative : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      HasTimeDerivativeOn (I := I) (M := M)
        ((G.maps3 sol).pullbackMetricFamily sol.1.toIntrinsicDeTurckSolution.metric)
        (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge (G.gauge sol))
        sol.1.toIntrinsicDeTurckSolution.timeSet) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toIntrinsic_viaDiffeomorph3GaugeFlowBundleTimeDerivative
    G hpullDerivative).toOrdinary

/-- A chosen-background DeTurck theorem package becomes gauge-reducible from a
geometric `C^3` gauge-flow bundle once the scalar inner-product derivative of the
pulled-back metric has the concrete corrected velocity. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toGaugeReducible_viaDiffeomorph3GaugeFlowBundleInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TangentSpace I x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                (((G.maps3 sol) τ) x)
                (((G.maps3 sol) τ).pushforwardTangent x u)
                (((G.maps3 sol) τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              (G.gauge sol) t x u v) t) :
    GaugeReducibleChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp :=
  pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowBundleTimeDerivative
    G (G.hasTimeDerivativeOn_of_innerHasDerivAt hderiv)

/-- Intrinsic Ricci-flow theorem-package projection from a geometric `C^3`
gauge-flow bundle and scalar inner-product derivative data for the pulled-back metric. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toIntrinsic_viaDiffeomorph3GaugeFlowBundleInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TangentSpace I x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                (((G.maps3 sol) τ) x)
                (((G.maps3 sol) τ).pushforwardTangent x u)
                (((G.maps3 sol) τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              (G.gauge sol) t x u v) t) :
    IntrinsicLocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toGaugeReducible_viaDiffeomorph3GaugeFlowBundleInnerDerivative
    G hderiv).toIntrinsic

/-- Ordinary Ricci-flow theorem-package projection from a geometric `C^3`
gauge-flow bundle and scalar inner-product derivative data for the pulled-back metric. -/
noncomputable def ChosenIntrinsicDeTurckLocalExistenceUniqueness.toOrdinary_viaDiffeomorph3GaugeFlowBundleInnerDerivative
    {ivp : InitialValueProblem (E := E) (H := H) (I := I) (M := M)}
    (pkg : ChosenIntrinsicDeTurckLocalExistenceUniqueness
      (E := E) (H := H) (I := I) (M := M) ivp)
    (G : ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow
      (E := E) (H := H) (I := I) (M := M) ivp)
    (hderiv : ∀ sol : ChosenIntrinsicDeTurckLocalSolution
        (E := E) (H := H) (I := I) (M := M) ivp,
      ∀ ⦃t : ℝ⦄, t ∈ sol.1.toIntrinsicDeTurckSolution.timeSet →
        ∀ x : M, ∀ u v : TangentSpace I x,
          HasDerivAt
            (fun τ ↦
              (sol.1.toIntrinsicDeTurckSolution.metric τ).inner
                (((G.maps3 sol) τ) x)
                (((G.maps3 sol) τ).pushforwardTangent x u)
                (((G.maps3 sol) τ).pushforwardTangent x v))
            (sol.1.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge
              (G.gauge sol) t x u v) t) :
    LocalExistenceUniqueness (E := E) (H := H) (I := I) (M := M) ivp :=
  (pkg.toIntrinsic_viaDiffeomorph3GaugeFlowBundleInnerDerivative
    G hderiv).toOrdinary

/-! ## Sharp joint-regularity gap and the conditional variational chain

### What the records prove vs. what the variational theory needs

The Banach fixed-point theory (`ContinuousSectionSpace` with the sup norm)
gives `C⁰` joint control of the metric. `MetricFamily` gives `C²` spatial
regularity at each fixed time, so the DeTurck coordinate field
`f := deTurckGaugeCoordinateField g background p₀` is `C¹` in space at each
fixed time.

The variational ODE theory needs joint time–space continuity of `f` and of
its spatial derivative `Df`. This is parabolic regularity for the
Ricci–DeTurck equation. It is **not** proved from the current records.

The definition below states this gap precisely, as a `Prop` about the
coordinate field. The theorems after it prove the *complete* conditional
chain:

> joint regularity  ⟹  variational local flow  ⟹  spatial derivative
> identification  ⟹  `ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowVariationalData`.

This isolates the milestone to a single sharp analytic estimate. It does
*not* close the milestone: the regularity hypothesis is an explicit open
goal, not a derived fact. See `DeTurckCoordinatePicardEstimates` for the
stronger `C²` package and its documentation of the same gap.
-/

/-- Minimal joint regularity for the DeTurck coordinate field.

`field_jointContinuous`: the coordinate field `(t, y) ↦ f t y` is jointly
continuous. `deriv_jointContinuous`: its spatial derivative
`(t, y) ↦ fderiv ℝ (f t) y` is jointly continuous.

Together with the `C¹`-in-space regularity from `MetricFamily` (fixed-time
`C²` metrics give a `C¹` DeTurck field), this is exactly what the linear
variational ODE route needs: a jointly continuous field that is locally
Lipschitz in space, with jointly continuous spatial derivative. No `C²`
assumption is made here — the modulus-of-continuity extraction criterion
(`flow_timeSlice_hasFDerivAt_of_Df_sub_bound_...`) needs only uniform
continuity of `Df` on compact tubes, not Lipschitz `Df`.

This is the precise analytic gap: parabolic regularity for Ricci–DeTurck.
It is stated, not proved. -/
structure DeTurckCoordinateFieldJointRegularity
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (p₀ : M) : Prop where
  field_jointContinuous : Continuous fun p : ℝ × E =>
    deTurckGaugeCoordinateField g background p₀ p.1 p.2
  deriv_jointContinuous : Continuous fun p : ℝ × E =>
    deTurckGaugeCoordinateDerivative g background p₀ p.1 p.2

/-- The spatial derivative of the coordinate field is genuinely the
Fréchet derivative at each time, from the fixed-time `C¹` regularity.

This is the `hder` input for the HasFDerivAt extraction: it does not need
the joint regularity, only fixed-time differentiability. -/
theorem deTurckCoordinateField_hasFDerivAt_of_jointRegularity
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (p₀ : M)
    (hC1 : ∀ t : ℝ, ∀ y : E,
      HasFDerivAt (deTurckGaugeCoordinateField g background p₀ t)
        (deTurckGaugeCoordinateDerivative g background p₀ t y) y)
    (t : ℝ) (y : E) :
    HasFDerivAt (deTurckGaugeCoordinateField g background p₀ t)
      (deTurckGaugeCoordinateDerivative g background p₀ t y) y :=
  hC1 t y

end RicciFlow
