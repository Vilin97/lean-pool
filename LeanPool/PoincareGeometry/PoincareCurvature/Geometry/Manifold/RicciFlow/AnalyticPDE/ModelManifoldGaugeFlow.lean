/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction.GaugeFlowAssembly
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothDependenceManifold
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.FieldJetContDiff

/-!
# Model-manifold raw `C³` gauge-flow existence from field-jet data (roadmap point 4, Item 2)

The compact-manifold gauge-flow constructor of Item 2 consumes its flow data through
`GaugeReduction/GaugeFlowAssembly.gaugeFlow_of_inverse_flow`, whose reduction target is a pair of
mutually inverse, spatially-`ContMDiff I I 3` time-slice maps `F`, `G : ℝ → M → M` together with the
anchoring `F t₀ = id` and the manifold ODE derivative equation
`HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun τ ↦ F τ x) s t ((1).smulRight (X t (F t x)))`.

The Banach → manifold smooth-dependence tower (`AnalyticPDE/SmoothDependenceCk`,
`AnalyticPDE/FlowDiffeomorphism`, `AnalyticPDE/SmoothDependenceManifold`) supplies **exactly** this
data for the **model manifold** `M = E` (`𝓘(ℝ, E)`), where a time-dependent vector field
`X : CovariantDerivative.TimeDependentVectorField 𝓘(ℝ, E) E` is definitionally an ordinary field
`ℝ → E → E` (`TangentSpace 𝓘(ℝ, E) x = E`).  This module closes the last mile of that connection:
from the `C^{3,1}` field jet of `v` alone (globally Lipschitz `v`, plus the Fréchet jet `Dv`, `D²v`,
`D³v` with the standard global Lipschitz/continuity/compatibility bounds), the raw `C³` DeTurck
gauge-flow structure `Diffeomorph3GaugeFlowOn (X := v) s t₀` is **inhabited** for the model manifold
`E`, on an *arbitrary* time set `s`.

Because Item 2's general-manifold smooth-dependence theorem is proved chart-by-chart with each chart
*the model space `E`*, this model-manifold gauge-flow existence is the load-bearing chart-level core
of the general compact-manifold constructor: the remaining work upstream is the chart-patching that
lives in the heavy `GaugeReduction/ModelGaugeFlowODE.lean` / `Diffeomorph3FlowExistence.lean`, not the
per-chart flow existence, which is now available here.

No new PDE or analytic content: a pure assembly of the already-proved model-manifold gauge-data
bundle `exists_flow_contMDiff_three_gaugeData` into the consumer `gaugeFlow_of_inverse_flow`.  Nothing
here touches the heavy gauge files.

* `exists_diffeomorph3GaugeFlowOn_of_field_jet` — the model-manifold (`M = E`) instance of Item 2's
  raw `C³` gauge-flow existence target, from field-jet data alone.

Proved sorry-free; axioms `propext`/`Classical.choice`/`Quot.sound` only.
-/

open Set Filter Topology
open scoped Topology NNReal Manifold ContDiff

namespace RicciFlow
namespace AnalyticPDE
namespace SmoothDependenceCk

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Model-manifold raw `C³` gauge-flow existence from field-jet data.**  For the model manifold
`M = E` (`𝓘(ℝ, E)`), a time-dependent vector field is definitionally an ordinary field
`v : ℝ → E → E`.  From its `C^{3,1}` jet — `v` globally `K`-Lipschitz and time-continuous, with the
everywhere Fréchet derivatives `Dv`, `D²v` (in both continuous-linear `D2vc` and multilinear `D2vm`
guises), `D³v` (`D3vm`/`D3v`), all globally Lipschitz / jointly continuous, and the standard
compatibility `D2vc = curry2 (D2vm)`, `D3vm = (D3v).curryLeft` — the raw `C³` DeTurck gauge-flow
structure `Diffeomorph3GaugeFlowOn (X := v) s t₀` is inhabited on an arbitrary time set `s`.

The flow data is the model-manifold gauge-data bundle `exists_flow_contMDiff_three_gaugeData`: the
forward flow map `F t = (x ↦ Φ x t)` and its per-time smooth inverse `G t` supply the mutually
inverse `ContMDiff I I 3` time slices, `Φ · t₀ = id` the anchoring, and the manifold integral-curve
derivative the ODE equation (weakened to the within-set form via `HasMFDerivAt.hasMFDerivWithinAt`).
This is the model-manifold instance — hence the chart-level core — of Item 2's compact-manifold
gauge-flow existence target. -/
theorem exists_diffeomorph3GaugeFlowOn_of_field_jet
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {v : ℝ → E → E} {K : ℝ≥0} {t₀ : ℝ} (s : Set ℝ)
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    {D2vc : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D2vm : ℝ → E → (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)}
    {D3vm : ℝ → E → (E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E}
    {L M₂ M₃ N : ℝ≥0}
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2vc : ∀ s ξ, HasFDerivAt (Dv s) (D2vc s ξ) ξ)
    (hD2vcc : Continuous fun p : ℝ × E => D2vc p.1 p.2)
    (hD2vclip : ∀ s, LipschitzWith M₂ (D2vc s))
    (hD2vmlip : ∀ s, LipschitzWith N (D2vm s))
    (hD3vm : ∀ s ξ, HasFDerivAt (D2vm s) (D3vm s ξ) ξ)
    (hD3vmc : Continuous fun p : ℝ × E => D3vm p.1 p.2)
    (hD3vmlip : ∀ s, LipschitzWith M₃ (D3vm s))
    (hD3vc : Continuous fun p : ℝ × E => D3v p.1 p.2)
    (hD3vlip : ∀ s, LipschitzWith M₃ (D3v s))
    (hcompat : ∀ s ξ, D2vc s ξ = curry2 (D2vm s ξ))
    (hcurry : ∀ s ξ, D3vm s ξ = (D3v s ξ).curryLeft) :
    Nonempty (RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E) (X := v) s t₀) := by
  obtain ⟨Φ, h0, hderiv, hdiff⟩ := exists_flow_contMDiff_three_gaugeData
    hv hvc hDv hDvc hDvlip hD2vc hD2vcc hD2vclip hD2vmlip hD3vm hD3vmc hD3vmlip
    hD3vc hD3vlip hcompat hcurry
  choose G hL hR hcdF hcdψ using hdiff
  exact PoincareCurvature.GaugeFlowAssembly.gaugeFlow_of_inverse_flow
    (I := 𝓘(ℝ, E)) (M := E) (X := v) (s := s) (t₀ := t₀)
    (fun t x => Φ x t) G hL hR hcdF hcdψ h0
    (fun t _ x => (hderiv x t).hasMFDerivWithinAt)

/-- **Model-manifold `C³` flow: first-class `Diffeomorph` family together with the ODE equation.**
From the `C^{3,1}` field jet of `v` alone there is a *single* flow family `Φ` on the model manifold
`𝓘(ℝ, E)` that simultaneously

* anchors, `Φ z t₀ = z`;
* satisfies the manifold integral-curve ODE derivative equation at every time,
  `HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun τ ↦ Φ z τ) t ((1).smulRight (v t (Φ z t)))`;
* is, for every `t`, the coercion of a genuine bundled `Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E 3`.

This threads a single `Φ` through both `exists_flow_diffeomorph_three` (which exposes the `Diffeomorph`
family but discards the flow equation) and the gauge-data bundle (which exposes the ODE but only an
unbundled inverse), giving the exact per-chart export the general compact-manifold lift transports:
in each chart, a first-class `C³` self-diffeomorphism family that *is* the flow of the (chart-local)
field.  A pure assembly of `exists_flow_contMDiff_three_gaugeData`. -/
theorem exists_flow_diffeomorph_three_hasMFDerivAt [FiniteDimensional ℝ E] [CompleteSpace E]
    {v : ℝ → E → E} {K : ℝ≥0} {t₀ : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    {D2vc : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D2vm : ℝ → E → (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)}
    {D3vm : ℝ → E → (E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E}
    {L M₂ M₃ N : ℝ≥0}
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2vc : ∀ s ξ, HasFDerivAt (Dv s) (D2vc s ξ) ξ)
    (hD2vcc : Continuous fun p : ℝ × E => D2vc p.1 p.2)
    (hD2vclip : ∀ s, LipschitzWith M₂ (D2vc s))
    (hD2vmlip : ∀ s, LipschitzWith N (D2vm s))
    (hD3vm : ∀ s ξ, HasFDerivAt (D2vm s) (D3vm s ξ) ξ)
    (hD3vmc : Continuous fun p : ℝ × E => D3vm p.1 p.2)
    (hD3vmlip : ∀ s, LipschitzWith M₃ (D3vm s))
    (hD3vc : Continuous fun p : ℝ × E => D3v p.1 p.2)
    (hD3vlip : ∀ s, LipschitzWith M₃ (D3v s))
    (hcompat : ∀ s ξ, D2vc s ξ = curry2 (D2vm s ξ))
    (hcurry : ∀ s ξ, D3vm s ξ = (D3v s ξ).curryLeft) :
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧
      (∀ z t, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun τ => Φ z τ) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (v t (Φ z t)))) ∧
      ∀ t, ∃ F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E 3, ∀ z, F z = Φ z t := by
  obtain ⟨Φ, h0, hderiv, hdiff⟩ := exists_flow_contMDiff_three_gaugeData
    hv hvc hDv hDvc hDvlip hD2vc hD2vcc hD2vclip hD2vmlip hD3vm hD3vmc hD3vmlip
    hD3vc hD3vlip hcompat hcurry
  refine ⟨Φ, h0, hderiv, fun t => ?_⟩
  obtain ⟨ψ, hL, hR, hcdΦ, hcdψ⟩ := hdiff t
  exact ⟨⟨⟨fun z => Φ z t, ψ, hL, hR⟩, hcdΦ, hcdψ⟩, fun z => rfl⟩

/-- **Model-manifold raw `C³` gauge-flow existence from a single joint-`ContDiff` field.**
Same conclusion as `exists_diffeomorph3GaugeFlowOn_of_field_jet` — the raw `C³` DeTurck gauge-flow
structure `Diffeomorph3GaugeFlowOn (X := v) s t₀` on the model manifold `M = E` (`𝓘(ℝ, E)`) — but with
the entire `C^{3,1}` Fréchet jet (`Dv`, `D²v` in both `curry`/multilinear guises, `D³v`) and its
pointwise-`HasFDerivAt`/joint-continuity/compatibility obligations *discharged from a single
`ContDiff ℝ n (Function.uncurry v)` hypothesis* (`3 ≤ n`).  Only the honest top-order controls remain
as hypotheses: `v` globally `K`-Lipschitz and time-continuous, plus the four Lipschitz bounds on the
first/second/third spatial-derivative fields (`hDvlip`/`hD2vclip`/`hD2vmlip`/`hD3vmlip`/`hD3vlip`),
matching the tower's own `C³` interface (expressing the top-order bounds as fourth-derivative bounds
would need a further multilinear jet).

This is the `ContDiff`-packaged form of the model-manifold gauge-flow existence — the chart-level core
of Item 2 stated behind the single smoothness hypothesis the compact-manifold gauge-flow lift will
supply from a `ContDiff` DeTurck gauge vector field, mirroring the `_of_contDiff` field-jet extraction
API (`exists_flow_contMDiff_three_diffeomorph_of_contDiff`). A pure assembly: the jet extraction of
`FieldJetContDiff` fed into `exists_diffeomorph3GaugeFlowOn_of_field_jet`. -/
theorem exists_diffeomorph3GaugeFlowOn_of_contDiff
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {v : ℝ → E → E} {K L M₂ M₃ N : ℝ≥0} {t₀ : ℝ} {n : WithTop ℕ∞} (s : Set ℝ)
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 3 ≤ n)
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    (hDvlip : ∀ s, LipschitzWith L (fderiv ℝ (v s)))
    (hD2vclip : ∀ s, LipschitzWith M₂ (fderiv ℝ (fderiv ℝ (v s))))
    (hD2vmlip : ∀ s, LipschitzWith N (iteratedFDeriv ℝ 2 (v s)))
    (hD3vmlip : ∀ s, LipschitzWith M₃ (fderiv ℝ (iteratedFDeriv ℝ 2 (v s))))
    (hD3vlip : ∀ s, LipschitzWith M₃ (iteratedFDeriv ℝ 3 (v s))) :
    Nonempty (RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E) (X := v) s t₀) := by
  have hn1 : (1 : WithTop ℕ∞) ≤ n := le_trans (by norm_num) hn
  have hn2 : (2 : WithTop ℕ∞) ≤ n := le_trans (by norm_num) hn
  exact exists_diffeomorph3GaugeFlowOn_of_field_jet (t₀ := t₀) s
    hv hvc
    (fun s ξ => hasFDerivAt_fderiv_of_contDiff_uncurry h hn1 s ξ)
    (continuous_fderiv_of_contDiff_uncurry h hn1)
    hDvlip
    (fun s ξ => hasFDerivAt_fderiv_fderiv_of_contDiff_uncurry h hn2 s ξ)
    (continuous_fderiv_fderiv_of_contDiff_uncurry h hn2)
    hD2vclip
    hD2vmlip
    (fun s ξ => hasFDerivAt_fderiv_iteratedFDeriv_two_of_contDiff_uncurry h hn s ξ)
    (continuous_fderiv_iteratedFDeriv_two_of_contDiff_uncurry h hn)
    hD3vmlip
    (continuous_iteratedFDeriv_three_of_contDiff_uncurry h hn)
    hD3vlip
    (fun s ξ => fderiv_fderiv_eq_curry2_iteratedFDeriv_two (v s) ξ)
    (fun s ξ => fderiv_iteratedFDeriv_two_eq_curryLeft (v s) ξ)

/-- **Model-manifold `C³` flow family + ODE equation from a single joint-`ContDiff` field.**
The `ContDiff`-packaged form of `exists_flow_diffeomorph_three_hasMFDerivAt`: from a single
`ContDiff ℝ n (Function.uncurry v)` hypothesis (`3 ≤ n`) plus the honest top-order Lipschitz controls,
there is a *single* flow family `Φ` on the model manifold `𝓘(ℝ, E)` that simultaneously anchors
(`Φ z t₀ = z`), solves the manifold integral-curve ODE derivative equation at every time, and is —
for every `t` — the coercion of a genuine bundled `Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E 3`.  The entire
`C^{3,1}` Fréchet jet and its `HasFDerivAt`/joint-continuity/compatibility obligations are discharged
from the one smoothness hypothesis.

This is the second documented per-chart export the general compact-manifold lift transports (a
first-class `C³` self-diffeomorphism family that *is* the flow of the chart-local field), now stated
behind the single `ContDiff` hypothesis, completing the `_of_contDiff` entry points to both
model-manifold gauge-flow exports.  A pure assembly of the `FieldJetContDiff` jet extraction fed into
`exists_flow_diffeomorph_three_hasMFDerivAt`. -/
theorem exists_flow_diffeomorph_three_hasMFDerivAt_of_contDiff
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {v : ℝ → E → E} {K L M₂ M₃ N : ℝ≥0} {t₀ : ℝ} {n : WithTop ℕ∞}
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 3 ≤ n)
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    (hDvlip : ∀ s, LipschitzWith L (fderiv ℝ (v s)))
    (hD2vclip : ∀ s, LipschitzWith M₂ (fderiv ℝ (fderiv ℝ (v s))))
    (hD2vmlip : ∀ s, LipschitzWith N (iteratedFDeriv ℝ 2 (v s)))
    (hD3vmlip : ∀ s, LipschitzWith M₃ (fderiv ℝ (iteratedFDeriv ℝ 2 (v s))))
    (hD3vlip : ∀ s, LipschitzWith M₃ (iteratedFDeriv ℝ 3 (v s))) :
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧
      (∀ z t, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun τ => Φ z τ) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (v t (Φ z t)))) ∧
      ∀ t, ∃ F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E 3, ∀ z, F z = Φ z t := by
  have hn1 : (1 : WithTop ℕ∞) ≤ n := le_trans (by norm_num) hn
  have hn2 : (2 : WithTop ℕ∞) ≤ n := le_trans (by norm_num) hn
  exact exists_flow_diffeomorph_three_hasMFDerivAt (t₀ := t₀)
    hv hvc
    (fun s ξ => hasFDerivAt_fderiv_of_contDiff_uncurry h hn1 s ξ)
    (continuous_fderiv_of_contDiff_uncurry h hn1)
    hDvlip
    (fun s ξ => hasFDerivAt_fderiv_fderiv_of_contDiff_uncurry h hn2 s ξ)
    (continuous_fderiv_fderiv_of_contDiff_uncurry h hn2)
    hD2vclip
    hD2vmlip
    (fun s ξ => hasFDerivAt_fderiv_iteratedFDeriv_two_of_contDiff_uncurry h hn s ξ)
    (continuous_fderiv_iteratedFDeriv_two_of_contDiff_uncurry h hn)
    hD3vmlip
    (continuous_iteratedFDeriv_three_of_contDiff_uncurry h hn)
    hD3vlip
    (fun s ξ => fderiv_fderiv_eq_curry2_iteratedFDeriv_two (v s) ξ)
    (fun s ξ => fderiv_iteratedFDeriv_two_eq_curryLeft (v s) ξ)

/-!
## Compact-support jet bounds for the bump-globalised gauge field (Item 2 GAP 1)

The compact-manifold lift feeds `exists_diffeomorph3GaugeFlowOn_of_contDiff` a field
`v : ℝ → E → E` obtained by bump-cutting the chart pushforward field to a globally-`C^{3,1}`,
compactly-supported representative.  Its hypotheses demand *uniform-in-time* Lipschitz bounds on the
spatial-derivative fields `Dⁱ (v s)`.  These reduce to the following two purely model-space facts
about a jointly-`ContDiff`, compactly-supported two-variable function `F = uncurry v`:

* the `n`-th iterated derivative of a time slice `y ↦ F (s, y)` is dominated in norm by the full
  `n`-th iterated derivative of `F` at `(s, y)` (`norm_iteratedFDeriv_prodMk_left_le`); and
* consequently the slice iterated derivatives are **uniformly bounded** in `(s, y)` whenever `F` has
  compact support (`exists_bound_iteratedFDeriv_prodMk_left`).

Both are the reusable analytic core supplying the uniform jet bounds of the globalised field; no
gauge-flow content.
-/

/-- **Norm slice bound for iterated derivatives of a two-variable function.**  The `n`-th iterated
Fréchet derivative of the `s`-slice `y ↦ F (s, y)` of `F : ℝ × E → G` is bounded in norm by the full
`n`-th iterated derivative of `F` at `(s, y)`.

The slice factors as `(fun p ↦ F (p + (s, 0))) ∘ inr` with `inr : E →L[ℝ] ℝ × E` the norm-`≤ 1`
inclusion `y ↦ (0, y)`; iterated differentiation of that composition
(`ContinuousLinearMap.iteratedFDeriv_comp_right`) precomposes the full iterated derivative with `inr`
in every slot, and the constant shift moves the base point from `inr x` to `(s, x)`
(`iteratedFDeriv_comp_add_right`).  Taking norms with `‖inr‖ ≤ 1` gives the bound. -/
theorem norm_iteratedFDeriv_prodMk_left_le
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ℝ × E → G} {N : WithTop ℕ∞} (hF : ContDiff ℝ N F)
    {n : ℕ} (hn : (n : WithTop ℕ∞) ≤ N) (s : ℝ) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => F (s, y)) x‖ ≤ ‖iteratedFDeriv ℝ n F (s, x)‖ := by
  have hcomp : (fun y => F (s, y))
      = (fun p : ℝ × E => F (p + (s, 0))) ∘ (ContinuousLinearMap.inr ℝ ℝ E : E → ℝ × E) := by
    funext y
    simp only [Function.comp_apply, ContinuousLinearMap.inr_apply, Prod.mk_add_mk,
      zero_add, add_zero]
  have hG : ContDiff ℝ N (fun p : ℝ × E => F (p + (s, 0))) :=
    hF.comp (contDiff_id.add contDiff_const)
  rw [hcomp,
    ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.inr ℝ ℝ E) hG x hn]
  have hshift : iteratedFDeriv ℝ n (fun p : ℝ × E => F (p + (s, 0)))
        (ContinuousLinearMap.inr ℝ ℝ E x)
      = iteratedFDeriv ℝ n F ((s, x) : ℝ × E) := by
    rw [iteratedFDeriv_comp_add_right n (s, 0) (ContinuousLinearMap.inr ℝ ℝ E x)]
    congr 1
    simp only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, zero_add, add_zero]
  rw [hshift]
  calc ‖(iteratedFDeriv ℝ n F ((s, x) : ℝ × E)).compContinuousLinearMap
          (fun _ : Fin n => ContinuousLinearMap.inr ℝ ℝ E)‖
      ≤ ‖iteratedFDeriv ℝ n F ((s, x) : ℝ × E)‖
          * ∏ _i : Fin n, ‖ContinuousLinearMap.inr ℝ ℝ E‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ n F ((s, x) : ℝ × E)‖ * 1 := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact Finset.prod_le_one (fun i _ => norm_nonneg _)
          (fun i _ => ContinuousLinearMap.norm_inr_le_one ℝ ℝ E)
    _ = ‖iteratedFDeriv ℝ n F ((s, x) : ℝ × E)‖ := mul_one _

/-- **Uniform bound on the slice iterated derivatives of a compactly-supported field.**  If
`F : ℝ × E → G` is jointly `C^N` with compact support then, for each `n ≤ N`, the `n`-th iterated
derivative of every time slice `y ↦ F (s, y)` is uniformly bounded in `(s, y)`.  Combines the slice
bound `norm_iteratedFDeriv_prodMk_left_le` with the global bound on `iteratedFDeriv ℝ n F` obtained
from compact support (`HasCompactSupport.iteratedFDeriv` + `HasCompactSupport.exists_bound_of_continuous`).
This is the uniform-in-time control the globalised gauge field's jet Lipschitz bounds are built on. -/
theorem exists_bound_iteratedFDeriv_prodMk_left
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ℝ × E → G} {N : WithTop ℕ∞} (hF : ContDiff ℝ N F) (hcs : HasCompactSupport F)
    {n : ℕ} (hn : (n : WithTop ℕ∞) ≤ N) :
    ∃ C : ℝ, ∀ (s : ℝ) (x : E), ‖iteratedFDeriv ℝ n (fun y => F (s, y)) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (hcs.iteratedFDeriv (𝕜 := ℝ) n).exists_bound_of_continuous
    (hF.continuous_iteratedFDeriv hn)
  exact ⟨C, fun s x => (norm_iteratedFDeriv_prodMk_left_le hF hn s x).trans (hC (s, x))⟩

/-- **Uniform-in-time Lipschitz bound on the slice iterated derivatives of a compactly-supported
field.**  If `F : ℝ × E → G` is jointly `C^N` with compact support and `n + 1 ≤ N`, then there is a
single Lipschitz constant `C` such that the `n`-th iterated derivative of *every* time slice
`y ↦ F (s, y)` is `C`-Lipschitz.

This is the exact shape of the uniform derivative-field Lipschitz hypotheses
(`hD2vmlip`/`hD3vlip`) consumed by `exists_diffeomorph3GaugeFlowOn_of_contDiff`: the constant is
obtained from the uniform order-`(n+1)` bound `exists_bound_iteratedFDeriv_prodMk_left`, converted to
a Lipschitz estimate via `norm_fderiv_iteratedFDeriv` (`‖fderiv (Dⁿf)‖ = ‖Dⁿ⁺¹f‖`) and
`lipschitzWith_of_nnnorm_fderiv_le`. -/
theorem exists_lipschitzWith_iteratedFDeriv_prodMk_left
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ℝ × E → G} {N : WithTop ℕ∞} (hF : ContDiff ℝ N F) (hcs : HasCompactSupport F)
    {n : ℕ} (hn : ((n + 1 : ℕ) : WithTop ℕ∞) ≤ N) :
    ∃ C : ℝ≥0, ∀ s : ℝ, LipschitzWith C (iteratedFDeriv ℝ n (fun y => F (s, y))) := by
  obtain ⟨C₀, hC₀⟩ := exists_bound_iteratedFDeriv_prodMk_left (n := n + 1) hF hcs hn
  refine ⟨NNReal.mk (max C₀ 0) (le_max_right _ _), fun s => ?_⟩
  have hslice : ContDiff ℝ N (fun y => F (s, y)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  have hle : (1 : WithTop ℕ∞) + (n : WithTop ℕ∞) ≤ N := by
    have h1 : (1 : WithTop ℕ∞) + (n : WithTop ℕ∞) = ((n + 1 : ℕ) : WithTop ℕ∞) := by
      push_cast; exact add_comm _ _
    rw [h1]; exact hn
  refine lipschitzWith_of_nnnorm_fderiv_le
    ((hslice.iteratedFDeriv_right (m := 1) hle).differentiable one_ne_zero) (fun x => ?_)
  have hb : ‖fderiv ℝ (iteratedFDeriv ℝ n (fun y => F (s, y))) x‖ ≤ max C₀ 0 := by
    rw [norm_fderiv_iteratedFDeriv]
    exact (hC₀ s x).trans (le_max_left _ _)
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mk]
  exact hb

/-- **Uniform-in-time Lipschitz bound on the time slices themselves.**  If `F : ℝ × E → G` is jointly
`C^N` with compact support and `1 ≤ N`, there is a single Lipschitz constant `C` with every time slice
`y ↦ F (s, y)` being `C`-Lipschitz.  This is the `hv` datum of `exists_diffeomorph3GaugeFlowOn_of_contDiff`
(the field itself uniformly Lipschitz).  Proof: the uniform order-`1` slice bound
`exists_bound_iteratedFDeriv_prodMk_left` combined with `norm_iteratedFDeriv_one`
(`‖D¹f‖ = ‖fderiv f‖`) and `lipschitzWith_of_nnnorm_fderiv_le`. -/
theorem exists_lipschitzWith_prodMk_left
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : ℝ × E → G} {N : WithTop ℕ∞} (hF : ContDiff ℝ N F) (hcs : HasCompactSupport F)
    (hN : 1 ≤ N) :
    ∃ C : ℝ≥0, ∀ s : ℝ, LipschitzWith C (fun y => F (s, y)) := by
  obtain ⟨C₀, hC₀⟩ := exists_bound_iteratedFDeriv_prodMk_left (n := 1) hF hcs (by exact_mod_cast hN)
  have hN0 : N ≠ 0 := by rintro rfl; exact absurd hN (by norm_num)
  refine ⟨NNReal.mk (max C₀ 0) (le_max_right _ _), fun s => ?_⟩
  have hslice : ContDiff ℝ N (fun y => F (s, y)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  refine lipschitzWith_of_nnnorm_fderiv_le (hslice.differentiable hN0) (fun x => ?_)
  have hb : ‖fderiv ℝ (fun y => F (s, y)) x‖ ≤ max C₀ 0 := by
    rw [← norm_iteratedFDeriv_one]
    exact (hC₀ s x).trans (le_max_left _ _)
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mk]
  exact hb

/-- **Lipschitz transport across the `fderiv`↔iterated-derivative currying isometry.**  Since
`fderiv ℝ (iteratedFDeriv ℝ n f) = e ∘ iteratedFDeriv ℝ (n+1) f` with `e` the currying
`LinearIsometryEquiv` (`fderiv_iteratedFDeriv`), a Lipschitz bound on the `(n+1)`-st iterated
derivative transports to the same bound on `fderiv` of the `n`-th iterated derivative.  This turns the
`iteratedFDeriv`-shaped bounds of `exists_lipschitzWith_iteratedFDeriv_prodMk_left` into the
`fderiv (iteratedFDeriv …)`-shaped hypothesis `hD3vmlip` of `exists_diffeomorph3GaugeFlowOn_of_contDiff`. -/
theorem lipschitzWith_fderiv_iteratedFDeriv_of_lipschitzWith_iteratedFDeriv_succ
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → G} {C : ℝ≥0} {n : ℕ}
    (h : LipschitzWith C (iteratedFDeriv ℝ (n + 1) f)) :
    LipschitzWith C (fderiv ℝ (iteratedFDeriv ℝ n f)) := by
  rw [fderiv_iteratedFDeriv]
  exact (Isometry.lipschitzWith_iff C
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) G).isometry).mpr h

/-- **Model-manifold raw `C³` gauge-flow existence from a compactly-supported `C^N` field (`N ≥ 4`).**
The bump-globalised gauge field is a jointly-`ContDiff`, compactly-supported `v : ℝ → E → E`; from that
data *alone* (no separately-supplied jet Lipschitz constants) the raw `C³` DeTurck gauge-flow structure
`Diffeomorph3GaugeFlowOn (X := v) s t₀` is inhabited on the model manifold `E`.

Every uniform-in-time jet Lipschitz hypothesis of `exists_diffeomorph3GaugeFlowOn_of_contDiff` is
discharged from compact support:
* `hv` from `exists_lipschitzWith_prodMk_left`;
* `hD2vmlip` / `hD3vlip` from `exists_lipschitzWith_iteratedFDeriv_prodMk_left` (orders `2`, `3`);
* `hD3vmlip` by transporting the order-`3` bound through the currying isometry
  (`lipschitzWith_fderiv_iteratedFDeriv_of_lipschitzWith_iteratedFDeriv_succ`) — with the *same*
  constant `M₃` as `hD3vlip`;
* the nested-`fderiv` bounds `hDvlip` / `hD2vclip` through the two-fold curry `curry2`, which is
  norm-nonexpansive (`norm_curry2_le`) and linear (`curry2_sub`), hence `1`-Lipschitz, combined with
  the uniform order-`2` slice bound.

This is the compact-support entry point the general compact-manifold gauge-flow lift consumes after
bump-cutting the chart pushforward field to a globally-`C^{3,1}` representative. -/
theorem exists_diffeomorph3GaugeFlowOn_of_contDiff_hasCompactSupport
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {v : ℝ → E → E} {t₀ : ℝ} {N : WithTop ℕ∞} (s : Set ℝ)
    (hF : ContDiff ℝ N (Function.uncurry v))
    (hcs : HasCompactSupport (Function.uncurry v)) (hN : 4 ≤ N) :
    Nonempty (RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E) (X := v) s t₀) := by
  have hsl : ∀ σ : ℝ, (fun y => Function.uncurry v (σ, y)) = v σ := fun _ => rfl
  have hslc : ∀ σ : ℝ, ContDiff ℝ N (fun y => Function.uncurry v (σ, y)) :=
    fun _ => hF.comp (contDiff_const.prodMk contDiff_id)
  have hN1 : (1 : WithTop ℕ∞) ≤ N := le_trans (by norm_num) hN
  have hN2 : (2 : WithTop ℕ∞) ≤ N := le_trans (by norm_num) hN
  have hN3 : (3 : WithTop ℕ∞) ≤ N := le_trans (by norm_num) hN
  obtain ⟨K, hK⟩ := exists_lipschitzWith_prodMk_left hF hcs hN1
  obtain ⟨Nc, hNc⟩ :=
    exists_lipschitzWith_iteratedFDeriv_prodMk_left (n := 2) hF hcs (by exact_mod_cast hN3)
  obtain ⟨M₃, hM₃⟩ :=
    exists_lipschitzWith_iteratedFDeriv_prodMk_left (n := 3) hF hcs (by exact_mod_cast hN)
  obtain ⟨C₂, hC₂⟩ :=
    exists_bound_iteratedFDeriv_prodMk_left (n := 2) hF hcs (by exact_mod_cast hN2)
  have hcurry2 : LipschitzWith 1 (curry2 (E := E)) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro X Y
    rw [dist_eq_norm, dist_eq_norm, ← curry2_sub]
    simpa using norm_curry2_le (X - Y)
  refine exists_diffeomorph3GaugeFlowOn_of_contDiff
    (K := K) (L := NNReal.mk (max C₂ 0) (le_max_right _ _))
    (M₂ := 1 * Nc) (N := Nc) (M₃ := M₃) s hF hN3
    ?hv ?hvc ?hDvlip ?hD2vclip ?hD2vmlip ?hD3vmlip ?hD3vlip
  case hv => intro σ; rw [← hsl σ]; exact hK σ
  case hvc =>
    intro x
    exact hF.continuous.comp (continuous_id.prodMk continuous_const)
  case hDvlip =>
    intro σ
    rw [← hsl σ]
    refine lipschitzWith_of_nnnorm_fderiv_le
      (C := NNReal.mk (max C₂ 0) (le_max_right _ _))
      (((hslc σ).fderiv_right (m := 1) hN2).differentiable one_ne_zero) (fun x => ?_)
    rw [fderiv_fderiv_eq_curry2_iteratedFDeriv_two, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mk]
    calc ‖curry2 (iteratedFDeriv ℝ 2 (fun y => Function.uncurry v (σ, y)) x)‖
        ≤ ‖iteratedFDeriv ℝ 2 (fun y => Function.uncurry v (σ, y)) x‖ := norm_curry2_le _
      _ ≤ C₂ := hC₂ σ x
      _ ≤ max C₂ 0 := le_max_left _ _
  case hD2vclip =>
    intro σ
    rw [← hsl σ]
    have hmap : fderiv ℝ (fderiv ℝ (fun y => Function.uncurry v (σ, y)))
        = curry2 ∘ iteratedFDeriv ℝ 2 (fun y => Function.uncurry v (σ, y)) := by
      funext x; exact fderiv_fderiv_eq_curry2_iteratedFDeriv_two _ x
    rw [hmap]
    exact hcurry2.comp (hNc σ)
  case hD2vmlip => intro σ; rw [← hsl σ]; exact hNc σ
  case hD3vmlip =>
    intro σ
    rw [← hsl σ]
    exact lipschitzWith_fderiv_iteratedFDeriv_of_lipschitzWith_iteratedFDeriv_succ (n := 2) (hM₃ σ)
  case hD3vlip => intro σ; rw [← hsl σ]; exact hM₃ σ

/-- **A cutoff multiple of a locally-`C^n` field is globally `C^n` with compact support.**  If `w` is
`C^n` on an open set `U`, and `χ` is a globally-`C^n`, compactly-supported cutoff with `tsupport χ ⊆ U`,
then `fun x ↦ χ x • w x` is globally `C^n` and compactly supported.  This is the extension-by-zero step
of the bump-globalisation: at a point of `tsupport χ ⊆ U` both factors are `C^n` (`ContDiffOn.contDiffAt`
on the open `U`); off `tsupport χ` the product vanishes on the neighbourhood `(tsupport χ)ᶜ`
(`image_eq_zero_of_notMem_tsupport`).  It globalises the chart-local pushforward field to a field defined
and regular on all of the model space with compact support, the exact input shape of
`exists_diffeomorph3GaugeFlowOn_of_contDiff_hasCompactSupport`. -/
theorem contDiff_and_hasCompactSupport_cutoff_smul
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : WithTop ℕ∞} {U : Set H} {w : H → V} {χ : H → ℝ}
    (hU : IsOpen U) (hw : ContDiffOn ℝ n w U)
    (hχ : ContDiff ℝ n χ) (hχc : HasCompactSupport χ) (hsub : tsupport χ ⊆ U) :
    ContDiff ℝ n (fun x => χ x • w x) ∧ HasCompactSupport (fun x => χ x • w x) := by
  refine ⟨contDiff_iff_contDiffAt.mpr (fun x => ?_), ?_⟩
  · by_cases hx : x ∈ tsupport χ
    · exact hχ.contDiffAt.smul (hw.contDiffAt (hU.mem_nhds (hsub hx)))
    · refine (contDiffAt_const (c := (0 : V))).congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
  · refine hχc.of_isClosed_subset (isClosed_tsupport _) (closure_mono ?_)
    intro x hx
    rw [Function.mem_support] at hx ⊢
    exact fun hχx => hx (by rw [hχx, zero_smul])

/-- **Bump-globalised chart pushforward field: globally `C^N` with compact support.**  Combining the
joint-in-time field regularity `contDiffOn_prod_chartPushforwardField` with the extension-by-zero cutoff
product `contDiff_and_hasCompactSupport_cutoff_smul`: given joint `C^N` regularity of the time-dependent
tangent-bundle section `(τ, y) ↦ ⟨y, X τ y⟩` on `ℝ ×ˢ (extChartAt I p).source`, and a globally-`C^N`,
compactly-supported cutoff `χ : ℝ × E → ℝ` with `tsupport χ ⊆ ℝ ×ˢ (extChartAt I p).target`, the cutoff
multiple `(τ, q) ↦ χ (τ, q) • chartPushforwardField I X p τ q` is globally `ContDiff ℝ N` on the model
product `ℝ × E` and has compact support.  The chart target is open
(`isOpen_extChartAt_target`, using `I.Boundaryless`), so the field is `C^N` on the open tube where the
cutoff lives.  This is GAP-1 step (iii): the compactly-supported `C^N` field
`v := Function.curry (χ • chartPushforwardField …)` whose `(ContDiff, HasCompactSupport)` pair is exactly
the input consumed by `exists_diffeomorph3GaugeFlowOn_of_contDiff_hasCompactSupport` to produce the model
gauge flow `Ψ`. -/
theorem contDiff_hasCompactSupport_cutoff_chartPushforwardField
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {N : WithTop ℕ∞} [IsManifold I N M]
    [ContMDiffVectorBundle N E (TangentSpace I : M → Type _) I]
    {X : ℝ → M → E} {p : M}
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) N
      (fun r : ℝ × M => (⟨r.2, X r.1 r.2⟩ : TangentBundle I M))
      (Set.univ ×ˢ (extChartAt I p).source))
    {χ : ℝ × E → ℝ} (hχ : ContDiff ℝ N χ) (hχc : HasCompactSupport χ)
    (hsub : tsupport χ ⊆ Set.univ ×ˢ (extChartAt I p).target) :
    ContDiff ℝ N (fun r : ℝ × E => χ r •
        PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p r.1 r.2) ∧
      HasCompactSupport (fun r : ℝ × E => χ r •
        PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p r.1 r.2) :=
  contDiff_and_hasCompactSupport_cutoff_smul
    (isOpen_univ.prod (isOpen_extChartAt_target p))
    (PoincareCurvature.GaugeFlowAssembly.contDiffOn_prod_chartPushforwardField hX) hχ hχc hsub

/-- **Model gauge flow `Ψ` from a jointly-`C^N` section plus a chart-target cutoff (`N ≥ 4`).**  The
capstone of GAP-1 steps (i)–(iv): from joint `C^N` regularity of the time-dependent tangent-bundle
section `(τ, y) ↦ ⟨y, X τ y⟩` on `ℝ ×ˢ (extChartAt I p).source` and a globally-`C^N`, compactly-supported
cutoff `χ` with `tsupport χ ⊆ ℝ ×ˢ (extChartAt I p).target`, the bump-globalised chart pushforward field
`v := fun τ q ↦ χ (τ, q) • chartPushforwardField I X p τ q` is a compactly-supported `C^N` field on the
model manifold `E`, and hence (`exists_diffeomorph3GaugeFlowOn_of_contDiff_hasCompactSupport`) inhabits
the raw `C³` DeTurck gauge-flow structure `Diffeomorph3GaugeFlowOn (X := v) s t₀`.  This is the model
comparison flow `Ψ` used by `contMDiffOn_of_extChartAt_conjugation'` to transfer spatial `C³` regularity
to the compact manifold `M` (step (v), `hslicesC3`); only the construction of the cutoff `χ` around the
compact trajectory (step (ii)) remains between this and the compact-manifold gauge-flow lift. -/
theorem exists_diffeomorph3GaugeFlowOn_cutoff_chartPushforwardField
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {N : WithTop ℕ∞} [IsManifold I N M]
    [ContMDiffVectorBundle N E (TangentSpace I : M → Type _) I]
    {X : ℝ → M → E} {p : M}
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) N
      (fun r : ℝ × M => (⟨r.2, X r.1 r.2⟩ : TangentBundle I M))
      (Set.univ ×ˢ (extChartAt I p).source))
    {χ : ℝ × E → ℝ} (hχ : ContDiff ℝ N χ) (hχc : HasCompactSupport χ)
    (hsub : tsupport χ ⊆ Set.univ ×ˢ (extChartAt I p).target)
    (hN : 4 ≤ N) (s : Set ℝ) (t₀ : ℝ) :
    Nonempty (RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E)
      (X := fun τ q => χ (τ, q) •
        PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ q) s t₀) := by
  obtain ⟨hF, hcs⟩ :=
    contDiff_hasCompactSupport_cutoff_chartPushforwardField hX hχ hχc hsub
  exact exists_diffeomorph3GaugeFlowOn_of_contDiff_hasCompactSupport s hF hcs hN

/-- **Smooth cutoff equal to `1` near a compact set, supported in an open set (GAP-1 step (ii)).**
On a finite-dimensional real normed space `F`, for a compact set `K` inside an open set `U`, there is
a globally-`C^n` function `χ : F → ℝ` that
  * has compact support,
  * has `tsupport χ ⊆ U`,
  * is identically `1` on a neighbourhood of `K` (`∀ᶠ x in 𝓝ˢ K, χ x = 1`), and
  * takes values in `[0, 1]`.

This is the cutoff datum consumed by `exists_diffeomorph3GaugeFlowOn_cutoff_chartPushforwardField`:
applied with `F := ℝ × E`, `U := Set.univ ×ˢ (extChartAt I p).target` (open) and `K` the compact
trajectory window, it supplies the `hχ`/`hχc`/`hsub` hypotheses of that capstone, while the extra
`χ ≡ 1` near `K` clause is what makes the bump-cut field agree with the un-cut chart pushforward field
on the orbit (the input to the step-(v) integral-curve comparison
`extChartAt_comp_eqOn_of_lipschitzOnWith`).

Construction: interpose (`exists_compact_between`, using local compactness) a compact `L` with
`K ⊆ interior L ⊆ L ⊆ U`; view `F` as the model manifold `𝓘(ℝ, F)` and apply the manifold cutoff
`exists_contMDiffMap_one_nhds_of_subset_interior` with `s := K`, `t := L` to get a smooth `f` equal to
`1` near `K` and vanishing off `L`; `support f ⊆ L` (compact) gives `HasCompactSupport` and
`tsupport f ⊆ L ⊆ U`; the `ContMDiff → ContDiff` transfer is `contMDiff_iff_contDiff`. -/
theorem exists_contDiff_cutoff_one_nhdsSet_of_isCompact
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {n : ℕ∞} {K U : Set F} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : F → ℝ, ContDiff ℝ n χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨L, hLc, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨f, h1, h0, hIcc⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, F) hK.isClosed hKL (n := n)
  have hsupp : Function.support (f : F → ℝ) ⊆ L := by
    intro x hx
    by_contra hxL
    exact hx (h0 x hxL)
  have hcs : HasCompactSupport (f : F → ℝ) :=
    HasCompactSupport.of_support_subset_isCompact hLc hsupp
  refine ⟨(f : F → ℝ), contMDiff_iff_contDiff.mp f.contMDiff, hcs, ?_, h1, hIcc⟩
  calc tsupport (f : F → ℝ) = closure (Function.support (f : F → ℝ)) := rfl
    _ ⊆ closure L := closure_mono hsupp
    _ = L := hLc.isClosed.closure_eq
    _ ⊆ U := hLU

/-- **Model gauge flow `Ψ` from an internally-constructed chart-target cutoff around a compact orbit
window (`4 ≤ n`).**  Removes the "cutoff assumed" residual of
`exists_diffeomorph3GaugeFlowOn_cutoff_chartPushforwardField`: given only the joint `C^n` section
regularity `hX` and a *compact* trajectory window `K ⊆ ℝ ×ˢ (extChartAt I p).target`, this constructs
the cutoff `χ` itself (`exists_contDiff_cutoff_one_nhdsSet_of_isCompact` on the finite-dimensional
model `ℝ × E`, with `U := ℝ ×ˢ (extChartAt I p).target` open via `isOpen_extChartAt_target`) and hands
back both

  * the guarantee `∀ᶠ r in 𝓝ˢ K, χ r = 1` — so where `χ ≡ 1` the bump-cut field
    `(τ, q) ↦ χ (τ, q) • chartPushforwardField I X p τ q` agrees with the un-cut chart pushforward
    field, the hypothesis the step-(v) integral-curve comparison
    `extChartAt_comp_eqOn_of_lipschitzOnWith` consumes on the orbit; and
  * the model comparison flow `Ψ`, i.e. `Nonempty (Diffeomorph3GaugeFlowOn … s t₀)` for that cut field
    (`exists_diffeomorph3GaugeFlowOn_cutoff_chartPushforwardField`).

This is GAP-1 steps (ii)+(iv) packaged for the compact-manifold spatial-`C³` transfer (step (v),
`hslicesC3`); the remaining residual is supplying `hX` from the actual gauge field `X`. -/
theorem exists_diffeomorph3GaugeFlowOn_cutoff_eqOne_of_isCompact_window
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {n : ℕ∞} [IsManifold I n M]
    [ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I]
    {X : ℝ → M → E} {p : M}
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) n
      (fun r : ℝ × M => (⟨r.2, X r.1 r.2⟩ : TangentBundle I M))
      (Set.univ ×ˢ (extChartAt I p).source))
    {K : Set (ℝ × E)} (hK : IsCompact K)
    (hKU : K ⊆ Set.univ ×ˢ (extChartAt I p).target)
    (hn : 4 ≤ n) (s : Set ℝ) (t₀ : ℝ) :
    ∃ χ : ℝ × E → ℝ, (∀ᶠ r in 𝓝ˢ K, χ r = 1) ∧
      Nonempty (RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E)
        (X := fun τ q => χ (τ, q) •
          PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ q) s t₀) := by
  obtain ⟨χ, hχC, hχcs, hχsub, hχ1, _hχIcc⟩ :=
    exists_contDiff_cutoff_one_nhdsSet_of_isCompact (n := n) hK
      (isOpen_univ.prod (isOpen_extChartAt_target p)) hKU
  exact ⟨χ, hχ1,
    exists_diffeomorph3GaugeFlowOn_cutoff_chartPushforwardField hX hχC hχcs hχsub
      (by simpa using WithTop.coe_le_coe.mpr hn) s t₀⟩

/-- **Model gauge-flow slices are `ContDiff ℝ 3` (the step-(v) `hΨ` datum).**  On the model manifold
`E`, every time slice `G.maps3 t : E ≃ₘ^3⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E` of a raw `C³` gauge-flow witness is a
bundled `C³` self-diffeomorphism, so its underlying map is `ContDiff ℝ 3` (`Diffeomorph.contMDiff`
followed by the model-space `contMDiff_iff_contDiff`).  This is exactly the `hΨ : ContDiff ℝ 3 Ψ`
hypothesis consumed by the chart-conjugation spatial-`C³` transfer
`GaugeFlowAssembly.contMDiffOn_of_extChartAt_conjugation'` when the comparison flow `Ψ := G.maps3 t`
is the model gauge flow produced by `exists_diffeomorph3GaugeFlowOn_cutoff_eqOne_of_isCompact_window`
(GAP-1 step (v)). -/
theorem contDiff_three_maps3_of_model_diffeomorph3GaugeFlowOn
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {Xc : CovariantDerivative.TimeDependentVectorField (I := 𝓘(ℝ, E)) (M := E)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E) Xc s t₀) (t : ℝ) :
    ContDiff ℝ 3 (G.maps3 t : E → E) :=
  contMDiff_iff_contDiff.mp (G.maps3 t).contMDiff

/-- **Model gauge-flow curves are integral curves of the field (ordinary within-set derivative).**  On
the model manifold `E`, the manifold ODE readout `Diffeomorph3GaugeFlowOn.hasMFDerivWithinAt` becomes a
genuine `HasDerivWithinAt`: for a fixed base point `q`, the flow curve `τ ↦ G.maps3 τ q` has, at every
time `t ∈ s`, derivative `Xc t (G.maps3 t q)` (the field value at the current position).  The manifold
Fréchet derivative `(1).smulRight (Xc t (G.maps3 t q))` transfers to the ordinary derivative via the
model-space `HasMFDerivWithinAt.hasFDerivWithinAt` and `smulRight_one_eq_toSpanSingleton`.

This is the `hg'` datum consumed by `GaugeFlowAssembly.extChartAt_comp_eqOn_of_lipschitzOnWith`: with
`g := τ ↦ G.maps3 τ q` the model comparison curve, on the region where the cutoff `χ ≡ 1` the field
`Xc = χ • chartPushforwardField` reduces to `chartPushforwardField`, so this readout supplies the
integral-curve hypothesis of the step-(v) temporal uniqueness comparison. -/
theorem hasDerivWithinAt_maps3_eval_of_model_diffeomorph3GaugeFlowOn
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {Xc : CovariantDerivative.TimeDependentVectorField (I := 𝓘(ℝ, E)) (M := E)}
    {s : Set ℝ} {t₀ : ℝ}
    (G : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E) Xc s t₀)
    {t : ℝ} (ht : t ∈ s) (q : E) :
    HasDerivWithinAt (fun τ : ℝ => (G.maps3 τ) q) (Xc t ((G.maps3 t) q)) s t := by
  have hfd := (G.hasMFDerivWithinAt ht q).hasFDerivWithinAt
  rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton] at hfd
  exact hasDerivWithinAt_iff_hasFDerivWithinAt.mpr hfd

/-- **The `hg'` datum of the step-(v) glue: the model comparison curve is a full `HasDerivAt` integral
curve of the *uncut* `chartPushforwardField` wherever the cutoff `χ ≡ 1`.**  For the model gauge flow
`G` of the cut field `fun τ q ↦ χ (τ, q) • chartPushforwardField I X p τ q` produced by
`exists_diffeomorph3GaugeFlowOn_cutoff_chartPushforwardField` /
`exists_diffeomorph3GaugeFlowOn_cutoff_eqOne_of_isCompact_window`, on an open time window
(`hs : s ∈ 𝓝 t`) and at a base point `q` whose current position `(G.maps3 t) q` lies in the region where
the cutoff equals one (`hχ`), the within-set flow-ODE readout
`hasDerivWithinAt_maps3_eval_of_model_diffeomorph3GaugeFlowOn` — which carries the *cut* field value
`χ (t, (G.maps3 t) q) • chartPushforwardField …` — collapses to the un-cut field
(`1 • chartPushforwardField = chartPushforwardField`, `one_smul`) and upgrades from `HasDerivWithinAt` to
`HasDerivAt` via the window neighbourhood (`HasDerivWithinAt.hasDerivAt`).

This is exactly the shape of the
`hg' : ∀ t ∈ Set.Ioo a b, HasDerivAt g (chartPushforwardField I X p t (g t)) t` hypothesis consumed by
`GaugeFlowAssembly.extChartAt_comp_eqOn_of_lipschitzOnWith`, with the model comparison curve
`g := fun τ ↦ (G.maps3 τ) q`.  The `χ ≡ 1` fact `hχ` is the pointwise face of the orbit-containment
control (supplied separately), keeping this readout free of that delicate step. -/
theorem hasDerivAt_maps3_eval_of_cutoff_eqOne
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {X : ℝ → M → E} {p : M} {χ : ℝ × E → ℝ} {s : Set ℝ} {t₀ : ℝ}
    (G : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E)
      (X := fun τ q => χ (τ, q) •
        PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ q) s t₀)
    {t : ℝ} (hs : s ∈ 𝓝 t) (ht : t ∈ s) (q : E)
    (hχ : χ (t, (G.maps3 t) q) = 1) :
    HasDerivAt (fun τ : ℝ => (G.maps3 τ) q)
      (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p t ((G.maps3 t) q)) t := by
  have h := hasDerivWithinAt_maps3_eval_of_model_diffeomorph3GaugeFlowOn G ht q
  have key : (fun τ q => χ (τ, q) •
        PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ q) t ((G.maps3 t) q)
      = PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p t ((G.maps3 t) q) := by
    show χ (t, (G.maps3 t) q) •
        PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p t ((G.maps3 t) q)
        = PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p t ((G.maps3 t) q)
    rw [hχ, one_smul]
  rw [← key]
  exact h.hasDerivAt hs

/-- **Step-(v) uniqueness packaging: the manifold-flow chart representation equals the model
`G.maps3`-curve on the window, modulo orbit-containment hypotheses.**  Instantiates the temporal
integral-curve uniqueness comparison
`GaugeFlowAssembly.extChartAt_comp_eqOn_of_lipschitzOnWith` with the model gauge flow `G` (of the cut
field `χ • chartPushforwardField`) as the comparison curve `g := fun τ ↦ (G.maps3 τ) (extChartAt I p x)`,
supplying the `hg'` integral-curve hypothesis via `hasDerivAt_maps3_eval_of_cutoff_eqOne` on the region
where `χ ≡ 1`.  Given the raw manifold flow's ODE (`hγ`) and chart-source containment (`hγ_src`), the
time-uniform field Lipschitz bound (`hlip`, e.g. from
`exists_lipschitzOnWith_forall_mem_Icc_chartPushforwardField`), the orbit-containment facts
(`hχ` — the cutoff equals one along the model curve; `hγ_mem`/`hg_mem` — both curves stay in the state
tube), and agreement at `t₀` (`heq`), the two curves coincide on the whole open window `Set.Ioo a b`.

Evaluated at any interior time `t`, this yields the *spatial conjugation identity*
`extChartAt I p (γ t) = (G.maps3 t) (extChartAt I p x)` — the `hconj` datum fed (together with the model
slice `C³` bound `contDiff_three_maps3_of_model_diffeomorph3GaugeFlowOn`) to
`GaugeFlowAssembly.contMDiffOn_of_extChartAt_conjugation'` to establish the spatial-`C³` regularity
`hslicesC3` of the compact-manifold gauge flow (GAP-1 step (v)).  Only the orbit-containment facts remain
to be discharged; the uniqueness/derivative machinery is now fully assembled. -/
theorem extChartAt_comp_eqOn_maps3_of_cutoff_eqOne
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {X : ℝ → M → E} {p : M} {χ : ℝ × E → ℝ} {sTime : Set ℝ} {t₀' : ℝ}
    (G : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E)
      (X := fun τ q => χ (τ, q) •
        PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ q) sTime t₀')
    {γ : ℝ → M} {a b t₀ : ℝ} {K : NNReal} {state : ℝ → Set E} {x : M}
    (hnhds : ∀ τ ∈ Set.Ioo a b, sTime ∈ 𝓝 τ)
    (hγ : ∀ τ ∈ Set.Ioo a b,
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I γ (Set.Ioo a b) τ
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (γ τ))))
    (hγ_src : ∀ τ ∈ Set.Ioo a b, γ τ ∈ (extChartAt I p).source)
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hlip : ∀ τ ∈ Set.Ioo a b,
      LipschitzOnWith K
        (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ) (state τ))
    (hχ : ∀ τ ∈ Set.Ioo a b, χ (τ, (G.maps3 τ) (extChartAt I p x)) = 1)
    (hγ_mem : ∀ τ ∈ Set.Ioo a b, extChartAt I p (γ τ) ∈ state τ)
    (hg_mem : ∀ τ ∈ Set.Ioo a b, (G.maps3 τ) (extChartAt I p x) ∈ state τ)
    (heq : extChartAt I p (γ t₀) = (G.maps3 t₀) (extChartAt I p x)) :
    Set.EqOn (fun τ : ℝ => extChartAt I p (γ τ))
      (fun τ : ℝ => (G.maps3 τ) (extChartAt I p x)) (Set.Ioo a b) := by
  refine PoincareCurvature.GaugeFlowAssembly.extChartAt_comp_eqOn_of_lipschitzOnWith
    hγ hγ_src ht₀ hlip ?_ hγ_mem hg_mem heq
  intro τ hτ
  exact hasDerivAt_maps3_eval_of_cutoff_eqOne G (hnhds τ hτ)
    (mem_of_mem_nhds (hnhds τ hτ)) (extChartAt I p x) (hχ τ hτ)

/-- **Step-(v) capstone: the compact-manifold gauge-flow slice is `ContMDiffOn I I 3` on a chart patch,
modulo orbit-containment hypotheses.**  Assembles the full spatial-`C³` transfer of GAP-1 step (v) for a
single time slice `Φ t` on a patch `U ⊆ (chartAt H p).source`.  For each `x ∈ U`, the uniqueness
packaging `extChartAt_comp_eqOn_maps3_of_cutoff_eqOne` identifies the manifold-flow chart representation
`τ ↦ extChartAt I p (Φ τ x)` with the model `G.maps3`-curve `τ ↦ (G.maps3 τ) (extChartAt I p x)` on the
window; evaluated at the interior time `t` this is the spatial conjugation identity
`extChartAt I p (Φ t x) = (G.maps3 t) (extChartAt I p x)`.  Feeding that (as `hconj`) together with the
model slice-`C³` bound `contDiff_three_maps3_of_model_diffeomorph3GaugeFlowOn G t` (as `hΨ`) into the
chart-conjugation transfer `GaugeFlowAssembly.contMDiffOn_of_extChartAt_conjugation'` (single chart `p`
for source and target) yields `ContMDiffOn I I 3 (fun x ↦ Φ t x) U`.

This is exactly the per-patch content of the `hslicesC3` obligation
(`∀ t ∈ Set.Ioo a b, ContMDiff I I 3 (Φ t)`) consumed by
`GaugeFlowAssembly.exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3`: with the compact
manifold covered by finitely many such chart patches and the orbit-containment facts discharged, the
per-patch `ContMDiffOn` glue to global `ContMDiff` closes GAP 1.  The remaining input is purely the
orbit-containment control (the raw flow's chart-source stay `hγ_src`, the cutoff `hχ`, the tube
memberships `hγ_mem`/`hg_mem`); all derivative/uniqueness/`C³`-transfer machinery is assembled here. -/
theorem contMDiffOn_flowSlice_of_cutoff_orbit_control
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {X : ℝ → M → E} {p : M} {χ : ℝ × E → ℝ} {sTime : Set ℝ} {t₀' : ℝ}
    (G : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E)
      (X := fun τ q => χ (τ, q) •
        PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ q) sTime t₀')
    (Φ : ℝ → M → M) {U : Set M} {a b t₀ t : ℝ} {K : NNReal} {state : ℝ → Set E}
    (hU : U ⊆ (chartAt H p).source)
    (ht : t ∈ Set.Ioo a b)
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hnhds : ∀ τ ∈ Set.Ioo a b, sTime ∈ 𝓝 τ)
    (hlip : ∀ τ ∈ Set.Ioo a b,
      LipschitzOnWith K
        (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ) (state τ))
    (hγ : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b,
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun σ : ℝ => Φ σ x) (Set.Ioo a b) τ
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (Φ τ x))))
    (hγ_src : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b, Φ τ x ∈ (extChartAt I p).source)
    (hχ : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b, χ (τ, (G.maps3 τ) (extChartAt I p x)) = 1)
    (hγ_mem : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b, extChartAt I p (Φ τ x) ∈ state τ)
    (hg_mem : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b, (G.maps3 τ) (extChartAt I p x) ∈ state τ)
    (heq : ∀ x ∈ U, extChartAt I p (Φ t₀ x) = (G.maps3 t₀) (extChartAt I p x)) :
    ContMDiffOn I I 3 (fun x : M => Φ t x) U := by
  have hFU : Set.MapsTo (fun x : M => Φ t x) U (chartAt H p).source := by
    intro x hx
    have hsrc := hγ_src x hx t ht
    rwa [extChartAt_source] at hsrc
  refine PoincareCurvature.GaugeFlowAssembly.contMDiffOn_of_extChartAt_conjugation'
    (x₀ := p) (y₀ := p) hU
    (contDiff_three_maps3_of_model_diffeomorph3GaugeFlowOn G t) hFU ?_
  intro x hx
  have hEqOn := extChartAt_comp_eqOn_maps3_of_cutoff_eqOne (γ := fun σ : ℝ => Φ σ x) G hnhds
    (hγ x hx) (hγ_src x hx) ht₀ hlip (hχ x hx) (hγ_mem x hx) (hg_mem x hx) (heq x hx)
  exact hEqOn ht

/-- **Reducing the `hχ` orbit-containment face of the step-(v) capstone to graph-containment in the
compact cutoff window.**  The cutoff `χ` produced by
`exists_diffeomorph3GaugeFlowOn_cutoff_eqOne_of_isCompact_window` satisfies `∀ᶠ r in 𝓝ˢ K, χ r = 1` for
the chosen compact window `K`.  Hence whenever the graph `τ ↦ (τ, g τ)` of the model comparison curve
over the time set lies inside `K`, the cutoff equals one along it — `Filter.Eventually.self_of_nhdsSet`
turns `χ ≡ 1` on a neighbourhood of `K` into `χ ≡ 1` on `K` itself.  This packages the `hχ` hypothesis of
`extChartAt_comp_eqOn_maps3_of_cutoff_eqOne` / `contMDiffOn_flowSlice_of_cutoff_orbit_control` into the
single geometric orbit-containment fact "the model curve's graph stays in the cutoff window", isolating
the remaining delicate GAP-1 step (v) content to that flow-trajectory-confinement estimate. -/
theorem cutoff_eqOne_along_curve_of_graph_subset
    {χ : ℝ × E → ℝ} {g : ℝ → E} {s : Set ℝ} {K : Set (ℝ × E)}
    (hχ : ∀ᶠ r in 𝓝ˢ K, χ r = 1)
    (hgraph : ∀ τ ∈ s, ((τ, g τ) : ℝ × E) ∈ K) :
    ∀ τ ∈ s, χ (τ, g τ) = 1 :=
  fun τ hτ => hχ.self_of_nhdsSet (τ, g τ) (hgraph τ hτ)

/-- **Uniform short-time orbit-graph confinement — the *producing* companion of
`cutoff_eqOne_along_curve_of_graph_subset`.**  For a time-dependent flow map `Ψ : ℝ → E → E` whose
space-time graph map `z ↦ (z.1, Ψ z.1 z.2)` is (jointly) continuous at every *anchored* point `(t₀, q)`
with `q` ranging over a compact initial set `Q`, and an open space-time target `W` containing the whole
anchored graph `{(t₀, Ψ t₀ q) | q ∈ Q}`, there is an open time window `Set.Ioo a b ∋ t₀` on which **every**
orbit graph stays in `W`:
`∀ τ ∈ Set.Ioo a b, ∀ q ∈ Q, (τ, Ψ τ q) ∈ W`.

This is precisely the flow-trajectory-confinement mechanism the GAP-1 step-(v) orbit control needs:
applied with `W` the interior of the compact cutoff window `K` (so `W ⊆ K`), it produces the
`graph ⊆ K` hypothesis of `cutoff_eqOne_along_curve_of_graph_subset` *uniformly over a chart patch*,
once the joint continuity of the model gauge flow `(τ, q) ↦ (G.maps3 τ) q` is supplied.  The proof is
the tube-lemma confinement: `IsCompact.eventually_forall_of_forall_eventually` turns the pointwise
"the anchored orbit starts in the open target" facts (each an open-preimage neighbourhood via
`ContinuousAt.preimage_mem_nhds`) into a single *time* neighbourhood of `t₀` valid for all `q ∈ Q`,
whence an honest `Set.Ioo` window through `mem_nhds_iff_exists_Ioo_subset`. -/
theorem exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt
    {Ψ : ℝ → E → E} {Q : Set E} {W : Set (ℝ × E)} {t₀ : ℝ}
    (hQ : IsCompact Q) (hW : IsOpen W)
    (hgraph0 : ∀ q ∈ Q, ((t₀, Ψ t₀ q) : ℝ × E) ∈ W)
    (hcont : ∀ q ∈ Q, ContinuousAt (fun z : ℝ × E => Ψ z.1 z.2) (t₀, q)) :
    ∃ a b : ℝ, t₀ ∈ Set.Ioo a b ∧
      ∀ τ ∈ Set.Ioo a b, ∀ q ∈ Q, ((τ, Ψ τ q) : ℝ × E) ∈ W := by
  have hev : ∀ᶠ τ in 𝓝 t₀, ∀ q ∈ Q, ((τ, Ψ τ q) : ℝ × E) ∈ W := by
    refine IsCompact.eventually_forall_of_forall_eventually hQ ?_
    intro q hq
    have hgraphcont :
        ContinuousAt (fun z : ℝ × E => ((z.1, Ψ z.1 z.2) : ℝ × E)) (t₀, q) :=
      continuousAt_fst.prodMk (hcont q hq)
    exact hgraphcont.preimage_mem_nhds (hW.mem_nhds (hgraph0 q hq))
  obtain ⟨l, u, hmem, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hev
  exact ⟨l, u, hmem, fun τ hτ q hq => hsub hτ q hq⟩

/-- **Joint continuity of the model gauge flow `(τ, q) ↦ (G.maps3 τ) q`.**  On the model manifold `E`,
a raw `C³` gauge-flow witness `G : Diffeomorph3GaugeFlowOn (X := X) Set.univ t₀` of a *uniformly-in-time
globally `K`-Lipschitz* field `X : ℝ → E → E` has jointly continuous total flow map.  Each base curve
`τ ↦ (G.maps3 τ) q` is a genuine global `IsIntegralCurve` of `X` (the within-`Set.univ` manifold ODE
readout `hasDerivWithinAt_maps3_eval_of_model_diffeomorph3GaugeFlowOn` upgraded via `hasDerivWithinAt_univ`),
and the flow is anchored at `t₀` (`SmoothSelfDiffeomorph3Family.AnchoredAt.apply`), so the abstract
Grönwall joint-continuity theorem `continuous_flow` (uniform-exponential Lipschitz-in-initial-value ×
integral-curve continuity-in-time) applies verbatim.

This supplies the joint-continuity input that the tube-lemma confinement
`exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt` consumes: it is the concrete
`(τ, q) ↦ (G.maps3 τ) q` continuity the GAP-1 step-(v) orbit control needs for the model comparison
flow.  Crucially the joint continuity is *not* a missing Banach→manifold-ODE-regularity primitive here —
it is already available for globally-Lipschitz fields through `continuous_flow`, which the compactly
supported cut field `χ • chartPushforwardField` satisfies. -/
theorem continuous_maps3_of_lipschitzWith
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {X : ℝ → E → E} {t₀ : ℝ} {K : ℝ≥0}
    (G : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E) (X := X) Set.univ t₀)
    (hX : ∀ t, LipschitzWith K (X t)) :
    Continuous (fun p : ℝ × E => (G.maps3 p.1) p.2) := by
  have hΦ : ∀ q : E, IsIntegralCurve (fun τ : ℝ => (G.maps3 τ) q) X := by
    intro q t
    have h := hasDerivWithinAt_maps3_eval_of_model_diffeomorph3GaugeFlowOn G (Set.mem_univ t) q
    rwa [hasDerivWithinAt_univ] at h
  have h0 : ∀ q : E, (fun τ : ℝ => (G.maps3 τ) q) t₀ = q :=
    fun q => SmoothSelfDiffeomorph3Family.AnchoredAt.apply (Φ := G.maps3) G.anchored q
  exact continuous_flow (Φ := fun q τ => (G.maps3 τ) q) hX hΦ h0

/-- **Joint continuity of the model gauge flow from the cut field's `ContDiff`/compact-support data.**
The natural interface form of `continuous_maps3_of_lipschitzWith`: for a model gauge flow `G` of a field
`v : ℝ → E → E` whose uncurried form is `ContDiff ℝ N` (`1 ≤ N`) with compact support — exactly the shape
`contDiff_hasCompactSupport_cutoff_chartPushforwardField` produces for the bump-globalised cut field
`χ • chartPushforwardField` — the total flow map `(τ, q) ↦ (G.maps3 τ) q` is jointly continuous.  The
required uniform-in-time Lipschitz constant of the field is *derived* (not assumed) from the compact
support via `exists_lipschitzWith_prodMk_left`, so no free-floating Lipschitz hypothesis is needed. -/
theorem continuous_maps3_of_contDiff_hasCompactSupport
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {v : ℝ → E → E} {t₀ : ℝ} {N : WithTop ℕ∞}
    (hF : ContDiff ℝ N (Function.uncurry v))
    (hcs : HasCompactSupport (Function.uncurry v)) (hN : 1 ≤ N)
    (G : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E) (X := v) Set.univ t₀) :
    Continuous (fun p : ℝ × E => (G.maps3 p.1) p.2) := by
  obtain ⟨C, hC⟩ := exists_lipschitzWith_prodMk_left hF hcs hN
  exact continuous_maps3_of_lipschitzWith G (fun t => hC t)

/-- **Uniform short-time orbit-graph confinement for the model gauge flow.**  The direct composition of
`continuous_maps3_of_lipschitzWith` (joint continuity of `(τ, q) ↦ (G.maps3 τ) q`) with the tube-lemma
confinement `exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt`: for a model gauge flow `G`
of a uniformly `K`-Lipschitz field on `E`, a compact initial set `Q`, and an open space-time target `W`
containing the anchored graph `{(t₀, (G.maps3 t₀) q) | q ∈ Q}`, there is an honest open time window
`Set.Ioo a b ∋ t₀` on which **every** orbit graph `τ ↦ (τ, (G.maps3 τ) q)` (for `q ∈ Q`) stays in `W`.

Applied with `W` the interior of the compact cutoff window `K₀` (so `W ⊆ K₀`), this yields the
`graph ⊆ K₀` hypothesis consumed by `cutoff_eqOne_along_curve_of_graph_subset` **uniformly over a chart
patch** — closing the flow-trajectory-confinement obligation for the model comparison curve of GAP-1
step (v). -/
theorem exists_Ioo_forall_forall_graph_maps3_mem_of_lipschitzWith
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {X : ℝ → E → E} {t₀ : ℝ} {K : ℝ≥0} {Q : Set E} {W : Set (ℝ × E)}
    (G : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E) (X := X) Set.univ t₀)
    (hX : ∀ t, LipschitzWith K (X t))
    (hQ : IsCompact Q) (hW : IsOpen W)
    (hgraph0 : ∀ q ∈ Q, ((t₀, (G.maps3 t₀) q) : ℝ × E) ∈ W) :
    ∃ a b : ℝ, t₀ ∈ Set.Ioo a b ∧
      ∀ τ ∈ Set.Ioo a b, ∀ q ∈ Q, ((τ, (G.maps3 τ) q) : ℝ × E) ∈ W := by
  have hcont := continuous_maps3_of_lipschitzWith G hX
  exact exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt
    (Ψ := fun τ q => (G.maps3 τ) q) hQ hW hgraph0
    (fun q _ => hcont.continuousAt)

/-- **Manifold-target generalisation of the uniform short-time orbit-graph confinement.**  The
tube-lemma confinement `exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt` holds with the
model normed space `E` replaced by an *arbitrary topological space* `Y`: its proof only ever uses `E`
through its topology (never the linear structure — the elaborator even flags `[NormedSpace ℝ E]` as
unused there).  This is exactly the form the GAP-1 step-(v) **raw-manifold** orbit control needs, where
the flow `Φ : ℝ → M → M` maps the general compact manifold `M` to itself and `M` carries no normed-space
structure, so the model `E`-target confinement cannot be applied directly.  For a time-dependent flow
`Ψ : ℝ → Y → Y` whose space-time graph map `z ↦ (z.1, Ψ z.1 z.2)` is jointly continuous at each
*anchored* point `(t₀, q)` (with `q` ranging over a compact initial set `Q`) and an open space-time
target `W` containing the whole anchored graph `{(t₀, Ψ t₀ q) | q ∈ Q}`, there is an open time window
`Set.Ioo a b ∋ t₀` on which **every** orbit graph stays in `W`.  Proof: identical to the `E`-version —
`IsCompact.eventually_forall_of_forall_eventually` turns the pointwise open-preimage neighbourhoods
(`ContinuousAt.preimage_mem_nhds`) into a single *time* neighbourhood of `t₀` valid for all `q ∈ Q`,
whence an honest `Set.Ioo` window through `mem_nhds_iff_exists_Ioo_subset`. -/
theorem exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt_manifoldTarget
    {Y : Type*} [TopologicalSpace Y]
    {Ψ : ℝ → Y → Y} {Q : Set Y} {W : Set (ℝ × Y)} {t₀ : ℝ}
    (hQ : IsCompact Q) (hW : IsOpen W)
    (hgraph0 : ∀ q ∈ Q, ((t₀, Ψ t₀ q) : ℝ × Y) ∈ W)
    (hcont : ∀ q ∈ Q, ContinuousAt (fun z : ℝ × Y => Ψ z.1 z.2) (t₀, q)) :
    ∃ a b : ℝ, t₀ ∈ Set.Ioo a b ∧
      ∀ τ ∈ Set.Ioo a b, ∀ q ∈ Q, ((τ, Ψ τ q) : ℝ × Y) ∈ W := by
  have hev : ∀ᶠ τ in 𝓝 t₀, ∀ q ∈ Q, ((τ, Ψ τ q) : ℝ × Y) ∈ W := by
    refine IsCompact.eventually_forall_of_forall_eventually hQ ?_
    intro q hq
    have hgraphcont :
        ContinuousAt (fun z : ℝ × Y => ((z.1, Ψ z.1 z.2) : ℝ × Y)) (t₀, q) :=
      continuousAt_fst.prodMk (hcont q hq)
    exact hgraphcont.preimage_mem_nhds (hW.mem_nhds (hgraph0 q hq))
  obtain ⟨l, u, hmem, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hev
  exact ⟨l, u, hmem, fun τ hτ q hq => hsub hτ q hq⟩

/-- **Single-orbit short-time source confinement (manifold-target).**  The `Q = {x}` case of
`exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt_manifoldTarget`, packaged directly for
the `hγ_src` obligation of GAP-1 step (v): if the space-time flow `Ψ : ℝ → Y → Y` (`Y` an arbitrary
topological space) is jointly continuous at `(t₀, x)` and `U` is an open set containing the anchor value
`Ψ t₀ x`, there is an open time window `Set.Ioo a b ∋ t₀` on which the single orbit `τ ↦ Ψ τ x` stays
inside `U`.  Applied with `Ψ = Φ` the raw manifold gauge flow, `x` a chart-patch point and
`U = (extChartAt I p).source`, this is exactly the "the orbit stays in the chart source" window the
step-(v) chart-conjugation transfer (`extChartAt_comp_eqOn_maps3_of_cutoff_eqOne`) requires. -/
theorem exists_Ioo_forall_mem_of_continuousAt_source
    {Y : Type*} [TopologicalSpace Y]
    {Ψ : ℝ → Y → Y} {U : Set Y} {t₀ : ℝ} {x : Y}
    (hU : IsOpen U) (hx : Ψ t₀ x ∈ U)
    (hcont : ContinuousAt (fun z : ℝ × Y => Ψ z.1 z.2) (t₀, x)) :
    ∃ a b : ℝ, t₀ ∈ Set.Ioo a b ∧ ∀ τ ∈ Set.Ioo a b, Ψ τ x ∈ U := by
  obtain ⟨a, b, hmem, hgraph⟩ :=
    exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt_manifoldTarget
      (Ψ := Ψ) (Q := ({x} : Set Y)) (W := Set.univ ×ˢ U) (t₀ := t₀)
      isCompact_singleton (isOpen_univ.prod hU)
      (fun q hq => by
        rw [Set.mem_singleton_iff] at hq; subst hq
        exact ⟨Set.mem_univ _, hx⟩)
      (fun q hq => by
        rw [Set.mem_singleton_iff] at hq; subst hq
        exact hcont)
  exact ⟨a, b, hmem, fun τ hτ => (hgraph τ hτ x rfl).2⟩

/-- **Compact-window orbit-graph containment (manifold-target) — the bridge to
`cutoff_eqOne_along_curve_of_graph_subset`.**  Where
`exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt_manifoldTarget` confines the orbit
graphs into an *open* space-time target, this variant delivers containment in a *compact window* `K`
whose **interior** contains the anchored graph — the exact `∀ τ ∈ s, (τ, g τ) ∈ K` datum that
`cutoff_eqOne_along_curve_of_graph_subset` consumes (a cutoff `χ` with `∀ᶠ r in 𝓝ˢ K, χ r = 1` is then
`≡ 1` along every confined orbit).  Proof: apply the open-target confinement to `interior K`
(`isOpen_interior`), then `interior_subset`.  This closes the "open target ⟹ compact-window graph
containment" glue for the raw-manifold side of GAP-1 step (v), uniformly over a compact chart patch. -/
theorem exists_Ioo_forall_forall_graph_mem_compact_of_isCompact_of_continuousAt_manifoldTarget
    {Y : Type*} [TopologicalSpace Y]
    {Ψ : ℝ → Y → Y} {Q : Set Y} {K : Set (ℝ × Y)} {t₀ : ℝ}
    (hQ : IsCompact Q)
    (hgraph0 : ∀ q ∈ Q, ((t₀, Ψ t₀ q) : ℝ × Y) ∈ interior K)
    (hcont : ∀ q ∈ Q, ContinuousAt (fun z : ℝ × Y => Ψ z.1 z.2) (t₀, q)) :
    ∃ a b : ℝ, t₀ ∈ Set.Ioo a b ∧
      ∀ τ ∈ Set.Ioo a b, ∀ q ∈ Q, ((τ, Ψ τ q) : ℝ × Y) ∈ K := by
  obtain ⟨a, b, hmem, hgraph⟩ :=
    exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt_manifoldTarget
      hQ isOpen_interior hgraph0 hcont
  exact ⟨a, b, hmem, fun τ hτ q hq => interior_subset (hgraph τ hτ q hq)⟩

/-- **Uniform short-time source confinement over a compact set (manifold-target).**  The compact-`Q`
generalisation of `exists_Ioo_forall_mem_of_continuousAt_source`: where that lemma confines a *single*
orbit `τ ↦ Ψ τ x` into an open set `U`, this one confines *every* orbit `τ ↦ Ψ τ q` (for `q` in a
compact set `Q`) into `U` on a **single** time window.  For a time-dependent flow `Ψ : ℝ → Y → Y` (`Y`
an arbitrary topological space) jointly continuous at each anchored point `(t₀, q)` (`q ∈ Q`), with the
anchor values `Ψ t₀ q ∈ U` for all `q ∈ Q` and `U` open, there is an open time window `Set.Ioo a b ∋ t₀`
on which `Ψ τ q ∈ U` for every `τ` in the window and every `q ∈ Q`.  Proof: apply the manifold-target
tube-lemma confinement `exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt_manifoldTarget`
to the open space-time target `W = univ ×ˢ U`, then read off the second component.  This is the
`hγ_src`-producing datum of GAP-1 step (v) **uniformly over a compact chart patch** (take
`U = (extChartAt I p).source` and `Q` a compact neighbourhood of the patch). -/
theorem exists_Ioo_forall_forall_mem_of_isCompact_of_continuousAt_source
    {Y : Type*} [TopologicalSpace Y]
    {Ψ : ℝ → Y → Y} {Q U : Set Y} {t₀ : ℝ}
    (hQ : IsCompact Q) (hU : IsOpen U)
    (hanchor : ∀ q ∈ Q, Ψ t₀ q ∈ U)
    (hcont : ∀ q ∈ Q, ContinuousAt (fun z : ℝ × Y => Ψ z.1 z.2) (t₀, q)) :
    ∃ a b : ℝ, t₀ ∈ Set.Ioo a b ∧ ∀ τ ∈ Set.Ioo a b, ∀ q ∈ Q, Ψ τ q ∈ U := by
  obtain ⟨a, b, hmem, hgraph⟩ :=
    exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt_manifoldTarget
      (Ψ := Ψ) (Q := Q) (W := Set.univ ×ˢ U) (t₀ := t₀)
      hQ (isOpen_univ.prod hU)
      (fun q hq => ⟨Set.mem_univ _, hanchor q hq⟩) hcont
  exact ⟨a, b, hmem, fun τ hτ q hq => (hgraph τ hτ q hq).2⟩

/-- **The `hγ_src` datum of GAP-1 step (v), produced from the raw manifold flow's joint continuity.**
Specialises `exists_Ioo_forall_forall_mem_of_isCompact_of_continuousAt_source` to the open target
`U = (extChartAt I p).source` and an **anchored** flow `Φ` (`Φ 0 = id` on `Q`): the anchor condition
`Φ 0 x ∈ (extChartAt I p).source` then reduces to `Q ⊆ (extChartAt I p).source`.  For a jointly-continuous
(at each `(0, x)`, `x ∈ Q`) anchored flow `Φ` on a compact patch `Q` contained in a chart source, there
is an open window `Set.Ioo a b ∋ 0` on which every orbit stays in the chart source:
`∀ τ ∈ Ioo a b, ∀ x ∈ Q, Φ τ x ∈ (extChartAt I p).source`.  Since `U ⊆ Q` for the open chart patch `U`
of the step-(v) capstone, this delivers exactly the `hγ_src` hypothesis of
`contMDiffOn_flowSlice_of_cutoff_orbit_control`, derived from the raw manifold gauge flow's joint
continuity (`exists_timeDependent_flow_compact_continuousAt`) rather than assumed. -/
theorem exists_Ioo_forall_forall_mem_extChartAt_source_of_continuousAt
    {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    {Φ : ℝ → M → M} {Q : Set M} {p : M}
    (hQ : IsCompact Q) (hQsub : Q ⊆ (extChartAt I p).source)
    (hanchor : ∀ x ∈ Q, Φ 0 x = x)
    (hcont : ∀ x ∈ Q, ContinuousAt (fun z : ℝ × M => Φ z.1 z.2) (0, x)) :
    ∃ a b : ℝ, (0 : ℝ) ∈ Set.Ioo a b ∧
      ∀ τ ∈ Set.Ioo a b, ∀ x ∈ Q, Φ τ x ∈ (extChartAt I p).source := by
  have hUopen : IsOpen (extChartAt I p).source := by
    rw [extChartAt_source]; exact (chartAt H p).open_source
  exact exists_Ioo_forall_forall_mem_of_isCompact_of_continuousAt_source
    hQ hUopen (fun x hx => by rw [hanchor x hx]; exact hQsub hx) hcont

/-- **General tube-lemma confinement with distinct source/target types.**  Identical to
`exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt_manifoldTarget`, but allowing the
compact initial set `Q ⊆ Y` and the space-time target `W ⊆ ℝ × Z` to live over *different* topological
spaces `Y` (domain) and `Z` (codomain) — the proof never uses `Y = Z`.  This is what the raw-manifold
`hγ_mem` control needs, where the confined quantity is the **chart image** `extChartAt I p (Φ τ x) : E`
of the orbit `Φ τ x : M`, so the domain `M` and codomain `E` genuinely differ.  For a map `Ψ : ℝ → Y → Z`
jointly continuous at each anchored point `(t₀, q)` (`q ∈ Q` compact) into an open space-time target `W`
containing the anchored graph, there is an open time window `Set.Ioo a b ∋ t₀` on which every orbit
graph `τ ↦ (τ, Ψ τ q)` stays in `W`. -/
theorem exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt_prod
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {Ψ : ℝ → Y → Z} {Q : Set Y} {W : Set (ℝ × Z)} {t₀ : ℝ}
    (hQ : IsCompact Q) (hW : IsOpen W)
    (hgraph0 : ∀ q ∈ Q, ((t₀, Ψ t₀ q) : ℝ × Z) ∈ W)
    (hcont : ∀ q ∈ Q, ContinuousAt (fun z : ℝ × Y => Ψ z.1 z.2) (t₀, q)) :
    ∃ a b : ℝ, t₀ ∈ Set.Ioo a b ∧
      ∀ τ ∈ Set.Ioo a b, ∀ q ∈ Q, ((τ, Ψ τ q) : ℝ × Z) ∈ W := by
  have hev : ∀ᶠ τ in 𝓝 t₀, ∀ q ∈ Q, ((τ, Ψ τ q) : ℝ × Z) ∈ W := by
    refine IsCompact.eventually_forall_of_forall_eventually hQ ?_
    intro q hq
    have hgraphcont :
        ContinuousAt (fun z : ℝ × Y => ((z.1, Ψ z.1 z.2) : ℝ × Z)) (t₀, q) :=
      continuousAt_fst.prodMk (hcont q hq)
    exact hgraphcont.preimage_mem_nhds (hW.mem_nhds (hgraph0 q hq))
  obtain ⟨l, u, hmem, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hev
  exact ⟨l, u, hmem, fun τ hτ q hq => hsub hτ q hq⟩

/-- **Joint continuity of the chart-composed manifold flow at the anchor.**  For an anchored flow
`Φ` (`Φ 0 x = x`) jointly continuous at `(0, x)` with `x` in the chart source, the chart-composed map
`z ↦ extChartAt I p (Φ z.1 z.2)` is `ContinuousAt (0, x)`: post-compose `Φ`'s joint continuity with the
continuity of `extChartAt I p` at `Φ 0 x = x ∈ (extChartAt I p).source` (`continuousAt_extChartAt'`).
This is the joint-continuity input the `hγ_mem` confinement of GAP-1 step (v) consumes (the confined
quantity being the chart image of the orbit). -/
theorem continuousAt_zero_prod_extChartAt_flow
    {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    {Φ : ℝ → M → M} {p x : M}
    (hxsrc : x ∈ (extChartAt I p).source)
    (hanchor : Φ 0 x = x)
    (hcont : ContinuousAt (fun z : ℝ × M => Φ z.1 z.2) (0, x)) :
    ContinuousAt (fun z : ℝ × M => extChartAt I p (Φ z.1 z.2)) (0, x) := by
  have hchart : ContinuousAt (extChartAt I p) x := continuousAt_extChartAt' hxsrc
  exact hchart.comp_of_eq hcont (by exact hanchor)

/-- **The `hγ_mem` datum of GAP-1 step (v), produced from the raw manifold flow's joint continuity.**
Applies the distinct-type tube-lemma confinement
`exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt_prod` to the chart-composed flow
`Ψ τ x = extChartAt I p (Φ τ x)` (jointly continuous by `continuousAt_zero_prod_extChartAt_flow`), over a
compact patch `Q ⊆ (extChartAt I p).source` and an open space-time target `W ⊆ ℝ × E` containing the
anchored chart-image graph.  Yields an open window `Set.Ioo a b ∋ 0` on which the chart image of every
orbit stays in `W`: `∀ τ ∈ Ioo a b, ∀ x ∈ Q, (τ, extChartAt I p (Φ τ x)) ∈ W`.  With `W` the state graph
`{z | z.2 ∈ state z.1}` (open) this is exactly the `hγ_mem` hypothesis of
`contMDiffOn_flowSlice_of_cutoff_orbit_control`. -/
theorem exists_Ioo_forall_forall_extChartAt_mem_of_continuousAt
    {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    {Φ : ℝ → M → M} {Q : Set M} {p : M} {W : Set (ℝ × E)}
    (hQ : IsCompact Q) (hQsub : Q ⊆ (extChartAt I p).source) (hW : IsOpen W)
    (hanchor : ∀ x ∈ Q, Φ 0 x = x)
    (hgraph0 : ∀ x ∈ Q, ((0 : ℝ), extChartAt I p x) ∈ W)
    (hcont : ∀ x ∈ Q, ContinuousAt (fun z : ℝ × M => Φ z.1 z.2) (0, x)) :
    ∃ a b : ℝ, (0 : ℝ) ∈ Set.Ioo a b ∧
      ∀ τ ∈ Set.Ioo a b, ∀ x ∈ Q, ((τ, extChartAt I p (Φ τ x)) : ℝ × E) ∈ W := by
  refine exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt_prod
    (Ψ := fun τ x => extChartAt I p (Φ τ x)) (Q := Q) (W := W) hQ hW ?_ ?_
  · intro x hx
    simpa only [hanchor x hx] using hgraph0 x hx
  · intro x hx
    exact continuousAt_zero_prod_extChartAt_flow (hQsub hx) (hanchor x hx) (hcont x hx)

/-- **Intersecting two open-window confinements at a common anchor.**  Given two short-time confinements
`∃ a b, t₀ ∈ Ioo a b ∧ ∀ τ ∈ Ioo a b, P τ` and the same for `R`, their windows intersect to a single
open window `Ioo (max a₁ a₂) (min b₁ b₂) ∋ t₀` on which **both** `P τ` and `R τ` hold.  The generic glue
for assembling the several separate short-time orbit-confinement windows of GAP-1 step (v)
(`hγ_src`, `hγ_mem`, the model-curve `hg_mem`, the cutoff window) into the *single* window
`contMDiffOn_flowSlice_of_cutoff_orbit_control` consumes. -/
theorem exists_Ioo_forall_and {t₀ : ℝ} {P R : ℝ → Prop}
    (h₁ : ∃ a b : ℝ, t₀ ∈ Set.Ioo a b ∧ ∀ τ ∈ Set.Ioo a b, P τ)
    (h₂ : ∃ a b : ℝ, t₀ ∈ Set.Ioo a b ∧ ∀ τ ∈ Set.Ioo a b, R τ) :
    ∃ a b : ℝ, t₀ ∈ Set.Ioo a b ∧ ∀ τ ∈ Set.Ioo a b, P τ ∧ R τ := by
  obtain ⟨a₁, b₁, ⟨ha₁, hb₁⟩, hP⟩ := h₁
  obtain ⟨a₂, b₂, ⟨ha₂, hb₂⟩, hR⟩ := h₂
  refine ⟨max a₁ a₂, min b₁ b₂, ⟨max_lt ha₁ ha₂, lt_min hb₁ hb₂⟩, fun τ hτ => ?_⟩
  exact ⟨hP τ (Set.Ioo_subset_Ioo (le_max_left a₁ a₂) (min_le_left b₁ b₂) hτ),
         hR τ (Set.Ioo_subset_Ioo (le_max_right a₁ a₂) (min_le_right b₁ b₂) hτ)⟩

/-- **The `hγ_src` *and* `hγ_mem` data of GAP-1 step (v) on a single common window.**  Bundles
`exists_Ioo_forall_forall_mem_extChartAt_source_of_continuousAt` (orbit stays in the chart source) and
`exists_Ioo_forall_forall_extChartAt_mem_of_continuousAt` (chart image of orbit stays in the open
space-time target `W`) into one open window `Set.Ioo a b ∋ 0` via `exists_Ioo_forall_and`.  For a
jointly-continuous anchored raw manifold flow `Φ` over a compact patch `Q ⊆ (extChartAt I p).source`,
delivers both raw-manifold orbit-confinement faces of the step-(v) capstone simultaneously — the exact
common time window `contMDiffOn_flowSlice_of_cutoff_orbit_control` needs. -/
theorem exists_Ioo_forall_forall_extChartAt_source_and_mem_of_continuousAt
    {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    {Φ : ℝ → M → M} {Q : Set M} {p : M} {W : Set (ℝ × E)}
    (hQ : IsCompact Q) (hQsub : Q ⊆ (extChartAt I p).source) (hW : IsOpen W)
    (hanchor : ∀ x ∈ Q, Φ 0 x = x)
    (hgraph0 : ∀ x ∈ Q, ((0 : ℝ), extChartAt I p x) ∈ W)
    (hcont : ∀ x ∈ Q, ContinuousAt (fun z : ℝ × M => Φ z.1 z.2) (0, x)) :
    ∃ a b : ℝ, (0 : ℝ) ∈ Set.Ioo a b ∧
      ∀ τ ∈ Set.Ioo a b,
        (∀ x ∈ Q, Φ τ x ∈ (extChartAt I p).source) ∧
        (∀ x ∈ Q, ((τ, extChartAt I p (Φ τ x)) : ℝ × E) ∈ W) :=
  exists_Ioo_forall_and
    (exists_Ioo_forall_forall_mem_extChartAt_source_of_continuousAt hQ hQsub hanchor hcont)
    (exists_Ioo_forall_forall_extChartAt_mem_of_continuousAt hQ hQsub hW hanchor hgraph0 hcont)

/-- **The compact-manifold time-dependent flow together with its raw-manifold orbit confinement, on one
window.**  End-to-end assembly: from a jointly-`C¹` time-dependent field `X` on a compact boundaryless
`T2` manifold, `exists_timeDependent_flow_compact_continuousAt` produces the anchored flow `Φ`
(`Φ 0 = id`), its orbit ODE on `Ioo (-ε) ε`, and its joint continuity at every anchor `(0, x)`.  Feeding
the joint continuity into `exists_Ioo_forall_forall_extChartAt_source_and_mem_of_continuousAt` and
intersecting the resulting confinement window with the ODE window `Ioo (-ε) ε` (via
`exists_Ioo_forall_and` against the identity confinement of `Ioo (-ε) ε`) yields a **single** open window
`Set.Ioo a b ∋ 0` on which, over a compact chart patch `Q ⊆ (extChartAt I p).source`:
the orbit ODE holds (`hγ`, `mono`-restricted from `Ioo (-ε) ε`), every orbit stays in the chart source
(`hγ_src`), and the chart image of every orbit stays in the open space-time target `W` (`hγ_mem`).  This
is the raw-manifold-side input package of `contMDiffOn_flowSlice_of_cutoff_orbit_control`, produced
unconditionally from the field's jet — no assumed flow or confinement. -/
theorem exists_timeDependent_flow_compact_extChartAt_source_and_mem
    {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [CompleteSpace E]
    [BoundarylessManifold I M] [CompactSpace M] [T2Space M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun q : ℝ × M => (⟨q, ((1 : ℝ), X q.1 q.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    {Q : Set M} {p : M} {W : Set (ℝ × E)}
    (hQ : IsCompact Q) (hQsub : Q ⊆ (extChartAt I p).source) (hW : IsOpen W)
    (hgraph0 : ∀ x ∈ Q, ((0 : ℝ), extChartAt I p x) ∈ W) :
    ∃ (Φ : ℝ → M → M) (a b : ℝ), (0 : ℝ) ∈ Set.Ioo a b ∧
      (∀ x, Φ 0 x = x) ∧
      (∀ x ∈ Q, ∀ τ ∈ Set.Ioo a b,
        HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun σ : ℝ => Φ σ x) (Set.Ioo a b) τ
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (Φ τ x)))) ∧
      (∀ τ ∈ Set.Ioo a b,
        (∀ x ∈ Q, Φ τ x ∈ (extChartAt I p).source) ∧
        (∀ x ∈ Q, ((τ, extChartAt I p (Φ τ x)) : ℝ × E) ∈ W)) := by
  obtain ⟨ε, hε, Φ, hanchor, horbit, hcontA⟩ :=
    PoincareCurvature.ManifoldFlow.exists_timeDependent_flow_compact_continuousAt hX
  have hconf := exists_Ioo_forall_forall_extChartAt_source_and_mem_of_continuousAt
    (Φ := Φ) hQ hQsub hW (fun x _ => hanchor x) hgraph0 (fun x _ => hcontA x)
  obtain ⟨a, b, hmem0, hboth⟩ := exists_Ioo_forall_and hconf
    ⟨-ε, ε, ⟨neg_lt_zero.mpr hε, hε⟩, fun τ hτ => hτ⟩
  have hsub : Set.Ioo a b ⊆ Set.Ioo (-ε) ε := fun τ hτ => (hboth τ hτ).2
  refine ⟨Φ, a, b, hmem0, hanchor, ?_, fun τ hτ => (hboth τ hτ).1⟩
  intro x _ τ hτ
  exact (horbit x τ (hsub hτ)).mono hsub

/-- **Chart-source confinement + membership faces for an *abstract* compact-manifold flow.**  Variant
of `exists_timeDependent_flow_compact_extChartAt_source_and_mem` in which the raw manifold flow `Φ` is
**supplied** (with only its anchor `hanchor` and ODE `horbit` on `Set.Ioo (-ε) ε`) rather than produced
internally.  The joint space-time continuity needed to run the tube-lemma confinement
(`exists_Ioo_forall_forall_extChartAt_source_and_mem_of_continuousAt`) is **derived** from the raw `C¹`
field jet `hX` via `ManifoldFlow.continuousAt_timeDependent_flow_of_anchor_ode`.  On a short common
window `Set.Ioo a b ∋ 0` it produces, for the *given* `Φ`, the two orbit-control faces the step-(v)
capstone consumes on its `Φ`-side — every orbit stays in the chart source
(`Φ τ x ∈ (extChartAt I p).source`) and its chart image stays in the open target `W`
(`(τ, extChartAt I p (Φ τ x)) ∈ W`) — together with the ODE restricted to that window.  Instantiating
`W := Set.univ ×ˢ state₀` gives the `Φ`-side `state`-membership face; this is the abstract-flow analogue
that lets the per-point cutoff-orbit-control package be built for the `hslicesC3`-supplied flow of
`exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3`. -/
theorem exists_timeDependent_flow_compact_extChartAt_source_and_mem_of_flow
    {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [CompleteSpace E]
    [BoundarylessManifold I M] [CompactSpace M] [T2Space M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun q : ℝ × M => (⟨q, ((1 : ℝ), X q.1 q.2)⟩ : TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    {ε : ℝ} (hε : 0 < ε) {Φ : ℝ → M → M}
    (hanchor : ∀ x, Φ 0 x = x)
    (horbit : ∀ x, ∀ t ∈ Set.Ioo (-ε) ε,
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun σ : ℝ => Φ σ x) (Set.Ioo (-ε) ε) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x))))
    {Q : Set M} {p : M} {W : Set (ℝ × E)}
    (hQ : IsCompact Q) (hQsub : Q ⊆ (extChartAt I p).source) (hW : IsOpen W)
    (hgraph0 : ∀ x ∈ Q, ((0 : ℝ), extChartAt I p x) ∈ W) :
    ∃ a b : ℝ, (0 : ℝ) ∈ Set.Ioo a b ∧
      (∀ x ∈ Q, ∀ τ ∈ Set.Ioo a b,
        HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun σ : ℝ => Φ σ x) (Set.Ioo a b) τ
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (Φ τ x)))) ∧
      (∀ τ ∈ Set.Ioo a b,
        (∀ x ∈ Q, Φ τ x ∈ (extChartAt I p).source) ∧
        (∀ x ∈ Q, ((τ, extChartAt I p (Φ τ x)) : ℝ × E) ∈ W)) := by
  have hcontA : ∀ x, ContinuousAt (fun z : ℝ × M => Φ z.1 z.2) (0, x) := fun x =>
    PoincareCurvature.ManifoldFlow.continuousAt_timeDependent_flow_of_anchor_ode hX hε hanchor horbit x
  have hconf := exists_Ioo_forall_forall_extChartAt_source_and_mem_of_continuousAt
    (Φ := Φ) hQ hQsub hW (fun x _ => hanchor x) hgraph0 (fun x _ => hcontA x)
  obtain ⟨a, b, hmem0, hboth⟩ := exists_Ioo_forall_and hconf
    ⟨-ε, ε, ⟨neg_lt_zero.mpr hε, hε⟩, fun τ hτ => hτ⟩
  have hsub : Set.Ioo a b ⊆ Set.Ioo (-ε) ε := fun τ hτ => (hboth τ hτ).2
  refine ⟨a, b, hmem0, ?_, fun τ hτ => (hboth τ hτ).1⟩
  intro x _ τ hτ
  exact (horbit x τ (hsub hτ)).mono hsub

/-- **The `heq` datum of GAP-1 step (v) at the common anchor `0`.**  When the model gauge flow `G` is
anchored at `0` (`Diffeomorph3GaugeFlowOn … sTime 0`) and the raw manifold flow `Φ` is anchored at `0`
(`Φ 0 = id`), the step-(v) agreement `extChartAt I p (Φ t₀ x) = (G.maps3 t₀) (extChartAt I p x)` holds at
the reference time `t₀ = 0`: both sides equal `extChartAt I p x` — the left because `Φ 0 x = x`, the right
because `G.maps3 0 = id` (`SmoothSelfDiffeomorph3Family.AnchoredAt.apply`).  Choosing the reference time of
`contMDiffOn_flowSlice_of_cutoff_orbit_control` to be the common anchor `0 ∈ Ioo a b` thus discharges its
`heq` hypothesis for free — the integral-curve uniqueness comparison only needs agreement at a single
interior time. -/
theorem extChartAt_flow_eq_maps3_at_zero
    {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E] [CompleteSpace E]
    {X' : ℝ → E → E} {sTime : Set ℝ}
    (G : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E) (X := X') sTime 0)
    {Φ : ℝ → M → M} {p : M}
    (hanchor : ∀ x, Φ 0 x = x) (x : M) :
    extChartAt I p (Φ 0 x) = (G.maps3 0) (extChartAt I p x) := by
  rw [hanchor]
  exact (SmoothSelfDiffeomorph3Family.AnchoredAt.apply (Φ := G.maps3) G.anchored
    (extChartAt I p x)).symm

/-- **Compactness of the chart image of a compact patch.**  For a compact set `Q` contained in the
chart source `(extChartAt I p).source`, its image `extChartAt I p '' Q ⊆ E` under the chart is compact —
the continuous image (`continuousOn_extChartAt`, restricted to `Q`) of a compact set.  This is the
compact model-space initial set `Q_E` over which the **model-curve** confinement
`exists_Ioo_forall_forall_graph_maps3_mem_of_lipschitzWith` (for the `hg_mem` / `hχ` faces of the
step-(v) capstone) is taken, obtained from the raw-manifold compact patch `Q` of the `hγ_src` / `hγ_mem`
faces — the bridge between the two sides' initial sets. -/
theorem isCompact_extChartAt_image
    {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    {Q : Set M} {p : M} (hQ : IsCompact Q) (hQsub : Q ⊆ (extChartAt I p).source) :
    IsCompact (extChartAt I p '' Q) :=
  hQ.image_of_continuousOn ((continuousOn_extChartAt p).mono hQsub)

/-- **The `hχ` *and* `hg_mem` model-curve faces of GAP-1 step (v) on a single common window — the
model-side analogue of `exists_timeDependent_flow_compact_extChartAt_source_and_mem`.**  For a model
gauge flow `G : Diffeomorph3GaugeFlowOn (X := X) Set.univ t₀` of a *uniformly-in-time* `K`-Lipschitz
field `X` (exactly the shape the bump-globalised cut field `χ • chartPushforwardField` supplies via its
compact support), a compact model-space initial set `Q`, a cutoff `χ` that is `≡ 1` on a neighbourhood
of a compact window `Kwin` (as produced by `exists_diffeomorph3GaugeFlowOn_cutoff_eqOne_of_isCompact_window`),
and an open state tube `state`, this bundles the two model-curve orbit-containment faces of the step-(v)
capstone onto ONE window `Set.Ioo a b ∋ t₀`:

* `hχ`  — `χ (τ, (G.maps3 τ) q) = 1` along every orbit (`q ∈ Q`); obtained by confining the orbit graphs
  into `interior Kwin` (`exists_Ioo_forall_forall_graph_maps3_mem_of_lipschitzWith`), whence
  `interior_subset` puts the graph in `Kwin` and `hcut.self_of_nhdsSet` fires the cutoff.
* `hg_mem` — `(G.maps3 τ) q ∈ state`; obtained by confining the orbits into `Set.univ ×ˢ state`.

The two confinement windows are merged with `exists_Ioo_forall_and`.  Instantiated with
`Q := extChartAt I p '' U` (compact by `isCompact_extChartAt_image`) and a constant `state`, this is
exactly the `hχ` / `hg_mem` data of `contMDiffOn_flowSlice_of_cutoff_orbit_control` — the model-side
input package of the step-(v) capstone, produced from the model gauge flow's Lipschitz field. -/
theorem exists_Ioo_maps3_cutoff_eqOne_and_state_mem
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {X : ℝ → E → E} {χ : ℝ × E → ℝ} {t₀ : ℝ} {K : ℝ≥0}
    {Q : Set E} {Kwin : Set (ℝ × E)} {state : Set E}
    (G : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E) (X := X) Set.univ t₀)
    (hX : ∀ t, LipschitzWith K (X t))
    (hQ : IsCompact Q)
    (hcut : ∀ᶠ r in 𝓝ˢ Kwin, χ r = 1)
    (hstate : IsOpen state)
    (hwin0 : ∀ q ∈ Q, ((t₀, (G.maps3 t₀) q) : ℝ × E) ∈ interior Kwin)
    (hstate0 : ∀ q ∈ Q, (G.maps3 t₀) q ∈ state) :
    ∃ a b : ℝ, t₀ ∈ Set.Ioo a b ∧
      (∀ q ∈ Q, ∀ τ ∈ Set.Ioo a b, χ (τ, (G.maps3 τ) q) = 1) ∧
      (∀ q ∈ Q, ∀ τ ∈ Set.Ioo a b, (G.maps3 τ) q ∈ state) := by
  have hconf₁ : ∃ a b : ℝ, t₀ ∈ Set.Ioo a b ∧
      ∀ τ ∈ Set.Ioo a b, ∀ q ∈ Q, χ (τ, (G.maps3 τ) q) = 1 := by
    obtain ⟨a, b, hmem, hconf⟩ :=
      exists_Ioo_forall_forall_graph_maps3_mem_of_lipschitzWith G hX hQ isOpen_interior hwin0
    exact ⟨a, b, hmem, fun τ hτ q hq =>
      hcut.self_of_nhdsSet (τ, (G.maps3 τ) q) (interior_subset (hconf τ hτ q hq))⟩
  have hconf₂ : ∃ a b : ℝ, t₀ ∈ Set.Ioo a b ∧
      ∀ τ ∈ Set.Ioo a b, ∀ q ∈ Q, (G.maps3 τ) q ∈ state := by
    obtain ⟨a, b, hmem, hconf⟩ :=
      exists_Ioo_forall_forall_graph_maps3_mem_of_lipschitzWith G hX hQ
        (isOpen_univ.prod hstate)
        (fun q hq => ⟨Set.mem_univ _, hstate0 q hq⟩)
    exact ⟨a, b, hmem, fun τ hτ q hq => (hconf τ hτ q hq).2⟩
  obtain ⟨a, b, hmem, hboth⟩ := exists_Ioo_forall_and
    (P := fun τ => ∀ q ∈ Q, χ (τ, (G.maps3 τ) q) = 1)
    (R := fun τ => ∀ q ∈ Q, (G.maps3 τ) q ∈ state) hconf₁ hconf₂
  exact ⟨a, b, hmem,
    fun q hq τ hτ => (hboth τ hτ).1 q hq,
    fun q hq τ hτ => (hboth τ hτ).2 q hq⟩

/-- **End-to-end model-side face producer from field + cutoff data — the model analogue of
`exists_timeDependent_flow_compact_extChartAt_source_and_mem`.**  From the joint `C^N` (`N ≥ 4`)
regularity of the tangent-bundle section `(τ, y) ↦ ⟨y, X τ y⟩` on `ℝ ×ˢ (extChartAt I p).source` and a
globally-`C^N`, compactly-supported cutoff `χ` with `tsupport χ ⊆ ℝ ×ˢ (extChartAt I p).target` that is
`≡ 1` on a neighbourhood of a compact window `Kwin`, this produces the model comparison gauge flow `G`
of the bump-globalised cut field `χ • chartPushforwardField I X p` *together with* both model-curve
orbit-containment faces of the step-(v) capstone on a single window `Set.Ioo a b ∋ t₀`:

* the gauge flow `G : Diffeomorph3GaugeFlowOn (χ • chartPushforwardField I X p) Set.univ t₀` itself,
  built by `exists_diffeomorph3GaugeFlowOn_cutoff_chartPushforwardField`;
* `hχ`  — `χ (τ, (G.maps3 τ) q) = 1` along every orbit (`q ∈ Q`);
* `hg_mem` — `(G.maps3 τ) q ∈ state`.

The uniform-in-time Lipschitz constant of the cut field needed by
`exists_Ioo_maps3_cutoff_eqOne_and_state_mem` is *derived* — not assumed — from the cut field's compact
support via `exists_lipschitzWith_prodMk_left` (through
`contDiff_hasCompactSupport_cutoff_chartPushforwardField`).  The anchored positions `(G.maps3 t₀) q = q`
(`AnchoredAt.apply`) reduce the containment hypotheses to `(t₀, q) ∈ interior Kwin` and `q ∈ state`.
Instantiated with `Q := extChartAt I p '' U` (`isCompact_extChartAt_image`), this is exactly the `G` /
`hχ` / `hg_mem` model-side input of `contMDiffOn_flowSlice_of_cutoff_orbit_control`, produced from the
chart field jet alone. -/
theorem exists_diffeomorph3GaugeFlowOn_Ioo_cutoff_eqOne_and_state_mem
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {N : WithTop ℕ∞} [IsManifold I N M]
    [ContMDiffVectorBundle N E (TangentSpace I : M → Type _) I]
    {X : ℝ → M → E} {p : M}
    (hX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) N
      (fun r : ℝ × M => (⟨r.2, X r.1 r.2⟩ : TangentBundle I M))
      (Set.univ ×ˢ (extChartAt I p).source))
    {χ : ℝ × E → ℝ} (hχ : ContDiff ℝ N χ) (hχc : HasCompactSupport χ)
    (hsub : tsupport χ ⊆ Set.univ ×ˢ (extChartAt I p).target)
    (hN : 4 ≤ N) (t₀ : ℝ)
    {Q : Set E} {Kwin : Set (ℝ × E)} {state : Set E}
    (hQ : IsCompact Q)
    (hcut : ∀ᶠ r in 𝓝ˢ Kwin, χ r = 1)
    (hstate : IsOpen state)
    (hwin0 : ∀ q ∈ Q, ((t₀, q) : ℝ × E) ∈ interior Kwin)
    (hstate0 : ∀ q ∈ Q, q ∈ state) :
    ∃ (G : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E)
        (X := fun τ q => χ (τ, q) •
          PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ q) Set.univ t₀),
      ∃ a b : ℝ, t₀ ∈ Set.Ioo a b ∧
      (∀ q ∈ Q, ∀ τ ∈ Set.Ioo a b, χ (τ, (G.maps3 τ) q) = 1) ∧
      (∀ q ∈ Q, ∀ τ ∈ Set.Ioo a b, (G.maps3 τ) q ∈ state) := by
  obtain ⟨hF, hcs⟩ :=
    contDiff_hasCompactSupport_cutoff_chartPushforwardField hX hχ hχc hsub
  obtain ⟨C, hC⟩ := exists_lipschitzWith_prodMk_left hF hcs
    ((by norm_num : (1 : WithTop ℕ∞) ≤ 4).trans hN)
  obtain ⟨G⟩ :=
    exists_diffeomorph3GaugeFlowOn_cutoff_chartPushforwardField hX hχ hχc hsub hN Set.univ t₀
  refine ⟨G, ?_⟩
  have hanchor : ∀ q : E, (G.maps3 t₀) q = q :=
    fun q => SmoothSelfDiffeomorph3Family.AnchoredAt.apply (Φ := G.maps3) G.anchored q
  exact exists_Ioo_maps3_cutoff_eqOne_and_state_mem G (fun t => hC t) hQ hcut hstate
    (fun q hq => by rw [hanchor]; exact hwin0 q hq)
    (fun q hq => by rw [hanchor]; exact hstate0 q hq)

/-- **Per-patch slice-`C³` of the compact-manifold gauge flow, assembled from the field jet alone
(GAP-1 step (v) capstone assembly).**  This is the FINAL step-(v) assembly: from the two field-jet
regularity inputs on a single compact chart patch `Q_M ⊆ (extChartAt I p).source` (the *global* `C¹`
product-tangent smoothness `hXraw` feeding the raw manifold flow, and the *local* `C^N` (`N ≥ 4`)
tangent-bundle smoothness `hXchart` on the chart source feeding the model comparison flow), a cutoff
`χ` that is `≡ 1` near a compact window `Kwin`, and the two field-analytic residuals — the chart
pushforward field's Lipschitz control on the state tube `state₀` (`hlip`) and the initial-data
placement (`hplace_state`, `hplace_win`) — it produces the raw manifold gauge flow `Φ` and an honest
open time window `Set.Ioo a b ∋ 0` on which every time slice `Φ t` is `ContMDiffOn I I 3` on the patch
`U`.

The proof wires together the two field-to-faces bundles committed for GAP 1:
`exists_timeDependent_flow_compact_extChartAt_source_and_mem` (raw side: `Φ`, `hγ`, `hγ_src`, `hγ_mem`
into `W = Set.univ ×ˢ state₀`) and `exists_diffeomorph3GaugeFlowOn_Ioo_cutoff_eqOne_and_state_mem`
(model side: `G`, `hχ`, `hg_mem` over `Q := extChartAt I p '' Q_M`, compact by
`isCompact_extChartAt_image`); it intersects their two time windows (`max`/`min` endpoints), takes the
common anchor `0` — at which `heq` holds for free (`extChartAt_flow_eq_maps3_at_zero`) — and feeds all
six orbit-control faces into `contMDiffOn_flowSlice_of_cutoff_orbit_control` with `sTime = Set.univ`
(so `hnhds` is `Filter.univ_mem`) and constant `state τ = state₀`.  Only the field-analytic residuals
`hlip` / `hplace_*` and the two field jets remain as hypotheses — exactly the GAP-1 step-(v) residual
the plan isolates before the finite-cover globalisation. -/
theorem contMDiffOn_flowSlice_perPatch_of_field_jets
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    [BoundarylessManifold I M] [CompactSpace M] [IsManifold I 1 M]
    {N : WithTop ℕ∞} [IsManifold I N M]
    [ContMDiffVectorBundle N E (TangentSpace I : M → Type _) I]
    {X : ℝ → M → E} {p : M} {χ : ℝ × E → ℝ}
    {U Q_M : Set M} {Kwin : Set (ℝ × E)} {state₀ : Set E} {K : ℝ≥0}
    (hXraw : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun q : ℝ × M => (⟨q, ((1 : ℝ), X q.1 q.2)⟩ :
        TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    (hXchart : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) N
      (fun r : ℝ × M => (⟨r.2, X r.1 r.2⟩ : TangentBundle I M))
      (Set.univ ×ˢ (extChartAt I p).source))
    (hχC : ContDiff ℝ N χ) (hχc : HasCompactSupport χ)
    (hsub : tsupport χ ⊆ Set.univ ×ˢ (extChartAt I p).target)
    (hcut : ∀ᶠ r in 𝓝ˢ Kwin, χ r = 1) (hN : 4 ≤ N)
    (hstate : IsOpen state₀)
    (hlip : ∀ τ : ℝ, LipschitzOnWith K
      (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ) state₀)
    (hU : U ⊆ (chartAt H p).source) (hUQ : U ⊆ (Q_M : Set M))
    (hQ_M : IsCompact Q_M) (hQ_M_src : Q_M ⊆ (extChartAt I p).source)
    (hplace_state : ∀ x ∈ Q_M, extChartAt I p x ∈ state₀)
    (hplace_win : ∀ x ∈ Q_M, ((0 : ℝ), extChartAt I p x) ∈ interior Kwin) :
    ∃ (Φ : ℝ → M → M) (a b : ℝ), (0 : ℝ) ∈ Set.Ioo a b ∧ (∀ x, Φ 0 x = x) ∧
      ∀ t ∈ Set.Ioo a b, ContMDiffOn I I 3 (fun x : M => Φ t x) U := by
  obtain ⟨Φ, a₁, b₁, hmem0₁, hanchor, hγ_raw, hsrcmem⟩ :=
    exists_timeDependent_flow_compact_extChartAt_source_and_mem (X := X) (p := p)
      hXraw hQ_M hQ_M_src (isOpen_univ.prod hstate)
      (fun x hx => ⟨Set.mem_univ _, hplace_state x hx⟩)
  obtain ⟨G, a₂, b₂, hmem0₂, hχ_mod, hg_mem_mod⟩ :=
    exists_diffeomorph3GaugeFlowOn_Ioo_cutoff_eqOne_and_state_mem (X := X) (p := p)
      hXchart hχC hχc hsub hN (0 : ℝ)
      (isCompact_extChartAt_image hQ_M hQ_M_src) hcut hstate
      (fun q hq => by obtain ⟨x, hx, rfl⟩ := hq; exact hplace_win x hx)
      (fun q hq => by obtain ⟨x, hx, rfl⟩ := hq; exact hplace_state x hx)
  refine ⟨Φ, max a₁ a₂, min b₁ b₂,
    ⟨max_lt hmem0₁.1 hmem0₂.1, lt_min hmem0₁.2 hmem0₂.2⟩, hanchor, ?_⟩
  intro t ht
  have hsub₁ : Set.Ioo (max a₁ a₂) (min b₁ b₂) ⊆ Set.Ioo a₁ b₁ :=
    Set.Ioo_subset_Ioo (le_max_left a₁ a₂) (min_le_left b₁ b₂)
  have hsub₂ : Set.Ioo (max a₁ a₂) (min b₁ b₂) ⊆ Set.Ioo a₂ b₂ :=
    Set.Ioo_subset_Ioo (le_max_right a₁ a₂) (min_le_right b₁ b₂)
  have ht₀ : (0 : ℝ) ∈ Set.Ioo (max a₁ a₂) (min b₁ b₂) :=
    ⟨max_lt hmem0₁.1 hmem0₂.1, lt_min hmem0₁.2 hmem0₂.2⟩
  refine contMDiffOn_flowSlice_of_cutoff_orbit_control (X := X) (p := p) (χ := χ)
    (state := fun _ : ℝ => state₀) G Φ hU ht ht₀ (fun τ _ => Filter.univ_mem)
    (fun τ _ => hlip τ) ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx τ hτ
    exact (hγ_raw x (hUQ hx) τ (hsub₁ hτ)).mono hsub₁
  · intro x hx τ hτ
    exact (hsrcmem τ (hsub₁ hτ)).1 x (hUQ hx)
  · intro x hx τ hτ
    exact hχ_mod (extChartAt I p x) ⟨x, hUQ hx, rfl⟩ τ (hsub₂ hτ)
  · intro x hx τ hτ
    exact ((hsrcmem τ (hsub₁ hτ)).2 x (hUQ hx)).2
  · intro x hx τ hτ
    exact hg_mem_mod (extChartAt I p x) ⟨x, hUQ hx, rfl⟩ τ (hsub₂ hτ)
  · intro x _
    exact extChartAt_flow_eq_maps3_at_zero (p := p) G hanchor x

/-- **Per-patch slice-`C³` for a GIVEN global compact flow (the finite-cover globalisation enabler).**
The `Φ`-input variant of `contMDiffOn_flowSlice_perPatch_of_field_jets`: rather than *constructing* the
raw manifold flow from the field jet, it takes the global compact time-dependent flow `Φ` — the output
of `exists_timeDependent_flow_compact_continuousAt` (anchored `Φ 0 = id`, orbit ODE on `Ioo (-ε) ε`,
joint continuity at every anchor `(0, x)`) — as a HYPOTHESIS, and produces the per-patch slice-`C³`
window for THAT same `Φ`.

This decoupling is exactly what the finite-cover globalisation needs: one global flow `Φ` is constructed
once (from the DeTurck gauge field jet), and this lemma is applied on each chart patch of a finite cover
to lift the model `C³` tower to `ContMDiffOn I I 3 (Φ t)` on each patch — all for the *same* `Φ`, whose
per-patch windows then intersect (finite cover ⇒ neighbourhood of `0`) and glue to a global
`ContMDiff I I 3 (Φ t)`.  The proof feeds the raw-manifold confinement
`exists_Ioo_forall_forall_extChartAt_source_and_mem_of_continuousAt` (from `Φ`'s joint continuity), the
model-side face producer `exists_diffeomorph3GaugeFlowOn_Ioo_cutoff_eqOne_and_state_mem`, and the
orbit ODE (`.mono`-restricted from the `Ioo (-ε) ε` window) into
`contMDiffOn_flowSlice_of_cutoff_orbit_control`, intersecting the three time windows explicitly.  No
`[CompactSpace M]` is required here — compactness enters only in the global flow existence and the
finite cover. -/
theorem contMDiffOn_flowSlice_perPatch_of_flow
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {N : WithTop ℕ∞} [IsManifold I N M]
    [ContMDiffVectorBundle N E (TangentSpace I : M → Type _) I]
    {X : ℝ → M → E} {p : M} {χ : ℝ × E → ℝ} {Φ : ℝ → M → M} {ε : ℝ}
    {U Q_M : Set M} {Kwin : Set (ℝ × E)} {state₀ : Set E} {K : ℝ≥0}
    (hε : 0 < ε)
    (hanchor : ∀ x, Φ 0 x = x)
    (horbit : ∀ x, ∀ t ∈ Set.Ioo (-ε) ε,
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun σ : ℝ => Φ σ x) (Set.Ioo (-ε) ε) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x))))
    (hcontA : ∀ x, ContinuousAt (fun z : ℝ × M => Φ z.1 z.2) (0, x))
    (hXchart : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) N
      (fun r : ℝ × M => (⟨r.2, X r.1 r.2⟩ : TangentBundle I M))
      (Set.univ ×ˢ (extChartAt I p).source))
    (hχC : ContDiff ℝ N χ) (hχc : HasCompactSupport χ)
    (hsub : tsupport χ ⊆ Set.univ ×ˢ (extChartAt I p).target)
    (hcut : ∀ᶠ r in 𝓝ˢ Kwin, χ r = 1) (hN : 4 ≤ N)
    (hstate : IsOpen state₀)
    (hlip : ∀ τ : ℝ, LipschitzOnWith K
      (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ) state₀)
    (hU : U ⊆ (chartAt H p).source) (hUQ : U ⊆ (Q_M : Set M))
    (hQ_M : IsCompact Q_M) (hQ_M_src : Q_M ⊆ (extChartAt I p).source)
    (hplace_state : ∀ x ∈ Q_M, extChartAt I p x ∈ state₀)
    (hplace_win : ∀ x ∈ Q_M, ((0 : ℝ), extChartAt I p x) ∈ interior Kwin) :
    ∃ a b : ℝ, (0 : ℝ) ∈ Set.Ioo a b ∧
      ∀ t ∈ Set.Ioo a b, ContMDiffOn I I 3 (fun x : M => Φ t x) U := by
  obtain ⟨a₁, b₁, hmem0₁, hconf⟩ :=
    exists_Ioo_forall_forall_extChartAt_source_and_mem_of_continuousAt (Φ := Φ)
      hQ_M hQ_M_src (isOpen_univ.prod hstate) (fun x _ => hanchor x)
      (fun x hx => ⟨Set.mem_univ _, hplace_state x hx⟩) (fun x _ => hcontA x)
  obtain ⟨G, a₂, b₂, hmem0₂, hχ_mod, hg_mem_mod⟩ :=
    exists_diffeomorph3GaugeFlowOn_Ioo_cutoff_eqOne_and_state_mem (X := X) (p := p)
      hXchart hχC hχc hsub hN (0 : ℝ)
      (isCompact_extChartAt_image hQ_M hQ_M_src) hcut hstate
      (fun q hq => by obtain ⟨x, hx, rfl⟩ := hq; exact hplace_win x hx)
      (fun q hq => by obtain ⟨x, hx, rfl⟩ := hq; exact hplace_state x hx)
  refine ⟨max (max a₁ a₂) (-ε), min (min b₁ b₂) ε,
    ⟨max_lt (max_lt hmem0₁.1 hmem0₂.1) (neg_lt_zero.mpr hε),
      lt_min (lt_min hmem0₁.2 hmem0₂.2) hε⟩, ?_⟩
  intro t ht
  have hsub_conf : Set.Ioo (max (max a₁ a₂) (-ε)) (min (min b₁ b₂) ε) ⊆ Set.Ioo a₁ b₁ :=
    Set.Ioo_subset_Ioo ((le_max_left a₁ a₂).trans (le_max_left (max a₁ a₂) (-ε)))
      ((min_le_left (min b₁ b₂) ε).trans (min_le_left b₁ b₂))
  have hsub_mod : Set.Ioo (max (max a₁ a₂) (-ε)) (min (min b₁ b₂) ε) ⊆ Set.Ioo a₂ b₂ :=
    Set.Ioo_subset_Ioo ((le_max_right a₁ a₂).trans (le_max_left (max a₁ a₂) (-ε)))
      ((min_le_left (min b₁ b₂) ε).trans (min_le_right b₁ b₂))
  have hsub_ode : Set.Ioo (max (max a₁ a₂) (-ε)) (min (min b₁ b₂) ε) ⊆ Set.Ioo (-ε) ε :=
    Set.Ioo_subset_Ioo (le_max_right (max a₁ a₂) (-ε)) (min_le_right (min b₁ b₂) ε)
  have ht₀ : (0 : ℝ) ∈ Set.Ioo (max (max a₁ a₂) (-ε)) (min (min b₁ b₂) ε) :=
    ⟨max_lt (max_lt hmem0₁.1 hmem0₂.1) (neg_lt_zero.mpr hε),
      lt_min (lt_min hmem0₁.2 hmem0₂.2) hε⟩
  refine contMDiffOn_flowSlice_of_cutoff_orbit_control (X := X) (p := p) (χ := χ)
    (state := fun _ : ℝ => state₀) G Φ hU ht ht₀ (fun τ _ => Filter.univ_mem)
    (fun τ _ => hlip τ) ?_ ?_ ?_ ?_ ?_ ?_
  · intro x _ τ hτ
    exact (horbit x τ (hsub_ode hτ)).mono hsub_ode
  · intro x hx τ hτ
    exact (hconf τ (hsub_conf hτ)).1 x (hUQ hx)
  · intro x hx τ hτ
    exact hχ_mod (extChartAt I p x) ⟨x, hUQ hx, rfl⟩ τ (hsub_mod hτ)
  · intro x hx τ hτ
    exact ((hconf τ (hsub_conf hτ)).2 x (hUQ hx)).2
  · intro x hx τ hτ
    exact hg_mem_mod (extChartAt I p x) ⟨x, hUQ hx, rfl⟩ τ (hsub_mod hτ)
  · intro x _
    exact extChartAt_flow_eq_maps3_at_zero (p := p) G hanchor x

/-- **Window-restricted Lipschitz variant of `contMDiffOn_flowSlice_perPatch_of_flow`.**  Identical to
`contMDiffOn_flowSlice_perPatch_of_flow` except the field-Lipschitz control `hlip` is required only on a
fixed bounded time window `Set.Icc c d` (with `0 ∈ Set.Ioo c d`) rather than for *all* `τ : ℝ`.  Because
the per-patch capstone only ever uses the Lipschitz bound on the (bounded) time window it internally
builds, this weaker hypothesis suffices — and it is exactly the shape produced by
`GaugeFlowAssembly.exists_lipschitzOnWith_forall_mem_Icc_chartPushforwardField`, which delivers a
Lipschitz bound for `chartPushforwardField` only on a compact time interval `Set.Icc a b`, not for all
time.  The proof simply intersects the internally-built slice-`C³` window with `Set.Ioo c d`, so every
`τ` fed to `hlip` lies in `Set.Icc c d`.  This removes the artificial `∀ τ : ℝ` impedance mismatch that
blocked feeding the bounded-time field-Lipschitz lemma into the step-(v) globalisation. -/
theorem contMDiffOn_flowSlice_perPatch_of_flow_windowLip
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {N : WithTop ℕ∞} [IsManifold I N M]
    [ContMDiffVectorBundle N E (TangentSpace I : M → Type _) I]
    {X : ℝ → M → E} {p : M} {χ : ℝ × E → ℝ} {Φ : ℝ → M → M} {ε : ℝ}
    {U Q_M : Set M} {Kwin : Set (ℝ × E)} {state₀ : Set E} {K : ℝ≥0} {c d : ℝ}
    (hε : 0 < ε)
    (hcd0 : (0 : ℝ) ∈ Set.Ioo c d)
    (hanchor : ∀ x, Φ 0 x = x)
    (horbit : ∀ x, ∀ t ∈ Set.Ioo (-ε) ε,
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun σ : ℝ => Φ σ x) (Set.Ioo (-ε) ε) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x))))
    (hcontA : ∀ x, ContinuousAt (fun z : ℝ × M => Φ z.1 z.2) (0, x))
    (hXchart : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) N
      (fun r : ℝ × M => (⟨r.2, X r.1 r.2⟩ : TangentBundle I M))
      (Set.univ ×ˢ (extChartAt I p).source))
    (hχC : ContDiff ℝ N χ) (hχc : HasCompactSupport χ)
    (hsub : tsupport χ ⊆ Set.univ ×ˢ (extChartAt I p).target)
    (hcut : ∀ᶠ r in 𝓝ˢ Kwin, χ r = 1) (hN : 4 ≤ N)
    (hstate : IsOpen state₀)
    (hlip : ∀ τ ∈ Set.Icc c d, LipschitzOnWith K
      (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ) state₀)
    (hU : U ⊆ (chartAt H p).source) (hUQ : U ⊆ (Q_M : Set M))
    (hQ_M : IsCompact Q_M) (hQ_M_src : Q_M ⊆ (extChartAt I p).source)
    (hplace_state : ∀ x ∈ Q_M, extChartAt I p x ∈ state₀)
    (hplace_win : ∀ x ∈ Q_M, ((0 : ℝ), extChartAt I p x) ∈ interior Kwin) :
    ∃ a b : ℝ, (0 : ℝ) ∈ Set.Ioo a b ∧
      ∀ t ∈ Set.Ioo a b, ContMDiffOn I I 3 (fun x : M => Φ t x) U := by
  obtain ⟨a₁, b₁, hmem0₁, hconf⟩ :=
    exists_Ioo_forall_forall_extChartAt_source_and_mem_of_continuousAt (Φ := Φ)
      hQ_M hQ_M_src (isOpen_univ.prod hstate) (fun x _ => hanchor x)
      (fun x hx => ⟨Set.mem_univ _, hplace_state x hx⟩) (fun x _ => hcontA x)
  obtain ⟨G, a₂, b₂, hmem0₂, hχ_mod, hg_mem_mod⟩ :=
    exists_diffeomorph3GaugeFlowOn_Ioo_cutoff_eqOne_and_state_mem (X := X) (p := p)
      hXchart hχC hχc hsub hN (0 : ℝ)
      (isCompact_extChartAt_image hQ_M hQ_M_src) hcut hstate
      (fun q hq => by obtain ⟨x, hx, rfl⟩ := hq; exact hplace_win x hx)
      (fun q hq => by obtain ⟨x, hx, rfl⟩ := hq; exact hplace_state x hx)
  refine ⟨max (max (max a₁ a₂) (-ε)) c, min (min (min b₁ b₂) ε) d,
    ⟨max_lt (max_lt (max_lt hmem0₁.1 hmem0₂.1) (neg_lt_zero.mpr hε)) hcd0.1,
      lt_min (lt_min (lt_min hmem0₁.2 hmem0₂.2) hε) hcd0.2⟩, ?_⟩
  intro t ht
  have hsub_conf : Set.Ioo (max (max (max a₁ a₂) (-ε)) c) (min (min (min b₁ b₂) ε) d)
      ⊆ Set.Ioo a₁ b₁ :=
    Set.Ioo_subset_Ioo
      ((le_max_left a₁ a₂).trans ((le_max_left _ _).trans (le_max_left _ _)))
      ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hsub_mod : Set.Ioo (max (max (max a₁ a₂) (-ε)) c) (min (min (min b₁ b₂) ε) d)
      ⊆ Set.Ioo a₂ b₂ :=
    Set.Ioo_subset_Ioo
      ((le_max_right a₁ a₂).trans ((le_max_left _ _).trans (le_max_left _ _)))
      ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hsub_ode : Set.Ioo (max (max (max a₁ a₂) (-ε)) c) (min (min (min b₁ b₂) ε) d)
      ⊆ Set.Ioo (-ε) ε :=
    Set.Ioo_subset_Ioo
      ((le_max_right _ _).trans (le_max_left _ _))
      ((min_le_left _ _).trans (min_le_right _ _))
  have hsub_cd : Set.Ioo (max (max (max a₁ a₂) (-ε)) c) (min (min (min b₁ b₂) ε) d)
      ⊆ Set.Icc c d :=
    (Set.Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)).trans Set.Ioo_subset_Icc_self
  have ht₀ : (0 : ℝ) ∈ Set.Ioo (max (max (max a₁ a₂) (-ε)) c) (min (min (min b₁ b₂) ε) d) :=
    ⟨max_lt (max_lt (max_lt hmem0₁.1 hmem0₂.1) (neg_lt_zero.mpr hε)) hcd0.1,
      lt_min (lt_min (lt_min hmem0₁.2 hmem0₂.2) hε) hcd0.2⟩
  refine contMDiffOn_flowSlice_of_cutoff_orbit_control (X := X) (p := p) (χ := χ)
    (state := fun _ : ℝ => state₀) G Φ hU ht ht₀ (fun τ _ => Filter.univ_mem)
    (fun τ hτ => hlip τ (hsub_cd hτ)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro x _ τ hτ
    exact (horbit x τ (hsub_ode hτ)).mono hsub_ode
  · intro x hx τ hτ
    exact (hconf τ (hsub_conf hτ)).1 x (hUQ hx)
  · intro x hx τ hτ
    exact hχ_mod (extChartAt I p x) ⟨x, hUQ hx, rfl⟩ τ (hsub_mod hτ)
  · intro x hx τ hτ
    exact ((hconf τ (hsub_conf hτ)).2 x (hUQ hx)).2
  · intro x hx τ hτ
    exact hg_mem_mod (extChartAt I p x) ⟨x, hUQ hx, rfl⟩ τ (hsub_mod hτ)
  · intro x _
    exact extChartAt_flow_eq_maps3_at_zero (p := p) G hanchor x

/-- **Finite-cover globalisation of per-patch slice-`C³` to a global slice-`C³` window.**  The gluing
step of GAP-1 step (v): given a family `U : ι → Set M` (`ι` finite) of OPEN sets covering `M`, and for
each patch `i` an honest open time window `Set.Ioo (a i) (b i) ∋ 0` on which the flow slice `Φ t` is
`ContMDiffOn I I 3` on `U i` (exactly the output of `contMDiffOn_flowSlice_perPatch_of_flow`), there is a
single open window `Set.Ioo c d ∋ 0` on which `Φ t` is **globally** `ContMDiff I I 3` on all of `M`.

The finite intersection `⋂ i, Set.Ioo (a i) (b i)` of the patch windows is an open neighbourhood of `0`
(`isOpen_iInter_of_finite`), hence contains an honest `Set.Ioo c d ∋ 0` (`mem_nhds_iff_exists_Ioo_subset`);
for `t` in it, `t` lies in every patch window, so `Φ t` is `ContMDiffOn` on every `U i`, and since the
`U i` are open and cover `M`, `contMDiff_of_locally_contMDiffOn` upgrades this to global `ContMDiff`.
Together with the global compact flow existence and `contMDiffOn_flowSlice_perPatch_of_flow` on each
chart patch of a finite cover, this is the finite-cover globalisation that closes the `hslicesC3`
(`∀ t, ContMDiff I I 3 (Φ t)`) content of GAP-1 step (v) once the per-patch field-analytic data is
supplied. -/
theorem exists_Ioo_forall_contMDiff_of_finite_cover
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Finite ι] {Φ : ℝ → M → M} {U : ι → Set M}
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (hpatch : ∀ i : ι, ∃ a b : ℝ, (0 : ℝ) ∈ Set.Ioo a b ∧
      ∀ t ∈ Set.Ioo a b, ContMDiffOn I I 3 (fun x : M => Φ t x) (U i)) :
    ∃ c d : ℝ, (0 : ℝ) ∈ Set.Ioo c d ∧
      ∀ t ∈ Set.Ioo c d, ContMDiff I I 3 (fun x : M => Φ t x) := by
  choose a b hmem hslice using hpatch
  have hWopen : IsOpen (⋂ i, Set.Ioo (a i) (b i)) :=
    isOpen_iInter_of_finite (fun i => isOpen_Ioo)
  have hW0 : (0 : ℝ) ∈ ⋂ i, Set.Ioo (a i) (b i) :=
    Set.mem_iInter.mpr (fun i => hmem i)
  obtain ⟨c, d, hcd, hsubW⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hWopen.mem_nhds hW0)
  refine ⟨c, d, hcd, fun t ht => ?_⟩
  have htIoo : ∀ i, t ∈ Set.Ioo (a i) (b i) :=
    fun i => Set.mem_iInter.mp (hsubW ht) i
  refine contMDiff_of_locally_contMDiffOn (fun x => ?_)
  obtain ⟨i, hxi⟩ := hcover x
  exact ⟨U i, hopen i, hxi, hslice i t (htIoo i)⟩

/-- **GAP-1 step (v), globalised: from the DeTurck gauge-field jet + per-patch field-analytic data over
a finite chart cover to a single global flow whose slices are `ContMDiff I I 3` on a time window.**  This
assembles the whole step (v): the global compact time-dependent flow `Φ` is constructed ONCE from the
global `C¹` product-tangent field jet `hXraw` (`exists_timeDependent_flow_compact_continuousAt`); the
`Φ`-input per-patch capstone `contMDiffOn_flowSlice_perPatch_of_flow` is applied on each patch `i` of a
finite open cover to yield the per-patch slice-`C³` windows for that same `Φ`; and the finite-cover
gluing `exists_Ioo_forall_contMDiff_of_finite_cover` intersects the windows and globalises to
`ContMDiff I I 3 (Φ t)` on a single window `Set.Ioo c d ∋ 0`.

Everything downstream of the two field jets (`hXraw`, the per-patch `hXchart i`) and the per-patch
field-analytic residuals (the cutoffs `χ i`, states `state₀ i`, cut windows `Kwin i`, the Lipschitz
control `hlip i`, and the initial-data placements) is now MECHANICAL.  What remains for a general compact
`M` is to SUPPLY that per-patch data from the actual Ricci-DeTurck gauge field `X` — i.e. exhibit the
finite chart cover with a cutoff-flow package on each patch — the residual `(b) hX` plus the
field-analytic faces the plan isolates. -/
theorem exists_flow_Ioo_forall_contMDiff_of_field_jets_finite_cover
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    [BoundarylessManifold I M] [CompactSpace M] [IsManifold I 1 M]
    {N : WithTop ℕ∞} [IsManifold I N M]
    [ContMDiffVectorBundle N E (TangentSpace I : M → Type _) I]
    {X : ℝ → M → E}
    (hXraw : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun q : ℝ × M => (⟨q, ((1 : ℝ), X q.1 q.2)⟩ :
        TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    {ι : Type*} [Finite ι]
    {p : ι → M} {U Q_M : ι → Set M} {χ : ι → (ℝ × E → ℝ)}
    {Kwin : ι → Set (ℝ × E)} {state₀ : ι → Set E} {K : ι → ℝ≥0}
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (hXchart : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) N
      (fun r : ℝ × M => (⟨r.2, X r.1 r.2⟩ : TangentBundle I M))
      (Set.univ ×ˢ (extChartAt I (p i)).source))
    (hχC : ∀ i, ContDiff ℝ N (χ i)) (hχc : ∀ i, HasCompactSupport (χ i))
    (hsub : ∀ i, tsupport (χ i) ⊆ Set.univ ×ˢ (extChartAt I (p i)).target)
    (hcut : ∀ i, ∀ᶠ r in 𝓝ˢ (Kwin i), (χ i) r = 1) (hN : 4 ≤ N)
    (hstate : ∀ i, IsOpen (state₀ i))
    (hlip : ∀ i, ∀ τ : ℝ, LipschitzOnWith (K i)
      (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X (p i) τ) (state₀ i))
    (hU : ∀ i, U i ⊆ (chartAt H (p i)).source) (hUQ : ∀ i, U i ⊆ (Q_M i : Set M))
    (hQ_M : ∀ i, IsCompact (Q_M i)) (hQ_M_src : ∀ i, Q_M i ⊆ (extChartAt I (p i)).source)
    (hplace_state : ∀ i, ∀ x ∈ Q_M i, extChartAt I (p i) x ∈ state₀ i)
    (hplace_win : ∀ i, ∀ x ∈ Q_M i, ((0 : ℝ), extChartAt I (p i) x) ∈ interior (Kwin i)) :
    ∃ (Φ : ℝ → M → M) (c d : ℝ), (∀ x, Φ 0 x = x) ∧ (0 : ℝ) ∈ Set.Ioo c d ∧
      ∀ t ∈ Set.Ioo c d, ContMDiff I I 3 (fun x : M => Φ t x) := by
  obtain ⟨ε, hε, Φ, hanchor, horbit, hcontA⟩ :=
    PoincareCurvature.ManifoldFlow.exists_timeDependent_flow_compact_continuousAt hXraw
  obtain ⟨c, d, hcd, hglob⟩ :=
    exists_Ioo_forall_contMDiff_of_finite_cover (Φ := Φ) hopen hcover
      (fun i => contMDiffOn_flowSlice_perPatch_of_flow (X := X) (p := p i)
        hε hanchor horbit hcontA (hXchart i) (hχC i) (hχc i) (hsub i) (hcut i) hN
        (hstate i) (hlip i) (hU i) (hUQ i) (hQ_M i) (hQ_M_src i)
        (hplace_state i) (hplace_win i))
  exact ⟨Φ, c, d, hanchor, hcd, hglob⟩

/-- **Window-restricted Lipschitz variant of the step-(v) globalisation capstone
`exists_flow_Ioo_forall_contMDiff_of_field_jets_finite_cover`.**  Identical to the capstone except the
per-patch field-Lipschitz control `hlip` is required only on a fixed bounded time window `Set.Icc cw dw`
(with `0 ∈ Set.Ioo cw dw`) rather than for *all* `τ : ℝ`.  This is the exact shape delivered by
`GaugeFlowAssembly.exists_lipschitzOnWith_forall_mem_Icc_chartPushforwardField`, so with this variant the
whole `hlip` residual is dischargeable directly from the per-patch field jet `hXchart i` on a compact
convex chart tube — no artificial global-in-time Lipschitz bound is needed.  Proof: identical to the
capstone but routed through `contMDiffOn_flowSlice_perPatch_of_flow_windowLip`. -/
theorem exists_flow_Ioo_forall_contMDiff_of_field_jets_finite_cover_windowLip
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    [BoundarylessManifold I M] [CompactSpace M] [IsManifold I 1 M]
    {N : WithTop ℕ∞} [IsManifold I N M]
    [ContMDiffVectorBundle N E (TangentSpace I : M → Type _) I]
    {X : ℝ → M → E}
    (hXraw : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun q : ℝ × M => (⟨q, ((1 : ℝ), X q.1 q.2)⟩ :
        TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    {ι : Type*} [Finite ι] {cw dw : ℝ}
    {p : ι → M} {U Q_M : ι → Set M} {χ : ι → (ℝ × E → ℝ)}
    {Kwin : ι → Set (ℝ × E)} {state₀ : ι → Set E} {K : ι → ℝ≥0}
    (hcd0 : (0 : ℝ) ∈ Set.Ioo cw dw)
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (hXchart : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) N
      (fun r : ℝ × M => (⟨r.2, X r.1 r.2⟩ : TangentBundle I M))
      (Set.univ ×ˢ (extChartAt I (p i)).source))
    (hχC : ∀ i, ContDiff ℝ N (χ i)) (hχc : ∀ i, HasCompactSupport (χ i))
    (hsub : ∀ i, tsupport (χ i) ⊆ Set.univ ×ˢ (extChartAt I (p i)).target)
    (hcut : ∀ i, ∀ᶠ r in 𝓝ˢ (Kwin i), (χ i) r = 1) (hN : 4 ≤ N)
    (hstate : ∀ i, IsOpen (state₀ i))
    (hlip : ∀ i, ∀ τ ∈ Set.Icc cw dw, LipschitzOnWith (K i)
      (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X (p i) τ) (state₀ i))
    (hU : ∀ i, U i ⊆ (chartAt H (p i)).source) (hUQ : ∀ i, U i ⊆ (Q_M i : Set M))
    (hQ_M : ∀ i, IsCompact (Q_M i)) (hQ_M_src : ∀ i, Q_M i ⊆ (extChartAt I (p i)).source)
    (hplace_state : ∀ i, ∀ x ∈ Q_M i, extChartAt I (p i) x ∈ state₀ i)
    (hplace_win : ∀ i, ∀ x ∈ Q_M i, ((0 : ℝ), extChartAt I (p i) x) ∈ interior (Kwin i)) :
    ∃ (Φ : ℝ → M → M) (c d : ℝ), (∀ x, Φ 0 x = x) ∧ (0 : ℝ) ∈ Set.Ioo c d ∧
      ∀ t ∈ Set.Ioo c d, ContMDiff I I 3 (fun x : M => Φ t x) := by
  obtain ⟨ε, hε, Φ, hanchor, horbit, hcontA⟩ :=
    PoincareCurvature.ManifoldFlow.exists_timeDependent_flow_compact_continuousAt hXraw
  obtain ⟨c, d, hcd, hglob⟩ :=
    exists_Ioo_forall_contMDiff_of_finite_cover (Φ := Φ) hopen hcover
      (fun i => contMDiffOn_flowSlice_perPatch_of_flow_windowLip (X := X) (p := p i)
        hε hcd0 hanchor horbit hcontA (hXchart i) (hχC i) (hχc i) (hsub i) (hcut i) hN
        (hstate i) (hlip i) (hU i) (hUQ i) (hQ_M i) (hQ_M_src i)
        (hplace_state i) (hplace_win i))
  exact ⟨Φ, c, d, hanchor, hcd, hglob⟩

/-- **Global slice-`C³` of an *abstract* compact-manifold flow from the field jets — the forward half
of the `hslicesC3` obligation for a *given* flow.**  Identical to
`exists_flow_Ioo_forall_contMDiff_of_field_jets_finite_cover_windowLip`, except that the raw manifold
flow `Φ` is **supplied as a hypothesis** (with only its anchor `hanchor` and ODE `horbit` on
`Set.Ioo (-ε) ε`) rather than produced internally by
`exists_timeDependent_flow_compact_continuousAt`.  The missing joint space-time continuity `hcontA`
that the per-patch capstone needs is **derived** from the raw `C¹` field jet `hXraw` alone via
`ManifoldFlow.continuousAt_timeDependent_flow_of_anchor_ode` (the abstract flow agrees, by
`timeDependent_flow_unique`, with the canonical continuous flow on an open space-time neighbourhood of
`{0} × M`).  The conclusion produces `ContMDiff I I 3 (Φ t)` for **that same** `Φ` on a window
`Set.Ioo c d ∋ 0` — exactly the forward conjunct of the `hslicesC3` hypothesis of
`GaugeFlowAssembly.exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3`, which hands the
proof obligation a fixed abstract flow with no continuity datum.  The proof is verbatim the internal
body of the `_windowLip` capstone with the internal flow-production `obtain` replaced by the supplied
`Φ`/`hanchor`/`horbit` and the derived `hcontA`. -/
theorem exists_flow_Ioo_forall_contMDiff_of_field_jets_finite_cover_windowLip_of_flow
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    [BoundarylessManifold I M] [CompactSpace M] [IsManifold I 1 M]
    {N : WithTop ℕ∞} [IsManifold I N M]
    [ContMDiffVectorBundle N E (TangentSpace I : M → Type _) I]
    {X : ℝ → M → E}
    (hXraw : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun q : ℝ × M => (⟨q, ((1 : ℝ), X q.1 q.2)⟩ :
        TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))))
    {Φ : ℝ → M → M} {ε : ℝ} (hε : 0 < ε)
    (hanchor : ∀ x, Φ 0 x = x)
    (horbit : ∀ x, ∀ t ∈ Set.Ioo (-ε) ε,
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun σ : ℝ => Φ σ x) (Set.Ioo (-ε) ε) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ t x))))
    {ι : Type*} [Finite ι] {cw dw : ℝ}
    {p : ι → M} {U Q_M : ι → Set M} {χ : ι → (ℝ × E → ℝ)}
    {Kwin : ι → Set (ℝ × E)} {state₀ : ι → Set E} {K : ι → ℝ≥0}
    (hcd0 : (0 : ℝ) ∈ Set.Ioo cw dw)
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (hXchart : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) N
      (fun r : ℝ × M => (⟨r.2, X r.1 r.2⟩ : TangentBundle I M))
      (Set.univ ×ˢ (extChartAt I (p i)).source))
    (hχC : ∀ i, ContDiff ℝ N (χ i)) (hχc : ∀ i, HasCompactSupport (χ i))
    (hsub : ∀ i, tsupport (χ i) ⊆ Set.univ ×ˢ (extChartAt I (p i)).target)
    (hcut : ∀ i, ∀ᶠ r in 𝓝ˢ (Kwin i), (χ i) r = 1) (hN : 4 ≤ N)
    (hstate : ∀ i, IsOpen (state₀ i))
    (hlip : ∀ i, ∀ τ ∈ Set.Icc cw dw, LipschitzOnWith (K i)
      (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X (p i) τ) (state₀ i))
    (hU : ∀ i, U i ⊆ (chartAt H (p i)).source) (hUQ : ∀ i, U i ⊆ (Q_M i : Set M))
    (hQ_M : ∀ i, IsCompact (Q_M i)) (hQ_M_src : ∀ i, Q_M i ⊆ (extChartAt I (p i)).source)
    (hplace_state : ∀ i, ∀ x ∈ Q_M i, extChartAt I (p i) x ∈ state₀ i)
    (hplace_win : ∀ i, ∀ x ∈ Q_M i, ((0 : ℝ), extChartAt I (p i) x) ∈ interior (Kwin i)) :
    ∃ c d : ℝ, (0 : ℝ) ∈ Set.Ioo c d ∧
      ∀ t ∈ Set.Ioo c d, ContMDiff I I 3 (fun x : M => Φ t x) := by
  have hcontA : ∀ x, ContinuousAt (fun z : ℝ × M => Φ z.1 z.2) (0, x) := fun x =>
    PoincareCurvature.ManifoldFlow.continuousAt_timeDependent_flow_of_anchor_ode
      hXraw hε hanchor horbit x
  obtain ⟨c, d, hcd, hglob⟩ :=
    exists_Ioo_forall_contMDiff_of_finite_cover (Φ := Φ) hopen hcover
      (fun i => contMDiffOn_flowSlice_perPatch_of_flow_windowLip (X := X) (p := p i)
        hε hcd0 hanchor horbit hcontA (hXchart i) (hχC i) (hχc i) (hsub i) (hcut i) hN
        (hstate i) (hlip i) (hU i) (hUQ i) (hQ_M i) (hQ_M_src i)
        (hplace_state i) (hplace_win i))
  exact ⟨c, d, hcd, hglob⟩


/-- **Finite chart cover of a compact manifold — the cover-side data package consumed by the step-(v)
globalisation capstone `exists_flow_Ioo_forall_contMDiff_of_field_jets_finite_cover`.**  For a compact
Hausdorff manifold `M` charted on the model `H` (`I : ModelWithCorners ℝ E H`), there is a finite index
type `ι`, chart centres `p : ι → M`, open patches `U : ι → Set M`, and compact patches
`Q_M : ι → Set M` with:

* `U i` open and covering `M` (`hopen`, `hcover`);
* each open patch inside its chart source, `U i ⊆ (chartAt H (p i)).source` (`hU`);
* each open patch inside its compact patch, `U i ⊆ Q_M i` (`hUQ`);
* each `Q_M i` compact (`hQ_M`) and inside the extended-chart source
  `Q_M i ⊆ (extChartAt I (p i)).source` (`hQ_M_src`).

This is exactly the cover-side hypothesis bundle
`hopen`/`hcover`/`hU`/`hUQ`/`hQ_M`/`hQ_M_src` of
`exists_flow_Ioo_forall_contMDiff_of_field_jets_finite_cover`; the remaining per-patch field-analytic
data (`hXchart`, cutoff `χ`, Lipschitz tube `state₀`, placements) are supplied separately from the real
gauge field.  No analytic content: `M` compact + Hausdorff is locally compact, so around each point a
compact neighbourhood `Q_M x` with `x ∈ interior (Q_M x) ⊆ Q_M x ⊆ (extChartAt I x).source` exists
(`exists_compact_subset`); the interiors form an open cover, and compactness of `M` extracts a finite
subcover (`isCompact_univ.elim_finite_subcover`).  The chart-source containment uses
`extChartAt_source`. -/
theorem exists_finite_chart_cover_compact
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [CompactSpace M] :
    ∃ (ι : Type uM) (_ : Finite ι) (p : ι → M) (U Q_M : ι → Set M),
      (∀ i, IsOpen (U i)) ∧ (∀ x : M, ∃ i, x ∈ U i) ∧
      (∀ i, U i ⊆ (chartAt H (p i)).source) ∧
      (∀ i, U i ⊆ Q_M i) ∧ (∀ i, IsCompact (Q_M i)) ∧
      (∀ i, Q_M i ⊆ (extChartAt I (p i)).source) := by
  have hpt : ∀ x : M, ∃ K : Set M, IsCompact K ∧ x ∈ interior K ∧
      K ⊆ (extChartAt I x).source := by
    intro x
    exact exists_compact_subset (isOpen_extChartAt_source (I := I) x)
      (mem_extChartAt_source (I := I) x)
  choose K hKcpt hKint hKsrc using hpt
  have hcov : (Set.univ : Set M) ⊆ ⋃ x : M, interior (K x) := by
    intro x _
    exact Set.mem_iUnion.2 ⟨x, hKint x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : M => interior (K x))
    (fun x => isOpen_interior) hcov
  refine ⟨{x : M // x ∈ t}, inferInstance, Subtype.val,
    fun i => interior (K i.1), fun i => K i.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact isOpen_interior
  · intro x
    have hx : x ∈ ⋃ i ∈ t, interior (K i) := ht (Set.mem_univ x)
    rcases Set.mem_iUnion₂.1 hx with ⟨x0, hx0t, hx0int⟩
    exact ⟨⟨x0, hx0t⟩, hx0int⟩
  · intro i
    have h : interior (K i.1) ⊆ (extChartAt I i.1).source :=
      interior_subset.trans (hKsrc i.1)
    rw [extChartAt_source I i.1] at h
    exact h
  · intro i; exact interior_subset
  · intro i; exact hKcpt i.1
  · intro i; exact hKsrc i.1

/-- **Compact space-time window around the chart image of a compact patch — the `Kwin`/`hplace_win`
data package consumed by the step-(v) globalisation capstone.**  For a compact patch
`Q ⊆ (extChartAt I p).source` on a boundaryless manifold modelled on a finite-dimensional `E`, there is
a compact window `Kwin ⊆ ℝ × E` with:

* `Kwin ⊆ Set.univ ×ˢ (extChartAt I p).target` (the containment the cutoff `χ`'s
  `tsupport ⊆ univ ×ˢ target` obligation `hsub` rests on);
* every anchored chart image in its interior: `∀ x ∈ Q, ((0 : ℝ), extChartAt I p x) ∈ interior Kwin`
  (the capstone's `hplace_win`).

This is exactly the `Kwin`/`hplace_win` pair of
`exists_flow_Ioo_forall_contMDiff_of_field_jets_finite_cover`; the cutoff `χ ≡ 1` near `Kwin` is then a
smooth bump on `ℝ × E` supported in `univ ×ˢ target`.  No analytic content: the chart image
`extChartAt I p '' Q` is compact (`isCompact_extChartAt_image`) and inside the open target
(`PartialEquiv.image_source_eq_target`, `isOpen_extChartAt_target`); `E` finite-dimensional is locally
compact, so `exists_compact_between` gives a compact `C` with
`extChartAt I p '' Q ⊆ interior C ⊆ C ⊆ target`, and `Kwin := Icc (-1) 1 ×ˢ C` works
(`interior_prod_eq`, `interior_Icc`). -/
theorem exists_compact_window_of_compact_patch
    [FiniteDimensional ℝ E]
    {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] {Q : Set M} {p : M}
    (hQ : IsCompact Q) (hQsub : Q ⊆ (extChartAt I p).source) :
    ∃ Kwin : Set (ℝ × E), IsCompact Kwin ∧
      Kwin ⊆ Set.univ ×ˢ (extChartAt I p).target ∧
      (∀ x ∈ Q, ((0 : ℝ), extChartAt I p x) ∈ interior Kwin) := by
  have himg_cpt : IsCompact (extChartAt I p '' Q) := isCompact_extChartAt_image hQ hQsub
  have himg_sub : extChartAt I p '' Q ⊆ (extChartAt I p).target := by
    calc extChartAt I p '' Q ⊆ extChartAt I p '' (extChartAt I p).source := Set.image_mono hQsub
      _ = (extChartAt I p).target := (extChartAt I p).image_source_eq_target
  obtain ⟨C, hC_cpt, hC_int, hC_sub⟩ :=
    exists_compact_between himg_cpt (isOpen_extChartAt_target (I := I) p) himg_sub
  refine ⟨Set.Icc (-1 : ℝ) 1 ×ˢ C, isCompact_Icc.prod hC_cpt, ?_, ?_⟩
  · exact Set.prod_mono (Set.subset_univ _) hC_sub
  · intro x hx
    rw [interior_prod_eq, interior_Icc]
    exact ⟨by norm_num, hC_int (Set.mem_image_of_mem _ hx)⟩

/-- **A closed metric ball around a chart centre's image sits inside the chart target.**  For a
boundaryless `I` and a point `p : M`, the extended-chart image `extChartAt I p p` lies in the open chart
target `(extChartAt I p).target`, so some closed ball around it is contained in the target.  Fed to
`GaugeFlowAssembly.exists_lipschitzOnWith_forall_mem_Icc_chartPushforwardField_ball` (finite dimension
makes that closed ball compact, and it is convex), this supplies the open, convex Lipschitz tube
`state₀ := Metric.ball (extChartAt I p p) ρ` — with `IsOpen state₀` and the time-uniform field-Lipschitz
bound on it — that the step-(v) globalisation capstone consumes around the chart centre `p`. -/
theorem exists_pos_closedBall_subset_extChartAt_target
    {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Metric.closedBall (extChartAt I p p) ρ ⊆ (extChartAt I p).target := by
  have hmem : extChartAt I p p ∈ (extChartAt I p).target :=
    (extChartAt I p).map_source (mem_extChartAt_source (I := I) p)
  have hopen : IsOpen (extChartAt I p).target := isOpen_extChartAt_target (I := I) p
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem)
  exact ⟨ε / 2, by linarith, (Metric.closedBall_subset_ball (by linarith)).trans hball⟩

/-- **Finite chart BALL cover of a compact manifold.**  Strengthens `exists_finite_chart_cover_compact`:
for a compact boundaryless finite-dimensional manifold, the cover can be chosen so that each compact patch
`Q_M i` has its extended-chart image contained in an OPEN metric ball
`Metric.ball (extChartAt I (p i) (p i)) (ρ i)` whose closure lies in the chart target.  Combined with the
closed-ball-in-target existence and `GaugeFlowAssembly.exists_lipschitzOnWith_forall_mem_Icc_chartPushforwardField_ball`,
this supplies the whole `state₀`/`hstate`/`hlip`/`hplace_state` residual of the step-(v) globalisation
capstone `exists_flow_Ioo_forall_contMDiff_of_field_jets_finite_cover_windowLip` directly from the
per-patch chart field jet — taking `state₀ i := Metric.ball (extChartAt I (p i) (p i)) (ρ i)`.  The only
remaining capstone input is then the two gauge-field jets `hXraw`/`hXchart`.

Construction: around each point the closed-ball radius `R x` (from `exists_pos_closedBall_subset_extChartAt_target`)
gives an open cover set `U x := (extChartAt I x).source ∩ extChartAt I x ⁻¹' Metric.ball _ (R x / 2)`
(open by `ContinuousOn.isOpen_inter_preimage`), whose finite subcover is indexed; the patch
`Q_M i := (extChartAt I (p i)).symm '' Metric.closedBall _ (R (p i) / 2)` is compact
(`IsCompact.image_of_continuousOn`), lies in the chart source (`PartialEquiv.map_target`), and its image is
the half-radius closed ball (`PartialEquiv.right_inv`) ⊆ the full open ball. -/
theorem exists_finite_chart_ball_cover_compact
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [CompactSpace M] [FiniteDimensional ℝ E] :
    ∃ (ι : Type uM) (_ : Finite ι) (p : ι → M) (U Q_M : ι → Set M) (ρ : ι → ℝ),
      (∀ i, IsOpen (U i)) ∧ (∀ x : M, ∃ i, x ∈ U i) ∧
      (∀ i, U i ⊆ (chartAt H (p i)).source) ∧
      (∀ i, U i ⊆ Q_M i) ∧ (∀ i, IsCompact (Q_M i)) ∧
      (∀ i, Q_M i ⊆ (extChartAt I (p i)).source) ∧
      (∀ i, 0 < ρ i) ∧
      (∀ i, Metric.closedBall (extChartAt I (p i) (p i)) (ρ i) ⊆ (extChartAt I (p i)).target) ∧
      (∀ i, ∀ x ∈ Q_M i,
        extChartAt I (p i) x ∈ Metric.ball (extChartAt I (p i) (p i)) (ρ i)) := by
  choose R hRpos hRsub using
    fun x : M => exists_pos_closedBall_subset_extChartAt_target (I := I) x
  have hhalf : ∀ x : M,
      Metric.closedBall (extChartAt I x x) (R x / 2) ⊆ (extChartAt I x).target := fun x =>
    (Metric.closedBall_subset_closedBall (by linarith [hRpos x])).trans (hRsub x)
  have hUopen : ∀ x : M, IsOpen ((extChartAt I x).source ∩
      extChartAt I x ⁻¹' Metric.ball (extChartAt I x x) (R x / 2)) := fun x =>
    (continuousOn_extChartAt (I := I) x).isOpen_inter_preimage
      (isOpen_extChartAt_source (I := I) x) Metric.isOpen_ball
  have hUmem : ∀ x : M, x ∈ (extChartAt I x).source ∩
      extChartAt I x ⁻¹' Metric.ball (extChartAt I x x) (R x / 2) := fun x =>
    ⟨mem_extChartAt_source (I := I) x, Metric.mem_ball_self (by linarith [hRpos x])⟩
  have hcov : (Set.univ : Set M) ⊆ ⋃ x : M, ((extChartAt I x).source ∩
      extChartAt I x ⁻¹' Metric.ball (extChartAt I x x) (R x / 2)) := fun x _ =>
    Set.mem_iUnion.2 ⟨x, hUmem x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M => (extChartAt I x).source ∩
      extChartAt I x ⁻¹' Metric.ball (extChartAt I x x) (R x / 2))
    (fun x => hUopen x) hcov
  refine ⟨{x : M // x ∈ t}, inferInstance, Subtype.val,
    fun i => (extChartAt I i.1).source ∩
      extChartAt I i.1 ⁻¹' Metric.ball (extChartAt I i.1 i.1) (R i.1 / 2),
    fun i => (extChartAt I i.1).symm '' Metric.closedBall (extChartAt I i.1 i.1) (R i.1 / 2),
    fun i => R i.1, fun i => hUopen i.1, ?_, ?_, ?_, ?_, ?_, fun i => hRpos i.1,
    fun i => hRsub i.1, ?_⟩
  · intro x
    have hx : x ∈ ⋃ x0 ∈ t, ((extChartAt I x0).source ∩
        extChartAt I x0 ⁻¹' Metric.ball (extChartAt I x0 x0) (R x0 / 2)) := ht (Set.mem_univ x)
    rcases Set.mem_iUnion₂.1 hx with ⟨x0, hx0t, hx0⟩
    exact ⟨⟨x0, hx0t⟩, hx0⟩
  · intro i
    rw [← extChartAt_source I i.1]
    exact Set.inter_subset_left
  · intro i y hy
    exact ⟨extChartAt I i.1 y, Metric.ball_subset_closedBall hy.2,
      (extChartAt I i.1).left_inv hy.1⟩
  · intro i
    exact (isCompact_closedBall _ _).image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := I) i.1).mono (hhalf i.1))
  · intro i
    exact Set.image_subset_iff.mpr
      (fun z hz => (extChartAt I i.1).map_target (hhalf i.1 hz))
  · intro i x hx
    rcases hx with ⟨z, hz, rfl⟩
    rw [(extChartAt I i.1).right_inv (hhalf i.1 hz)]
    exact Metric.closedBall_subset_ball (by linarith [hRpos i.1]) hz

/-- **Compact-manifold `C³` gauge-flow slice regularity from a single global field smoothness.**
The end-to-end step-(v) globalisation, reduced to ONE hypothesis: the joint space-time smoothness of
the gauge field `X : ℝ → M → E` as a `C^∞` section `(t, x) ↦ ⟨x, X t x⟩` of the tangent bundle
`TangentBundle I M` over `ℝ × M`.  From it — for a compact boundaryless finite-dimensional manifold —
there is a global flow `Φ` on some window `Ioo c d ∋ 0`, anchored `Φ 0 = id`, whose every time slice
`Φ t` is `ContMDiff I I 3`.

All the field-independent capstone data are produced internally: the finite chart BALL cover
(`exists_finite_chart_ball_cover_compact`), the two field jets `hXraw` (via the space-time bridge
`ManifoldFlow.contMDiff_spaceTimeField_of_contMDiff_tangentSection`) and `hXchart` (`ContMDiff.contMDiffOn`
of `hXfield`), the per-patch field-Lipschitz tube on the chart ball
(`GaugeFlowAssembly.exists_lipschitzOnWith_forall_mem_Icc_chartPushforwardField_ball`), the compact
space-time cutoff window (`exists_compact_window_of_compact_patch`) and its smooth bump
(`exists_contDiff_cutoff_one_nhdsSet_of_isCompact`), all fed to
`exists_flow_Ioo_forall_contMDiff_of_field_jets_finite_cover_windowLip`.  This closes the entire
field-independent GAP-1 assembly: the ONLY remaining obligation for the general compact `M` is the
global joint smoothness `hXfield` of the real Ricci–DeTurck gauge field.  (`C^∞` matches the natural
regularity of the gauge field of a smooth metric family and makes the smooth-bump cutoff available.) -/
theorem exists_flow_Ioo_forall_contMDiff_of_contMDiff_tangentSection_compact
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    [BoundarylessManifold I M] [CompactSpace M] [IsManifold I 1 M]
    [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
    {X : ℝ → M → E}
    (hXfield : ContMDiff ((𝓘(ℝ, ℝ)).prod I) I.tangent ∞
      (fun p : ℝ × M => (⟨p.2, X p.1 p.2⟩ : TangentBundle I M))) :
    ∃ (Φ : ℝ → M → M) (c d : ℝ), (∀ x, Φ 0 x = x) ∧ (0 : ℝ) ∈ Set.Ioo c d ∧
      ∀ t ∈ Set.Ioo c d, ContMDiff I I 3 (fun x : M => Φ t x) := by
  obtain ⟨ι, hιfin, p, U, Q_M, ρ, hopen, hcover, hU, hUQ, hQ_M, hQ_M_src,
      hρpos, hball, hplace⟩ := exists_finite_chart_ball_cover_compact (I := I) (M := M)
  haveI : Finite ι := hιfin
  have hXchart : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun r : ℝ × M => (⟨r.2, X r.1 r.2⟩ : TangentBundle I M))
      (Set.univ ×ˢ (extChartAt I (p i)).source) := fun i => hXfield.contMDiffOn
  have hXraw : ContMDiff ((𝓘(ℝ, ℝ)).prod I) (((𝓘(ℝ, ℝ)).prod I).tangent) 1
      (fun q : ℝ × M => (⟨q, ((1 : ℝ), X q.1 q.2)⟩ :
        TangentBundle ((𝓘(ℝ, ℝ)).prod I) (ℝ × M))) :=
    PoincareCurvature.ManifoldFlow.contMDiff_spaceTimeField_of_contMDiff_tangentSection
      (hXfield.of_le (by exact_mod_cast le_top))
  have hlipex : ∀ i, ∃ K : ℝ≥0, ∀ t ∈ Set.Icc (-1 : ℝ) 1, LipschitzOnWith K
      (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X (p i) t)
      (Metric.ball (extChartAt I (p i) (p i)) (ρ i)) := fun i =>
    PoincareCurvature.GaugeFlowAssembly.exists_lipschitzOnWith_forall_mem_Icc_chartPushforwardField_ball
      (a := -1) (b := 1) (hXfield.contMDiffOn) (by simp) (hball i)
  choose K hK using hlipex
  have hwinex : ∀ i, ∃ Kwin : Set (ℝ × E), IsCompact Kwin ∧
      Kwin ⊆ Set.univ ×ˢ (extChartAt I (p i)).target ∧
      (∀ x ∈ Q_M i, ((0 : ℝ), extChartAt I (p i) x) ∈ interior Kwin) := fun i =>
    exists_compact_window_of_compact_patch (hQ_M i) (hQ_M_src i)
  choose Kwin hKwinCpt hKwinSub hplaceWin using hwinex
  have hcutex : ∀ i, ∃ χ : ℝ × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ Set.univ ×ˢ (extChartAt I (p i)).target ∧
      (∀ᶠ r in 𝓝ˢ (Kwin i), χ r = 1) ∧ ∀ r, χ r ∈ Set.Icc (0 : ℝ) 1 := fun i =>
    exists_contDiff_cutoff_one_nhdsSet_of_isCompact (hKwinCpt i)
      (isOpen_univ.prod (isOpen_extChartAt_target (I := I) (p i))) (hKwinSub i)
  choose χ hχC0 hχc hsub hcut _hIcc using hcutex
  exact exists_flow_Ioo_forall_contMDiff_of_field_jets_finite_cover_windowLip
    (N := ∞) (cw := -1) (dw := 1) (p := p) (U := U) (Q_M := Q_M) (χ := χ) (Kwin := Kwin)
    (state₀ := fun i => Metric.ball (extChartAt I (p i) (p i)) (ρ i)) (K := K)
    hXraw ⟨by norm_num, by norm_num⟩ hopen hcover hXchart
    (fun i => hχC0 i) hχc hsub hcut (by decide)
    (fun i => Metric.isOpen_ball) hK hU hUQ hQ_M hQ_M_src hplace hplaceWin

/-- **Globalising joint `(t, x)`-smoothness from spatial neighbourhoods.**  A map on `ℝ × M` is
`ContMDiff` as soon as, around every point `x : M`, there is an open set `s ∋ x` on which the map is
`ContMDiffOn` over the time-full slab `Set.univ ×ˢ s`.  This is the pure-locality glue that turns the
per-chart joint smoothness produced by the field-raising capstone
(`ParametrizedInner.contMDiffOn_timeDependentRaisedSection`) into the *global* `hXfield` hypothesis of
the compact-`M` gauge-flow assembly `exists_flow_Ioo_forall_contMDiff_of_contMDiff_tangentSection_compact`. -/
theorem contMDiff_of_locally_contMDiffOn_univ_prod
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F H' N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
    {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]
    {n : WithTop ℕ∞} {f : ℝ × M → N}
    (h : ∀ x : M, ∃ s : Set M, IsOpen s ∧ x ∈ s ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) J n f (Set.univ ×ˢ s)) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) J n f := by
  rintro ⟨t, x⟩
  obtain ⟨s, hs, hx, hcont⟩ := h x
  exact hcont.contMDiffAt ((isOpen_univ.prod hs).mem_nhds (Set.mk_mem_prod (Set.mem_univ t) hx))

/-- **Compact-`M` gauge flow from spatially-local joint smoothness of the gauge field.**  A
convenience form of `exists_flow_Ioo_forall_contMDiff_of_contMDiff_tangentSection_compact` that accepts
the gauge-field jet in the *local* form produced by the per-chart raising capstone: joint `C^∞`
smoothness of the tangent-bundle section `(τ, y) ↦ ⟨y, X τ y⟩` on `Set.univ ×ˢ s` for some open `s`
around every point.  The spatial neighbourhoods are glued to the global `hXfield` via
`contMDiff_of_locally_contMDiffOn_univ_prod`, then fed to the field-independent assembly, yielding the
anchored gauge flow with `ContMDiff I I 3` time slices on an open window around `0`. -/
theorem exists_flow_Ioo_forall_contMDiff_of_locally_contMDiffOn_tangentSection_compact
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    [BoundarylessManifold I M] [CompactSpace M] [IsManifold I 1 M]
    [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
    {X : ℝ → M → E}
    (hXloc : ∀ x : M, ∃ s : Set M, IsOpen s ∧ x ∈ s ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I.tangent ∞
        (fun p : ℝ × M => (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)) (Set.univ ×ˢ s)) :
    ∃ (Φ : ℝ → M → M) (c d : ℝ), (∀ x, Φ 0 x = x) ∧ (0 : ℝ) ∈ Set.Ioo c d ∧
      ∀ t ∈ Set.Ioo c d, ContMDiff I I 3 (fun x : M => Φ t x) :=
  exists_flow_Ioo_forall_contMDiff_of_contMDiff_tangentSection_compact
    (contMDiff_of_locally_contMDiffOn_univ_prod hXloc)

/-- **Global flow-slice `C³` (Route-A `hslicesC3`) from a per-point family of *cutoff model gauge
flows* + orbit control.**  The concrete-`G` companion of the abstract-`Ψ` Route-A capstone
`GaugeFlowAssembly.contMDiff_flowSlice_of_forall_rawFlow_modelFlow_eqOn`: instead of asking the caller
to supply an abstract model comparison flow `Ψ` together with its `hg'` integral-curve co-solution, this
form consumes, around every base point `x`, a genuine cutoff model gauge flow
`G : Diffeomorph3GaugeFlowOn (χ • chartPushforwardField) sTime t₀'` and the *graph-containment* datum
`hχ` (the cutoff `χ ≡ 1` along the model orbit) — exactly the package produced by the cutoff machinery
`exists_diffeomorph3GaugeFlowOn_cutoff_eqOne_of_isCompact_window`.

The abstract comparison flow is realised as `Ψ := fun τ ↦ (G.maps3 τ : E → E)`; its `hΨ` datum is the
model-slice `C³` bound `contDiff_three_maps3_of_model_diffeomorph3GaugeFlowOn`, and its `hg'`
integral-curve co-solution is `hasDerivAt_maps3_eval_of_cutoff_eqOne` (which collapses the cut field
`χ • chartPushforwardField` to the un-cut `chartPushforwardField` on the region where `χ ≡ 1`, supplied
by `hχ`).  The raw-flow ODE (`hγ`), chart-source stay (`hγ_src`), tube memberships (`hγ_mem`/`hg_mem`),
tube-Lipschitz control (`hlip`), and anchor agreement (`heq₀`) are threaded through unchanged, and the
`hΦU` `MapsTo` face is discharged from `hγ_src` at time `t` via `extChartAt_source`.  Feeding the
resulting per-point abstract package to the Route-A global gluer yields `ContMDiff I I 3 (Φ t)` — the
Route-A `hslicesC3` datum — directly from cutoff-model-flow data, no spatial regularity of `Φ`
assumed. -/
theorem contMDiff_flowSlice_of_forall_cutoff_orbit_control
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {X : ℝ → M → E} {Φ : ℝ → M → M} {t : ℝ}
    (h : ∀ x : M, ∃ (p : M) (χ : ℝ × E → ℝ) (sTime : Set ℝ) (t₀' : ℝ)
        (G : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E)
          (X := fun τ q => χ (τ, q) •
            PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ q) sTime t₀')
        (a b t₀ : ℝ) (K : NNReal) (state : ℝ → Set E) (U : Set M),
      U ∈ nhds x ∧ U ⊆ (chartAt H p).source ∧ t ∈ Set.Ioo a b ∧ t₀ ∈ Set.Ioo a b ∧
      (∀ τ ∈ Set.Ioo a b, sTime ∈ 𝓝 τ) ∧
      (∀ τ ∈ Set.Ioo a b, LipschitzOnWith K
        (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ) (state τ)) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
        HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun σ : ℝ => Φ σ y) (Set.Ioo a b) τ
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (Φ τ y)))) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, Φ τ y ∈ (extChartAt I p).source) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, χ (τ, (G.maps3 τ) (extChartAt I p y)) = 1) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, extChartAt I p (Φ τ y) ∈ state τ) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, (G.maps3 τ) (extChartAt I p y) ∈ state τ) ∧
      (∀ y ∈ U, extChartAt I p (Φ t₀ y) = (G.maps3 t₀) (extChartAt I p y))) :
    ContMDiff I I 3 (fun x : M => Φ t x) := by
  refine PoincareCurvature.GaugeFlowAssembly.contMDiff_flowSlice_of_forall_rawFlow_modelFlow_eqOn
    (Φ := Φ) (X := X) (t := t) (fun x => ?_)
  obtain ⟨p, χ, sTime, t₀', G, a, b, t₀, K, state, U, hUmem, hU, ht, ht₀, hnhds, hlip,
    hγ, hγ_src, hχ, hγ_mem, hg_mem, heq₀⟩ := h x
  refine ⟨p, fun τ => (G.maps3 τ : E → E), a, b, t₀, K, state, U, hUmem, hU,
    contDiff_three_maps3_of_model_diffeomorph3GaugeFlowOn G t, ?_, ht, ht₀, hlip,
    hγ, hγ_src, ?_, hγ_mem, hg_mem, heq₀⟩
  · intro y hy
    have hsrc := hγ_src y hy t ht
    rwa [extChartAt_source] at hsrc
  · intro y hy τ hτ
    exact hasDerivAt_maps3_eval_of_cutoff_eqOne G (hnhds τ hτ)
      (mem_of_mem_nhds (hnhds τ hτ)) (extChartAt I p y) (hχ y hy τ hτ)

/-- **Route-A `hslicesC3` from per-point cutoff model gauge flows, consuming the cutoff's *native*
`𝓝ˢ`-eventually datum + orbit-graph confinement.**  The graph-form companion of
`contMDiff_flowSlice_of_forall_cutoff_orbit_control`: instead of the pre-digested pointwise
`hχ : χ (τ, (G.maps3 τ) (extChartAt I p y)) = 1`, it consumes the two facts the cutoff machinery
`exists_diffeomorph3GaugeFlowOn_cutoff_eqOne_of_isCompact_window` actually produces — the raw
neighbourhood-of-a-compact-window cutoff datum `∀ᶠ r in 𝓝ˢ Kwin, χ r = 1`, and the geometric
orbit-graph confinement `(τ, (G.maps3 τ) (extChartAt I p y)) ∈ Kwin` — reducing them to the pointwise
`hχ` via `cutoff_eqOne_along_curve_of_graph_subset` (`Filter.Eventually.self_of_nhdsSet`).  This isolates
the remaining GAP-1 step-(v) content to the single flow-trajectory-confinement estimate
`orbit-graph ⊆ Kwin` (dischargeable, uniformly over a chart patch, by
`exists_Ioo_forall_forall_graph_mem_of_isCompact_of_continuousAt`), the honest interface between the
cutoff-window machinery and the Route-A slice-`C³` gluer. -/
theorem contMDiff_flowSlice_of_forall_cutoff_orbit_control_of_graph_subset
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {X : ℝ → M → E} {Φ : ℝ → M → M} {t : ℝ}
    (h : ∀ x : M, ∃ (p : M) (χ : ℝ × E → ℝ) (sTime : Set ℝ) (t₀' : ℝ)
        (G : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E)
          (X := fun τ q => χ (τ, q) •
            PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ q) sTime t₀')
        (a b t₀ : ℝ) (K : NNReal) (state : ℝ → Set E) (Kwin : Set (ℝ × E)) (U : Set M),
      U ∈ nhds x ∧ U ⊆ (chartAt H p).source ∧ t ∈ Set.Ioo a b ∧ t₀ ∈ Set.Ioo a b ∧
      (∀ τ ∈ Set.Ioo a b, sTime ∈ 𝓝 τ) ∧
      (∀ᶠ r in 𝓝ˢ Kwin, χ r = 1) ∧
      (∀ τ ∈ Set.Ioo a b, LipschitzOnWith K
        (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ) (state τ)) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
        HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun σ : ℝ => Φ σ y) (Set.Ioo a b) τ
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (Φ τ y)))) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, Φ τ y ∈ (extChartAt I p).source) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
        ((τ, (G.maps3 τ) (extChartAt I p y)) : ℝ × E) ∈ Kwin) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, extChartAt I p (Φ τ y) ∈ state τ) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, (G.maps3 τ) (extChartAt I p y) ∈ state τ) ∧
      (∀ y ∈ U, extChartAt I p (Φ t₀ y) = (G.maps3 t₀) (extChartAt I p y))) :
    ContMDiff I I 3 (fun x : M => Φ t x) := by
  refine contMDiff_flowSlice_of_forall_cutoff_orbit_control (X := X) (Φ := Φ) (t := t) (fun x => ?_)
  obtain ⟨p, χ, sTime, t₀', G, a, b, t₀, K, state, Kwin, U, hUmem, hU, ht, ht₀, hnhds, hχK, hlip,
    hγ, hγ_src, hgraph, hγ_mem, hg_mem, heq₀⟩ := h x
  refine ⟨p, χ, sTime, t₀', G, a, b, t₀, K, state, U, hUmem, hU, ht, ht₀, hnhds, hlip,
    hγ, hγ_src, ?_, hγ_mem, hg_mem, heq₀⟩
  intro y hy
  exact cutoff_eqOne_along_curve_of_graph_subset hχK (hgraph y hy)

/-- **Inverse flow-slice `C³` (Route-A `hslicesC3` backward half) from per-point cutoff model gauge
flows + orbit control.**  The concrete-`G` companion of the abstract-`Ψ` backward capstone
`GaugeFlowAssembly.contMDiff_symm_flowSlice_of_forall_rawFlow_modelFlow_eqOn`, and the inverse-slice
mirror of the forward `contMDiff_flowSlice_of_forall_cutoff_orbit_control`.  For the fixed time `t`, it
produces `ContMDiff I I 3 Gt` for the spatial inverse `Gt` of the compact-flow slice `Φ t` — the
backward half of the Route-A `hslicesC3` obligation — from:

* the topological packaging of `Φ t` as a homeomorphism on the compact `T2` manifold `M`: continuity
  `hΦcont` (supplied in the final assembly by the already-proved forward slice `C³`), surjectivity
  `hΦsurj`, and the global left inverse `hGleft` (`Gt ∘ Φ t = id`); and
* per base point `x`, exactly the same cutoff-model-flow package the forward capstone consumes — a
  genuine cutoff model gauge flow `G : Diffeomorph3GaugeFlowOn (χ • chartPushforwardField) sTime t₀'`
  with the pointwise cutoff datum `χ (τ, (G.maps3 τ) (extChartAt I p y)) = 1`, the raw gauge ODE,
  tube-Lipschitz control, and confinement/anchor facts.

The abstract comparison flow is realised as the genuine `C³`-*diffeomorph* family `Ψ := fun τ ↦ G.maps3 τ`
(so its inverse is `C³` for free); its `hg'` integral-curve co-solution is
`hasDerivAt_maps3_eval_of_cutoff_eqOne` (collapsing `χ • chartPushforwardField ↦ chartPushforwardField`
where `χ ≡ 1`), and the `MapsTo` face falls out of the `src` datum at time `t`.  These feed the abstract
backward capstone, whose homeomorphism gluer discharges the global inverse-slice `C³`.  Paired with the
forward `contMDiff_flowSlice_of_forall_cutoff_orbit_control` this discharges both halves of `hslicesC3`
in cutoff-model-flow vocabulary. -/
theorem contMDiff_symm_flowSlice_of_forall_cutoff_orbit_control
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [CompactSpace M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {X : ℝ → M → E} {Φ : ℝ → M → M} {Gt : M → M} {t : ℝ}
    (hΦcont : Continuous (Φ t))
    (hΦsurj : Function.Surjective (Φ t))
    (hGleft : Function.LeftInverse Gt (Φ t))
    (h : ∀ x : M, ∃ (p : M) (χ : ℝ × E → ℝ) (sTime : Set ℝ) (t₀' : ℝ)
        (G : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E)
          (X := fun τ q => χ (τ, q) •
            PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ q) sTime t₀')
        (a b t₀ : ℝ) (K : NNReal) (state : ℝ → Set E) (U : Set M),
      U ∈ nhds x ∧ U ⊆ (chartAt H p).source ∧ t ∈ Set.Ioo a b ∧ t₀ ∈ Set.Ioo a b ∧
      (∀ τ ∈ Set.Ioo a b, sTime ∈ 𝓝 τ) ∧
      (∀ τ ∈ Set.Ioo a b, LipschitzOnWith K
        (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ) (state τ)) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
        HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun σ : ℝ => Φ σ y) (Set.Ioo a b) τ
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (Φ τ y)))) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, Φ τ y ∈ (extChartAt I p).source) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, χ (τ, (G.maps3 τ) (extChartAt I p y)) = 1) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, extChartAt I p (Φ τ y) ∈ state τ) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, (G.maps3 τ) (extChartAt I p y) ∈ state τ) ∧
      (∀ y ∈ U, extChartAt I p (Φ t₀ y) = (G.maps3 t₀) (extChartAt I p y))) :
    ContMDiff I I 3 Gt := by
  refine PoincareCurvature.GaugeFlowAssembly.contMDiff_symm_flowSlice_of_forall_rawFlow_modelFlow_eqOn
    (Φ := Φ) (Gt := Gt) (X := X) (t := t) hΦcont hΦsurj hGleft (fun x => ?_)
  obtain ⟨p, χ, sTime, t₀', G, a, b, t₀, K, state, U, hUmem, hU, ht, ht₀, hnhds, hlip,
    hγ, hγ_src, hχ, hγ_mem, hg_mem, heq₀⟩ := h x
  refine ⟨p, fun τ => G.maps3 τ, a, b, t₀, K, state, U, hUmem, hU, ?_, ht, ht₀, hlip,
    hγ, hγ_src, ?_, hγ_mem, hg_mem, heq₀⟩
  · intro y hy
    have hsrc := hγ_src y hy t ht
    rwa [extChartAt_source] at hsrc
  · intro y hy τ hτ
    exact hasDerivAt_maps3_eval_of_cutoff_eqOne G (hnhds τ hτ)
      (mem_of_mem_nhds (hnhds τ hτ)) (extChartAt I p y) (hχ y hy τ hτ)

/-- **Inverse flow-slice `C³` (Route-A `hslicesC3` backward half), consuming the cutoff's *native*
`𝓝ˢ`-eventually datum + orbit-graph confinement.**  The graph-form companion of
`contMDiff_symm_flowSlice_of_forall_cutoff_orbit_control`, and the inverse-slice mirror of the forward
`contMDiff_flowSlice_of_forall_cutoff_orbit_control_of_graph_subset`.  Instead of the pre-digested
pointwise `hχ : χ (τ, (G.maps3 τ) (extChartAt I p y)) = 1`, it consumes the two facts the cutoff
machinery `exists_diffeomorph3GaugeFlowOn_cutoff_eqOne_of_isCompact_window` actually produces — the raw
neighbourhood-of-a-compact-window cutoff datum `∀ᶠ r in 𝓝ˢ Kwin, χ r = 1` and the geometric orbit-graph
confinement `(τ, (G.maps3 τ) (extChartAt I p y)) ∈ Kwin` — reducing them to the pointwise `hχ` via
`cutoff_eqOne_along_curve_of_graph_subset`, then delegating to the backward capstone
`contMDiff_symm_flowSlice_of_forall_cutoff_orbit_control`.  With the forward graph-form capstone this is
the cutoff-machinery-native interface for both halves of `hslicesC3`: the remaining GAP-1 content is
isolated to the single flow-trajectory-confinement estimate `orbit-graph ⊆ Kwin` plus the homeomorphism
inputs (`Continuous`/`Surjective`/left-inverse of `Φ t`) that the compact `T2` forward slice supplies. -/
theorem contMDiff_symm_flowSlice_of_forall_cutoff_orbit_control_of_graph_subset
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [CompactSpace M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {X : ℝ → M → E} {Φ : ℝ → M → M} {Gt : M → M} {t : ℝ}
    (hΦcont : Continuous (Φ t))
    (hΦsurj : Function.Surjective (Φ t))
    (hGleft : Function.LeftInverse Gt (Φ t))
    (h : ∀ x : M, ∃ (p : M) (χ : ℝ × E → ℝ) (sTime : Set ℝ) (t₀' : ℝ)
        (G : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E)
          (X := fun τ q => χ (τ, q) •
            PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ q) sTime t₀')
        (a b t₀ : ℝ) (K : NNReal) (state : ℝ → Set E) (Kwin : Set (ℝ × E)) (U : Set M),
      U ∈ nhds x ∧ U ⊆ (chartAt H p).source ∧ t ∈ Set.Ioo a b ∧ t₀ ∈ Set.Ioo a b ∧
      (∀ τ ∈ Set.Ioo a b, sTime ∈ 𝓝 τ) ∧
      (∀ᶠ r in 𝓝ˢ Kwin, χ r = 1) ∧
      (∀ τ ∈ Set.Ioo a b, LipschitzOnWith K
        (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ) (state τ)) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
        HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun σ : ℝ => Φ σ y) (Set.Ioo a b) τ
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (Φ τ y)))) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, Φ τ y ∈ (extChartAt I p).source) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
        ((τ, (G.maps3 τ) (extChartAt I p y)) : ℝ × E) ∈ Kwin) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, extChartAt I p (Φ τ y) ∈ state τ) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, (G.maps3 τ) (extChartAt I p y) ∈ state τ) ∧
      (∀ y ∈ U, extChartAt I p (Φ t₀ y) = (G.maps3 t₀) (extChartAt I p y))) :
    ContMDiff I I 3 Gt := by
  refine contMDiff_symm_flowSlice_of_forall_cutoff_orbit_control
    (X := X) (Φ := Φ) (Gt := Gt) (t := t) hΦcont hΦsurj hGleft (fun x => ?_)
  obtain ⟨p, χ, sTime, t₀', G, a, b, t₀, K, state, Kwin, U, hUmem, hU, ht, ht₀, hnhds, hχK, hlip,
    hγ, hγ_src, hgraph, hγ_mem, hg_mem, heq₀⟩ := h x
  refine ⟨p, χ, sTime, t₀', G, a, b, t₀, K, state, U, hUmem, hU, ht, ht₀, hnhds, hlip,
    hγ, hγ_src, ?_, hγ_mem, hg_mem, heq₀⟩
  intro y hy
  exact cutoff_eqOne_along_curve_of_graph_subset hχK (hgraph y hy)

/-- **Both slices `C³` (full Route-A `hslicesC3` conclusion, fixed time) from one per-point cutoff
model gauge flow family.**  The concrete-`G` capstone of capstones: for the fixed time `t`, it produces
the exact `ContMDiff I I 3 (Φ t) ∧ ContMDiff I I 3 Gt` shape of the `hslicesC3` conclusion of
`GaugeFlowAssembly.exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3`, from *one* uniform
per-base-point supply of cutoff-model-flow comparison packages (the native cutoff-machinery output —
cutoff `G`, `∀ᶠ 𝓝ˢ` datum, orbit-graph confinement, raw gauge ODE, tube-Lipschitz, anchor) together
with only the forward slice's spatial-inverse data `hΦsurj` (`Φ t` surjective) and `hGleft`
(`Gt ∘ Φ t = id`).

The forward conjunct is `contMDiff_flowSlice_of_forall_cutoff_orbit_control_of_graph_subset`; the
inverse conjunct reuses that forward `C³` as the *continuity* input
(`ContMDiff.continuous`) — so `Continuous (Φ t)` is *derived*, not assumed — and passes the same
package (plus `hΦsurj`/`hGleft`) to
`contMDiff_symm_flowSlice_of_forall_cutoff_orbit_control_of_graph_subset`.  Quantifying `t` over the
flow window discharges both conjuncts of `hslicesC3` from a single supply of comparison packages, the
compact-`T2` homeomorphism obligation of the backward half being absorbed into the already-proved
forward half. -/
theorem contMDiff_flowSlice_and_symm_of_forall_cutoff_orbit_control_of_graph_subset
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [CompactSpace M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {X : ℝ → M → E} {Φ : ℝ → M → M} {Gt : M → M} {t : ℝ}
    (hΦsurj : Function.Surjective (Φ t))
    (hGleft : Function.LeftInverse Gt (Φ t))
    (h : ∀ x : M, ∃ (p : M) (χ : ℝ × E → ℝ) (sTime : Set ℝ) (t₀' : ℝ)
        (G : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E)
          (X := fun τ q => χ (τ, q) •
            PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ q) sTime t₀')
        (a b t₀ : ℝ) (K : NNReal) (state : ℝ → Set E) (Kwin : Set (ℝ × E)) (U : Set M),
      U ∈ nhds x ∧ U ⊆ (chartAt H p).source ∧ t ∈ Set.Ioo a b ∧ t₀ ∈ Set.Ioo a b ∧
      (∀ τ ∈ Set.Ioo a b, sTime ∈ 𝓝 τ) ∧
      (∀ᶠ r in 𝓝ˢ Kwin, χ r = 1) ∧
      (∀ τ ∈ Set.Ioo a b, LipschitzOnWith K
        (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ) (state τ)) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
        HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun σ : ℝ => Φ σ y) (Set.Ioo a b) τ
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (Φ τ y)))) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, Φ τ y ∈ (extChartAt I p).source) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b,
        ((τ, (G.maps3 τ) (extChartAt I p y)) : ℝ × E) ∈ Kwin) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, extChartAt I p (Φ τ y) ∈ state τ) ∧
      (∀ y ∈ U, ∀ τ ∈ Set.Ioo a b, (G.maps3 τ) (extChartAt I p y) ∈ state τ) ∧
      (∀ y ∈ U, extChartAt I p (Φ t₀ y) = (G.maps3 t₀) (extChartAt I p y))) :
    ContMDiff I I 3 (Φ t) ∧ ContMDiff I I 3 Gt := by
  have hfwd : ContMDiff I I 3 (Φ t) :=
    contMDiff_flowSlice_of_forall_cutoff_orbit_control_of_graph_subset (X := X) (Φ := Φ) (t := t) h
  exact ⟨hfwd, contMDiff_symm_flowSlice_of_forall_cutoff_orbit_control_of_graph_subset
    (X := X) (Φ := Φ) (Gt := Gt) (t := t) hfwd.continuous hΦsurj hGleft h⟩

/-- **Windowed backward per-patch inverse-slice `C³` producer.**  The inverse-slice (`G t`) analogue of
`contMDiffOn_flowSlice_perPatch_of_flow`: a direct quantification over the time window of the fixed-time
backward per-patch brick `GaugeFlowAssembly.contMDiffOn_symm_flowSlice_of_rawFlow_modelFlow_eqOn`.  Every
one of that brick's comparison hypotheses is already uniform in `τ ∈ Set.Ioo a b` — a model-`C³`
comparison flow `Ψ`, the tube-Lipschitz chart pushforward field, the raw gauge ODE, the model
co-solution `hg'`, the state placements, and the anchor identity at `t₀` — while only the conclusion time
and the spatial left inverse `G t` are time-specific.  Quantifying `t` over `Set.Ioo a b` (which contains
`0`) therefore delivers, on that single window, the per-patch inverse regularity
`ContMDiffOn I I 3 (G t) (Φ t '' U)` for every `t`.  This is exactly the per-patch datum
`exists_Ioo_forall_contMDiff_symm_of_finite_cover` consumes as its `hpatch i`, so the two together
globalise the inverse slice from local temporal integral-curve comparison data — the backward-side
mirror of `contMDiffOn_flowSlice_perPatch_of_flow` + `exists_Ioo_forall_contMDiff_of_finite_cover`. -/
theorem contMDiffOn_symm_flowSlice_perPatch_of_flow
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {Φ : ℝ → M → M} {G : ℝ → M → M}
    {Ψ : ℝ → (E ≃ₘ^3⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E)}
    {p : M} {X : ℝ → M → E} {a b t₀ : ℝ} {K : NNReal} {state : ℝ → Set E} {U : Set M}
    (hab0 : (0 : ℝ) ∈ Set.Ioo a b) (ht₀ : t₀ ∈ Set.Ioo a b)
    (hU : U ⊆ (chartAt H p).source)
    (hΦU : ∀ t ∈ Set.Ioo a b, Set.MapsTo (Φ t) U (chartAt H p).source)
    (hlip : ∀ τ ∈ Set.Ioo a b, LipschitzOnWith K
      (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ) (state τ))
    (hraw : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b,
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ : ℝ ↦ Φ τ x) (Set.Ioo a b) τ
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (Φ τ x))))
    (hsrc : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b, Φ τ x ∈ (extChartAt I p).source)
    (hg' : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b,
      HasDerivAt (fun τ : ℝ ↦ (Ψ τ : E → E) (extChartAt I p x))
        (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ
          ((Ψ τ : E → E) (extChartAt I p x))) τ)
    (hγ_mem : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b, extChartAt I p (Φ τ x) ∈ state τ)
    (hg_mem : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b, (Ψ τ : E → E) (extChartAt I p x) ∈ state τ)
    (heq₀ : ∀ x ∈ U, extChartAt I p (Φ t₀ x) = (Ψ t₀ : E → E) (extChartAt I p x))
    (hGleft : ∀ t ∈ Set.Ioo a b, ∀ x ∈ U, G t (Φ t x) = x) :
    ∃ a' b' : ℝ, (0 : ℝ) ∈ Set.Ioo a' b' ∧
      ∀ t ∈ Set.Ioo a' b', ContMDiffOn I I 3 (G t) (Φ t '' U) := by
  refine ⟨a, b, hab0, fun t ht => ?_⟩
  exact PoincareCurvature.GaugeFlowAssembly.contMDiffOn_symm_flowSlice_of_rawFlow_modelFlow_eqOn
    hU (hΦU t ht) ht ht₀ hlip hraw hsrc hg' hγ_mem hg_mem heq₀ (hGleft t ht)

/-- **Backward finite-cover gluer for inverse flow slices (windowed).**  The inverse-slice (`G t`)
analogue of `exists_Ioo_forall_contMDiff_of_finite_cover`: from a finite open cover `U : ι → Set M` of
the compact `T2` manifold `M`, per-patch inverse-slice regularity windows (`hpatch`: on each patch a
window `Set.Ioo (a i) (b i) ∋ 0` with `ContMDiffOn I I 3 (G t)` on the image `Φ t '' U i` for every `t`
in that window), and the per-slice topological data on a reference window `Set.Ioo lo hi ∋ 0` (each
`Φ t` continuous, surjective, with global left inverse `G t`), there is a single sub-window
`Set.Ioo c d ∋ 0` on which `G t` is *globally* `ContMDiff I I 3`.

This is the backward half of the `hslicesC3` conclusion
(`∃ c d, 0 ∈ Set.Ioo c d ∧ ∀ t ∈ Set.Ioo c d, ContMDiff I I 3 (G t)`) consumed by
`GaugeFlowAssembly.exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowAsymSubwindowSlicesC3`.  Unlike
the forward gluer, the inverse slice is globalised through the open-map route: on a compact `T2`
manifold a continuous bijective `Φ t` is a homeomorphism (`Continuous.homeoOfEquivCompactToT2`), hence an
open map, so the per-patch inverse regularity on `Φ t '' U i` glues to global `C³` via
`GaugeFlowAssembly.contMDiff_symm_flowSlice_of_forall_openImage`.  The reference window `Set.Ioo lo hi`
carries the topological data (in the asymmetric-capstone application it is the mutual-inverse window
`Set.Ioo (-ε) ε`); the returned sub-window is contained in `Set.Ioo lo hi ∩ ⋂ i, Set.Ioo (a i) (b i)`. -/
theorem exists_Ioo_forall_contMDiff_symm_of_finite_cover
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [CompactSpace M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {ι : Type*} [Finite ι] {Φ : ℝ → M → M} {G : ℝ → M → M} {U : ι → Set M}
    {lo hi : ℝ} (hlohi : (0 : ℝ) ∈ Set.Ioo lo hi)
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (hΦcont : ∀ t ∈ Set.Ioo lo hi, Continuous (Φ t))
    (hΦsurj : ∀ t ∈ Set.Ioo lo hi, Function.Surjective (Φ t))
    (hGleft : ∀ t ∈ Set.Ioo lo hi, Function.LeftInverse (G t) (Φ t))
    (hpatch : ∀ i : ι, ∃ a b : ℝ, (0 : ℝ) ∈ Set.Ioo a b ∧
      ∀ t ∈ Set.Ioo a b, ContMDiffOn I I 3 (G t) (Φ t '' U i)) :
    ∃ c d : ℝ, (0 : ℝ) ∈ Set.Ioo c d ∧
      ∀ t ∈ Set.Ioo c d, ContMDiff I I 3 (G t) := by
  choose a b hmem hslice using hpatch
  have hWopen : IsOpen (Set.Ioo lo hi ∩ ⋂ i, Set.Ioo (a i) (b i)) :=
    isOpen_Ioo.inter (isOpen_iInter_of_finite (fun i => isOpen_Ioo))
  have hW0 : (0 : ℝ) ∈ Set.Ioo lo hi ∩ ⋂ i, Set.Ioo (a i) (b i) :=
    ⟨hlohi, Set.mem_iInter.mpr (fun i => hmem i)⟩
  obtain ⟨c, d, hcd, hsubW⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hWopen.mem_nhds hW0)
  refine ⟨c, d, hcd, fun t ht => ?_⟩
  have htW : t ∈ Set.Ioo lo hi ∩ ⋂ i, Set.Ioo (a i) (b i) := hsubW ht
  have htlohi : t ∈ Set.Ioo lo hi := htW.1
  have htIoo : ∀ i, t ∈ Set.Ioo (a i) (b i) :=
    fun i => Set.mem_iInter.mp htW.2 i
  have hbij : Function.Bijective (Φ t) :=
    ⟨(hGleft t htlohi).injective, hΦsurj t htlohi⟩
  have hopenMap : IsOpenMap (Φ t) :=
    (Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective (Φ t) hbij)
      (hΦcont t htlohi)).isOpenMap
  refine PoincareCurvature.GaugeFlowAssembly.contMDiff_symm_flowSlice_of_forall_openImage
    hopenMap (hΦsurj t htlohi) (fun x => ?_)
  obtain ⟨i, hxi⟩ := hcover x
  exact ⟨U i, hopen i, hxi, hslice i t (htIoo i)⟩

/-- **Global inverse-slice `C³` producer from per-patch model-comparison data (for a given flow).**  The
backward-slice (`G t`) analogue of the forward finite-cover producer
`exists_flow_Ioo_forall_contMDiff_of_field_jets_finite_cover_windowLip_of_flow`: it composes the two
backward bricks — the windowed per-patch inverse producer `contMDiffOn_symm_flowSlice_perPatch_of_flow`
(applied on each patch `i` of a finite open cover, from that patch's integral-curve comparison data: a
model-`C³` self-diffeomorph family `Ψ i`, the tube-Lipschitz chart pushforward field, the raw gauge ODE,
the model co-solution `hg'`, the state placements, and the anchor identity at `t₀ i`) and the backward
finite-cover gluer `exists_Ioo_forall_contMDiff_symm_of_finite_cover` (which, on a compact `T2` `M` where
each continuous bijective `Φ t` is an open map, globalises the per-patch inverse regularity on `Φ t '' U i`
to global `ContMDiff I I 3 (G t)`).  The reference window `Set.Ioo lo hi` carries the per-slice
topological data (each `Φ t` continuous, surjective, with global left inverse `G t`).

This delivers the backward conjunct `∃ c d, 0 ∈ Set.Ioo c d ∧ ∀ t ∈ Set.Ioo c d, ContMDiff I I 3 (G t)`
of the `hslicesC3` hypothesis consumed by
`GaugeFlowAssembly.exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowAsymSubwindowSlicesC3`, mirroring
on the inverse side what the field-jet finite-cover producer delivers for the forward slice — no window
bookkeeping beyond intersecting the per-patch windows with the reference window is required of the caller. -/
theorem exists_Ioo_forall_contMDiff_symm_of_comparison_finite_cover_of_flow
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [CompactSpace M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {ι : Type*} [Finite ι] {Φ : ℝ → M → M} {G : ℝ → M → M}
    {Ψ : ι → ℝ → (E ≃ₘ^3⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E)}
    {p : ι → M} {X : ℝ → M → E} {a b t₀ : ι → ℝ} {K : ι → NNReal}
    {state : ι → ℝ → Set E} {U : ι → Set M} {lo hi : ℝ}
    (hlohi : (0 : ℝ) ∈ Set.Ioo lo hi)
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (hΦcont : ∀ t ∈ Set.Ioo lo hi, Continuous (Φ t))
    (hΦsurj : ∀ t ∈ Set.Ioo lo hi, Function.Surjective (Φ t))
    (hGleft : ∀ t ∈ Set.Ioo lo hi, Function.LeftInverse (G t) (Φ t))
    (hab0 : ∀ i, (0 : ℝ) ∈ Set.Ioo (a i) (b i)) (ht₀ : ∀ i, t₀ i ∈ Set.Ioo (a i) (b i))
    (hU : ∀ i, U i ⊆ (chartAt H (p i)).source)
    (hΦU : ∀ i, ∀ t ∈ Set.Ioo (a i) (b i), Set.MapsTo (Φ t) (U i) (chartAt H (p i)).source)
    (hlip : ∀ i, ∀ τ ∈ Set.Ioo (a i) (b i), LipschitzOnWith (K i)
      (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X (p i) τ) (state i τ))
    (hraw : ∀ i, ∀ x ∈ U i, ∀ τ ∈ Set.Ioo (a i) (b i),
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ : ℝ ↦ Φ τ x) (Set.Ioo (a i) (b i)) τ
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (Φ τ x))))
    (hsrc : ∀ i, ∀ x ∈ U i, ∀ τ ∈ Set.Ioo (a i) (b i), Φ τ x ∈ (extChartAt I (p i)).source)
    (hg' : ∀ i, ∀ x ∈ U i, ∀ τ ∈ Set.Ioo (a i) (b i),
      HasDerivAt (fun τ : ℝ ↦ (Ψ i τ : E → E) (extChartAt I (p i) x))
        (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X (p i) τ
          ((Ψ i τ : E → E) (extChartAt I (p i) x))) τ)
    (hγ_mem : ∀ i, ∀ x ∈ U i, ∀ τ ∈ Set.Ioo (a i) (b i),
      extChartAt I (p i) (Φ τ x) ∈ state i τ)
    (hg_mem : ∀ i, ∀ x ∈ U i, ∀ τ ∈ Set.Ioo (a i) (b i),
      (Ψ i τ : E → E) (extChartAt I (p i) x) ∈ state i τ)
    (heq₀ : ∀ i, ∀ x ∈ U i,
      extChartAt I (p i) (Φ (t₀ i) x) = (Ψ i (t₀ i) : E → E) (extChartAt I (p i) x))
    (hGleft_patch : ∀ i, ∀ t ∈ Set.Ioo (a i) (b i), ∀ x ∈ U i, G t (Φ t x) = x) :
    ∃ c d : ℝ, (0 : ℝ) ∈ Set.Ioo c d ∧
      ∀ t ∈ Set.Ioo c d, ContMDiff I I 3 (G t) :=
  exists_Ioo_forall_contMDiff_symm_of_finite_cover hlohi hopen hcover hΦcont hΦsurj hGleft
    (fun i => contMDiffOn_symm_flowSlice_perPatch_of_flow (hab0 i) (ht₀ i) (hU i) (hΦU i)
      (hlip i) (hraw i) (hsrc i) (hg' i) (hγ_mem i) (hg_mem i) (heq₀ i) (hGleft_patch i))

/-- **Windowed forward per-patch flow-slice `C³` producer (diffeomorph comparison).**  The forward-slice
(`Φ t`) analogue of `contMDiffOn_symm_flowSlice_perPatch_of_flow`: a direct quantification over the time
window of the fixed-time forward per-patch brick
`GaugeFlowAssembly.contMDiffOn_flowSlice_of_rawFlow_modelFlow_eqOn`, with the model comparison flow given
as a genuine `C³` self-diffeomorph family `Ψ : ℝ → (E ≃ₘ^3 E)` (whose forward map's `C³` regularity is
extracted from `(Ψ t).contMDiff`).  Every comparison hypothesis is uniform in `τ ∈ Set.Ioo a b`; only the
conclusion time is `t`-specific, so quantifying `t` over `Set.Ioo a b` (∋ `0`) yields
`ContMDiffOn I I 3 (Φ t) U` for every `t` in that window — the per-patch datum
`exists_Ioo_forall_contMDiff_of_finite_cover` consumes as its `hpatch i`.  This consumes the SAME
diffeomorph comparison package as the backward `contMDiffOn_symm_flowSlice_perPatch_of_flow` (minus the
left-inverse datum), so ONE per-patch supply feeds both slices. -/
theorem contMDiffOn_flowSlice_perPatch_of_flow_comparison
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {Φ : ℝ → M → M} {Ψ : ℝ → (E ≃ₘ^3⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E)}
    {p : M} {X : ℝ → M → E} {a b t₀ : ℝ} {K : NNReal} {state : ℝ → Set E} {U : Set M}
    (hab0 : (0 : ℝ) ∈ Set.Ioo a b) (ht₀ : t₀ ∈ Set.Ioo a b)
    (hU : U ⊆ (chartAt H p).source)
    (hΦU : ∀ t ∈ Set.Ioo a b, Set.MapsTo (Φ t) U (chartAt H p).source)
    (hlip : ∀ τ ∈ Set.Ioo a b, LipschitzOnWith K
      (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ) (state τ))
    (hraw : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b,
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ : ℝ ↦ Φ τ x) (Set.Ioo a b) τ
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (Φ τ x))))
    (hsrc : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b, Φ τ x ∈ (extChartAt I p).source)
    (hg' : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b,
      HasDerivAt (fun τ : ℝ ↦ (Ψ τ : E → E) (extChartAt I p x))
        (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ
          ((Ψ τ : E → E) (extChartAt I p x))) τ)
    (hγ_mem : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b, extChartAt I p (Φ τ x) ∈ state τ)
    (hg_mem : ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b, (Ψ τ : E → E) (extChartAt I p x) ∈ state τ)
    (heq₀ : ∀ x ∈ U, extChartAt I p (Φ t₀ x) = (Ψ t₀ : E → E) (extChartAt I p x)) :
    ∃ a' b' : ℝ, (0 : ℝ) ∈ Set.Ioo a' b' ∧
      ∀ t ∈ Set.Ioo a' b', ContMDiffOn I I 3 (Φ t) U := by
  refine ⟨a, b, hab0, fun t ht => ?_⟩
  exact PoincareCurvature.GaugeFlowAssembly.contMDiffOn_flowSlice_of_rawFlow_modelFlow_eqOn
    (Ψ := fun τ => (Ψ τ : E → E)) hU (contMDiff_iff_contDiff.mp (Ψ t).contMDiff)
    (hΦU t ht) ht ht₀ hlip hraw hsrc hg' hγ_mem hg_mem heq₀

/-- **Global forward-slice `C³` producer from per-patch diffeomorph comparison data (for a given flow).**
The forward-slice (`Φ t`) analogue of
`exists_Ioo_forall_contMDiff_symm_of_comparison_finite_cover_of_flow`: composes the windowed forward
per-patch producer `contMDiffOn_flowSlice_perPatch_of_flow_comparison` on each patch `i` of a finite open
cover with the forward finite-cover gluer `exists_Ioo_forall_contMDiff_of_finite_cover` (which glues the
per-patch `ContMDiffOn (Φ t) (U i)` to global `ContMDiff I I 3 (Φ t)` via
`contMDiff_of_locally_contMDiffOn`).  Unlike the backward producer it needs NO reference-window
topological data (no continuity/surjectivity/left-inverse of `Φ t`).  Delivers the forward conjunct
`∃ c d, 0 ∈ Set.Ioo c d ∧ ∀ t ∈ Set.Ioo c d, ContMDiff I I 3 (Φ t)` of the `hslicesC3` hypothesis, from
the SAME per-patch diffeomorph comparison supply the backward producer consumes. -/
theorem exists_Ioo_forall_contMDiff_of_comparison_finite_cover_of_flow
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {ι : Type*} [Finite ι] {Φ : ℝ → M → M}
    {Ψ : ι → ℝ → (E ≃ₘ^3⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E)}
    {p : ι → M} {X : ℝ → M → E} {a b t₀ : ι → ℝ} {K : ι → NNReal}
    {state : ι → ℝ → Set E} {U : ι → Set M}
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (hab0 : ∀ i, (0 : ℝ) ∈ Set.Ioo (a i) (b i)) (ht₀ : ∀ i, t₀ i ∈ Set.Ioo (a i) (b i))
    (hU : ∀ i, U i ⊆ (chartAt H (p i)).source)
    (hΦU : ∀ i, ∀ t ∈ Set.Ioo (a i) (b i), Set.MapsTo (Φ t) (U i) (chartAt H (p i)).source)
    (hlip : ∀ i, ∀ τ ∈ Set.Ioo (a i) (b i), LipschitzOnWith (K i)
      (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X (p i) τ) (state i τ))
    (hraw : ∀ i, ∀ x ∈ U i, ∀ τ ∈ Set.Ioo (a i) (b i),
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ : ℝ ↦ Φ τ x) (Set.Ioo (a i) (b i)) τ
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (Φ τ x))))
    (hsrc : ∀ i, ∀ x ∈ U i, ∀ τ ∈ Set.Ioo (a i) (b i), Φ τ x ∈ (extChartAt I (p i)).source)
    (hg' : ∀ i, ∀ x ∈ U i, ∀ τ ∈ Set.Ioo (a i) (b i),
      HasDerivAt (fun τ : ℝ ↦ (Ψ i τ : E → E) (extChartAt I (p i) x))
        (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X (p i) τ
          ((Ψ i τ : E → E) (extChartAt I (p i) x))) τ)
    (hγ_mem : ∀ i, ∀ x ∈ U i, ∀ τ ∈ Set.Ioo (a i) (b i),
      extChartAt I (p i) (Φ τ x) ∈ state i τ)
    (hg_mem : ∀ i, ∀ x ∈ U i, ∀ τ ∈ Set.Ioo (a i) (b i),
      (Ψ i τ : E → E) (extChartAt I (p i) x) ∈ state i τ)
    (heq₀ : ∀ i, ∀ x ∈ U i,
      extChartAt I (p i) (Φ (t₀ i) x) = (Ψ i (t₀ i) : E → E) (extChartAt I (p i) x)) :
    ∃ c d : ℝ, (0 : ℝ) ∈ Set.Ioo c d ∧
      ∀ t ∈ Set.Ioo c d, ContMDiff I I 3 (Φ t) :=
  exists_Ioo_forall_contMDiff_of_finite_cover hopen hcover
    (fun i => contMDiffOn_flowSlice_perPatch_of_flow_comparison (hab0 i) (ht₀ i) (hU i) (hΦU i)
      (hlip i) (hraw i) (hsrc i) (hg' i) (hγ_mem i) (hg_mem i) (heq₀ i))

/-- **Paired global slice-`C³` producer (both `hslicesC3` conjuncts from one diffeomorph comparison
supply).**  Combines the forward global producer
`exists_Ioo_forall_contMDiff_of_comparison_finite_cover_of_flow` and the backward global producer
`exists_Ioo_forall_contMDiff_symm_of_comparison_finite_cover_of_flow` into the exact conjunction
`(∃ c₁ d₁, ∀ t ∈ …, ContMDiff (Φ t)) ∧ (∃ c₂ d₂, ∀ t ∈ …, ContMDiff (G t))` concluded by the `hslicesC3`
hypothesis of `GaugeFlowAssembly.exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowAsymSubwindowSlicesC3`.
Because the forward and backward per-patch bricks consume IDENTICAL diffeomorph comparison data (`Ψ i`,
the raw gauge ODE, the tube-Lipschitz control, the model co-solution, the state placements, the anchor),
ONE uniform per-patch supply — plus the reference-window topological data (each `Φ t`
continuous/surjective with global left inverse `G t`) that only the inverse slice needs — discharges BOTH
slice-`C³` conjuncts.  This is the direct precursor to discharging `hslicesC3`: only the construction of
the per-patch comparison packages from the actual gauge field remains. -/
theorem exists_flowSlicesC3Pair_of_comparison_finite_cover_of_flow
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [CompactSpace M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {ι : Type*} [Finite ι] {Φ : ℝ → M → M} {G : ℝ → M → M}
    {Ψ : ι → ℝ → (E ≃ₘ^3⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E)}
    {p : ι → M} {X : ℝ → M → E} {a b t₀ : ι → ℝ} {K : ι → NNReal}
    {state : ι → ℝ → Set E} {U : ι → Set M} {lo hi : ℝ}
    (hlohi : (0 : ℝ) ∈ Set.Ioo lo hi)
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (hΦcont : ∀ t ∈ Set.Ioo lo hi, Continuous (Φ t))
    (hΦsurj : ∀ t ∈ Set.Ioo lo hi, Function.Surjective (Φ t))
    (hGleft : ∀ t ∈ Set.Ioo lo hi, Function.LeftInverse (G t) (Φ t))
    (hab0 : ∀ i, (0 : ℝ) ∈ Set.Ioo (a i) (b i)) (ht₀ : ∀ i, t₀ i ∈ Set.Ioo (a i) (b i))
    (hU : ∀ i, U i ⊆ (chartAt H (p i)).source)
    (hΦU : ∀ i, ∀ t ∈ Set.Ioo (a i) (b i), Set.MapsTo (Φ t) (U i) (chartAt H (p i)).source)
    (hlip : ∀ i, ∀ τ ∈ Set.Ioo (a i) (b i), LipschitzOnWith (K i)
      (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X (p i) τ) (state i τ))
    (hraw : ∀ i, ∀ x ∈ U i, ∀ τ ∈ Set.Ioo (a i) (b i),
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ : ℝ ↦ Φ τ x) (Set.Ioo (a i) (b i)) τ
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (Φ τ x))))
    (hsrc : ∀ i, ∀ x ∈ U i, ∀ τ ∈ Set.Ioo (a i) (b i), Φ τ x ∈ (extChartAt I (p i)).source)
    (hg' : ∀ i, ∀ x ∈ U i, ∀ τ ∈ Set.Ioo (a i) (b i),
      HasDerivAt (fun τ : ℝ ↦ (Ψ i τ : E → E) (extChartAt I (p i) x))
        (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X (p i) τ
          ((Ψ i τ : E → E) (extChartAt I (p i) x))) τ)
    (hγ_mem : ∀ i, ∀ x ∈ U i, ∀ τ ∈ Set.Ioo (a i) (b i),
      extChartAt I (p i) (Φ τ x) ∈ state i τ)
    (hg_mem : ∀ i, ∀ x ∈ U i, ∀ τ ∈ Set.Ioo (a i) (b i),
      (Ψ i τ : E → E) (extChartAt I (p i) x) ∈ state i τ)
    (heq₀ : ∀ i, ∀ x ∈ U i,
      extChartAt I (p i) (Φ (t₀ i) x) = (Ψ i (t₀ i) : E → E) (extChartAt I (p i) x))
    (hGleft_patch : ∀ i, ∀ t ∈ Set.Ioo (a i) (b i), ∀ x ∈ U i, G t (Φ t x) = x) :
    (∃ c₁ d₁ : ℝ, (0 : ℝ) ∈ Set.Ioo c₁ d₁ ∧ ∀ t ∈ Set.Ioo c₁ d₁, ContMDiff I I 3 (Φ t)) ∧
      (∃ c₂ d₂ : ℝ, (0 : ℝ) ∈ Set.Ioo c₂ d₂ ∧ ∀ t ∈ Set.Ioo c₂ d₂, ContMDiff I I 3 (G t)) :=
  ⟨exists_Ioo_forall_contMDiff_of_comparison_finite_cover_of_flow hopen hcover hab0 ht₀ hU hΦU
      hlip hraw hsrc hg' hγ_mem hg_mem heq₀,
    exists_Ioo_forall_contMDiff_symm_of_comparison_finite_cover_of_flow hlohi hopen hcover
      hΦcont hΦsurj hGleft hab0 ht₀ hU hΦU hlip hraw hsrc hg' hγ_mem hg_mem heq₀ hGleft_patch⟩

/-- **Paired global slice-`C³` producer with the inverse-slice continuity BOOTSTRAPPED from the forward
slice.**  Same as `exists_flowSlicesC3Pair_of_comparison_finite_cover_of_flow` but it does NOT take the
per-slice continuity `hΦcont : ∀ t ∈ …, Continuous (Φ t)` as a hypothesis — it DERIVES it from the forward
producer's output (`ContMDiff I I 3 (Φ t) ⟹ Continuous (Φ t)` via `ContMDiff.continuous`).  Concretely:
the forward global producer supplies a window `Set.Ioo c₁ d₁ ∋ 0` on which every `Φ t` is `C³`; the
reference window handed to the backward producer is shrunk to
`Set.Ioo (max lo c₁) (min hi d₁) ⊆ Set.Ioo lo hi ∩ Set.Ioo c₁ d₁`, on which the surjectivity/left-inverse
data restrict from `Set.Ioo lo hi` and the continuity is read off from the forward `C³`.

The upshot: the ONLY topological inputs are the slice surjectivity `hΦsurj` and left inverse `hGleft` —
exactly the `hright` (⟹ surjective) and `hleft` faces the `hslicesC3` hypothesis of
`GaugeFlowAssembly.exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowAsymSubwindowSlicesC3` supplies
for an arbitrary flow pair `(Φ, G)`.  So discharging that `hslicesC3` from this producer needs only the
per-patch diffeomorph comparison packages — no separately-argued per-slice continuity. -/
theorem exists_flowSlicesC3Pair_of_comparison_finite_cover_of_flow_of_surj_left
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [CompactSpace M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {ι : Type*} [Finite ι] {Φ : ℝ → M → M} {G : ℝ → M → M}
    {Ψ : ι → ℝ → (E ≃ₘ^3⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E)}
    {p : ι → M} {X : ℝ → M → E} {a b t₀ : ι → ℝ} {K : ι → NNReal}
    {state : ι → ℝ → Set E} {U : ι → Set M} {lo hi : ℝ}
    (hlohi : (0 : ℝ) ∈ Set.Ioo lo hi)
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : M, ∃ i, x ∈ U i)
    (hΦsurj : ∀ t ∈ Set.Ioo lo hi, Function.Surjective (Φ t))
    (hGleft : ∀ t ∈ Set.Ioo lo hi, Function.LeftInverse (G t) (Φ t))
    (hab0 : ∀ i, (0 : ℝ) ∈ Set.Ioo (a i) (b i)) (ht₀ : ∀ i, t₀ i ∈ Set.Ioo (a i) (b i))
    (hU : ∀ i, U i ⊆ (chartAt H (p i)).source)
    (hΦU : ∀ i, ∀ t ∈ Set.Ioo (a i) (b i), Set.MapsTo (Φ t) (U i) (chartAt H (p i)).source)
    (hlip : ∀ i, ∀ τ ∈ Set.Ioo (a i) (b i), LipschitzOnWith (K i)
      (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X (p i) τ) (state i τ))
    (hraw : ∀ i, ∀ x ∈ U i, ∀ τ ∈ Set.Ioo (a i) (b i),
      HasMFDerivWithinAt (𝓘(ℝ, ℝ)) I (fun τ : ℝ ↦ Φ τ x) (Set.Ioo (a i) (b i)) τ
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X τ (Φ τ x))))
    (hsrc : ∀ i, ∀ x ∈ U i, ∀ τ ∈ Set.Ioo (a i) (b i), Φ τ x ∈ (extChartAt I (p i)).source)
    (hg' : ∀ i, ∀ x ∈ U i, ∀ τ ∈ Set.Ioo (a i) (b i),
      HasDerivAt (fun τ : ℝ ↦ (Ψ i τ : E → E) (extChartAt I (p i) x))
        (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X (p i) τ
          ((Ψ i τ : E → E) (extChartAt I (p i) x))) τ)
    (hγ_mem : ∀ i, ∀ x ∈ U i, ∀ τ ∈ Set.Ioo (a i) (b i),
      extChartAt I (p i) (Φ τ x) ∈ state i τ)
    (hg_mem : ∀ i, ∀ x ∈ U i, ∀ τ ∈ Set.Ioo (a i) (b i),
      (Ψ i τ : E → E) (extChartAt I (p i) x) ∈ state i τ)
    (heq₀ : ∀ i, ∀ x ∈ U i,
      extChartAt I (p i) (Φ (t₀ i) x) = (Ψ i (t₀ i) : E → E) (extChartAt I (p i) x))
    (hGleft_patch : ∀ i, ∀ t ∈ Set.Ioo (a i) (b i), ∀ x ∈ U i, G t (Φ t x) = x) :
    (∃ c₁ d₁ : ℝ, (0 : ℝ) ∈ Set.Ioo c₁ d₁ ∧ ∀ t ∈ Set.Ioo c₁ d₁, ContMDiff I I 3 (Φ t)) ∧
      (∃ c₂ d₂ : ℝ, (0 : ℝ) ∈ Set.Ioo c₂ d₂ ∧ ∀ t ∈ Set.Ioo c₂ d₂, ContMDiff I I 3 (G t)) := by
  have hfwd := exists_Ioo_forall_contMDiff_of_comparison_finite_cover_of_flow
    hopen hcover hab0 ht₀ hU hΦU hlip hraw hsrc hg' hγ_mem hg_mem heq₀
  refine ⟨hfwd, ?_⟩
  obtain ⟨c₁, d₁, ⟨hc₁, hd₁⟩, hΦC3⟩ := hfwd
  obtain ⟨hlo, hhi⟩ := hlohi
  have hsub_lo : Set.Ioo (max lo c₁) (min hi d₁) ⊆ Set.Ioo lo hi :=
    Set.Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)
  have hsub_c : Set.Ioo (max lo c₁) (min hi d₁) ⊆ Set.Ioo c₁ d₁ :=
    Set.Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)
  have h0 : (0 : ℝ) ∈ Set.Ioo (max lo c₁) (min hi d₁) := ⟨max_lt hlo hc₁, lt_min hhi hd₁⟩
  exact exists_Ioo_forall_contMDiff_symm_of_comparison_finite_cover_of_flow
    h0 hopen hcover
    (fun t ht => (hΦC3 t (hsub_c ht)).continuous)
    (fun t ht => hΦsurj t (hsub_lo ht))
    (fun t ht => hGleft t (hsub_lo ht))
    hab0 ht₀ hU hΦU hlip hraw hsrc hg' hγ_mem hg_mem heq₀ hGleft_patch

/-- **Windowed co-solution supply — the model `G.maps3`-orbit solves the *un-cut* chart pushforward ODE,
uniformly over a chart patch, from graph confinement in the cutoff window.**  This discharges the
distinctive co-solution hypothesis `hg'` of the Ψ-comparison producers
(`contMDiffOn_flowSlice_perPatch_of_flow_comparison` and its `_symm` twin, with `Ψ := G.maps3`) directly
from the confinement machinery.  For the model cutoff gauge flow `G` (of the cut field
`χ • chartPushforwardField I X p` over all time, anchored at `t₀`) with the cut field uniformly Lipschitz,
a compact initial set `Q` carrying every chart image `extChartAt I p x` (`x ∈ U`), and a compact
space-time window `Kwin` with `χ ≡ 1` near it and the anchored graph in its interior, the short-time
orbit-graph confinement `exists_Ioo_forall_forall_graph_maps3_mem_of_lipschitzWith` (applied to
`interior Kwin`) yields a window `Set.Ioo a b ∋ t₀` on which every orbit graph stays in `Kwin`;
`cutoff_eqOne_along_curve_of_graph_subset` then gives `χ ≡ 1` along each orbit, so
`hasDerivAt_maps3_eval_of_cutoff_eqOne` upgrades the cut-field integral-curve derivative to the *un-cut*
`chartPushforwardField` — exactly the `hg'` datum, uniformly for all `x ∈ U` and `τ` in the window. -/
theorem exists_Ioo_forall_forall_hasDerivAt_maps3_eval_of_lipschitzWith
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
    {X : ℝ → M → E} {p : M} {χ : ℝ × E → ℝ} {t₀ : ℝ} {K : ℝ≥0}
    {Q : Set E} {Kwin : Set (ℝ × E)} {U : Set M}
    (G : RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E)
      (X := fun τ q => χ (τ, q) •
        PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ q) Set.univ t₀)
    (hlipX : ∀ t, LipschitzWith K (fun q => χ (t, q) •
        PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p t q))
    (hQ : IsCompact Q)
    (hχ1 : ∀ᶠ r in 𝓝ˢ Kwin, χ r = 1)
    (hgraph0 : ∀ q ∈ Q, ((t₀, (G.maps3 t₀) q) : ℝ × E) ∈ interior Kwin)
    (hUQ : ∀ x ∈ U, extChartAt I p x ∈ Q) :
    ∃ a b : ℝ, t₀ ∈ Set.Ioo a b ∧
      ∀ x ∈ U, ∀ τ ∈ Set.Ioo a b,
        HasDerivAt (fun τ : ℝ => (G.maps3 τ) (extChartAt I p x))
          (PoincareCurvature.GaugeFlowAssembly.chartPushforwardField I X p τ
            ((G.maps3 τ) (extChartAt I p x))) τ := by
  obtain ⟨a, b, ht₀ab, hgraph⟩ :=
    exists_Ioo_forall_forall_graph_maps3_mem_of_lipschitzWith G hlipX hQ isOpen_interior hgraph0
  refine ⟨a, b, ht₀ab, fun x hx τ hτ => ?_⟩
  have hmemK : ∀ σ ∈ Set.Ioo a b, ((σ, (G.maps3 σ) (extChartAt I p x)) : ℝ × E) ∈ Kwin :=
    fun σ hσ => interior_subset (hgraph σ hσ (extChartAt I p x) (hUQ x hx))
  have hχτ : χ (τ, (G.maps3 τ) (extChartAt I p x)) = 1 :=
    cutoff_eqOne_along_curve_of_graph_subset hχ1 hmemK τ hτ
  exact hasDerivAt_maps3_eval_of_cutoff_eqOne G Filter.univ_mem (Set.mem_univ τ)
    (extChartAt I p x) hχτ

end

end SmoothDependenceCk
end AnalyticPDE
end RicciFlow
