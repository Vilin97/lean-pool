/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothDependenceManifold

/-!
# Field-jet extraction from a jointly-`ContDiff` time-dependent field (roadmap point 4, Item 2)

The Banach → manifold smooth-dependence tower (`AnalyticPDE/SmoothDependenceCk`,
`AnalyticPDE/FlowDiffeomorphism`, `AnalyticPDE/SmoothDependenceManifold`,
`AnalyticPDE/ModelManifoldGaugeFlow`) drives the `C³` gauge flow of Item 2 from a **field jet**:
the spatial Fréchet derivatives `Dv`, `D²v`, `D³v` of the time-dependent field `v : ℝ → E → E`,
supplied as separate objects with pointwise `HasFDerivAt`, joint `(t, x)`-continuity, and global
Lipschitz bounds.

Those jet hypotheses are stated abstractly so the tower is agnostic to how the derivatives arise.
This module supplies the honest bridge from a *single* clean smoothness hypothesis — `v` jointly
`ContDiff` in `(time, space)` (`ContDiff ℝ n (Function.uncurry v)`) — to the **first jet layer**:

* `contDiff_apply_of_contDiff_uncurry` — each time slice `v s` is spatially `ContDiff ℝ n`;
* `hasFDerivAt_fderiv_of_contDiff_uncurry` — the spatial derivative object `fderiv ℝ (v s)` is a
  genuine Fréchet derivative of `v s` at every point (`1 ≤ n`);
* `continuous_fderiv_of_contDiff_uncurry` — the spatial derivative is jointly continuous in `(t, x)`,
  via the partial-derivative identity `fderiv ℝ (v t) x = fderiv ℝ (uncurry v) (t, x) ∘L inr`.

Together these produce exactly the `hDv`/`hDvc` inputs of the tower's flow theorems (`Dv := fun s ↦
fderiv ℝ (v s)`).  No new analytic content: a transport of Mathlib's `ContDiff` calculus into the
jet shape the smooth-dependence tower consumes.
-/

open Set Filter Topology
open scoped Topology NNReal Manifold ContDiff

@[expose] public section

namespace RicciFlow
namespace AnalyticPDE
namespace SmoothDependenceCk

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {v : ℝ → E → E} {n : WithTop ℕ∞}

/-- Each time slice `v s` of a jointly-`ContDiff` field is spatially `ContDiff ℝ n`, obtained by
precomposing `Function.uncurry v` with the affine inclusion `x ↦ (s, x)`. -/
theorem contDiff_apply_of_contDiff_uncurry
    (h : ContDiff ℝ n (Function.uncurry v)) (s : ℝ) :
    ContDiff ℝ n (v s) := by
  have hcomp : ContDiff ℝ n (Function.uncurry v ∘ fun x : E => (s, x)) :=
    h.comp (contDiff_prodMk_right s)
  have heq : (Function.uncurry v ∘ fun x : E => (s, x)) = v s := by funext x; rfl
  rwa [heq] at hcomp

/-- The spatial derivative object `fderiv ℝ (v s)` is a genuine Fréchet derivative of the time slice
`v s` at every point, for a jointly-`ContDiff` field with `1 ≤ n`.  This is the `hDv` input of the
smooth-dependence tower with `Dv := fun s ↦ fderiv ℝ (v s)`. -/
theorem hasFDerivAt_fderiv_of_contDiff_uncurry
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 1 ≤ n) (s : ℝ) (ξ : E) :
    HasFDerivAt (v s) (fderiv ℝ (v s) ξ) ξ :=
  (((contDiff_apply_of_contDiff_uncurry h s).differentiable
    ((lt_of_lt_of_le zero_lt_one hn).ne')).differentiableAt).hasFDerivAt

/-- **Joint `(t, x)`-continuity of the spatial derivative** of a jointly-`ContDiff` field
(`1 ≤ n`).  The partial spatial derivative equals the full joint derivative postcomposed with the
inclusion `inr : E →L[ℝ] ℝ × E`, `fderiv ℝ (v t) x = fderiv ℝ (Function.uncurry v) (t, x) ∘L inr`,
and both `p ↦ fderiv ℝ (uncurry v) p` and right-composition with the fixed `inr` are continuous.
This is the `hDvc` input of the smooth-dependence tower. -/
theorem continuous_fderiv_of_contDiff_uncurry
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 1 ≤ n) :
    Continuous (fun p : ℝ × E => fderiv ℝ (v p.1) p.2) := by
  have hne : n ≠ 0 := (lt_of_lt_of_le zero_lt_one hn).ne'
  have key : (fun p : ℝ × E => fderiv ℝ (v p.1) p.2)
      = fun p : ℝ × E =>
        (fderiv ℝ (Function.uncurry v) p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    funext p
    have h1 : HasFDerivAt (Function.uncurry v) (fderiv ℝ (Function.uncurry v) p) p :=
      ((h.differentiable hne).differentiableAt).hasFDerivAt
    have h2 : HasFDerivAt (fun x : E => (p.1, x)) (ContinuousLinearMap.inr ℝ ℝ E) p.2 :=
      hasFDerivAt_prodMk_right p.1 p.2
    have hc : HasFDerivAt (v p.1)
        ((fderiv ℝ (Function.uncurry v) p).comp (ContinuousLinearMap.inr ℝ ℝ E)) p.2 := by
      have hcomp := h1.comp p.2 h2
      have heq : (Function.uncurry v ∘ fun x : E => (p.1, x)) = v p.1 := by funext x; rfl
      rwa [heq] at hcomp
    exact hc.fderiv
  rw [key]
  exact (h.continuous_fderiv hne).clm_comp continuous_const

/-- **Global Lipschitz bound on the spatial derivative from a second-derivative bound.**  If `v` is
jointly `ContDiff ℝ n` with `2 ≤ n` and the second spatial derivative `fderiv ℝ (fderiv ℝ (v s))` is
globally bounded in operator norm by `L`, then the spatial derivative object `fderiv ℝ (v s)` is
`L`-Lipschitz.  This is the `hDvlip` input of the smooth-dependence tower, obtained from the
mean-value bound `lipschitzWith_of_nnnorm_fderiv_le` together with differentiability of the derivative
(`ContDiff.fderiv_right`). -/
theorem lipschitzWith_fderiv_of_contDiff_of_nnnorm_secondFDeriv_le
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 2 ≤ n)
    {L : ℝ≥0} (hL : ∀ s ξ, ‖fderiv ℝ (fderiv ℝ (v s)) ξ‖₊ ≤ L) (s : ℝ) :
    LipschitzWith L (fderiv ℝ (v s)) := by
  have hvs : ContDiff ℝ n (v s) := contDiff_apply_of_contDiff_uncurry h s
  have hmn : (1 : WithTop ℕ∞) + 1 ≤ n := le_trans (by norm_num) hn
  have hdiff : Differentiable ℝ (fderiv ℝ (v s)) :=
    (hvs.fderiv_right (m := 1) hmn).differentiable one_ne_zero
  exact lipschitzWith_of_nnnorm_fderiv_le hdiff (hL s)

/-- **Manifold spatial `C¹` regularity of the flow from a genuine `ContDiff` field.**  Packaging the
field-jet extraction with the tower's `C^{1,1}` manifold regularity theorem
`contMDiff_one_flow_apply_of_lipschitz_deriv`: for a jointly-`ContDiff ℝ n` field `v` (`2 ≤ n`) that
is spatially `K`-Lipschitz and time-continuous, with a globally bounded second spatial derivative, any
integral-curve flow family `Φ` of `v` anchored at `t₀` has each time-`t` map `z ↦ Φ z t` in
`ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1`.  The field-jet hypotheses `hDv`/`hDvc`/`hDvlip` are supplied here from
the single `ContDiff` hypothesis via `hasFDerivAt_fderiv_of_contDiff_uncurry`,
`continuous_fderiv_of_contDiff_uncurry`, and
`lipschitzWith_fderiv_of_contDiff_of_nnnorm_secondFDeriv_le`; this is the first flow-regularity
statement in the tower stated purely in terms of joint `ContDiff` of the field. -/
theorem contMDiff_one_flow_apply_of_contDiff [CompleteSpace E]
    {K L : ℝ≥0} {t₀ : ℝ} {Φ : E → ℝ → E}
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 2 ≤ n)
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    (hL : ∀ s ξ, ‖fderiv ℝ (fderiv ℝ (v s)) ξ‖₊ ≤ L)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z) (t : ℝ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (fun z => Φ z t) := by
  have hn1 : (1 : WithTop ℕ∞) ≤ n := le_trans (by norm_num) hn
  exact contMDiff_one_flow_apply_of_lipschitz_deriv (Dv := fun s => fderiv ℝ (v s))
    hv hvc
    (fun s ξ => hasFDerivAt_fderiv_of_contDiff_uncurry h hn1 s ξ)
    (continuous_fderiv_of_contDiff_uncurry h hn1)
    (fun s => lipschitzWith_fderiv_of_contDiff_of_nnnorm_secondFDeriv_le h hn hL s)
    hΦ h0 t

/-- **Spatial Lipschitz bound of the field from a first-derivative bound.**  If `v` is jointly
`ContDiff ℝ n` with `1 ≤ n` and the spatial derivative `fderiv ℝ (v s)` is globally bounded in
operator norm by `K`, then each time slice `v s` is `K`-Lipschitz.  Supplies the `hv` input from a
derivative bound (via `lipschitzWith_of_nnnorm_fderiv_le`). -/
theorem lipschitzWith_apply_of_contDiff_of_nnnorm_fderiv_le
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 1 ≤ n)
    {K : ℝ≥0} (hK : ∀ s ξ, ‖fderiv ℝ (v s) ξ‖₊ ≤ K) (s : ℝ) :
    LipschitzWith K (v s) := by
  have hdiff : Differentiable ℝ (v s) :=
    (contDiff_apply_of_contDiff_uncurry h s).differentiable ((lt_of_lt_of_le zero_lt_one hn).ne')
  exact lipschitzWith_of_nnnorm_fderiv_le hdiff (hK s)

/-- **Time-continuity of the field slice** from joint `ContDiff`: for each `x`, `s ↦ v s x` is
continuous, since it is `Function.uncurry v` (continuous) precomposed with `s ↦ (s, x)`.  Supplies the
`hvc` input. -/
theorem continuous_apply_of_contDiff_uncurry
    (h : ContDiff ℝ n (Function.uncurry v)) (x : E) :
    Continuous (fun s : ℝ => v s x) := by
  have heq : (fun s : ℝ => v s x) = Function.uncurry v ∘ fun s : ℝ => (s, x) := by
    funext s; rfl
  rw [heq]
  exact h.continuous.comp (continuous_id.prodMk continuous_const)

/-- **Manifold spatial `C¹` regularity of the flow from joint `ContDiff` and derivative bounds
alone.**  The fully self-contained form of `contMDiff_one_flow_apply_of_contDiff`: from `v` jointly
`ContDiff ℝ n` (`2 ≤ n`) with globally bounded first and second spatial derivatives (bounds `K`, `L`),
plus an integral-curve flow family `Φ` anchored at `t₀`, each time-`t` map `z ↦ Φ z t` is
`ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1`.  The spatial Lipschitz and time-continuity inputs are here also
discharged from the `ContDiff` hypothesis (`lipschitzWith_apply_of_contDiff_of_nnnorm_fderiv_le`,
`continuous_apply_of_contDiff_uncurry`), so the field is described by a single smoothness hypothesis
and two derivative bounds. -/
theorem contMDiff_one_flow_apply_of_contDiff_of_bddDerivs [CompleteSpace E]
    {K L : ℝ≥0} {t₀ : ℝ} {Φ : E → ℝ → E}
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 2 ≤ n)
    (hK : ∀ s ξ, ‖fderiv ℝ (v s) ξ‖₊ ≤ K)
    (hL : ∀ s ξ, ‖fderiv ℝ (fderiv ℝ (v s)) ξ‖₊ ≤ L)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z) (t : ℝ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (fun z => Φ z t) := by
  have hn1 : (1 : WithTop ℕ∞) ≤ n := le_trans (by norm_num) hn
  exact contMDiff_one_flow_apply_of_contDiff h hn
    (fun τ => lipschitzWith_apply_of_contDiff_of_nnnorm_fderiv_le h hn1 hK τ)
    (fun x => continuous_apply_of_contDiff_uncurry h x)
    hL hΦ h0 t

/-! ## Layer-2 field-jet extraction (`C²` flow regularity from a single `ContDiff` hypothesis)

The layer-1 lemmas above fix the field codomain as `E`.  To iterate the jet extraction one derivative
order higher we re-apply them to the derivative field `fun s ↦ fderiv ℝ (v s) : ℝ → E → (E →L[ℝ] E)`,
whose codomain is `E →L[ℝ] E`, not `E`.  So we first record codomain-general (`'`) forms of the two
layer-1 building blocks, then assemble the second-jet inputs `hD2v`/`hD2vc`/`hD2vlip` of the tower's
`C²` flow theorem `contMDiff_two_flow_apply_of_lipschitz_secondDeriv` from a single joint-`ContDiff`
hypothesis plus global spatial second/third-derivative bounds. -/

/-- **Codomain-general joint `(t, x)`-continuity of the spatial derivative.**  The codomain-general
form of `continuous_fderiv_of_contDiff_uncurry`: for a jointly-`ContDiff ℝ n` field `w : ℝ → E → F`
(`1 ≤ n`) the spatial derivative `fderiv ℝ (w t) x` is jointly continuous, via the partial-derivative
identity `fderiv ℝ (w t) x = fderiv ℝ (uncurry w) (t, x) ∘L inr`.  This enables iterating the field-jet
extraction to the next derivative order (the derivative field takes values in `E →L[ℝ] E`, not `E`). -/
theorem continuous_fderiv_of_contDiff_uncurry' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {w : ℝ → E → F} (h : ContDiff ℝ n (Function.uncurry w)) (hn : 1 ≤ n) :
    Continuous (fun p : ℝ × E => fderiv ℝ (w p.1) p.2) := by
  have hne : n ≠ 0 := (lt_of_lt_of_le zero_lt_one hn).ne'
  have key : (fun p : ℝ × E => fderiv ℝ (w p.1) p.2)
      = fun p : ℝ × E =>
        (fderiv ℝ (Function.uncurry w) p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    funext p
    have h1 : HasFDerivAt (Function.uncurry w) (fderiv ℝ (Function.uncurry w) p) p :=
      ((h.differentiable hne).differentiableAt).hasFDerivAt
    have h2 : HasFDerivAt (fun x : E => (p.1, x)) (ContinuousLinearMap.inr ℝ ℝ E) p.2 :=
      hasFDerivAt_prodMk_right p.1 p.2
    have hc : HasFDerivAt (w p.1)
        ((fderiv ℝ (Function.uncurry w) p).comp (ContinuousLinearMap.inr ℝ ℝ E)) p.2 := by
      have hcomp := h1.comp p.2 h2
      have heq : (Function.uncurry w ∘ fun x : E => (p.1, x)) = w p.1 := by funext x; rfl
      rwa [heq] at hcomp
    exact hc.fderiv
  rw [key]
  exact (h.continuous_fderiv hne).clm_comp continuous_const

/-- **The layer-1 spatial-derivative field of a jointly-`ContDiff` field is itself jointly `ContDiff`
one order lower.**  If `w : ℝ → E → F` has `ContDiff ℝ n (uncurry w)` and `m + 1 ≤ n`, then
`uncurry (fun s ↦ fderiv ℝ (w s))` is `ContDiff ℝ m`, because it equals `fderiv ℝ (uncurry w)`
post-composed with the fixed inclusion `inr` (a bounded linear, hence `ContDiff`, map).  This is the
inductive step that lets the field-jet extraction recurse: apply the layer-1 lemmas to the derivative
field `fderiv ℝ (w ·)` to obtain the layer-2 jet. -/
theorem contDiff_uncurry_fderiv_of_contDiff_uncurry' {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {w : ℝ → E → F} {m : WithTop ℕ∞}
    (h : ContDiff ℝ n (Function.uncurry w)) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (Function.uncurry (fun s => fderiv ℝ (w s))) := by
  have hn1 : (1 : WithTop ℕ∞) ≤ n := le_trans (self_le_add_left 1 m) hmn
  have hne : n ≠ 0 := (lt_of_lt_of_le zero_lt_one hn1).ne'
  have key : Function.uncurry (fun s => fderiv ℝ (w s))
      = fun p : ℝ × E =>
        (fderiv ℝ (Function.uncurry w) p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    funext p
    have h1 : HasFDerivAt (Function.uncurry w) (fderiv ℝ (Function.uncurry w) p) p :=
      ((h.differentiable hne).differentiableAt).hasFDerivAt
    have h2 : HasFDerivAt (fun x : E => (p.1, x)) (ContinuousLinearMap.inr ℝ ℝ E) p.2 :=
      hasFDerivAt_prodMk_right p.1 p.2
    have hc : HasFDerivAt (w p.1)
        ((fderiv ℝ (Function.uncurry w) p).comp (ContinuousLinearMap.inr ℝ ℝ E)) p.2 := by
      have hcomp := h1.comp p.2 h2
      have heq : (Function.uncurry w ∘ fun x : E => (p.1, x)) = w p.1 := by funext x; rfl
      rwa [heq] at hcomp
    exact hc.fderiv
  rw [key]
  exact ContDiff.clm_comp (h.fderiv_right hmn) contDiff_const

/-- **Second spatial derivative exists as a genuine Fréchet derivative** (`2 ≤ n`).  The first spatial
derivative `fderiv ℝ (v s)` is itself `ContDiff ℝ 1`, hence differentiable, so `fderiv ℝ (fderiv ℝ
(v s)) ξ` is a genuine Fréchet derivative of `fderiv ℝ (v s)` at every point.  This is the `hD2v` input
of the tower's `C²` flow theorem `contMDiff_two_flow_apply_of_lipschitz_secondDeriv`. -/
theorem hasFDerivAt_fderiv_fderiv_of_contDiff_uncurry
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 2 ≤ n) (s : ℝ) (ξ : E) :
    HasFDerivAt (fderiv ℝ (v s)) (fderiv ℝ (fderiv ℝ (v s)) ξ) ξ := by
  have hvs : ContDiff ℝ n (v s) := contDiff_apply_of_contDiff_uncurry h s
  have hmn : (1 : WithTop ℕ∞) + 1 ≤ n := le_trans (by norm_num) hn
  have hdiff : Differentiable ℝ (fderiv ℝ (v s)) :=
    (hvs.fderiv_right (m := 1) hmn).differentiable one_ne_zero
  exact (hdiff ξ).hasFDerivAt

/-- **Joint `(t, x)`-continuity of the second spatial derivative** (`2 ≤ n`), obtained by applying the
codomain-general layer-1 continuity lemma `continuous_fderiv_of_contDiff_uncurry'` to the layer-1
derivative field `fderiv ℝ (v ·)`, which is itself jointly `ContDiff ℝ 1` by
`contDiff_uncurry_fderiv_of_contDiff_uncurry'`.  This is the `hD2vc` input of the tower's `C²` flow
theorem. -/
theorem continuous_fderiv_fderiv_of_contDiff_uncurry
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 2 ≤ n) :
    Continuous (fun p : ℝ × E => fderiv ℝ (fderiv ℝ (v p.1)) p.2) := by
  have hV : ContDiff ℝ (1 : WithTop ℕ∞) (Function.uncurry (fun s => fderiv ℝ (v s))) :=
    contDiff_uncurry_fderiv_of_contDiff_uncurry' h (le_trans (by norm_num) hn)
  exact continuous_fderiv_of_contDiff_uncurry' hV le_rfl

/-- **Manifold spatial `C²` regularity of the flow from a genuine `ContDiff` field.**  Packaging the
layer-1 + layer-2 field-jet extraction with the tower's `C^{2,1}` manifold regularity theorem
`contMDiff_two_flow_apply_of_lipschitz_secondDeriv`: for a jointly-`ContDiff ℝ n` field `v` (`2 ≤ n`)
that is spatially `K`-Lipschitz and time-continuous, with a globally bounded second spatial derivative
(bound `L`) and an `M`-Lipschitz second spatial-derivative field, any integral-curve flow family `Φ`
anchored at `t₀` has each time-`t` map `z ↦ Φ z t` in `ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 2`.  The layer-1 jet
inputs `hDv`/`hDvc`/`hDvlip` and the second-jet inputs `hD2v`/`hD2vc` are supplied here from the single
`ContDiff` hypothesis; the top-order Lipschitz control `hD2vlip` is supplied directly (matching the
tower's own `C²` theorem), so no third-order derivative object is required.  This is the second
flow-regularity statement in the tower stated in terms of joint `ContDiff` of the field. -/
theorem contMDiff_two_flow_apply_of_contDiff [CompleteSpace E]
    {K L M : ℝ≥0} {t₀ : ℝ} {Φ : E → ℝ → E}
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 2 ≤ n)
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    (hL : ∀ s ξ, ‖fderiv ℝ (fderiv ℝ (v s)) ξ‖₊ ≤ L)
    (hD2vlip : ∀ s, LipschitzWith M (fderiv ℝ (fderiv ℝ (v s))))
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z) (t : ℝ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 2 (fun z => Φ z t) := by
  have hn1 : (1 : WithTop ℕ∞) ≤ n := le_trans (by norm_num) hn
  exact contMDiff_two_flow_apply_of_lipschitz_secondDeriv
    (Dv := fun s => fderiv ℝ (v s)) (D2v := fun s => fderiv ℝ (fderiv ℝ (v s)))
    hv hvc
    (fun s ξ => hasFDerivAt_fderiv_of_contDiff_uncurry h hn1 s ξ)
    (continuous_fderiv_of_contDiff_uncurry h hn1)
    (fun s => lipschitzWith_fderiv_of_contDiff_of_nnnorm_secondFDeriv_le h hn hL s)
    (fun s ξ => hasFDerivAt_fderiv_fderiv_of_contDiff_uncurry h hn s ξ)
    (continuous_fderiv_fderiv_of_contDiff_uncurry h hn)
    hD2vlip
    hΦ h0 t

/-- **Manifold spatial `C²` regularity of the flow from joint `ContDiff` and a first-derivative bound.**
The convenience form of `contMDiff_two_flow_apply_of_contDiff` that discharges the spatial Lipschitz
(`hv`) and time-continuity (`hvc`) inputs from the `ContDiff` hypothesis together with a global
first-derivative bound (`hK`), matching the layer-1 `contMDiff_one_flow_apply_of_contDiff_of_bddDerivs`
API: from `v` jointly `ContDiff ℝ n` (`2 ≤ n`) with a globally bounded first and second spatial
derivative (bounds `K`, `L`) and an `M`-Lipschitz second spatial-derivative field, each time-`t` flow
map `z ↦ Φ z t` is `ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 2`.  The top-order Lipschitz control `hD2vlip` is
supplied directly, since expressing it as a third-derivative bound would require the multilinear
(rather than iterated-`fderiv`) representation of the third jet. -/
theorem contMDiff_two_flow_apply_of_contDiff_of_bddDerivs [CompleteSpace E]
    {K L M : ℝ≥0} {t₀ : ℝ} {Φ : E → ℝ → E}
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 2 ≤ n)
    (hK : ∀ s ξ, ‖fderiv ℝ (v s) ξ‖₊ ≤ K)
    (hL : ∀ s ξ, ‖fderiv ℝ (fderiv ℝ (v s)) ξ‖₊ ≤ L)
    (hD2vlip : ∀ s, LipschitzWith M (fderiv ℝ (fderiv ℝ (v s))))
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z) (t : ℝ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 2 (fun z => Φ z t) := by
  have hn1 : (1 : WithTop ℕ∞) ≤ n := le_trans (by norm_num) hn
  exact contMDiff_two_flow_apply_of_contDiff h hn
    (fun τ => lipschitzWith_apply_of_contDiff_of_nnnorm_fderiv_le h hn1 hK τ)
    (fun x => continuous_apply_of_contDiff_uncurry h x)
    hL hD2vlip hΦ h0 t

/-! ## Layer-3 multilinear compatibility identities (`hcompat`/`hcurry`)

The tower's `C³` flow theorem `contMDiff_three_flow_apply_of_lipschitz_thirdDeriv` consumes the third
jet in the **multilinear** (`iteratedFDeriv`) representation — the only form in which the third
derivative carries a synthesizable norm — together with two compatibility identities linking that
representation to the nested-`fderiv` second derivative used by the layer-2 forcing engine:

* `hcompat : D2vc s ξ = curry2 (D2vm s ξ)` with `D2vc s = fderiv ℝ (fderiv ℝ (v s))` and
  `D2vm s = iteratedFDeriv ℝ 2 (v s)`;
* `hcurry  : D3vm s ξ = (D3v s ξ).curryLeft` with `D3vm s = fderiv ℝ (iteratedFDeriv ℝ 2 (v s))` and
  `D3v s = iteratedFDeriv ℝ 3 (v s)`.

Both identities hold **unconditionally** (no smoothness hypothesis): the first is the pointwise
`iteratedFDeriv_two_apply` bridged through `curry2_apply`; the second is the definitional
`fderiv_iteratedFDeriv` (`fderiv ℝ (iteratedFDeriv ℝ 2 f) = continuousMultilinearCurryLeftEquiv … ∘
iteratedFDeriv ℝ 3 f`), whose currying equiv is exactly `ContinuousMultilinearMap.curryLeft`. -/

/-- **`hcompat` identity.**  The nested-`fderiv` second derivative `fderiv ℝ (fderiv ℝ f) ξ`, as an
`E →L[ℝ] E →L[ℝ] E`, is the two-fold curry `curry2` of the multilinear second derivative
`iteratedFDeriv ℝ 2 f ξ`.  Holds for every `f : E → E` and `ξ` with no smoothness hypothesis:
`curry2 X a b = X ![a, b]` (`curry2_apply`) and `iteratedFDeriv ℝ 2 f ξ ![a, b] =
fderiv ℝ (fderiv ℝ f) ξ a b` (`iteratedFDeriv_two_apply`).  This is exactly the `hcompat` input of the
tower's `C³` flow theorem (with `f := v s`). -/
theorem fderiv_fderiv_eq_curry2_iteratedFDeriv_two (f : E → E) (ξ : E) :
    fderiv ℝ (fderiv ℝ f) ξ = curry2 (iteratedFDeriv ℝ 2 f ξ) := by
  ext a b
  rw [curry2_apply, iteratedFDeriv_two_apply]
  simp

/-- **`hcurry` identity.**  The Fréchet derivative of the multilinear second derivative
`fderiv ℝ (iteratedFDeriv ℝ 2 f) ξ` — an `E →L[ℝ] (E[×2]→L E)` — is the left-curry
`(iteratedFDeriv ℝ 3 f ξ).curryLeft` of the multilinear third derivative.  Definitional: by
`fderiv_iteratedFDeriv` (`n = 2`) `fderiv ℝ (iteratedFDeriv ℝ 2 f)` is
`continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => E) E ∘ iteratedFDeriv ℝ 3 f`, and that
currying equiv's forward map is `ContinuousMultilinearMap.curryLeft`.  Exactly the `hcurry` input of
the tower's `C³` flow theorem (with `f := v s`). -/
theorem fderiv_iteratedFDeriv_two_eq_curryLeft (f : E → E) (ξ : E) :
    fderiv ℝ (iteratedFDeriv ℝ 2 f) ξ = (iteratedFDeriv ℝ 3 f ξ).curryLeft := by
  ext x m
  rw [fderiv_iteratedFDeriv]
  rfl

/-! ## Layer-3 multilinear field-jet extraction (`iteratedFDeriv` joint `ContDiff` from a single
`ContDiff` hypothesis)

The tower's `C³` flow theorem consumes the second and third derivatives in the multilinear
`iteratedFDeriv` representation, with joint `(t, x)`-continuity.  We supply their joint smoothness by a
single recursion: `uncurry (fun s ↦ iteratedFDeriv ℝ (k+1) (w s))` is the currying isometry applied to
`uncurry (fun s ↦ fderiv ℝ (iteratedFDeriv ℝ k (w s)))` (`iteratedFDeriv_succ_eq_comp_left`), whose
joint `ContDiff` (one order lower) comes from the codomain-general layer-1 recursion
`contDiff_uncurry_fderiv_of_contDiff_uncurry'` applied to the `k`-th jet field.  The base case
`k = 0` is `uncurry w` post-composed with the `Fin 0` currying isometry. -/

/-- **Multilinear field-jet joint `ContDiff` recursion.**  From a single joint-`ContDiff ℝ n` field
`w : ℝ → E → F`, the spatial multilinear jet field `(t, x) ↦ iteratedFDeriv ℝ k (w t) x` is jointly
`ContDiff ℝ m` whenever `m + k ≤ n`.  Proved by induction on `k`: the `succ` step rewrites
`iteratedFDeriv ℝ (k+1) (w s)` as the left-currying isometry of `fderiv ℝ (iteratedFDeriv ℝ k (w s))`
(`iteratedFDeriv_succ_eq_comp_left`) and applies the codomain-general layer-1 derivative-field
recursion `contDiff_uncurry_fderiv_of_contDiff_uncurry'` to the `k`-th jet field. -/
theorem contDiff_uncurry_iteratedFDeriv_of_contDiff_uncurry (k : ℕ) :
    ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {w : ℝ → E → F} {m : WithTop ℕ∞},
      ContDiff ℝ n (Function.uncurry w) → m + (k : WithTop ℕ∞) ≤ n →
      ContDiff ℝ m (Function.uncurry (fun s => iteratedFDeriv ℝ k (w s))) := by
  induction k with
  | zero =>
    intro F _ _ w m hw hmn
    have hcast : m ≤ n := by simpa using hmn
    have heq : (Function.uncurry (fun s => iteratedFDeriv ℝ 0 (w s)))
        = (continuousMultilinearCurryFin0 ℝ E F).symm ∘ Function.uncurry w := by
      funext p
      obtain ⟨s, x⟩ := p
      simp only [Function.comp_apply, Function.uncurry_apply_pair, iteratedFDeriv_zero_eq_comp]
    rw [heq]
    exact (LinearIsometryEquiv.contDiff _).comp (hw.of_le hcast)
  | succ k ih =>
    intro F _ _ w m hw hmn
    have hstep : m + 1 + (k : WithTop ℕ∞) ≤ n := by
      have hk1 : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; ring
      rw [hk1] at hmn
      calc m + 1 + (k : WithTop ℕ∞) = m + ((k : WithTop ℕ∞) + 1) := by
            rw [add_assoc, add_comm (1 : WithTop ℕ∞) (k : WithTop ℕ∞)]
        _ ≤ n := hmn
    have ihk : ContDiff ℝ (m + 1) (Function.uncurry (fun s => iteratedFDeriv ℝ k (w s))) :=
      ih hw hstep
    have hfd : ContDiff ℝ m
        (Function.uncurry (fun s => fderiv ℝ (iteratedFDeriv ℝ k (w s)))) :=
      contDiff_uncurry_fderiv_of_contDiff_uncurry' ihk (le_refl _)
    have heq : (Function.uncurry (fun s => iteratedFDeriv ℝ (k + 1) (w s)))
        = (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F).symm
          ∘ Function.uncurry (fun s => fderiv ℝ (iteratedFDeriv ℝ k (w s))) := by
      funext p
      obtain ⟨s, x⟩ := p
      simp only [Function.comp_apply, Function.uncurry_apply_pair]
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    rw [heq]
    fun_prop

/-! ## Layer-3 multilinear jet inputs and the `C³` `ContDiff` flow bridge

Combining the multilinear-jet recursion with the layer-1/2 jet lemmas and the compatibility identities
supplies every non-Lipschitz input of the tower's `C³` flow theorem
`contMDiff_three_flow_apply_of_lipschitz_thirdDeriv` from a single `ContDiff ℝ n (uncurry v)`
hypothesis (`3 ≤ n`).  The top-order Lipschitz controls are supplied directly (matching the layer-2
bridge, since expressing them as fourth-derivative bounds would require yet another multilinear jet). -/

/-- **`hD3vm` input.**  The multilinear second-derivative field `iteratedFDeriv ℝ 2 (v s)` is a genuine
Fréchet-differentiable field: `fderiv ℝ (iteratedFDeriv ℝ 2 (v s)) ξ` is its derivative at every `ξ`,
for a jointly-`ContDiff ℝ n` field with `3 ≤ n` (so each slice `v s` is spatially `ContDiff ℝ n` and
its `iteratedFDeriv ℝ 2` is `ContDiff ℝ 1`). -/
theorem hasFDerivAt_fderiv_iteratedFDeriv_two_of_contDiff_uncurry
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 3 ≤ n) (s : ℝ) (ξ : E) :
    HasFDerivAt (iteratedFDeriv ℝ 2 (v s)) (fderiv ℝ (iteratedFDeriv ℝ 2 (v s)) ξ) ξ := by
  have hvs : ContDiff ℝ n (v s) := contDiff_apply_of_contDiff_uncurry h s
  have hmn : (1 : WithTop ℕ∞) + (2 : ℕ) ≤ n := by exact_mod_cast hn
  have h2 : ContDiff ℝ 1 (iteratedFDeriv ℝ 2 (v s)) := hvs.iteratedFDeriv_right hmn
  exact ((h2.differentiable one_ne_zero).differentiableAt).hasFDerivAt

/-- **`hD3vmc` input.**  Joint `(t, x)`-continuity of the derivative of the multilinear second
derivative, `(t, x) ↦ fderiv ℝ (iteratedFDeriv ℝ 2 (v t)) x`, from the codomain-general layer-1
continuity lemma applied to the jointly-`ContDiff` multilinear second-derivative field
`iteratedFDeriv ℝ 2 (v ·)` (itself `ContDiff` by the multilinear-jet recursion, `3 ≤ n`). -/
theorem continuous_fderiv_iteratedFDeriv_two_of_contDiff_uncurry
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 3 ≤ n) :
    Continuous (fun p : ℝ × E => fderiv ℝ (iteratedFDeriv ℝ 2 (v p.1)) p.2) := by
  have hmn : (1 : WithTop ℕ∞) + (2 : ℕ) ≤ n := by exact_mod_cast hn
  have hcd : ContDiff ℝ 1 (Function.uncurry (fun s => iteratedFDeriv ℝ 2 (v s))) :=
    contDiff_uncurry_iteratedFDeriv_of_contDiff_uncurry 2 h hmn
  exact continuous_fderiv_of_contDiff_uncurry' hcd le_rfl

/-- **`hD3vc` input.**  Joint `(t, x)`-continuity of the multilinear third derivative,
`(t, x) ↦ iteratedFDeriv ℝ 3 (v t) x`, as the continuity of the jointly-`ContDiff ℝ 0`
multilinear third-derivative field `iteratedFDeriv ℝ 3 (v ·)` (`3 ≤ n`). -/
theorem continuous_iteratedFDeriv_three_of_contDiff_uncurry
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 3 ≤ n) :
    Continuous (fun p : ℝ × E => iteratedFDeriv ℝ 3 (v p.1) p.2) := by
  have hmn : (0 : WithTop ℕ∞) + (3 : ℕ) ≤ n := by exact_mod_cast hn
  have hcd : ContDiff ℝ 0 (Function.uncurry (fun s => iteratedFDeriv ℝ 3 (v s))) :=
    contDiff_uncurry_iteratedFDeriv_of_contDiff_uncurry 3 h hmn
  exact hcd.continuous

/-- **Manifold spatial `C³` regularity of the flow from a genuine `ContDiff` field.**  Packaging the
layer-1/2/3 field-jet extraction with the tower's `C^{3,1}` manifold regularity theorem
`contMDiff_three_flow_apply_of_lipschitz_thirdDeriv`: for a jointly-`ContDiff ℝ n` field `v` (`3 ≤ n`)
that is spatially `K`-Lipschitz and time-continuous, whose second and third spatial derivatives
(nested and multilinear) obey the stated Lipschitz bounds, any integral-curve flow family `Φ` anchored
at `t₀` has each time-`t` map `z ↦ Φ z t` in `ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3`.  The pointwise
`HasFDerivAt`, joint continuity, and multilinear compatibility (`hcompat`/`hcurry`) inputs of the tower
are all supplied here from the single `ContDiff` hypothesis; the top-order Lipschitz controls are
supplied directly.  This is the `C^{3,1}` jet the model-manifold `C³` gauge flow consumes, stated in
terms of joint `ContDiff` of the field. -/
theorem contMDiff_three_flow_apply_of_contDiff [CompleteSpace E]
    {K L M₂ M₃ N : ℝ≥0} {t₀ : ℝ} {Φ : E → ℝ → E}
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 3 ≤ n)
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    (hDvlip : ∀ s, LipschitzWith L (fderiv ℝ (v s)))
    (hD2vclip : ∀ s, LipschitzWith M₂ (fderiv ℝ (fderiv ℝ (v s))))
    (hD2vmlip : ∀ s, LipschitzWith N (iteratedFDeriv ℝ 2 (v s)))
    (hD3vmlip : ∀ s, LipschitzWith M₃ (fderiv ℝ (iteratedFDeriv ℝ 2 (v s))))
    (hD3vlip : ∀ s, LipschitzWith M₃ (iteratedFDeriv ℝ 3 (v s)))
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z) (t : ℝ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3 (fun z => Φ z t) := by
  have hn1 : (1 : WithTop ℕ∞) ≤ n := le_trans (by norm_num) hn
  have hn2 : (2 : WithTop ℕ∞) ≤ n := le_trans (by norm_num) hn
  exact contMDiff_three_flow_apply_of_lipschitz_thirdDeriv
    (Dv := fun s => fderiv ℝ (v s))
    (D2vc := fun s => fderiv ℝ (fderiv ℝ (v s)))
    (D2vm := fun s => iteratedFDeriv ℝ 2 (v s))
    (D3vm := fun s => fderiv ℝ (iteratedFDeriv ℝ 2 (v s)))
    (D3v := fun s => iteratedFDeriv ℝ 3 (v s))
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
    hΦ h0 t

/-- **Manifold spatial `C³` regularity of the flow from joint `ContDiff` and a first-derivative
bound.**  The convenience form of `contMDiff_three_flow_apply_of_contDiff` that discharges the spatial
Lipschitz (`hv`) and time-continuity (`hvc`) inputs from the `ContDiff` hypothesis together with a
global first-derivative bound (`hK`), matching the layer-1/2 `_of_bddDerivs` API: from `v` jointly
`ContDiff ℝ n` (`3 ≤ n`) with a globally bounded first spatial derivative (bound `K`) and the stated
second/third spatial-derivative Lipschitz controls, each time-`t` flow map `z ↦ Φ z t` is
`ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3`. -/
theorem contMDiff_three_flow_apply_of_contDiff_of_bddDerivs [CompleteSpace E]
    {K L M₂ M₃ N : ℝ≥0} {t₀ : ℝ} {Φ : E → ℝ → E}
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 3 ≤ n)
    (hK : ∀ s ξ, ‖fderiv ℝ (v s) ξ‖₊ ≤ K)
    (hDvlip : ∀ s, LipschitzWith L (fderiv ℝ (v s)))
    (hD2vclip : ∀ s, LipschitzWith M₂ (fderiv ℝ (fderiv ℝ (v s))))
    (hD2vmlip : ∀ s, LipschitzWith N (iteratedFDeriv ℝ 2 (v s)))
    (hD3vmlip : ∀ s, LipschitzWith M₃ (fderiv ℝ (iteratedFDeriv ℝ 2 (v s))))
    (hD3vlip : ∀ s, LipschitzWith M₃ (iteratedFDeriv ℝ 3 (v s)))
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z) (t : ℝ) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3 (fun z => Φ z t) := by
  have hn1 : (1 : WithTop ℕ∞) ≤ n := le_trans (by norm_num) hn
  exact contMDiff_three_flow_apply_of_contDiff h hn
    (fun τ => lipschitzWith_apply_of_contDiff_of_nnnorm_fderiv_le h hn1 hK τ)
    (fun x => continuous_apply_of_contDiff_uncurry h x)
    hDvlip hD2vclip hD2vmlip hD3vmlip hD3vlip hΦ h0 t

/-- **Field-data-only manifold `C³` smooth-dependence existence from a single `ContDiff` hypothesis.**
From `v` jointly `ContDiff ℝ n (uncurry v)` (`3 ≤ n`), spatially `K`-Lipschitz and time-continuous, with
the stated second/third spatial-derivative Lipschitz controls, there is a flow family `Φ` anchored at
`t₀` and integrating `v` whose time-`t` map is `ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3` for every `t`.  The
`ContDiff`-hypothesis form of `exists_flow_contMDiff_three` (obtained by combining `exists_flow_family`
with `contMDiff_three_flow_apply_of_contDiff`), packaging the entire `C^{3,1}` field jet the
model-manifold `C³` gauge flow consumes behind a single smoothness hypothesis. -/
theorem exists_flow_contMDiff_three_of_contDiff [CompleteSpace E]
    {K L M₂ M₃ N : ℝ≥0} {t₀ : ℝ}
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 3 ≤ n)
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    (hDvlip : ∀ s, LipschitzWith L (fderiv ℝ (v s)))
    (hD2vclip : ∀ s, LipschitzWith M₂ (fderiv ℝ (fderiv ℝ (v s))))
    (hD2vmlip : ∀ s, LipschitzWith N (iteratedFDeriv ℝ 2 (v s)))
    (hD3vmlip : ∀ s, LipschitzWith M₃ (fderiv ℝ (iteratedFDeriv ℝ 2 (v s))))
    (hD3vlip : ∀ s, LipschitzWith M₃ (iteratedFDeriv ℝ 3 (v s))) :
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) ∧
        ∀ t, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3 (fun z => Φ z t) := by
  obtain ⟨Φ, h0, hΦ⟩ := exists_flow_family (t₀ := t₀) hv hvc
  exact ⟨Φ, h0, hΦ, fun t => contMDiff_three_flow_apply_of_contDiff h hn hv hvc
    hDvlip hD2vclip hD2vmlip hD3vmlip hD3vlip hΦ h0 t⟩

/-- **Field-data-only manifold `C³` self-diffeomorphism family from a single `ContDiff` hypothesis.**
From `v` jointly `ContDiff ℝ n (uncurry v)` (`3 ≤ n`) with the stated Lipschitz controls, there is a
flow family `Φ` anchored at `t₀` and integrating `v` whose time-`t` map is a `C³` diffeomorphism of the
state space for every `t`: it has a two-sided inverse `ψ`, with both `x ↦ Φ x t` and `ψ` in
`ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3`.  The `ContDiff`-hypothesis form of
`exists_flow_contMDiff_three_diffeomorph`, supplying its `C^{3,1}` field jet from the single smoothness
hypothesis — exactly the mutually-inverse `C³` time-slice diffeomorphism data the compact-manifold gauge
flow of Item 2 consumes. -/
theorem exists_flow_contMDiff_three_diffeomorph_of_contDiff [CompleteSpace E]
    {K L M₂ M₃ N : ℝ≥0} {t₀ : ℝ}
    (h : ContDiff ℝ n (Function.uncurry v)) (hn : 3 ≤ n)
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    (hDvlip : ∀ s, LipschitzWith L (fderiv ℝ (v s)))
    (hD2vclip : ∀ s, LipschitzWith M₂ (fderiv ℝ (fderiv ℝ (v s))))
    (hD2vmlip : ∀ s, LipschitzWith N (iteratedFDeriv ℝ 2 (v s)))
    (hD3vmlip : ∀ s, LipschitzWith M₃ (fderiv ℝ (iteratedFDeriv ℝ 2 (v s))))
    (hD3vlip : ∀ s, LipschitzWith M₃ (iteratedFDeriv ℝ 3 (v s))) :
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) ∧
      ∀ t, ∃ ψ : E → E, Function.LeftInverse ψ (fun z => Φ z t) ∧
        Function.RightInverse ψ (fun z => Φ z t) ∧
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3 (fun z => Φ z t) ∧ ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3 ψ := by
  have hn1 : (1 : WithTop ℕ∞) ≤ n := le_trans (by norm_num) hn
  have hn2 : (2 : WithTop ℕ∞) ≤ n := le_trans (by norm_num) hn
  exact exists_flow_contMDiff_three_diffeomorph (t₀ := t₀)
    (Dv := fun s => fderiv ℝ (v s))
    (D2vc := fun s => fderiv ℝ (fderiv ℝ (v s)))
    (D2vm := fun s => iteratedFDeriv ℝ 2 (v s))
    (D3vm := fun s => fderiv ℝ (iteratedFDeriv ℝ 2 (v s)))
    (D3v := fun s => iteratedFDeriv ℝ 3 (v s))
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

end SmoothDependenceCk
end AnalyticPDE
end RicciFlow
