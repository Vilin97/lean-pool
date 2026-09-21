/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothDependenceCk
/-!
# The time-`t` flow map is a homeomorphism (bijectivity / inverse-flow half of the diffeomorphism)

The smooth-dependence tower (`SmoothDependenceCk`) already establishes that for a flow family
`Φ : E → ℝ → E` of a uniformly `K`-Lipschitz, time-continuous vector field `v` anchored at
`Φ x t₀ = x`, the time-`t` flow map `x ↦ Φ x t` is **injective** (`injective_flow_apply`) and
**Lipschitz/continuous** in the initial value (`lipschitzWith_flow_apply`, `continuous_flow_apply`).
Injectivity is exactly the "diffeomorphism onto its image" half that Item 2's compact-manifold
gauge-flow constructor needs; the *other* half — that the flow map is a **bijection with a
continuous inverse** (so the flow at each time is an ambient self-homeomorphism, the topological
skeleton of the self-diffeomorphism family `SmoothSelfDiffeomorph3Family`) — was still missing.

This module closes that gap, entirely from the existence and uniqueness theory already in
`SmoothDependenceCk`:

* `surjective_flow_apply` — the flow map is **surjective**: every `w` is `Φ z t` for the initial
  value `z = γ t₀`, where `γ` is the integral curve through `w` at time `t`
  (`exists_isIntegralCurve_of_lipschitzWith`), identified with `Φ (γ t₀)` by uniqueness
  (`eq_of_isIntegralCurve_of_eq_at`).
* `bijective_flow_apply` — combining with `injective_flow_apply`.
* `exists_inverse_flow_apply` — the **explicit inverse flow map**: taking a companion flow family
  `Ψ` anchored at time `t` (from `exists_flow_family`), the map `ψ = fun w ↦ Ψ w t₀` is a two-sided
  inverse of `x ↦ Φ x t`, and being itself the time-`t₀` map of a flow family it is Lipschitz (with
  the exponential constant) and hence continuous.  This is the reverse-time flow.
* `exists_homeomorph_flow_apply` — the packaged statement that the time-`t` flow map underlies a
  `Homeomorph E E`.

Everything is proved sorry-free from Mathlib and the `SmoothDependenceCk` tower; no PDE or manifold
content is used.  The state space needs only `[CompleteSpace E]` (for the companion existence).
-/

open Set Filter Topology
open scoped Topology NNReal

namespace RicciFlow
namespace AnalyticPDE
namespace SmoothDependenceCk

@[expose] public noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {v : ℝ → E → E} {K : ℝ≥0} {t₀ : ℝ}
variable {Φ : E → ℝ → E}

/-- **Surjectivity of the time-`t` flow map.**  For a flow family `Φ` of the uniformly
`K`-Lipschitz, time-continuous field `v` anchored at `Φ x t₀ = x`, every point `w` lies in the
image of `x ↦ Φ x t`.  Indeed the integral curve `γ` through `w` at time `t` (from
`exists_isIntegralCurve_of_lipschitzWith`) agrees at `t₀` with the anchored curve `Φ (γ t₀)`, so by
uniqueness (`eq_of_isIntegralCurve_of_eq_at`) they coincide, whence `Φ (γ t₀) t = γ t = w`. -/
theorem surjective_flow_apply [CompleteSpace E]
    (hv : ∀ s, LipschitzWith K (v s)) (hvc : ∀ x, Continuous fun s => v s x)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x) (t : ℝ) :
    Function.Surjective (fun z => Φ z t) := by
  intro w
  obtain ⟨γ, hγt, hγcurve⟩ := exists_isIntegralCurve_of_lipschitzWith hv hvc t w
  refine ⟨γ t₀, ?_⟩
  have heq := eq_of_isIntegralCurve_of_eq_at hv (hΦ (γ t₀)) hγcurve (h0 (γ t₀)) t
  show Φ (γ t₀) t = w
  rw [heq]; exact hγt

/-- **Bijectivity of the time-`t` flow map**, combining injectivity (`injective_flow_apply`) and
surjectivity (`surjective_flow_apply`). -/
theorem bijective_flow_apply [CompleteSpace E]
    (hv : ∀ s, LipschitzWith K (v s)) (hvc : ∀ x, Continuous fun s => v s x)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x) (t : ℝ) :
    Function.Bijective (fun z => Φ z t) :=
  ⟨injective_flow_apply hv hΦ h0 t, surjective_flow_apply hv hvc hΦ h0 t⟩

/-- **Explicit two-sided inverse (reverse-time flow) of the time-`t` flow map.**  From a companion
flow family `Ψ` anchored at time `t` (produced by `exists_flow_family`), the reverse map
`ψ = fun w ↦ Ψ w t₀` is a two-sided inverse of `x ↦ Φ x t` and, being itself the time-`t₀` map of a
flow family, is Lipschitz with constant `exp (K · |t₀ - t|)` (hence continuous).

The inverse identities are pure uniqueness of integral curves: `Ψ (Φ z t)` agrees with `Φ z` at
time `t`, so at `t₀` we get `ψ (Φ z t) = Φ z t₀ = z`; symmetrically `Φ (Ψ w t₀)` agrees with `Ψ w` at
`t₀`, so at `t` we get `Φ (ψ w) t = Ψ w t = w`. -/
theorem exists_inverse_flow_apply [CompleteSpace E]
    (hv : ∀ s, LipschitzWith K (v s)) (hvc : ∀ x, Continuous fun s => v s x)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x) (t : ℝ) :
    ∃ ψ : E → E, Function.LeftInverse ψ (fun z => Φ z t) ∧
      Function.RightInverse ψ (fun z => Φ z t) ∧
      LipschitzWith (Real.exp ((K : ℝ) * |t₀ - t|)).toNNReal ψ := by
  obtain ⟨Ψ, hΨ0, hΨcurve⟩ := exists_flow_family (t₀ := t) hv hvc
  refine ⟨fun w => Ψ w t₀, ?_, ?_, ?_⟩
  · -- LeftInverse: ψ (Φ z t) = z
    intro z
    have hagree : Ψ (Φ z t) t = Φ z t := hΨ0 (Φ z t)
    have heq := eq_of_isIntegralCurve_of_eq_at hv (hΨcurve (Φ z t)) (hΦ z) hagree t₀
    show Ψ (Φ z t) t₀ = z
    rw [heq]; exact h0 z
  · -- RightInverse: Φ (ψ w) t = w
    intro w
    have hagree : Φ (Ψ w t₀) t₀ = Ψ w t₀ := h0 (Ψ w t₀)
    have heq := eq_of_isIntegralCurve_of_eq_at hv (hΦ (Ψ w t₀)) (hΨcurve w) hagree t
    show Φ (Ψ w t₀) t = w
    rw [heq]; exact hΨ0 w
  · -- ψ is the time-`t₀` map of the family `Ψ` anchored at `t`, hence Lipschitz
    exact lipschitzWith_flow_apply (Φ := Ψ) (t₀ := t) hv hΨcurve hΨ0 t₀

/-- **The time-`t` flow map underlies a self-homeomorphism** of the state space.  Bundles the
bijectivity (`bijective_flow_apply`), the continuity of the flow map (`continuous_flow_apply`), and
the continuity of the reverse-time flow (`exists_inverse_flow_apply`) into a `Homeomorph E E` whose
coercion is `x ↦ Φ x t`.  This is the ambient-topological skeleton of the self-diffeomorphism family
consumed by the compact-manifold gauge flow of Item 2. -/
theorem exists_homeomorph_flow_apply [CompleteSpace E]
    (hv : ∀ s, LipschitzWith K (v s)) (hvc : ∀ x, Continuous fun s => v s x)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x) (t : ℝ) :
    ∃ e : Homeomorph E E, ⇑e = fun z => Φ z t := by
  obtain ⟨ψ, hleft, hright, hψlip⟩ := exists_inverse_flow_apply hv hvc hΦ h0 t
  refine ⟨{ toFun := fun z => Φ z t
            invFun := ψ
            left_inv := hleft
            right_inv := hright
            continuous_toFun := continuous_flow_apply hv hΦ h0 t
            continuous_invFun := hψlip.continuous }, rfl⟩

/-!
## Two-sided (all-time) differentiable dependence

The regularity layers of `SmoothDependenceCk` are all stated in *forward* time (`t₀ ≤ t`).  For the
flow at a time `t ≥ t₀` to be a **diffeomorphism**, its inverse is a *backward* flow (target time
`t₀` earlier than the anchor `t`), so backward-time differentiability is needed.  It follows from
the forward result by the time-reversal trick already used for the Grönwall bounds
(`isIntegralCurve_comp_neg`): the field `w s x = -(v (-s) x)` is `K`-Lipschitz with `L`-Lipschitz,
jointly continuous spatial derivative `Dw s x = -(Dv (-s) x)`, and the forward flow of `w` anchored
at `-t₀`, reflected by `s ↦ -s`, is the backward flow of `v` anchored at `t₀`.
-/

/-- **Backward-in-time differentiable dependence on initial data** for a `C^{1,1}` field.  Same
hypotheses as `exists_flow_differentiable_of_lipschitz_deriv` but for `t ≤ t₀`.  Proved by applying
the forward theorem to the time-reversed field `w s x = -(v (-s) x)` (with reversed derivative
`Dw s x = -(Dv (-s) x)`) anchored at `-t₀` and target `-t ≥ -t₀`, then reflecting the resulting flow
family by `s ↦ -s`. -/
theorem exists_flow_differentiable_of_lipschitz_deriv_backward [CompleteSpace E]
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ s x, HasFDerivAt (v s) (Dv s x) x)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    {L : ℝ≥0} (hDvlip : ∀ s, LipschitzWith L (Dv s))
    {t : ℝ} (ht0 : t ≤ t₀) :
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) ∧
        Differentiable ℝ (fun z => Φ z t) := by
  set w : ℝ → E → E := fun s x => -(v (-s) x) with hw_def
  set Dw : ℝ → E → (E →L[ℝ] E) := fun s x => -(Dv (-s) x) with hDw_def
  have hw : ∀ τ, LipschitzWith K (w τ) := by
    intro τ
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simp only [hw_def, dist_neg_neg]
    exact (hv (-τ)).dist_le_mul a b
  have hwc : ∀ x, Continuous fun s => w s x := by
    intro x
    simp only [hw_def]
    exact ((hvc x).comp continuous_neg).neg
  have hderivw : ∀ s x, HasFDerivAt (w s) (Dw s x) x := by
    intro s x
    change HasFDerivAt (fun y => -(v (-s) y)) (-(Dv (-s) x)) x
    have hfun : (fun y => -(v (-s) y)) = -(v (-s)) := by
      funext y
      rfl
    rw [hfun]
    exact (hderiv (-s) x).neg
  have hDwc : Continuous fun p : ℝ × E => Dw p.1 p.2 := by
    simp only [hDw_def]
    exact (hDvc.comp ((continuous_fst.neg).prodMk continuous_snd)).neg
  have hDwlip : ∀ s, LipschitzWith L (Dw s) := by
    intro s
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simp only [hDw_def, dist_neg_neg]
    exact (hDvlip (-s)).dist_le_mul a b
  obtain ⟨Φ', hΦ'0, hΦ'curve, hΦ'diff⟩ :=
    exists_flow_differentiable_of_lipschitz_deriv (v := w) (Dv := Dw) (t₀ := -t₀)
      hw hwc hderivw hDwc hDwlip (t := -t) (neg_le_neg ht0)
  have hVeq : (fun s (x : E) => -(w (-s) x)) = v := by
    funext s x; simp only [hw_def, neg_neg]
  refine ⟨fun z s => Φ' z (-s), fun z => hΦ'0 z, fun z => ?_, hΦ'diff⟩
  have hcurve := isIntegralCurve_comp_neg (hΦ'curve z)
  rw [hVeq] at hcurve
  exact hcurve

/-- **Two-sided (all-time) differentiable dependence on initial data** for a `C^{1,1}` field: for
*every* `t`, some flow family anchored at `t₀` has differentiable time-`t` map.  Combines the
forward (`exists_flow_differentiable_of_lipschitz_deriv`) and backward
(`exists_flow_differentiable_of_lipschitz_deriv_backward`) halves by `le_total`. -/
theorem exists_flow_differentiable_of_lipschitz_deriv_two_sided [CompleteSpace E]
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ s x, HasFDerivAt (v s) (Dv s x) x)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    {L : ℝ≥0} (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (t : ℝ) :
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) ∧
        Differentiable ℝ (fun z => Φ z t) := by
  rcases le_total t₀ t with h | h
  · exact exists_flow_differentiable_of_lipschitz_deriv hv hvc hderiv hDvc hDvlip h
  · exact exists_flow_differentiable_of_lipschitz_deriv_backward hv hvc hderiv hDvc hDvlip h

/-- **Differentiable dependence for a *given* flow family, at every time.**  Any flow family `Φ` of
the `C^{1,1}` field `v` anchored at `Φ z t₀ = z` has differentiable time-`t` map `z ↦ Φ z t` for
*all* `t` (both forward and backward of `t₀`).  Since the anchored integral curve through each point
is unique (`eq_of_isIntegralCurve_of_eq`), the given `Φ` agrees pointwise with the flow family
supplied by `exists_flow_differentiable_of_lipschitz_deriv_two_sided`, so differentiability
transfers.  This is the "one family, every time" form the diffeomorphism family consumes. -/
theorem differentiable_flow_apply_of_lipschitz_deriv [CompleteSpace E]
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ s x, HasFDerivAt (v s) (Dv s x) x)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    {L : ℝ≥0} (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z) (t : ℝ) :
    Differentiable ℝ (fun z => Φ z t) := by
  obtain ⟨Φ', h0', hΦ'curve, hΦ'diff⟩ :=
    exists_flow_differentiable_of_lipschitz_deriv_two_sided hv hvc hderiv hDvc hDvlip t
  have hEq : (fun z => Φ z t) = (fun z => Φ' z t) := by
    funext z
    exact eq_of_isIntegralCurve_of_eq hv (hΦ z) (hΦ'curve z) (by rw [h0 z, h0' z]) t
  rw [hEq]; exact hΦ'diff

/-!
## Two-sided (all-time) `C¹` dependence and the `C¹` diffeomorphism

The `C¹` (`ContDiff ℝ 1`) layer has the *same* field hypotheses as the differentiable one, so its
backward/two-sided/given-family forms are obtained by the identical time-reversal argument.  With
the "one family, every time" `C¹` form in hand, the time-`t` flow map is a genuine **`C¹`
diffeomorphism** of the state space for *every* `t`: it is a bijection (`bijective_flow_apply`), it
is `ContDiff ℝ 1`, and its inverse — the time-`t₀` map of a companion family anchored at `t` — is
also `ContDiff ℝ 1` (no forward/backward restriction, since the given-family `C¹` form is two-sided).
-/

/-- **Backward-in-time `C¹` dependence on initial data** for a `C^{1,1}` field (`t ≤ t₀`), by the
same time-reversal argument as the differentiable backward theorem. -/
theorem exists_flow_contDiff_one_of_lipschitz_deriv_backward [CompleteSpace E]
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ s x, HasFDerivAt (v s) (Dv s x) x)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    {L : ℝ≥0} (hDvlip : ∀ s, LipschitzWith L (Dv s))
    {t : ℝ} (ht0 : t ≤ t₀) :
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) ∧
        ContDiff ℝ 1 (fun z => Φ z t) := by
  set w : ℝ → E → E := fun s x => -(v (-s) x) with hw_def
  set Dw : ℝ → E → (E →L[ℝ] E) := fun s x => -(Dv (-s) x) with hDw_def
  have hw : ∀ τ, LipschitzWith K (w τ) := by
    intro τ
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simp only [hw_def, dist_neg_neg]
    exact (hv (-τ)).dist_le_mul a b
  have hwc : ∀ x, Continuous fun s => w s x := by
    intro x
    simp only [hw_def]
    exact ((hvc x).comp continuous_neg).neg
  have hderivw : ∀ s x, HasFDerivAt (w s) (Dw s x) x := by
    intro s x
    change HasFDerivAt (fun y => -(v (-s) y)) (-(Dv (-s) x)) x
    have hfun : (fun y => -(v (-s) y)) = -(v (-s)) := by
      funext y
      rfl
    rw [hfun]
    exact (hderiv (-s) x).neg
  have hDwc : Continuous fun p : ℝ × E => Dw p.1 p.2 := by
    simp only [hDw_def]
    exact (hDvc.comp ((continuous_fst.neg).prodMk continuous_snd)).neg
  have hDwlip : ∀ s, LipschitzWith L (Dw s) := by
    intro s
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simp only [hDw_def, dist_neg_neg]
    exact (hDvlip (-s)).dist_le_mul a b
  obtain ⟨Φ', hΦ'0, hΦ'curve, hΦ'cd⟩ :=
    exists_flow_contDiff_one_of_lipschitz_deriv (v := w) (Dv := Dw) (t₀ := -t₀)
      hw hwc hderivw hDwc hDwlip (t := -t) (neg_le_neg ht0)
  have hVeq : (fun s (x : E) => -(w (-s) x)) = v := by
    funext s x; simp only [hw_def, neg_neg]
  refine ⟨fun z s => Φ' z (-s), fun z => hΦ'0 z, fun z => ?_, hΦ'cd⟩
  have hcurve := isIntegralCurve_comp_neg (hΦ'curve z)
  rw [hVeq] at hcurve
  exact hcurve

/-- **Two-sided (all-time) `C¹` dependence on initial data** for a `C^{1,1}` field. -/
theorem exists_flow_contDiff_one_of_lipschitz_deriv_two_sided [CompleteSpace E]
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ s x, HasFDerivAt (v s) (Dv s x) x)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    {L : ℝ≥0} (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (t : ℝ) :
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) ∧
        ContDiff ℝ 1 (fun z => Φ z t) := by
  rcases le_total t₀ t with h | h
  · exact exists_flow_contDiff_one_of_lipschitz_deriv hv hvc hderiv hDvc hDvlip h
  · exact exists_flow_contDiff_one_of_lipschitz_deriv_backward hv hvc hderiv hDvc hDvlip h

/-- **`C¹` dependence for a *given* flow family, at every time.**  Any flow family `Φ` of the
`C^{1,1}` field `v` anchored at `Φ z t₀ = z` has `ContDiff ℝ 1` time-`t` map for *all* `t`,
transported from `exists_flow_contDiff_one_of_lipschitz_deriv_two_sided` by integral-curve
uniqueness. -/
theorem contDiff_one_flow_apply_of_lipschitz_deriv [CompleteSpace E]
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ s x, HasFDerivAt (v s) (Dv s x) x)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    {L : ℝ≥0} (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z) (t : ℝ) :
    ContDiff ℝ 1 (fun z => Φ z t) := by
  obtain ⟨Φ', h0', hΦ'curve, hΦ'cd⟩ :=
    exists_flow_contDiff_one_of_lipschitz_deriv_two_sided hv hvc hderiv hDvc hDvlip t
  have hEq : (fun z => Φ z t) = (fun z => Φ' z t) := by
    funext z
    exact eq_of_isIntegralCurve_of_eq hv (hΦ z) (hΦ'curve z) (by rw [h0 z, h0' z]) t
  rw [hEq]; exact hΦ'cd

/-- **The time-`t` flow map is a `C¹` diffeomorphism of the state space**, for *every* `t`.  Bundles
the reverse-time inverse `ψ` (the time-`t₀` map of a companion flow family anchored at `t`) with the
two-sided `ContDiff ℝ 1` regularity of both the flow map and its inverse.  This is the `C¹` skeleton
of the self-diffeomorphism family consumed by the compact-manifold gauge flow of Item 2, now with
genuine `C¹` regularity in *both* directions (no forward/backward restriction). -/
theorem exists_contDiff_one_diffeomorph_flow_apply [CompleteSpace E]
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ s x, HasFDerivAt (v s) (Dv s x) x)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    {L : ℝ≥0} (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z) (t : ℝ) :
    ∃ ψ : E → E, Function.LeftInverse ψ (fun z => Φ z t) ∧
      Function.RightInverse ψ (fun z => Φ z t) ∧
      ContDiff ℝ 1 (fun z => Φ z t) ∧ ContDiff ℝ 1 ψ := by
  obtain ⟨Ψ, hΨ0, hΨcurve⟩ := exists_flow_family (t₀ := t) hv hvc
  refine ⟨fun w => Ψ w t₀, ?_, ?_,
    contDiff_one_flow_apply_of_lipschitz_deriv hv hvc hderiv hDvc hDvlip hΦ h0 t,
    contDiff_one_flow_apply_of_lipschitz_deriv (Φ := Ψ) (t₀ := t)
      hv hvc hderiv hDvc hDvlip hΨcurve hΨ0 t₀⟩
  · intro z
    have heq := eq_of_isIntegralCurve_of_eq_at hv (hΨcurve (Φ z t)) (hΦ z) (hΨ0 (Φ z t)) t₀
    show Ψ (Φ z t) t₀ = z
    rw [heq]; exact h0 z
  · intro w
    have heq := eq_of_isIntegralCurve_of_eq_at hv (hΦ (Ψ w t₀)) (hΨcurve w) (h0 (Ψ w t₀)) t
    show Φ (Ψ w t₀) t = w
    rw [heq]; exact hΨ0 w

/-!
## Two-sided (all-time) `C²` dependence and the `C²` diffeomorphism

The `C²` layer carries clean (non-multilinear) second-derivative data `D2v s x : E →L[ℝ] (E →L[ℝ] E)`,
so the time-reversal argument extends verbatim with the extra reflected datum `D2w s x = -(D2v (-s) x)`
(the second derivative of `-(v (-s) ·)` is again the negation of the second derivative, jointly
continuous and `M`-Lipschitz through negation + time reflection).
-/

/-- **Backward-in-time `C²` dependence on initial data** for a `C^{2,1}` field (`t ≤ t₀`). -/
theorem exists_flow_contDiff_two_of_lipschitz_secondDeriv_backward [CompleteSpace E]
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    {L : ℝ≥0} (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2v : ∀ s ξ, HasFDerivAt (Dv s) (D2v s ξ) ξ)
    (hD2vc : Continuous fun p : ℝ × E => D2v p.1 p.2)
    {M : ℝ≥0} (hD2vlip : ∀ s, LipschitzWith M (D2v s))
    {t : ℝ} (ht0 : t ≤ t₀) :
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) ∧
        ContDiff ℝ 2 (fun z => Φ z t) := by
  set w : ℝ → E → E := fun s x => -(v (-s) x) with hw_def
  set Dw : ℝ → E → (E →L[ℝ] E) := fun s x => -(Dv (-s) x) with hDw_def
  set D2w : ℝ → E → (E →L[ℝ] (E →L[ℝ] E)) := fun s x => -(D2v (-s) x) with hD2w_def
  have hw : ∀ τ, LipschitzWith K (w τ) := by
    intro τ
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simp only [hw_def, dist_neg_neg]
    exact (hv (-τ)).dist_le_mul a b
  have hwc : ∀ x, Continuous fun s => w s x := by
    intro x
    simp only [hw_def]
    exact ((hvc x).comp continuous_neg).neg
  have hDw : ∀ s ξ, HasFDerivAt (w s) (Dw s ξ) ξ := by
    intro s ξ
    change HasFDerivAt (fun y => -(v (-s) y)) (-(Dv (-s) ξ)) ξ
    have hfun : (fun y => -(v (-s) y)) = -(v (-s)) := by
      funext y
      rfl
    rw [hfun]
    exact (hDv (-s) ξ).neg
  have hDwc : Continuous fun p : ℝ × E => Dw p.1 p.2 := by
    simp only [hDw_def]
    exact (hDvc.comp ((continuous_fst.neg).prodMk continuous_snd)).neg
  have hDwlip : ∀ s, LipschitzWith L (Dw s) := by
    intro s
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simp only [hDw_def, dist_neg_neg]
    exact (hDvlip (-s)).dist_le_mul a b
  have hD2w : ∀ s ξ, HasFDerivAt (Dw s) (D2w s ξ) ξ := by
    intro s ξ
    change HasFDerivAt (fun y => -(Dv (-s) y)) (-(D2v (-s) ξ)) ξ
    have hfun : (fun y => -(Dv (-s) y)) = -(Dv (-s)) := by
      funext y
      rfl
    rw [hfun]
    exact (hD2v (-s) ξ).neg
  have hD2wc : Continuous fun p : ℝ × E => D2w p.1 p.2 := by
    simp only [hD2w_def]
    exact (hD2vc.comp ((continuous_fst.neg).prodMk continuous_snd)).neg
  have hD2wlip : ∀ s, LipschitzWith M (D2w s) := by
    intro s
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simp only [hD2w_def, dist_neg_neg]
    exact (hD2vlip (-s)).dist_le_mul a b
  obtain ⟨Φ', hΦ'0, hΦ'curve, hΦ'cd⟩ :=
    exists_flow_contDiff_two_of_lipschitz_secondDeriv (v := w) (Dv := Dw) (D2v := D2w) (t₀ := -t₀)
      hw hwc hDw hDwc hDwlip hD2w hD2wc hD2wlip (t := -t) (neg_le_neg ht0)
  have hVeq : (fun s (x : E) => -(w (-s) x)) = v := by
    funext s x; simp only [hw_def, neg_neg]
  refine ⟨fun z s => Φ' z (-s), fun z => hΦ'0 z, fun z => ?_, hΦ'cd⟩
  have hcurve := isIntegralCurve_comp_neg (hΦ'curve z)
  rw [hVeq] at hcurve
  exact hcurve

/-- **Two-sided (all-time) `C²` dependence on initial data** for a `C^{2,1}` field. -/
theorem exists_flow_contDiff_two_of_lipschitz_secondDeriv_two_sided [CompleteSpace E]
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    {L : ℝ≥0} (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2v : ∀ s ξ, HasFDerivAt (Dv s) (D2v s ξ) ξ)
    (hD2vc : Continuous fun p : ℝ × E => D2v p.1 p.2)
    {M : ℝ≥0} (hD2vlip : ∀ s, LipschitzWith M (D2v s))
    (t : ℝ) :
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) ∧
        ContDiff ℝ 2 (fun z => Φ z t) := by
  rcases le_total t₀ t with h | h
  · exact exists_flow_contDiff_two_of_lipschitz_secondDeriv
      hv hvc hDv hDvc hDvlip hD2v hD2vc hD2vlip h
  · exact exists_flow_contDiff_two_of_lipschitz_secondDeriv_backward
      hv hvc hDv hDvc hDvlip hD2v hD2vc hD2vlip h

/-- **`C²` dependence for a *given* flow family, at every time.** -/
theorem contDiff_two_flow_apply_of_lipschitz_secondDeriv [CompleteSpace E]
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    {L : ℝ≥0} (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2v : ∀ s ξ, HasFDerivAt (Dv s) (D2v s ξ) ξ)
    (hD2vc : Continuous fun p : ℝ × E => D2v p.1 p.2)
    {M : ℝ≥0} (hD2vlip : ∀ s, LipschitzWith M (D2v s))
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z) (t : ℝ) :
    ContDiff ℝ 2 (fun z => Φ z t) := by
  obtain ⟨Φ', h0', hΦ'curve, hΦ'cd⟩ :=
    exists_flow_contDiff_two_of_lipschitz_secondDeriv_two_sided
      hv hvc hDv hDvc hDvlip hD2v hD2vc hD2vlip t
  have hEq : (fun z => Φ z t) = (fun z => Φ' z t) := by
    funext z
    exact eq_of_isIntegralCurve_of_eq hv (hΦ z) (hΦ'curve z) (by rw [h0 z, h0' z]) t
  rw [hEq]; exact hΦ'cd

/-- **The time-`t` flow map is a `C²` diffeomorphism of the state space**, for *every* `t`.  The
reverse-time inverse `ψ` and the flow map are both `ContDiff ℝ 2`. -/
theorem exists_contDiff_two_diffeomorph_flow_apply [CompleteSpace E]
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    {L : ℝ≥0} (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2v : ∀ s ξ, HasFDerivAt (Dv s) (D2v s ξ) ξ)
    (hD2vc : Continuous fun p : ℝ × E => D2v p.1 p.2)
    {M : ℝ≥0} (hD2vlip : ∀ s, LipschitzWith M (D2v s))
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z) (t : ℝ) :
    ∃ ψ : E → E, Function.LeftInverse ψ (fun z => Φ z t) ∧
      Function.RightInverse ψ (fun z => Φ z t) ∧
      ContDiff ℝ 2 (fun z => Φ z t) ∧ ContDiff ℝ 2 ψ := by
  obtain ⟨Ψ, hΨ0, hΨcurve⟩ := exists_flow_family (t₀ := t) hv hvc
  refine ⟨fun w => Ψ w t₀, ?_, ?_,
    contDiff_two_flow_apply_of_lipschitz_secondDeriv
      hv hvc hDv hDvc hDvlip hD2v hD2vc hD2vlip hΦ h0 t,
    contDiff_two_flow_apply_of_lipschitz_secondDeriv (Φ := Ψ) (t₀ := t)
      hv hvc hDv hDvc hDvlip hD2v hD2vc hD2vlip hΨcurve hΨ0 t₀⟩
  · intro z
    have heq := eq_of_isIntegralCurve_of_eq_at hv (hΨcurve (Φ z t)) (hΦ z) (hΨ0 (Φ z t)) t₀
    show Ψ (Φ z t) t₀ = z
    rw [heq]; exact h0 z
  · intro w
    have heq := eq_of_isIntegralCurve_of_eq_at hv (hΦ (Ψ w t₀)) (hΨcurve w) (h0 (Ψ w t₀)) t
    show Φ (Ψ w t₀) t = w
    rw [heq]; exact hΨ0 w

/-!
## `map_neg` for the currying maps (support for the `C³` time reversal)

The `C³` field hypotheses include the compatibility conditions `D2vc = curry2 D2vm` and
`D3vm = (D3v).curryLeft`.  Reversing them under negation needs that `curry2` and
`ContinuousMultilinearMap.curryLeft` commute with negation.
-/

/-- `curryLeft` of a `Fin 3` continuous multilinear map commutes with negation. -/
theorem curryLeft_neg_fin3 (X : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E) :
    (-X).curryLeft = -X.curryLeft := by
  ext x m
  simp only [ContinuousMultilinearMap.curryLeft_apply, ContinuousMultilinearMap.neg_apply,
    ContinuousLinearMap.neg_apply]

/-- The two-fold curry `curry2` commutes with negation. -/
theorem curry2_neg (X : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E) :
    curry2 (-X) = -curry2 X := by
  have hcl : (-X).curryLeft = -X.curryLeft := by
    ext x m
    simp only [ContinuousMultilinearMap.curryLeft_apply, ContinuousMultilinearMap.neg_apply,
      ContinuousLinearMap.neg_apply]
  simp only [curry2, hcl, ContinuousLinearMap.comp_neg]

/-!
## Two-sided (all-time) `C³` dependence and the `C³` diffeomorphism

The full `C³` layer reverses six spatial fields (`Dw, D2wc, D2wm, D3wm, D3wv`, each the negation of
the corresponding `v`-field at reflected time), including the multilinear second/third derivatives.
All the norm/continuity/Lipschitz hypotheses transfer through negation + time reflection, and the two
compatibility conditions transfer via `curry2_neg` / `curryLeft_neg_fin3`.
-/

/-- **Backward-in-time `C³` dependence on initial data** for a `C^{3,1}` field (`t ≤ t₀`), by the
time-reversal argument applied to the full third-order jet of `v`. -/
theorem exists_flow_contDiff_three_of_lipschitz_thirdDeriv_backward [CompleteSpace E]
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
    (hcurry : ∀ s ξ, D3vm s ξ = (D3v s ξ).curryLeft)
    {t : ℝ} (ht0 : t ≤ t₀) :
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) ∧
        ContDiff ℝ 3 (fun z => Φ z t) := by
  set w : ℝ → E → E := fun s x => -(v (-s) x) with hw_def
  set Dw : ℝ → E → (E →L[ℝ] E) := fun s x => -(Dv (-s) x) with hDw_def
  set D2wc : ℝ → E → (E →L[ℝ] (E →L[ℝ] E)) := fun s x => -(D2vc (-s) x) with hD2wc_def
  set D2wm : ℝ → E → (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E) :=
    fun s x => -(D2vm (-s) x) with hD2wm_def
  set D3wm : ℝ → E → (E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)) :=
    fun s x => -(D3vm (-s) x) with hD3wm_def
  set D3wv : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E :=
    fun s x => -(D3v (-s) x) with hD3wv_def
  have hw : ∀ τ, LipschitzWith K (w τ) := by
    intro τ; refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simp only [hw_def, dist_neg_neg]; exact (hv (-τ)).dist_le_mul a b
  have hwc : ∀ x, Continuous fun s => w s x := by
    intro x; simp only [hw_def]; exact ((hvc x).comp continuous_neg).neg
  have hDw : ∀ s ξ, HasFDerivAt (w s) (Dw s ξ) ξ := by
    intro s ξ
    change HasFDerivAt (fun y => -(v (-s) y)) (-(Dv (-s) ξ)) ξ
    have hfun : (fun y => -(v (-s) y)) = -(v (-s)) := by
      funext y
      rfl
    rw [hfun]
    exact (hDv (-s) ξ).neg
  have hDwc : Continuous fun p : ℝ × E => Dw p.1 p.2 := by
    simp only [hDw_def]; exact (hDvc.comp ((continuous_fst.neg).prodMk continuous_snd)).neg
  have hDwlip : ∀ s, LipschitzWith L (Dw s) := by
    intro s; refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simp only [hDw_def, dist_neg_neg]; exact (hDvlip (-s)).dist_le_mul a b
  have hD2wc : ∀ s ξ, HasFDerivAt (Dw s) (D2wc s ξ) ξ := by
    intro s ξ
    change HasFDerivAt (fun y => -(Dv (-s) y)) (-(D2vc (-s) ξ)) ξ
    have hfun : (fun y => -(Dv (-s) y)) = -(Dv (-s)) := by
      funext y
      rfl
    rw [hfun]
    exact (hD2vc (-s) ξ).neg
  have hD2wcc : Continuous fun p : ℝ × E => D2wc p.1 p.2 := by
    simp only [hD2wc_def]; exact (hD2vcc.comp ((continuous_fst.neg).prodMk continuous_snd)).neg
  have hD2wclip : ∀ s, LipschitzWith M₂ (D2wc s) := by
    intro s; refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simp only [hD2wc_def, dist_neg_neg]; exact (hD2vclip (-s)).dist_le_mul a b
  have hD2wmlip : ∀ s, LipschitzWith N (D2wm s) := by
    intro s; refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simp only [hD2wm_def, dist_neg_neg]; exact (hD2vmlip (-s)).dist_le_mul a b
  have hD3wm : ∀ s ξ, HasFDerivAt (D2wm s) (D3wm s ξ) ξ := by
    intro s ξ
    change HasFDerivAt (fun y => -(D2vm (-s) y)) (-(D3vm (-s) ξ)) ξ
    have hfun : (fun y => -(D2vm (-s) y)) = -(D2vm (-s)) := by
      funext y
      rfl
    rw [hfun]
    exact (hD3vm (-s) ξ).neg
  have hD3wmc : Continuous fun p : ℝ × E => D3wm p.1 p.2 := by
    simp only [hD3wm_def]; exact (hD3vmc.comp ((continuous_fst.neg).prodMk continuous_snd)).neg
  have hD3wmlip : ∀ s, LipschitzWith M₃ (D3wm s) := by
    intro s; refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simp only [hD3wm_def, dist_neg_neg]; exact (hD3vmlip (-s)).dist_le_mul a b
  have hD3wvc : Continuous fun p : ℝ × E => D3wv p.1 p.2 := by
    simp only [hD3wv_def]; exact (hD3vc.comp ((continuous_fst.neg).prodMk continuous_snd)).neg
  have hD3wvlip : ∀ s, LipschitzWith M₃ (D3wv s) := by
    intro s; refine LipschitzWith.of_dist_le_mul fun a b => ?_
    simp only [hD3wv_def, dist_neg_neg]; exact (hD3vlip (-s)).dist_le_mul a b
  have hwcompat : ∀ s ξ, D2wc s ξ = curry2 (D2wm s ξ) := by
    intro s ξ; simp only [hD2wc_def, hD2wm_def]
    rw [curry2_neg, ← hcompat (-s) ξ]
  have hwcurry : ∀ s ξ, D3wm s ξ = (D3wv s ξ).curryLeft := by
    intro s ξ; simp only [hD3wm_def, hD3wv_def]
    rw [curryLeft_neg_fin3, ← hcurry (-s) ξ]
  obtain ⟨Φ', hΦ'0, hΦ'curve, hΦ'cd⟩ :=
    exists_flow_contDiff_three_of_lipschitz_thirdDeriv
      (v := w) (Dv := Dw) (D2vc := D2wc) (D2vm := D2wm) (D3vm := D3wm) (D3v := D3wv) (t₀ := -t₀)
      hw hwc hDw hDwc hDwlip hD2wc hD2wcc hD2wclip hD2wmlip hD3wm hD3wmc hD3wmlip
      hD3wvc hD3wvlip hwcompat hwcurry (t := -t) (neg_le_neg ht0)
  have hVeq : (fun s (x : E) => -(w (-s) x)) = v := by
    funext s x; simp only [hw_def, neg_neg]
  refine ⟨fun z s => Φ' z (-s), fun z => hΦ'0 z, fun z => ?_, hΦ'cd⟩
  have hcurve := isIntegralCurve_comp_neg (hΦ'curve z)
  rw [hVeq] at hcurve
  exact hcurve

/-- **Two-sided (all-time) `C³` dependence on initial data** for a `C^{3,1}` field. -/
theorem exists_flow_contDiff_three_of_lipschitz_thirdDeriv_two_sided [CompleteSpace E]
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
    (hcurry : ∀ s ξ, D3vm s ξ = (D3v s ξ).curryLeft)
    (t : ℝ) :
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) ∧
        ContDiff ℝ 3 (fun z => Φ z t) := by
  rcases le_total t₀ t with h | h
  · exact exists_flow_contDiff_three_of_lipschitz_thirdDeriv
      hv hvc hDv hDvc hDvlip hD2vc hD2vcc hD2vclip hD2vmlip hD3vm hD3vmc hD3vmlip
      hD3vc hD3vlip hcompat hcurry h
  · exact exists_flow_contDiff_three_of_lipschitz_thirdDeriv_backward
      hv hvc hDv hDvc hDvlip hD2vc hD2vcc hD2vclip hD2vmlip hD3vm hD3vmc hD3vmlip
      hD3vc hD3vlip hcompat hcurry h

/-- **`C³` dependence for a *given* flow family, at every time.** -/
theorem contDiff_three_flow_apply_of_lipschitz_thirdDeriv [CompleteSpace E]
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
    (hcurry : ∀ s ξ, D3vm s ξ = (D3v s ξ).curryLeft)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z) (t : ℝ) :
    ContDiff ℝ 3 (fun z => Φ z t) := by
  obtain ⟨Φ', h0', hΦ'curve, hΦ'cd⟩ :=
    exists_flow_contDiff_three_of_lipschitz_thirdDeriv_two_sided
      hv hvc hDv hDvc hDvlip hD2vc hD2vcc hD2vclip hD2vmlip hD3vm hD3vmc hD3vmlip
      hD3vc hD3vlip hcompat hcurry t
  have hEq : (fun z => Φ z t) = (fun z => Φ' z t) := by
    funext z
    exact eq_of_isIntegralCurve_of_eq hv (hΦ z) (hΦ'curve z) (by rw [h0 z, h0' z]) t
  rw [hEq]; exact hΦ'cd

/-- **The time-`t` flow map is a `C³` diffeomorphism of the state space**, for *every* `t`.  Both the
flow map and its reverse-time inverse `ψ` are `ContDiff ℝ 3`.  This is the top-order (`C³`) skeleton
of the self-diffeomorphism family consumed by the compact-manifold gauge flow of Item 2, now with
genuine `C³` regularity in *both* directions and *without* the forward-time restriction of the
`SmoothDependenceCk` `C³` layer. -/
theorem exists_contDiff_three_diffeomorph_flow_apply [CompleteSpace E]
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
    (hcurry : ∀ s ξ, D3vm s ξ = (D3v s ξ).curryLeft)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z) (t : ℝ) :
    ∃ ψ : E → E, Function.LeftInverse ψ (fun z => Φ z t) ∧
      Function.RightInverse ψ (fun z => Φ z t) ∧
      ContDiff ℝ 3 (fun z => Φ z t) ∧ ContDiff ℝ 3 ψ := by
  obtain ⟨Ψ, hΨ0, hΨcurve⟩ := exists_flow_family (t₀ := t) hv hvc
  refine ⟨fun w => Ψ w t₀, ?_, ?_,
    contDiff_three_flow_apply_of_lipschitz_thirdDeriv
      hv hvc hDv hDvc hDvlip hD2vc hD2vcc hD2vclip hD2vmlip hD3vm hD3vmc hD3vmlip
      hD3vc hD3vlip hcompat hcurry hΦ h0 t,
    contDiff_three_flow_apply_of_lipschitz_thirdDeriv (Φ := Ψ) (t₀ := t)
      hv hvc hDv hDvc hDvlip hD2vc hD2vcc hD2vclip hD2vmlip hD3vm hD3vmc hD3vmlip
      hD3vc hD3vlip hcompat hcurry hΨcurve hΨ0 t₀⟩
  · intro z
    have heq := eq_of_isIntegralCurve_of_eq_at hv (hΨcurve (Φ z t)) (hΦ z) (hΨ0 (Φ z t)) t₀
    show Ψ (Φ z t) t₀ = z
    rw [heq]; exact h0 z
  · intro w
    have heq := eq_of_isIntegralCurve_of_eq_at hv (hΦ (Ψ w t₀)) (hΨcurve w) (h0 (Ψ w t₀)) t
    show Φ (Ψ w t₀) t = w
    rw [heq]; exact hΨ0 w

/-- **Field-data-only `C³` flow-diffeomorphism existence.**  From the `C^{3,1}` jet of the field `v`
alone (no pre-supplied flow family), there is a flow family `Φ` anchored at `t₀`, an integral curve
of `v`, whose time-`t` map is a `C³` diffeomorphism of the state space for *every* `t`: bijective
with reverse-time inverse `ψ`, both `ContDiff ℝ 3`.  This is the fully unconditional entry point —
the Banach/chart-level statement a compact-manifold gauge-flow constructor (Item 2) consumes. -/
theorem exists_flow_contDiff_three_diffeomorph [CompleteSpace E]
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
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) ∧
      ∀ t, ∃ ψ : E → E, Function.LeftInverse ψ (fun z => Φ z t) ∧
        Function.RightInverse ψ (fun z => Φ z t) ∧
        ContDiff ℝ 3 (fun z => Φ z t) ∧ ContDiff ℝ 3 ψ := by
  obtain ⟨Φ, h0, hΦ⟩ := exists_flow_family hv hvc
  refine ⟨Φ, h0, hΦ, fun t => ?_⟩
  exact exists_contDiff_three_diffeomorph_flow_apply
    hv hvc hDv hDvc hDvlip hD2vc hD2vcc hD2vclip hD2vmlip hD3vm hD3vmc hD3vmlip
    hD3vc hD3vlip hcompat hcurry hΦ h0 t

end

end SmoothDependenceCk
end AnalyticPDE
end RicciFlow
