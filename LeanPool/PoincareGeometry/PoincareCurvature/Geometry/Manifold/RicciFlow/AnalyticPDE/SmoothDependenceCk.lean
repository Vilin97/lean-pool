/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
/-!
# Smooth dependence of ODE flows on initial data — Lipschitz (`C^{0,1}`) base layer

This module begins the missing upstream theory needed by roadmap point 4,
Items 1 and 2: *dependence of the flow of a vector field on the initial
condition*.  Mathlib v4.29.1 provides Grönwall trajectory estimates and
local existence of integral curves, but the flow's dependence on the initial
point — the `C^k` regularity that the compact-manifold gauge flow ultimately
consumes — is not available.

This file proves the base (`C^0` / Lipschitz, i.e. `C^{0,1}`) layer of that
tower for *global* integral curves of a uniformly (in time) Lipschitz vector
field on a real Banach space:

* `isIntegralCurve_comp_neg`  — the time-reversed curve is an integral curve of
  the time-reversed field (an isometry-Lipschitz field with the same constant);
* `dist_le_of_isIntegralCurve_of_le` — the **forward** exponential dependence
  bound, packaging Mathlib's `dist_le_of_trajectories_ODE` in `IsIntegralCurve`
  form;
* `dist_le_of_isIntegralCurve` — the **two-sided** bound
  `dist (f t) (g t) ≤ dist (f t₀) (g t₀) · exp (K · |t - t₀|)`, obtained from the
  forward bound applied to the time-reversed curves (Mathlib only supplies the
  forward, `t ≥ t₀`, half);
* `dist_le_of_isIntegralCurve_of_abs_le` — a uniform Lipschitz-in-initial-data
  bound valid on a symmetric compact time interval;
* `eq_of_isIntegralCurve_of_eq` — the resulting global uniqueness of an integral
  curve through a given point.

Everything here is proved from Mathlib's Banach-level ODE results; no PDE or
manifold content is used.  Higher (`C^1`, …, `C^k`) dependence is deferred to
subsequent layers.
-/

@[expose] public noncomputable section

open Set
open scoped Topology NNReal

namespace RicciFlow
namespace AnalyticPDE
namespace SmoothDependenceCk

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {v : ℝ → E → E} {K : ℝ≥0} {f g : ℝ → E} {t₀ t : ℝ}

/-- If `f` is a global integral curve of `v`, then the time-reversed curve
`s ↦ f (-s)` is a global integral curve of the time-reversed vector field
`(s, x) ↦ -(v (-s) x)`.  This is the algebraic core of the backward-in-time
Grönwall estimate. -/
theorem isIntegralCurve_comp_neg (hf : IsIntegralCurve f v) :
    IsIntegralCurve (fun s => f (-s)) (fun s x => -(v (-s) x)) := by
  intro t
  have h2 : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) t := hasDerivAt_neg' t
  have hcomp : HasDerivAt (f ∘ fun s : ℝ => -s) ((-1 : ℝ) • v (-t) (f (-t))) t :=
    HasDerivAt.scomp t (hf (-t)) h2
  simpa only [Function.comp_def, neg_one_smul] using hcomp

/-- **Forward** exponential dependence on initial data: two global integral
curves of a uniformly (in time) `K`-Lipschitz vector field satisfy
`dist (f t) (g t) ≤ dist (f t₀) (g t₀) · exp (K · (t - t₀))` for `t₀ ≤ t`.
This repackages Mathlib's `dist_le_of_trajectories_ODE` in `IsIntegralCurve`
form. -/
theorem dist_le_of_isIntegralCurve_of_le
    (hv : ∀ t, LipschitzWith K (v t)) (hf : IsIntegralCurve f v) (hg : IsIntegralCurve g v)
    (h : t₀ ≤ t) :
    dist (f t) (g t) ≤ dist (f t₀) (g t₀) * Real.exp ((K : ℝ) * (t - t₀)) := by
  have key := dist_le_of_trajectories_ODE (a := t₀) (b := t) (δ := dist (f t₀) (g t₀)) hv
    hf.continuous.continuousOn (fun s _ => (hf s).hasDerivWithinAt)
    hg.continuous.continuousOn (fun s _ => (hg s).hasDerivWithinAt) le_rfl
  exact key t ⟨h, le_rfl⟩

/-- **Two-sided** exponential dependence on initial data:
`dist (f t) (g t) ≤ dist (f t₀) (g t₀) · exp (K · |t - t₀|)` for *all* `t`.
Mathlib supplies only the forward (`t ≥ t₀`) half; the backward half is obtained
by applying the forward bound to the time-reversed integral curves. -/
theorem dist_le_of_isIntegralCurve
    (hv : ∀ t, LipschitzWith K (v t)) (hf : IsIntegralCurve f v) (hg : IsIntegralCurve g v)
    (t₀ t : ℝ) :
    dist (f t) (g t) ≤ dist (f t₀) (g t₀) * Real.exp ((K : ℝ) * |t - t₀|) := by
  rcases le_total t₀ t with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact dist_le_of_isIntegralCurve_of_le hv hf hg h
  · have hw : ∀ s, LipschitzWith K (fun x => -(v (-s) x)) := by
      intro s
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      rw [dist_neg_neg]
      exact (hv (-s)).dist_le_mul a b
    have hfn := isIntegralCurve_comp_neg hf
    have hgn := isIntegralCurve_comp_neg hg
    have key := dist_le_of_isIntegralCurve_of_le hw hfn hgn (neg_le_neg h)
    simp only [neg_neg] at key
    rw [abs_of_nonpos (sub_nonpos.mpr h)]
    have harg : (K : ℝ) * -(t - t₀) = (K : ℝ) * (-t - -t₀) := by ring
    rw [harg]
    exact key

/-- Uniform Lipschitz dependence on initial data over a symmetric compact time
interval: if `|t - t₀| ≤ T` then
`dist (f t) (g t) ≤ dist (f t₀) (g t₀) · exp (K · T)`. -/
theorem dist_le_of_isIntegralCurve_of_abs_le
    (hv : ∀ t, LipschitzWith K (v t)) (hf : IsIntegralCurve f v) (hg : IsIntegralCurve g v)
    {T : ℝ} (hT : |t - t₀| ≤ T) :
    dist (f t) (g t) ≤ dist (f t₀) (g t₀) * Real.exp ((K : ℝ) * T) := by
  refine (dist_le_of_isIntegralCurve hv hf hg t₀ t).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ dist_nonneg
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hT K.coe_nonneg)

/-- Global uniqueness of an integral curve through a given point: two global
integral curves of a uniformly Lipschitz vector field that agree at one time
agree everywhere. -/
theorem eq_of_isIntegralCurve_of_eq
    (hv : ∀ t, LipschitzWith K (v t)) (hf : IsIntegralCurve f v) (hg : IsIntegralCurve g v)
    (h0 : f t₀ = g t₀) (t : ℝ) : f t = g t := by
  have hb := dist_le_of_isIntegralCurve hv hf hg t₀ t
  rw [h0, dist_self, zero_mul] at hb
  exact dist_le_zero.mp hb

/-- Uniqueness from agreement at *any* single time: two global integral curves of a
uniformly Lipschitz field that coincide at one time `t₁` coincide everywhere. -/
theorem eq_of_isIntegralCurve_of_eq_at
    (hv : ∀ t, LipschitzWith K (v t)) (hf : IsIntegralCurve f v) (hg : IsIntegralCurve g v)
    {t₁ : ℝ} (h1 : f t₁ = g t₁) (t : ℝ) : f t = g t := by
  have hb := dist_le_of_isIntegralCurve hv hf hg t₁ t
  rw [h1, dist_self, zero_mul] at hb
  exact dist_le_zero.mp hb

/-!
## Stability under perturbation of the vector field

Continuous dependence of an integral curve on the *field* it solves: if two curves solve
uniformly `ε`-close fields (one of them uniformly `K`-Lipschitz), their separation is
controlled by the Grönwall bound.  This is the driver behind "the flow depends
continuously on the vector field", used to transfer regularity of the DeTurck field to
the DeTurck flow.
-/

/-- **Forward stability under perturbation of the vector field.**  If `f` is an integral
curve of the uniformly `K`-Lipschitz field `v`, `g` is an integral curve of a field `w`
that stays within `ε` of `v` uniformly, then for `t₀ ≤ t`,
`dist (f t) (g t) ≤ gronwallBound (dist (f t₀) (g t₀)) K ε (t - t₀)`. -/
theorem dist_le_of_isIntegralCurve_perturb_of_le {w : ℝ → E → E} {ε : ℝ}
    (hv : ∀ t, LipschitzWith K (v t)) (hf : IsIntegralCurve f v) (hg : IsIntegralCurve g w)
    (hvw : ∀ t x, dist (v t x) (w t x) ≤ ε) (h : t₀ ≤ t) :
    dist (f t) (g t) ≤ gronwallBound (dist (f t₀) (g t₀)) (K : ℝ) ε (t - t₀) := by
  have key := dist_le_of_approx_trajectories_ODE (a := t₀) (b := t)
    (εf := 0) (εg := ε) (δ := dist (f t₀) (g t₀)) hv
    hf.continuous.continuousOn (fun s _ => (hf s).hasDerivWithinAt)
    (fun s _ => le_of_eq (dist_self _))
    hg.continuous.continuousOn (fun s _ => (hg s).hasDerivWithinAt)
    (fun s _ => by rw [dist_comm]; exact hvw s (g s)) le_rfl
  have hb := key t ⟨h, le_rfl⟩
  rwa [zero_add] at hb

/-- **Two-sided stability under perturbation of the vector field.**  If `f` is an integral
curve of the uniformly `K`-Lipschitz field `v` and `g` is an integral curve of a field `w`
that stays within `ε` of `v` uniformly, then for *all* `t`,
`dist (f t) (g t) ≤ gronwallBound (dist (f t₀) (g t₀)) K ε |t - t₀|`.  Mathlib's Grönwall
approximation lemma only supplies the forward (`t ≥ t₀`) half; the backward half comes
from applying the forward bound to the time-reversed curves, whose fields are still
`K`-Lipschitz and `ε`-close.  This is the two-sided *continuous dependence on the field*
that transfers regularity of the DeTurck vector field to the DeTurck flow. -/
theorem dist_le_of_isIntegralCurve_perturb {w : ℝ → E → E} {ε : ℝ}
    (hv : ∀ t, LipschitzWith K (v t)) (hf : IsIntegralCurve f v) (hg : IsIntegralCurve g w)
    (hvw : ∀ t x, dist (v t x) (w t x) ≤ ε) (t₀ t : ℝ) :
    dist (f t) (g t) ≤ gronwallBound (dist (f t₀) (g t₀)) (K : ℝ) ε |t - t₀| := by
  rcases le_total t₀ t with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact dist_le_of_isIntegralCurve_perturb_of_le hv hf hg hvw h
  · have hw : ∀ s, LipschitzWith K (fun x => -(v (-s) x)) := by
      intro s
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      rw [dist_neg_neg]
      exact (hv (-s)).dist_le_mul a b
    have hfn := isIntegralCurve_comp_neg hf
    have hgn := isIntegralCurve_comp_neg hg
    have hvw' : ∀ s x, dist (-(v (-s) x)) (-(w (-s) x)) ≤ ε := by
      intro s x
      rw [dist_neg_neg]
      exact hvw (-s) x
    have key := dist_le_of_isIntegralCurve_perturb_of_le hw hfn hgn hvw' (neg_le_neg h)
    simp only [neg_neg] at key
    rw [abs_of_nonpos (sub_nonpos.mpr h)]
    have harg : -t - -t₀ = -(t - t₀) := by ring
    rwa [harg] at key

/-!
## The flow map is exponentially Lipschitz in the initial value

Packaging the two-sided Grönwall bound for a *flow family* `Φ : E → ℝ → E`, where for
each initial value `x` the curve `Φ x` is the integral curve of `v` anchored at
`Φ x t₀ = x`.  This is exactly the `C^0` dependence-on-initial-data statement that the
compact-manifold gauge flow (Item 2) consumes: the time-`t` flow map `x ↦ Φ x t` is
Lipschitz, with an explicit exponential constant, uniformly on compact time intervals.
-/

variable {Φ : E → ℝ → E}

/-- Two-sided dependence bound for a flow family: if for each initial value `x` the
curve `Φ x` is an integral curve of the uniformly `K`-Lipschitz field `v` anchored at
`Φ x t₀ = x`, then `dist (Φ x t) (Φ y t) ≤ dist x y · exp (K · |t - t₀|)`. -/
theorem dist_flow_apply_le
    (hv : ∀ t, LipschitzWith K (v t)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (x y : E) (t : ℝ) :
    dist (Φ x t) (Φ y t) ≤ dist x y * Real.exp ((K : ℝ) * |t - t₀|) := by
  have hb := dist_le_of_isIntegralCurve hv (hΦ x) (hΦ y) t₀ t
  rwa [h0 x, h0 y] at hb

/-- The time-`t` flow map `x ↦ Φ x t` is Lipschitz with constant `exp (K · |t - t₀|)`. -/
theorem lipschitzWith_flow_apply
    (hv : ∀ t, LipschitzWith K (v t)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (t : ℝ) :
    LipschitzWith (Real.exp ((K : ℝ) * |t - t₀|)).toNNReal (fun x => Φ x t) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (Real.exp_pos _).le]
  calc dist (Φ x t) (Φ y t) ≤ dist x y * Real.exp ((K : ℝ) * |t - t₀|) :=
        dist_flow_apply_le hv hΦ h0 x y t
    _ = Real.exp ((K : ℝ) * |t - t₀|) * dist x y := mul_comm _ _

/-- The time-`t` flow map `x ↦ Φ x t` is continuous in the initial value. -/
theorem continuous_flow_apply
    (hv : ∀ t, LipschitzWith K (v t)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (t : ℝ) :
    Continuous (fun x => Φ x t) :=
  (lipschitzWith_flow_apply hv hΦ h0 t).continuous

/-- The time-`t` flow map `x ↦ Φ x t` is injective: distinct initial values stay distinct
under the flow.  (This is the injectivity half of the flow being a diffeomorphism onto its
image, consumed by the gauge-flow diffeomorphism family of Item 2.) -/
theorem injective_flow_apply
    (hv : ∀ t, LipschitzWith K (v t)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (t : ℝ) :
    Function.Injective (fun x => Φ x t) := by
  intro x y hxy
  have hb := eq_of_isIntegralCurve_of_eq_at hv (hΦ x) (hΦ y) hxy t₀
  rwa [h0 x, h0 y] at hb

/-- Uniform Lipschitz dependence of the flow map on a symmetric compact time interval:
whenever `|t - t₀| ≤ T`, the time-`t` flow map is Lipschitz with the single constant
`exp (K · T)`. -/
theorem lipschitzWith_flow_apply_of_abs_le
    (hv : ∀ t, LipschitzWith K (v t)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) {T : ℝ} (hT : |t - t₀| ≤ T) :
    LipschitzWith (Real.exp ((K : ℝ) * T)).toNNReal (fun x => Φ x t) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (Real.exp_pos _).le, mul_comm (Real.exp ((K : ℝ) * T)) (dist x y)]
  have hxy := dist_le_of_isIntegralCurve_of_abs_le hv (hΦ x) (hΦ y) hT
  rwa [h0 x, h0 y] at hxy

/-- **Joint continuity of the flow.**  For a flow family `Φ` of the uniformly
`K`-Lipschitz field `v` anchored at `Φ x t₀ = x`, the map `(t, x) ↦ Φ x t` is jointly
continuous on `ℝ × E`.  Continuity in the initial value is uniform (Lipschitz with the
exponential constant) and continuity in time comes from each curve being an integral
curve; the two combine by a triangle-inequality squeeze. -/
theorem continuous_flow
    (hv : ∀ t, LipschitzWith K (v t)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) :
    Continuous (fun p : ℝ × E => Φ p.2 p.1) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t₁, x₁⟩
  have key : Filter.Tendsto (fun p : ℝ × E => dist (Φ p.2 p.1) (Φ x₁ t₁))
      (nhds (t₁, x₁)) (nhds 0) := by
    refine squeeze_zero (fun p => dist_nonneg) (g := fun p : ℝ × E =>
        dist p.2 x₁ * Real.exp ((K : ℝ) * |p.1 - t₀|) + dist (Φ x₁ p.1) (Φ x₁ t₁))
        (fun p => ?_) ?_
    · calc dist (Φ p.2 p.1) (Φ x₁ t₁)
          ≤ dist (Φ p.2 p.1) (Φ x₁ p.1) + dist (Φ x₁ p.1) (Φ x₁ t₁) := dist_triangle _ _ _
        _ ≤ dist p.2 x₁ * Real.exp ((K : ℝ) * |p.1 - t₀|) + dist (Φ x₁ p.1) (Φ x₁ t₁) := by
            gcongr
            exact dist_flow_apply_le hv hΦ h0 p.2 x₁ p.1
    · have hd : Filter.Tendsto (fun p : ℝ × E => dist p.2 x₁) (nhds (t₁, x₁)) (nhds 0) := by
        have hcont : Continuous (fun p : ℝ × E => dist p.2 x₁) :=
          continuous_snd.dist continuous_const
        simpa using hcont.tendsto (t₁, x₁)
      have he : Filter.Tendsto (fun p : ℝ × E => Real.exp ((K : ℝ) * |p.1 - t₀|))
          (nhds (t₁, x₁)) (nhds (Real.exp ((K : ℝ) * |t₁ - t₀|))) := by
        have hcont : Continuous (fun p : ℝ × E => Real.exp ((K : ℝ) * |p.1 - t₀|)) :=
          Real.continuous_exp.comp
            (continuous_const.mul (continuous_fst.sub continuous_const).abs)
        simpa using hcont.tendsto (t₁, x₁)
      have hB2 : Filter.Tendsto (fun p : ℝ × E => dist (Φ x₁ p.1) (Φ x₁ t₁))
          (nhds (t₁, x₁)) (nhds 0) := by
        have hcont : Continuous (fun p : ℝ × E => dist (Φ x₁ p.1) (Φ x₁ t₁)) :=
          ((hΦ x₁).continuous.comp continuous_fst).dist continuous_const
        simpa using hcont.tendsto (t₁, x₁)
      have hB1 := hd.mul he
      simpa using (hB1.add hB2)
  have hiff := tendsto_iff_dist_tendsto_zero (a := Φ x₁ t₁)
    (f := fun p : ℝ × E => Φ p.2 p.1) (x := nhds (t₁, x₁))
  exact hiff.mpr key

/-!
## The flow map is a bi-Lipschitz uniform embedding in the initial value

The two-sided distance bound also yields a *lower* exponential control: the flow
cannot contract distances faster than `exp (-K · |t - t₀|)`.  Combined with the
Lipschitz upper bound this exhibits the time-`t` flow map as a **bi-Lipschitz**
(indeed a uniform) embedding onto its image — the `C^0` shadow of the
"diffeomorphism onto its image" property consumed by the compact-manifold gauge
flow of Item 2.  Antilipschitz packaging is the quantitative statement that the
inverse of the flow map (on its image) is itself Lipschitz with the reciprocal
exponential constant.
-/

/-- **Lower** two-sided exponential dependence for integral curves:
`dist (f t₀) (g t₀) · exp (-K · |t - t₀|) ≤ dist (f t) (g t)`.  Obtained from the
two-sided upper bound `dist_le_of_isIntegralCurve` with the anchor and evaluation
times swapped: the flow run *backward* from time `t` to `t₀` can expand
`dist (f t) (g t)` by at most `exp (K · |t - t₀|)`. -/
theorem dist_ge_of_isIntegralCurve
    (hv : ∀ t, LipschitzWith K (v t)) (hf : IsIntegralCurve f v) (hg : IsIntegralCurve g v)
    (t₀ t : ℝ) :
    dist (f t₀) (g t₀) * Real.exp (-(K : ℝ) * |t - t₀|) ≤ dist (f t) (g t) := by
  have hb := dist_le_of_isIntegralCurve hv hf hg t t₀
  rw [abs_sub_comm] at hb
  calc dist (f t₀) (g t₀) * Real.exp (-(K : ℝ) * |t - t₀|)
      ≤ dist (f t) (g t) * Real.exp ((K : ℝ) * |t - t₀|) * Real.exp (-(K : ℝ) * |t - t₀|) :=
        mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    _ = dist (f t) (g t) := by
        rw [mul_assoc, ← Real.exp_add,
          show (K : ℝ) * |t - t₀| + -(K : ℝ) * |t - t₀| = 0 by ring, Real.exp_zero, mul_one]

/-- Lower exponential dependence on initial data for a flow family:
`dist x y · exp (-K · |t - t₀|) ≤ dist (Φ x t) (Φ y t)`. -/
theorem dist_flow_apply_ge
    (hv : ∀ t, LipschitzWith K (v t)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (x y : E) (t : ℝ) :
    dist x y * Real.exp (-(K : ℝ) * |t - t₀|) ≤ dist (Φ x t) (Φ y t) := by
  have hb := dist_ge_of_isIntegralCurve hv (hΦ x) (hΦ y) t₀ t
  rwa [h0 x, h0 y] at hb

/-- The time-`t` flow map `x ↦ Φ x t` is **antilipschitz** with constant
`exp (K · |t - t₀|)`: distinct initial values are separated at least
`exp (-K · |t - t₀|)` as far after flowing.  This is the quantitative injectivity
that upgrades `injective_flow_apply` to a bi-Lipschitz embedding. -/
theorem antilipschitzWith_flow_apply
    (hv : ∀ t, LipschitzWith K (v t)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (t : ℝ) :
    AntilipschitzWith (Real.exp ((K : ℝ) * |t - t₀|)).toNNReal (fun x => Φ x t) := by
  refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
  rw [Real.coe_toNNReal _ (Real.exp_pos _).le]
  have hb := dist_flow_apply_ge hv hΦ h0 x y t
  have key := mul_le_mul_of_nonneg_right hb (Real.exp_pos ((K : ℝ) * |t - t₀|)).le
  rw [mul_assoc, ← Real.exp_add,
    show -(K : ℝ) * |t - t₀| + (K : ℝ) * |t - t₀| = 0 by ring, Real.exp_zero, mul_one] at key
  exact key.trans_eq (mul_comm _ _)

/-- Uniform antilipschitz dependence of the flow map on a symmetric compact time
interval: whenever `|t - t₀| ≤ T`, the time-`t` flow map is antilipschitz with the
single constant `exp (K · T)`. -/
theorem antilipschitzWith_flow_apply_of_abs_le
    (hv : ∀ t, LipschitzWith K (v t)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) {T : ℝ} (hT : |t - t₀| ≤ T) :
    AntilipschitzWith (Real.exp ((K : ℝ) * T)).toNNReal (fun x => Φ x t) := by
  refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
  rw [Real.coe_toNNReal _ (Real.exp_pos _).le]
  have hb := dist_flow_apply_ge hv hΦ h0 x y t
  have key := mul_le_mul_of_nonneg_right hb (Real.exp_pos ((K : ℝ) * |t - t₀|)).le
  rw [mul_assoc, ← Real.exp_add,
    show -(K : ℝ) * |t - t₀| + (K : ℝ) * |t - t₀| = 0 by ring, Real.exp_zero, mul_one] at key
  refine key.trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ dist_nonneg
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hT K.coe_nonneg)

/-- **The time-`t` flow map is a uniform embedding onto its image.**  Being both
Lipschitz (`lipschitzWith_flow_apply`) and antilipschitz (`antilipschitzWith_flow_apply`)
in the initial value, `x ↦ Φ x t` is a bi-Lipschitz — hence uniform — embedding.
This is the `C^0` incarnation of "the gauge flow is a diffeomorphism onto its
image" that Item 2 consumes. -/
theorem isUniformEmbedding_flow_apply
    (hv : ∀ t, LipschitzWith K (v t)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (t : ℝ) :
    IsUniformEmbedding (fun x => Φ x t) :=
  (antilipschitzWith_flow_apply hv hΦ h0 t).isUniformEmbedding
    (lipschitzWith_flow_apply hv hΦ h0 t).uniformContinuous

/-- The time-`t` flow map is a topological embedding onto its image. -/
theorem isEmbedding_flow_apply
    (hv : ∀ t, LipschitzWith K (v t)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (t : ℝ) :
    Topology.IsEmbedding (fun x => Φ x t) :=
  (isUniformEmbedding_flow_apply hv hΦ h0 t).isEmbedding

/-!
## Flow-family packaging of uniqueness and field-perturbation stability

The two-sided perturbation bound and the uniqueness lemma, packaged for two flow
*families* `Φ, Ψ` anchored at the same initial value.  With `ε = 0` the
perturbation bound degenerates to uniqueness of the flow family; with `ε > 0` it is
the quantitative "two flows of `ε`-close fields stay close" that transfers
regularity of the DeTurck vector field to the DeTurck flow (Item 3 / Item 2).
-/

/-- **Two flow families of uniformly `ε`-close fields, anchored at the same initial
value, stay close.**  If `Φ x` solves the uniformly `K`-Lipschitz field `v` and `Ψ x`
solves an `ε`-close field `w`, both with `Φ x t₀ = Ψ x t₀ = x`, then
`dist (Φ x t) (Ψ x t) ≤ gronwallBound 0 K ε |t - t₀|` for all `t`. -/
theorem dist_flow_perturb_le {w : ℝ → E → E} {Ψ : E → ℝ → E} {ε : ℝ}
    (hv : ∀ t, LipschitzWith K (v t))
    (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (hΨ : ∀ x, IsIntegralCurve (Ψ x) w)
    (hvw : ∀ t x, dist (v t x) (w t x) ≤ ε)
    (h0Φ : ∀ x, Φ x t₀ = x) (h0Ψ : ∀ x, Ψ x t₀ = x) (x : E) (t : ℝ) :
    dist (Φ x t) (Ψ x t) ≤ gronwallBound 0 (K : ℝ) ε |t - t₀| := by
  have hb := dist_le_of_isIntegralCurve_perturb hv (hΦ x) (hΨ x) hvw t₀ t
  rwa [h0Φ x, h0Ψ x, dist_self] at hb

/-- **Uniqueness of the flow family.**  Any two flow families of the *same* uniformly
`K`-Lipschitz field anchored at `Φ x t₀ = Ψ x t₀ = x` agree everywhere. -/
theorem flow_eq_of_isIntegralCurve {Ψ : E → ℝ → E}
    (hv : ∀ t, LipschitzWith K (v t))
    (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (hΨ : ∀ x, IsIntegralCurve (Ψ x) v)
    (h0Φ : ∀ x, Φ x t₀ = x) (h0Ψ : ∀ x, Ψ x t₀ = x) (x : E) (t : ℝ) :
    Φ x t = Ψ x t := by
  have h0 : Φ x t₀ = Ψ x t₀ := by rw [h0Φ x, h0Ψ x]
  exact eq_of_isIntegralCurve_of_eq hv (hΦ x) (hΨ x) h0 t

/-!
## Time regularity of the flow under a uniform velocity bound

The `continuous_flow` result gives *joint* continuity of `(t, x) ↦ Φ x t` but no
quantitative modulus in the time direction.  When the field is uniformly bounded
along the curve, `‖v t (f t)‖ ≤ M`, the integral curve is `M`-Lipschitz in time
(its derivative is the velocity, of norm `≤ M`).  This is the time-direction
companion of the exponential Lipschitz-in-initial-data bound, and together they
give a joint Lipschitz modulus of the flow on compact time intervals.
-/

/-- An integral curve of a field whose velocity along the curve is uniformly bounded by
`M` is `M`-Lipschitz in time: `dist (f s) (f t) ≤ M · dist s t`.  The curve's derivative
is `v t (f t)`, of norm `≤ M`, so the mean value inequality applies. -/
theorem lipschitzWith_of_isIntegralCurve_of_norm_le {M : ℝ}
    (hf : IsIntegralCurve f v) (hM : 0 ≤ M) (hvb : ∀ t, ‖v t (f t)‖ ≤ M) :
    LipschitzWith M.toNNReal f := by
  have hdiff : Differentiable ℝ f := fun t => (hf t).differentiableAt
  refine lipschitzWith_of_nnnorm_deriv_le hdiff fun t => ?_
  rw [(hf t).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal M hM]
  exact hvb t

/-- Each curve of a flow family whose velocity is uniformly bounded by `M` along the flow
is `M`-Lipschitz in time. -/
theorem lipschitzWith_flow_of_norm_le {M : ℝ}
    (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (hM : 0 ≤ M)
    (hvb : ∀ x t, ‖v t (Φ x t)‖ ≤ M) (x : E) :
    LipschitzWith M.toNNReal (Φ x) :=
  lipschitzWith_of_isIntegralCurve_of_norm_le (hΦ x) hM (hvb x)

/-- **Joint Lipschitz modulus of the flow on a symmetric compact time interval.**  Under a
uniform velocity bound `M` and with `|t - t₀|, |s - t₀| ≤ T`, the flow separation is
controlled by the time gap (rate `M`) plus the initial-value gap (rate `exp (K · T)`):
`dist (Φ x t) (Φ y s) ≤ M · |t - s| + exp (K · T) · dist x y`.  This is the quantitative
strengthening of `continuous_flow` combining time- and initial-value-regularity. -/
theorem dist_flow_le_of_norm_le {M : ℝ}
    (hv : ∀ t, LipschitzWith K (v t)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (hM : 0 ≤ M) (hvb : ∀ x t, ‖v t (Φ x t)‖ ≤ M)
    {T : ℝ} (x y : E) {s t : ℝ} (hs : |s - t₀| ≤ T) :
    dist (Φ x t) (Φ y s) ≤ M * |t - s| + Real.exp ((K : ℝ) * T) * dist x y := by
  calc dist (Φ x t) (Φ y s)
      ≤ dist (Φ x t) (Φ x s) + dist (Φ x s) (Φ y s) := dist_triangle _ _ _
    _ ≤ M * |t - s| + Real.exp ((K : ℝ) * T) * dist x y := by
        gcongr
        · have hL := lipschitzWith_flow_of_norm_le hΦ hM hvb x
          have hd := hL.dist_le_mul t s
          rwa [Real.coe_toNNReal M hM, Real.dist_eq] at hd
        · have hLip := lipschitzWith_flow_apply_of_abs_le hv hΦ h0 hs
          have hd := hLip.dist_le_mul x y
          rwa [Real.coe_toNNReal _ (Real.exp_pos _).le] at hd

/-!
## First brick of the `C^1` layer: the linear (variational) field is Lipschitz

Toward *differentiable* dependence on initial data one linearises: the flow
derivative `D_x Φ_t` is expected to solve the operator-valued **variational** ODE
`W'(t) = A(t) ∘ W(t)`, where `A(t) = D_x v (t, Φ_t x)` is the spatial derivative of
the field along the flow.  The algebraic core underpinning well-posedness of that
linear ODE is that, for a uniformly bounded operator path `A : ℝ → (E →L[ℝ] E)`
with `‖A t‖ ≤ K`, the associated linear vector field on the operator Banach space
`E →L[ℝ] E`, namely `W ↦ (A t).comp W`, is `K`-Lipschitz in `W`.  Uniqueness and
the exponential a priori bound for the variational ODE then follow from the `C^0`
dependence lemmas above, now instantiated on the Banach space of operators.  This
opens the `C^1` layer: the object on which differentiable dependence is built is
in place and well-posed. -/

/-- The linear (variational) vector field `W ↦ (A t).comp W` on the operator Banach space
`E →L[ℝ] E`, associated to an operator path `A`.  Its integral curves are the solutions of
the variational equation `W'(t) = A(t) ∘ W(t)`. -/
def variationalField (A : ℝ → (E →L[ℝ] E)) :
    ℝ → (E →L[ℝ] E) → (E →L[ℝ] E) :=
  fun t W => (A t).comp W

/-- **The variational field is Lipschitz.**  Under a uniform operator-norm bound
`‖A t‖ ≤ K`, the linear field `W ↦ (A t).comp W` is `K`-Lipschitz in `W` — the core
estimate behind well-posedness of the variational ODE.  (Submultiplicativity of the
operator norm: `‖A t ∘ (W₁ - W₂)‖ ≤ ‖A t‖ · ‖W₁ - W₂‖ ≤ K · ‖W₁ - W₂‖`.) -/
theorem lipschitzWith_variationalField {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) (t : ℝ) :
    LipschitzWith K (variationalField A t) := by
  refine LipschitzWith.of_dist_le_mul fun W₁ W₂ => ?_
  simp only [variationalField, dist_eq_norm, ← ContinuousLinearMap.comp_sub]
  calc ‖(A t).comp (W₁ - W₂)‖
      ≤ ‖A t‖ * ‖W₁ - W₂‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (K : ℝ) * ‖W₁ - W₂‖ := by
        gcongr
        exact_mod_cast hA t

/-- **Uniqueness for the variational ODE.**  Two solutions of the linear variational ODE
`W'(t) = (A t).comp (W t)` with `‖A t‖ ≤ K` that agree at one time agree everywhere. -/
theorem variational_eq_of_isIntegralCurve {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) {W₁ W₂ : ℝ → (E →L[ℝ] E)}
    (h1 : IsIntegralCurve W₁ (variationalField A))
    (h2 : IsIntegralCurve W₂ (variationalField A))
    {t₁ : ℝ} (h : W₁ t₁ = W₂ t₁) (t : ℝ) : W₁ t = W₂ t :=
  eq_of_isIntegralCurve_of_eq_at (fun s => lipschitzWith_variationalField hA s) h1 h2 h t

/-- **A priori exponential bound for the variational ODE.**  Two solutions of
`W'(t) = (A t).comp (W t)` with `‖A t‖ ≤ K` satisfy
`dist (W₁ t) (W₂ t) ≤ dist (W₁ t₀) (W₂ t₀) · exp (K · |t - t₀|)`. -/
theorem dist_variational_le {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) {W₁ W₂ : ℝ → (E →L[ℝ] E)}
    (h1 : IsIntegralCurve W₁ (variationalField A))
    (h2 : IsIntegralCurve W₂ (variationalField A))
    (t₀ t : ℝ) :
    dist (W₁ t) (W₂ t) ≤ dist (W₁ t₀) (W₂ t₀) * Real.exp ((K : ℝ) * |t - t₀|) :=
  dist_le_of_isIntegralCurve (fun s => lipschitzWith_variationalField hA s) h1 h2 t₀ t

/-- The **vector** variational field `u ↦ A t u` on `E`, associated to an operator path `A`.
Its integral curves solve the vector variational equation `u'(t) = A(t) (u(t))` satisfied
by the directional derivative `∂_h Φ_t` (evaluation of the fundamental solution on a fixed
direction) — the form of the linearised equation consumed by the tensor time-derivative
chain rule of Item 1. -/
def variationalFieldVec (A : ℝ → (E →L[ℝ] E)) : ℝ → E → E :=
  fun t u => A t u

/-- **The vector variational field is Lipschitz.**  Under a uniform bound `‖A t‖ ≤ K`, the
linear field `u ↦ A t u` is `K`-Lipschitz in `u`. -/
theorem lipschitzWith_variationalFieldVec {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) (t : ℝ) :
    LipschitzWith K (variationalFieldVec A t) := by
  refine LipschitzWith.of_dist_le_mul fun u₁ u₂ => ?_
  simp only [variationalFieldVec, dist_eq_norm, ← map_sub]
  calc ‖(A t) (u₁ - u₂)‖
      ≤ ‖A t‖ * ‖u₁ - u₂‖ := (A t).le_opNorm _
    _ ≤ (K : ℝ) * ‖u₁ - u₂‖ := by
        gcongr
        exact_mod_cast hA t

/-- **Uniqueness for the vector variational ODE.**  Two solutions of `u'(t) = A(t) (u(t))`
with `‖A t‖ ≤ K` that agree at one time agree everywhere. -/
theorem variationalVec_eq_of_isIntegralCurve {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) {u₁ u₂ : ℝ → E}
    (h1 : IsIntegralCurve u₁ (variationalFieldVec A))
    (h2 : IsIntegralCurve u₂ (variationalFieldVec A))
    {t₁ : ℝ} (h : u₁ t₁ = u₂ t₁) (t : ℝ) : u₁ t = u₂ t :=
  eq_of_isIntegralCurve_of_eq_at (fun s => lipschitzWith_variationalFieldVec hA s) h1 h2 h t

/-- **A priori exponential bound for the vector variational ODE.**
`dist (u₁ t) (u₂ t) ≤ dist (u₁ t₀) (u₂ t₀) · exp (K · |t - t₀|)`. -/
theorem dist_variationalVec_le {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) {u₁ u₂ : ℝ → E}
    (h1 : IsIntegralCurve u₁ (variationalFieldVec A))
    (h2 : IsIntegralCurve u₂ (variationalFieldVec A))
    (t₀ t : ℝ) :
    dist (u₁ t) (u₂ t) ≤ dist (u₁ t₀) (u₂ t₀) * Real.exp ((K : ℝ) * |t - t₀|) :=
  dist_le_of_isIntegralCurve (fun s => lipschitzWith_variationalFieldVec hA s) h1 h2 t₀ t

/-- **The operator variational solution, evaluated on a fixed direction, solves the vector
variational ODE.**  If `W` solves `W'(t) = A(t) ∘ W(t)` (the fundamental-solution equation),
then for any `u₀` the curve `t ↦ W t u₀` solves `u'(t) = A(t) (u(t))`.  This links the
operator- and vector-valued variational equations: the directional derivative
`∂_{u₀} Φ_t = D_x Φ_t · u₀ = W t u₀` obeys the vector variational equation, via the chain
rule for the (continuous linear) evaluation map `L ↦ L u₀`. -/
theorem isIntegralCurve_variational_apply {A : ℝ → (E →L[ℝ] E)}
    {W : ℝ → (E →L[ℝ] E)} (hW : IsIntegralCurve W (variationalField A)) (u₀ : E) :
    IsIntegralCurve (fun t => W t u₀) (variationalFieldVec A) := by
  intro t
  have hcomp := (hW t).clm_apply (hasDerivAt_const t u₀)
  simpa only [variationalField, variationalFieldVec, ContinuousLinearMap.comp_apply,
    map_zero, add_zero] using hcomp

/-!
### Superposition principle for the vector variational ODE

Being *linear*, the vector variational equation `u'(t) = A(t) (u(t))` has a solution set
closed under addition and scalar multiplication.  This is exactly what makes the map
`u₀ ↦ (solution through u₀) t` — i.e. the directional derivative `u₀ ↦ D_x Φ_t · u₀` —
**linear in the direction `u₀`**, so that it assembles into the bounded operator
`D_x Φ_t ∈ E →L[ℝ] E`.
-/

/-- **Superposition (additivity).**  The sum of two solutions of the vector variational
ODE is again a solution. -/
theorem isIntegralCurve_variationalFieldVec_add {A : ℝ → (E →L[ℝ] E)} {u w : ℝ → E}
    (hu : IsIntegralCurve u (variationalFieldVec A))
    (hw : IsIntegralCurve w (variationalFieldVec A)) :
    IsIntegralCurve (fun t => u t + w t) (variationalFieldVec A) := by
  intro t
  have h := (hu t).add (hw t)
  have h' : HasDerivAt (fun s => u s + w s)
      (A t (u t) + A t (w t)) t :=
    h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun _ => rfl))
  simpa only [variationalFieldVec, map_add] using h'

/-- **Superposition (homogeneity).**  A scalar multiple of a solution of the vector
variational ODE is again a solution. -/
theorem isIntegralCurve_variationalFieldVec_smul {A : ℝ → (E →L[ℝ] E)} {u : ℝ → E} (c : ℝ)
    (hu : IsIntegralCurve u (variationalFieldVec A)) :
    IsIntegralCurve (fun t => c • u t) (variationalFieldVec A) := by
  intro t
  have h := (hu t).const_smul c
  have h' : HasDerivAt (fun s => c • u s) (c • A t (u t)) t :=
    h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun _ => rfl))
  simpa only [variationalFieldVec, map_smul] using h'

/-!
### The fundamental solution operator `D_x Φ_t` as a bounded operator

Combining the superposition principle with the `C^0` uniqueness
(`variationalVec_eq_of_isIntegralCurve`) and the exponential a priori bound
(`dist_flow_apply_le`), the time-`t` flow map of the *linear* vector variational field is
additive, homogeneous, and operator-norm bounded, so it assembles into an honest bounded
operator `E →L[ℝ] E` — the fundamental solution / resolvent `D_x Φ_t` predicted by the
variational equation `u'(t) = A(t) (u(t))`.  Here `Φ : E → ℝ → E` is any flow family of
`variationalFieldVec A` anchored at `Φ x t₀ = x`.  This is the concrete `E →L[ℝ] E` object
— linear in the initial direction and with an explicit exponential operator bound — that
the compact-manifold gauge flow (Item 2) and the tensor time-derivative chain rule
(Item 1) ultimately consume.
-/

/-- **Additivity of the linear flow map.**  For a flow family `Φ` of the vector variational
field `variationalFieldVec A` (with `‖A t‖ ≤ K`) anchored at `Φ x t₀ = x`, the time-`t` map
`x ↦ Φ x t` is additive.  (Both `Φ (x + y)` and `t ↦ Φ x t + Φ y t` solve the same linear
ODE — the latter by superposition — and agree at the anchor `t₀`, so they agree everywhere
by uniqueness.) -/
theorem flow_variationalFieldVec_add {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (x y : E) (t : ℝ) : Φ (x + y) t = Φ x t + Φ y t :=
  variationalVec_eq_of_isIntegralCurve hA (hΦ (x + y))
    (isIntegralCurve_variationalFieldVec_add (hΦ x) (hΦ y)) (t₁ := t₀) (by simp only [h0]) t

/-- **Homogeneity of the linear flow map.**  The time-`t` map `x ↦ Φ x t` commutes with
scalar multiplication: `Φ (c • x) t = c • Φ x t`. -/
theorem flow_variationalFieldVec_smul {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (c : ℝ) (x : E) (t : ℝ) : Φ (c • x) t = c • Φ x t :=
  variationalVec_eq_of_isIntegralCurve hA (hΦ (c • x))
    (isIntegralCurve_variationalFieldVec_smul c (hΦ x)) (t₁ := t₀) (by simp only [h0]) t

/-- **The linear flow map fixes the origin.**  `Φ 0 t = 0`: the zero direction has zero
directional derivative (the special case `c = 0` of homogeneity). -/
theorem flow_variationalFieldVec_zero {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) : Φ 0 t = 0 := by
  have h := flow_variationalFieldVec_smul hA hΦ h0 (0 : ℝ) (0 : E) t
  simpa using h

/-- **Operator bound for the linear flow map.**  `‖Φ x t‖ ≤ exp (K · |t - t₀|) · ‖x‖`,
obtained from the `C^0` two-sided Lipschitz bound `dist_flow_apply_le` applied between the
initial values `x` and `0` together with `Φ 0 t = 0`.  This is the operator-norm bound that
makes the fundamental solution a *bounded* linear map. -/
theorem norm_flow_variationalFieldVec_le {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (x : E) (t : ℝ) : ‖Φ x t‖ ≤ Real.exp ((K : ℝ) * |t - t₀|) * ‖x‖ := by
  have hb := dist_flow_apply_le (fun s => lipschitzWith_variationalFieldVec hA s) hΦ h0 x 0 t
  rw [flow_variationalFieldVec_zero hA hΦ h0 t, dist_zero_right, dist_zero_right] at hb
  calc ‖Φ x t‖ ≤ ‖x‖ * Real.exp ((K : ℝ) * |t - t₀|) := hb
    _ = Real.exp ((K : ℝ) * |t - t₀|) * ‖x‖ := mul_comm _ _

/-- **The fundamental solution operator `D_x Φ_t ∈ E →L[ℝ] E`.**  For a flow family `Φ` of
the linear vector variational field `variationalFieldVec A` (`‖A t‖ ≤ K`) anchored at
`Φ x t₀ = x`, the time-`t` flow map `x ↦ Φ x t` — additive, homogeneous, and bounded by
`exp (K · |t - t₀|)` — packaged as an honest bounded linear operator.  This is the concrete
resolvent / fundamental solution that the directional derivatives `∂_{u₀} Φ_t = W t u₀`
assemble into. -/
def fundamentalSolution {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) : E →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun x => Φ x t
      map_add' := fun x y => flow_variationalFieldVec_add hA hΦ h0 x y t
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        exact flow_variationalFieldVec_smul hA hΦ h0 c x t }
    (Real.exp ((K : ℝ) * |t - t₀|))
    (fun x => norm_flow_variationalFieldVec_le hA hΦ h0 x t)

@[simp]
theorem fundamentalSolution_apply {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) (x : E) : fundamentalSolution hA hΦ h0 t x = Φ x t := rfl

/-- **The fundamental solution has operator norm at most `exp (K · |t - t₀|)`.**  The
quantitative bound `‖D_x Φ_t‖ ≤ exp (K · |t - t₀|)` on the resolvent, inherited from the
pointwise operator bound. -/
theorem norm_fundamentalSolution_le {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) : ‖fundamentalSolution hA hΦ h0 t‖ ≤ Real.exp ((K : ℝ) * |t - t₀|) := by
  exact LinearMap.mkContinuous_norm_le _ (Real.exp_pos _).le _

/-- **The fundamental solution is the identity at the anchor time.**  `D_x Φ_{t₀} = 1`: the
resolvent from `t₀` to `t₀` is the identity operator, matching the initial condition
`W t₀ = 1` of the fundamental-solution equation. -/
theorem fundamentalSolution_anchor {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x) :
    fundamentalSolution hA hΦ h0 t₀ = ContinuousLinearMap.id ℝ E := by
  ext x
  rw [fundamentalSolution_apply, h0, ContinuousLinearMap.id_apply]

/-!
### The fundamental solution is bounded below and injective (a non-degenerate resolvent)

Dual to the operator bound: the *lower* exponential control `dist_flow_apply_ge` of the
`C^0` layer forces the linear flow map to be bounded below by `exp (-K · |t - t₀|)`.  Hence
the fundamental solution `D_x Φ_t` has a controlled left inverse on its image — it is
injective, the linear/operator shadow of the bi-Lipschitz embedding
`isUniformEmbedding_flow_apply`, and the resolvent is non-degenerate. -/

/-- **Lower operator bound for the linear flow map.**  `exp (-K · |t - t₀|) · ‖x‖ ≤ ‖Φ x t‖`,
from the `C^0` lower dependence bound `dist_flow_apply_ge` applied between `x` and `0` with
`Φ 0 t = 0`.  The resolvent cannot contract a direction faster than `exp (-K · |t - t₀|)`. -/
theorem norm_flow_variationalFieldVec_ge {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (x : E) (t : ℝ) : Real.exp (-(K : ℝ) * |t - t₀|) * ‖x‖ ≤ ‖Φ x t‖ := by
  have hb := dist_flow_apply_ge (fun s => lipschitzWith_variationalFieldVec hA s) hΦ h0 x 0 t
  rw [flow_variationalFieldVec_zero hA hΦ h0 t, dist_zero_right, dist_zero_right] at hb
  calc Real.exp (-(K : ℝ) * |t - t₀|) * ‖x‖
      = ‖x‖ * Real.exp (-(K : ℝ) * |t - t₀|) := mul_comm _ _
    _ ≤ ‖Φ x t‖ := hb

/-- **The fundamental solution operator is bounded below.**
`exp (-K · |t - t₀|) · ‖x‖ ≤ ‖D_x Φ_t x‖`: the resolvent applied to a nonzero direction is
nonzero, with the reciprocal exponential lower bound. -/
theorem norm_fundamentalSolution_apply_ge {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (x : E) (t : ℝ) :
    Real.exp (-(K : ℝ) * |t - t₀|) * ‖x‖ ≤ ‖fundamentalSolution hA hΦ h0 t x‖ := by
  rw [fundamentalSolution_apply]
  exact norm_flow_variationalFieldVec_ge hA hΦ h0 x t

/-- **The fundamental solution operator is injective.**  Being bounded below, the resolvent
`D_x Φ_t ∈ E →L[ℝ] E` has trivial kernel — the operator shadow of the flow map being a
bi-Lipschitz embedding (`injective_flow_apply`).  This is the linear non-degeneracy that
makes the directional derivative assignment `u₀ ↦ D_x Φ_t u₀` faithful. -/
theorem fundamentalSolution_injective {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) : Function.Injective (fundamentalSolution hA hΦ h0 t) := by
  intro x y hxy
  refine injective_flow_apply (fun s => lipschitzWith_variationalFieldVec hA s) hΦ h0 t ?_
  simpa only [fundamentalSolution_apply] using hxy

/-!
### Identification with the operator-valued fundamental-matrix ODE

The `fundamentalSolution` built from the *vector* flow family coincides with any solution of
the *operator*-valued variational equation `W'(t) = A(t) ∘ W(t)` normalised by `W t₀ = 1`
(the fundamental matrix).  This ties the two variational ODEs together at the operator level:
whenever the operator fundamental matrix exists, it *is* the resolvent `D_x Φ_t`. -/

/-- **The resolvent equals the operator-valued fundamental matrix.**  If `W` solves the
operator variational ODE `W'(t) = A(t) ∘ W(t)` with `W t₀ = 1`, then for any vector flow
family `Φ` of `variationalFieldVec A` anchored at `Φ x t₀ = x`,
`fundamentalSolution hA hΦ h0 t = W t`.  (For each `x`, both `t ↦ Φ x t` and `t ↦ W t x`
solve the vector variational ODE — the latter by `isIntegralCurve_variational_apply` — and
agree at `t₀`, so they coincide by vector uniqueness.) -/
theorem fundamentalSolution_eq_of_operator_isIntegralCurve {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) {W : ℝ → (E →L[ℝ] E)}
    (hW : IsIntegralCurve W (variationalField A))
    (hW0 : W t₀ = ContinuousLinearMap.id ℝ E)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) : fundamentalSolution hA hΦ h0 t = W t := by
  ext x
  rw [fundamentalSolution_apply]
  refine variationalVec_eq_of_isIntegralCurve hA (hΦ x)
    (isIntegralCurve_variational_apply hW x) (t₁ := t₀) ?_ t
  rw [h0, hW0, ContinuousLinearMap.id_apply]

/-!
### Continuity of the resolvent action in time

Since the resolvent acts by `D_x Φ_t · u₀ = Φ u₀ t`, the `C^0` time/joint continuity of the
flow (`IsIntegralCurve.continuous`, `continuous_flow`) transfers verbatim to the fundamental
solution: `t ↦ D_x Φ_t u₀` is continuous, and the full action `(t, u₀) ↦ D_x Φ_t u₀` is jointly
continuous. -/

/-- **Strong continuity of the resolvent in time.**  For a fixed direction `u₀`, the path
`t ↦ D_x Φ_t · u₀` is continuous. -/
theorem continuous_fundamentalSolution_apply {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (u₀ : E) : Continuous (fun t => fundamentalSolution hA hΦ h0 t u₀) := by
  simp only [fundamentalSolution_apply]
  exact (hΦ u₀).continuous

/-- **Joint continuity of the resolvent action.**  The map `(t, u₀) ↦ D_x Φ_t · u₀` is jointly
continuous on `ℝ × E`. -/
theorem continuous_fundamentalSolution {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x) :
    Continuous (fun p : ℝ × E => fundamentalSolution hA hΦ h0 p.1 p.2) := by
  simp only [fundamentalSolution_apply]
  exact continuous_flow (fun s => lipschitzWith_variationalFieldVec hA s) hΦ h0

/-!
### The resolvent's columns are the variational-ODE solutions

The action `t ↦ D_x Φ_t · u₀` is exactly the solution of the vector variational ODE through
`u₀` at `t₀`.  This is the characterisation a subsequent `C^1`-differentiability proof
consumes: it is precisely the fact that the candidate derivative `D_x Φ_t` applied to a
direction obeys the linearised equation with the correct initial value. -/

/-- **The resolvent columns solve the variational ODE.**  For each direction `u₀`, the path
`t ↦ D_x Φ_t · u₀` is an integral curve of the vector variational field `variationalFieldVec A`. -/
theorem isIntegralCurve_fundamentalSolution_apply {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (u₀ : E) :
    IsIntegralCurve (fun t => fundamentalSolution hA hΦ h0 t u₀) (variationalFieldVec A) := by
  simp only [fundamentalSolution_apply]
  exact hΦ u₀

/-- **The resolvent recovers the initial direction at the anchor.**  `D_x Φ_{t₀} · u₀ = u₀`. -/
@[simp]
theorem fundamentalSolution_apply_anchor {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (u₀ : E) : fundamentalSolution hA hΦ h0 t₀ u₀ = u₀ := by
  rw [fundamentalSolution_apply, h0]

/-- **The resolvent is canonical.**  Any two flow families `Φ`, `Ψ` of `variationalFieldVec A`
anchored at `t₀` give the same fundamental solution operator: the resolvent `D_x Φ_t` depends
only on the field `A` (and `t₀`, `t`), not on the choice of flow family used to build it.
(Immediate from vector uniqueness `variationalVec_eq_of_isIntegralCurve`.) -/
theorem fundamentalSolution_congr {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    {Ψ : E → ℝ → E} (hΨ : ∀ x, IsIntegralCurve (Ψ x) (variationalFieldVec A))
    (h0Ψ : ∀ x, Ψ x t₀ = x) (t : ℝ) :
    fundamentalSolution hA hΦ h0 t = fundamentalSolution hA hΨ h0Ψ t := by
  ext x
  simp only [fundamentalSolution_apply]
  exact variationalVec_eq_of_isIntegralCurve hA (hΦ x) (hΨ x) (t₁ := t₀) (by rw [h0, h0Ψ]) t

/-!
### The linearisation-remainder Grönwall bound (the analytic core of `C¹` dependence)

The decisive estimate underlying *differentiable* dependence on initial data.  Let `f`, `g`
be two integral curves of a (possibly nonlinear) field `v`, and let `w` solve the vector
variational ODE `w'(s) = A(s) (w(s))` — the linearisation of `v` along the pair, with
`‖A s‖ ≤ K` — matching the *initial* separation exactly, `w t₀ = g t₀ - f t₀`.  If the
pointwise **linearisation defect** `‖v s (g s) - v s (f s) - A s (g s - f s)‖` is uniformly
`≤ δ`, then the linear prediction `w` tracks the true flow separation `g - f` to within
`gronwallBound 0 K δ |t - t₀|`.

The proof recognises the remainder `r := g - f - w` as an integral curve of the variational
field `variationalFieldVec A` **perturbed** by the (`δ`-bounded, `u`-independent) defect, and
compares it — via the two-sided perturbation Grönwall bound
`dist_le_of_isIntegralCurve_perturb` — to the zero solution, with which it shares its initial
value `r t₀ = 0`.  When `v` is `C¹` with `A s = D_x v (s, f s)` the defect is
`o(‖g s - f s‖) = o(‖g t₀ - f t₀‖)`, so `δ → 0` faster than the initial separation and this
bound upgrades to Fréchet differentiability of the flow with derivative the fundamental
solution `D_x Φ_t` — the `C¹` layer of the dependence tower.  Nothing about `v` beyond the two
integral curves and the defect bound is used (in particular `v` need not be Lipschitz). -/

/-- **Linearisation-remainder Grönwall bound.**  For two integral curves `f`, `g` of a field
`v`, a solution `w` of the vector variational ODE `w' = A(s) w` (`‖A s‖ ≤ K`) matching the
initial separation `w t₀ = g t₀ - f t₀`, and a uniform bound `δ` on the linearisation defect
`‖v s (g s) - v s (f s) - A s (g s - f s)‖`, the linear prediction `w` tracks the true flow
separation `g - f` to within `gronwallBound 0 K δ |t - t₀|`:
`‖(g t - f t) - w t‖ ≤ gronwallBound 0 K δ |t - t₀|`.  The analytic core of differentiable
dependence on initial data. -/
theorem norm_flow_sub_variational_le
    (hf : IsIntegralCurve f v) (hg : IsIntegralCurve g v)
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {w : ℝ → E} (hw : IsIntegralCurve w (variationalFieldVec A))
    {δ : ℝ} (hdefect : ∀ s, ‖v s (g s) - v s (f s) - A s (g s - f s)‖ ≤ δ)
    (hinit : w t₀ = g t₀ - f t₀) (t : ℝ) :
    ‖(g t - f t) - w t‖ ≤ gronwallBound 0 (K : ℝ) δ |t - t₀| := by
  -- the zero curve solves the (linear) vector variational ODE
  have hzero : IsIntegralCurve (fun _ : ℝ => (0 : E)) (variationalFieldVec A) := by
    intro s
    simpa only [variationalFieldVec, map_zero] using hasDerivAt_const (c := (0 : E)) (x := s)
  -- `r := g - f - w` solves the variational ODE perturbed by the (u-independent) defect
  have hr : IsIntegralCurve (fun s => g s - f s - w s)
      (fun s u => A s u + (v s (g s) - v s (f s) - A s (g s - f s))) := by
    intro s
    show HasDerivAt (fun s => g s - f s - w s)
        (A s (g s - f s - w s) + (v s (g s) - v s (f s) - A s (g s - f s))) s
    have hd := ((hg s).sub (hf s)).sub (hw s)
    convert hd using 1
    change A s (g s - f s - w s) +
        (v s (g s) - v s (f s) - A s (g s - f s)) =
      v s (g s) - v s (f s) - A s (w s)
    simp only [map_sub]
    abel
  -- the base and perturbed fields differ by at most `δ`, uniformly in `(s, u)`
  have hpert : ∀ s u, dist (variationalFieldVec A s u)
      (A s u + (v s (g s) - v s (f s) - A s (g s - f s))) ≤ δ := by
    intro s u
    simp only [variationalFieldVec, dist_eq_norm]
    rw [show A s u - (A s u + (v s (g s) - v s (f s) - A s (g s - f s)))
          = -(v s (g s) - v s (f s) - A s (g s - f s)) from by abel, norm_neg]
    exact hdefect s
  -- compare `r` to the zero solution by the perturbation Grönwall bound
  have hkey := dist_le_of_isIntegralCurve_perturb
      (fun s => lipschitzWith_variationalFieldVec hA s) hzero hr hpert t₀ t
  simp only [dist_eq_norm, zero_sub, norm_neg] at hkey
  rw [show g t₀ - f t₀ - w t₀ = (0 : E) from by rw [hinit]; abel, norm_zero] at hkey
  exact hkey

/-- **Interval-restricted linearisation-remainder bound.**  The refinement of
`norm_flow_sub_variational_le` in which the linearisation defect need only be controlled on the
*forward interval* `Ico t₀ b`, not for all times.  For integral curves `f`, `g` of a field `v`,
a solution `w` of the variational ODE `w' = A(s) w` (`‖A s‖ ≤ K`) matching the initial
separation `w t₀ = g t₀ - f t₀`, and a bound `δ` on the defect
`‖v s (g s) - v s (f s) - A s (g s - f s)‖` *for `s ∈ Ico t₀ b`*, the linear prediction tracks
the flow separation on `Icc t₀ b`:
`‖(g t - f t) - w t‖ ≤ gronwallBound 0 K δ (t - t₀)`  for `t ∈ Icc t₀ b`.

This is the version differentiable dependence actually consumes: as the flow separation
`‖g s - f s‖` grows exponentially in `s`, the defect can only be made uniformly small on a
*compact* time interval (the tube around the reference trajectory), so a globally-uniform `δ`
is unavailable — but on `[t₀, b]` the `C¹` modulus of `v` does supply one.  Proved by comparing
the remainder `r := g - f - w` (an approximate solution of the variational field, defect `≤ δ`
on `Ico t₀ b`) against the exact zero solution via Mathlib's interval Grönwall estimate
`dist_le_of_approx_trajectories_ODE`. -/
theorem norm_flow_sub_variational_le_Icc
    (hf : IsIntegralCurve f v) (hg : IsIntegralCurve g v)
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {w : ℝ → E} (hw : IsIntegralCurve w (variationalFieldVec A))
    {δ b : ℝ}
    (hdefect : ∀ s ∈ Ico t₀ b, ‖v s (g s) - v s (f s) - A s (g s - f s)‖ ≤ δ)
    (hinit : w t₀ = g t₀ - f t₀) {t : ℝ} (ht : t ∈ Icc t₀ b) :
    ‖(g t - f t) - w t‖ ≤ gronwallBound 0 (K : ℝ) δ (t - t₀) := by
  -- the zero curve is the exact solution of the (linear) variational ODE
  have hzero : IsIntegralCurve (fun _ : ℝ => (0 : E)) (variationalFieldVec A) := by
    intro s
    simpa only [variationalFieldVec, map_zero] using hasDerivAt_const (c := (0 : E)) (x := s)
  -- the remainder `r := g - f - w`: its derivative and continuity
  have hrderiv : ∀ s, HasDerivAt (fun s => g s - f s - w s)
      (v s (g s) - v s (f s) - variationalFieldVec A s (w s)) s :=
    fun s => ((hg s).sub (hf s)).sub (hw s)
  have hrcont : Continuous (fun s => g s - f s - w s) :=
    (hg.continuous.sub hf.continuous).sub hw.continuous
  -- the remainder's derivative is `A`-linear up to the defect, uniformly `≤ δ` on `Ico t₀ b`
  have g_bound : ∀ s ∈ Ico t₀ b,
      dist (v s (g s) - v s (f s) - variationalFieldVec A s (w s))
        (variationalFieldVec A s (g s - f s - w s)) ≤ δ := by
    intro s hs
    have hdef : (v s (g s) - v s (f s) - variationalFieldVec A s (w s))
        - variationalFieldVec A s (g s - f s - w s)
        = v s (g s) - v s (f s) - A s (g s - f s) := by
      simp only [variationalFieldVec, map_sub]; abel
    rw [dist_eq_norm, hdef]
    exact hdefect s hs
  -- initial separation is predicted exactly, so the remainder starts at `0`
  have ha : dist ((fun _ : ℝ => (0 : E)) t₀) ((fun s => g s - f s - w s) t₀) ≤ (0 : ℝ) := by
    have h0 : g t₀ - f t₀ - w t₀ = (0 : E) := by rw [hinit]; abel
    simp only [h0, dist_self, le_refl]
  -- interval Grönwall: compare the remainder to the exact zero solution
  have key := dist_le_of_approx_trajectories_ODE (a := t₀) (b := b)
    (εf := 0) (εg := δ) (δ := 0)
    (fun s => lipschitzWith_variationalFieldVec hA s)
    hzero.continuous.continuousOn (fun s _ => (hzero s).hasDerivWithinAt)
    (fun s _ => le_of_eq (dist_self _))
    hrcont.continuousOn (fun s _ => (hrderiv s).hasDerivWithinAt)
    g_bound ha
  have hb := key t ht
  rw [zero_add] at hb
  simp only [dist_eq_norm, zero_sub, norm_neg] at hb
  exact hb

/-- **Homogeneity of the (zero-initial) Grönwall bound in the defect.**  For the vanishing
initial value, the Grönwall bound is *linear* in the perturbation size `ε`:
`gronwallBound 0 K ε x = ε * gronwallBound 0 K 1 x`.  (Immediate from the closed form
`ε/K · (exp (K x) - 1)`, resp. `ε · x` when `K = 0`.)  This is the algebraic step that turns
the linearisation-remainder bound `‖(g t - f t) - w t‖ ≤ gronwallBound 0 K δ (t - t₀)` into an
estimate *proportional* to the defect `δ`, so that a defect of order `o(‖g t₀ - f t₀‖)` yields
a remainder of the same order — the passage from the remainder bound to Fréchet
differentiability of the flow. -/
theorem gronwallBound_zero_left_mul (K ε x : ℝ) :
    gronwallBound 0 K ε x = ε * gronwallBound 0 K 1 x := by
  by_cases hK : K = 0
  · subst hK; simp only [gronwallBound_K0]; ring
  · simp only [gronwallBound_of_K_ne_0 hK]; ring

/-- **Operator form of the interval remainder bound.**  The interval linearisation-remainder
bound `norm_flow_sub_variational_le_Icc` recast with the honest resolvent operator
`fundamentalSolution` (`D_x Φ_t`) as the linear prediction.  For the nonlinear flow family `Φ`
of `v` and the variational flow family `Φ'` of `variationalFieldVec A` (`‖A s‖ ≤ K`), the
difference between the actual flow separation `Φ y t - Φ x t` and its resolvent prediction
`D_x Φ_t · (y - x) = fundamentalSolution … t (y - x)` is controlled by the defect on the
forward interval:
`‖(Φ y t - Φ x t) - fundamentalSolution hA hΦ' h0' t (y - x)‖ ≤ gronwallBound 0 K δ (t - t₀)`
for `t ∈ Icc t₀ b`, whenever `‖v s (Φ y s) - v s (Φ x s) - A s (Φ y s - Φ x s)‖ ≤ δ` on
`Ico t₀ b`.  This is precisely the numerator of the Fréchet difference quotient for
`x ↦ Φ x t`, in the form its differentiability proof consumes. -/
theorem norm_flow_sub_fundamentalSolution_le_Icc
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x y : E) {δ b : ℝ}
    (hdefect : ∀ s ∈ Ico t₀ b,
      ‖v s (Φ y s) - v s (Φ x s) - A s (Φ y s - Φ x s)‖ ≤ δ)
    {t : ℝ} (ht : t ∈ Icc t₀ b) :
    ‖(Φ y t - Φ x t) - fundamentalSolution hA hΦ' h0' t (y - x)‖
      ≤ gronwallBound 0 (K : ℝ) δ (t - t₀) := by
  have hw : IsIntegralCurve (fun s => fundamentalSolution hA hΦ' h0' s (y - x))
      (variationalFieldVec A) := isIntegralCurve_fundamentalSolution_apply hA hΦ' h0' (y - x)
  have hinit : (fun s => fundamentalSolution hA hΦ' h0' s (y - x)) t₀ = Φ y t₀ - Φ x t₀ := by
    simp only [fundamentalSolution_apply_anchor, h0]
  exact norm_flow_sub_variational_le_Icc (hΦ x) (hΦ y) hA hw hdefect hinit ht

/-!
### `C¹` dependence on initial data (conditional on a linearisation modulus)

Assembling the pieces, the flow map `x ↦ Φ x t` is **Fréchet differentiable** at a base point
`x₀`, with derivative the fundamental solution / resolvent `D_x Φ_t = fundamentalSolution … t`,
*provided* the linearisation defect along the reference trajectory is of order `o(‖z - x₀‖)` as
`z → x₀`, uniformly on the forward time interval.  This isolates the remaining analytic input
(the `C¹` modulus of the field `v`, which — via the mean-value form `‖v(b) - v(a) - D_x v(a)
(b - a)‖ ≤ o(‖b - a‖)` and the exponential flow-separation bound — supplies such a defect
modulus on a compact time tube) as a single clean hypothesis, and derives the differentiable
dependence from it.  The proof: the interval remainder bound
`norm_flow_sub_fundamentalSolution_le_Icc` gives `‖numerator z‖ ≤ gronwallBound 0 K (D z)
(t - t₀)`, the Grönwall homogeneity `gronwallBound_zero_left_mul` turns the right side into
`gronwallBound 0 K 1 (t - t₀) · D z`, so `numerator = O(D)`; composing with the hypothesis
`D = o(z - x₀)` yields `numerator = o(z - x₀)`, i.e. `HasFDerivAt`. -/

open Asymptotics in
/-- **`C¹` dependence of the flow on the initial condition (conditional on a defect modulus).**
For a nonlinear flow family `Φ` of `v`, the variational flow family `Φ'` of the linearisation
`variationalFieldVec A` (`‖A s‖ ≤ K`), a forward time `t ≥ t₀`, and a defect bound `D : E → ℝ`
with `0 ≤ D z` and `‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ D z` on `Ico t₀ t`,
if the defect is little-o of the initial separation, `D =o[𝓝 x₀] (· - x₀)`, then
`x ↦ Φ x t` is Fréchet differentiable at `x₀` with derivative the resolvent
`fundamentalSolution hA hΦ' h0' t = D_x Φ_t`.  The `C¹` layer of the dependence tower. -/
theorem hasFDerivAt_flow_of_defect_isLittleO
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {D : E → ℝ} (hDnn : ∀ z, 0 ≤ D z)
    (hdefect : ∀ z, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ D z)
    (hDo : (fun z => D z) =o[𝓝 x₀] fun z => z - x₀) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ := by
  -- interval remainder bound + Grönwall homogeneity: the numerator is `O(D)`
  have hnum : ∀ z, ‖Φ z t - Φ x₀ t - fundamentalSolution hA hΦ' h0' t (z - x₀)‖
      ≤ gronwallBound 0 (K : ℝ) 1 (t - t₀) * D z := by
    intro z
    have hb := norm_flow_sub_fundamentalSolution_le_Icc hA hΦ' h0' hΦ h0 x₀ z
      (hdefect z) (Set.mem_Icc.mpr ⟨ht0, le_refl t⟩)
    rwa [gronwallBound_zero_left_mul, mul_comm (D z)] at hb
  have hbig : (fun z => Φ z t - Φ x₀ t - fundamentalSolution hA hΦ' h0' t (z - x₀))
      =O[𝓝 x₀] fun z => D z := by
    rw [isBigO_iff]
    refine ⟨gronwallBound 0 (K : ℝ) 1 (t - t₀), Filter.Eventually.of_forall (fun z => ?_)⟩
    show ‖Φ z t - Φ x₀ t - fundamentalSolution hA hΦ' h0' t (z - x₀)‖
        ≤ gronwallBound 0 (K : ℝ) 1 (t - t₀) * ‖D z‖
    rw [Real.norm_eq_abs, abs_of_nonneg (hDnn z)]
    exact hnum z
  -- compose with `D =o (z - x₀)` to get the little-o numerator, i.e. `HasFDerivAt`
  exact HasFDerivAt.of_isLittleO (hbig.trans_isLittleO hDo)

open Asymptotics in
/-- **The flow map is differentiable at the base point** (under the defect-modulus hypothesis of
`hasFDerivAt_flow_of_defect_isLittleO`): `x ↦ Φ x t` is `DifferentiableAt ℝ` at `x₀`. -/
theorem differentiableAt_flow_of_defect_isLittleO
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {D : E → ℝ} (hDnn : ∀ z, 0 ≤ D z)
    (hdefect : ∀ z, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ D z)
    (hDo : (fun z => D z) =o[𝓝 x₀] fun z => z - x₀) :
    DifferentiableAt ℝ (fun z => Φ z t) x₀ :=
  (hasFDerivAt_flow_of_defect_isLittleO hA hΦ' h0' hΦ h0 x₀ ht0 hDnn hdefect hDo).differentiableAt

open Asymptotics in
/-- **The Fréchet derivative of the flow map is the resolvent** (under the defect-modulus
hypothesis of `hasFDerivAt_flow_of_defect_isLittleO`):
`fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t = D_x Φ_t`.  The identification
consumed downstream: the spatial derivative of the flow *is* the fundamental solution operator. -/
theorem fderiv_flow_of_defect_isLittleO
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {D : E → ℝ} (hDnn : ∀ z, 0 ≤ D z)
    (hdefect : ∀ z, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ D z)
    (hDo : (fun z => D z) =o[𝓝 x₀] fun z => z - x₀) :
    fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t :=
  (hasFDerivAt_flow_of_defect_isLittleO hA hΦ' h0' hΦ h0 x₀ ht0 hDnn hdefect hDo).fderiv

/-!
### Toward discharging the defect modulus: the mean-value defect bound

A step toward making `hasFDerivAt_flow_of_defect_isLittleO` *unconditional*: the linearisation
defect along the flow is bounded by the *oscillation* of the field's spatial derivative on the
segment joining the two trajectories, times the flow separation — which the exponential
dependence bound turns into `exp (K |s - t₀|) · ‖z - x₀‖`.  A subsequent Heine–Cantor argument on
the compact trajectory tube (uniform continuity of `D_x v`) makes the oscillation `C(z) → 0` as
`z → x₀`, delivering the `o(‖z - x₀‖)` hypothesis. -/

/-- **Defect ≤ (derivative oscillation) × (flow separation).**  If `v s` has spatial derivative
`Dv s` on the segment `[Φ x₀ s, Φ z s]` with `‖Dv s ξ - A s‖ ≤ C` there, then the mean-value
inequality bounds the linearisation defect by `C · ‖Φ z s - Φ x₀ s‖`, and the exponential
initial-data dependence `dist_flow_apply_le` bounds the separation by `exp (K |s - t₀|) · ‖z -
x₀‖`:
`‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ C · (exp (K |s - t₀|) · ‖z - x₀‖)`.
The bridge from `C¹`-regularity of the field to the defect modulus consumed by
`hasFDerivAt_flow_of_defect_isLittleO`. -/
theorem norm_flow_defect_le_of_segment_oscillation
    (hv : ∀ τ, LipschitzWith K (v τ))
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    {A : ℝ → (E →L[ℝ] E)} {Dv : ℝ → E → (E →L[ℝ] E)} {C : ℝ}
    (x₀ z : E) (s : ℝ)
    (hderiv : ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    (hbound : ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s), ‖Dv s ξ - A s‖ ≤ C) :
    ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖
      ≤ C * (Real.exp ((K : ℝ) * |s - t₀|) * ‖z - x₀‖) := by
  have hC : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hbound (Φ x₀ s) (left_mem_segment ℝ _ _))
  have hmv : ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ C * ‖Φ z s - Φ x₀ s‖ :=
    (convex_segment (Φ x₀ s) (Φ z s)).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      hderiv hbound (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  have hsep : ‖Φ z s - Φ x₀ s‖ ≤ ‖z - x₀‖ * Real.exp ((K : ℝ) * |s - t₀|) := by
    have h := dist_flow_apply_le hv hΦ h0 z x₀ s
    rwa [dist_eq_norm, dist_eq_norm] at h
  refine hmv.trans ?_
  rw [mul_comm (Real.exp ((K : ℝ) * |s - t₀|)) (‖z - x₀‖)]
  exact mul_le_mul_of_nonneg_left hsep hC

/-!
### Asymptotic glue and the oscillation-driven `C¹` dependence theorem

The mean-value bound `norm_flow_defect_le_of_segment_oscillation` controls the linearisation
defect at each time `s` by `C · exp (K |s - t₀|) · ‖z - x₀‖`, where `C` is the oscillation of the
field's spatial derivative on the trajectory chord.  What `hasFDerivAt_flow_of_defect_isLittleO`
consumes is a *little-o* defect modulus.  The bridge is purely asymptotic: once a single
uniform-in-time oscillation modulus `C(z)` is available with `C(z) → 0` as `z → x₀`, the defect
bound is `(vanishing modulus) · ‖z - x₀‖`, which is `o(‖z - x₀‖)`.  This upgrades the conditional
`C¹` dependence to one whose only hypothesis is the *vanishing* of the uniform oscillation
modulus. -/

open Asymptotics Filter in
/-- **Little-o from a vanishing pointwise modulus.**  If `‖f x‖ ≤ g x · ‖u x‖` holds eventually
along `l` and the scalar modulus `g` tends to `0` along `l`, then `f =o[l] u`.  The asymptotic
glue turning a bound "`defect ≤ (modulus → 0) · separation`" into the little-o hypothesis
consumed by `hasFDerivAt_flow_of_defect_isLittleO`. -/
theorem isLittleO_of_norm_le_mul_of_tendsto_nhds_zero
    {α : Type*} {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedAddCommGroup F₂]
    {l : Filter α} {f : α → F₁} {u : α → F₂} {g : α → ℝ}
    (hle : ∀ᶠ x in l, ‖f x‖ ≤ g x * ‖u x‖) (hg : Tendsto g l (𝓝 0)) :
    f =o[l] u := by
  rw [isLittleO_iff]
  intro c hc
  have hgc : ∀ᶠ x in l, g x < c := hg.eventually (Iio_mem_nhds hc)
  filter_upwards [hle, hgc] with x hx hgx
  exact hx.trans (mul_le_mul_of_nonneg_right hgx.le (norm_nonneg _))

open Asymptotics Filter in
/-- **`C¹` dependence of the flow from a vanishing uniform oscillation modulus.**  Let `Φ` be a
nonlinear flow family of `v`, `Φ'` the variational flow family of the linearisation
`variationalFieldVec A` (`‖A s‖ ≤ K`), and `t ≥ t₀`.  Suppose a *single, time-uniform* oscillation
modulus `C : E → ℝ` with `0 ≤ C z`, `C z → 0` as `z → x₀`, bounds the linearisation defect on
`Ico t₀ t` by `‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ C z · (exp (K |s - t₀|) ·
‖z - x₀‖)`.  Then `x ↦ Φ x t` is Fréchet differentiable at `x₀` with derivative the resolvent
`fundamentalSolution … t = D_x Φ_t`.  This discharges the defect-modulus hypothesis of
`hasFDerivAt_flow_of_defect_isLittleO` down to the *vanishing* of the uniform oscillation modulus
(the residual `C¹`-regularity input, supplied by Heine–Cantor on the compact trajectory tube). -/
theorem hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {C : E → ℝ} (hCnn : ∀ z, 0 ≤ C z) (hCto : Tendsto C (𝓝 x₀) (𝓝 0))
    (hdefect : ∀ z, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖
        ≤ C z * (Real.exp ((K : ℝ) * |s - t₀|) * ‖z - x₀‖)) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ := by
  set D : E → ℝ := fun z => C z * (Real.exp ((K : ℝ) * (t - t₀)) * ‖z - x₀‖) with hD
  have hDnn : ∀ z, 0 ≤ D z := fun z =>
    mul_nonneg (hCnn z) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
  have hdefect' : ∀ z, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ D z := by
    intro z s hs
    have hsle : |s - t₀| ≤ t - t₀ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
      exact sub_le_sub_right hs.2.le t₀
    have hexple : Real.exp ((K : ℝ) * |s - t₀|) ≤ Real.exp ((K : ℝ) * (t - t₀)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsle K.coe_nonneg)
    refine (hdefect z s hs).trans ?_
    simp only [hD]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hexple (norm_nonneg _)) (hCnn z)
  have hDo : (fun z => D z) =o[𝓝 x₀] fun z => z - x₀ := by
    refine isLittleO_of_norm_le_mul_of_tendsto_nhds_zero
      (g := fun z => C z * Real.exp ((K : ℝ) * (t - t₀))) ?_ ?_
    · refine Filter.Eventually.of_forall (fun z => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hDnn z)]
      refine le_of_eq ?_
      simp only [hD]
      ring
    · simpa using hCto.mul_const (Real.exp ((K : ℝ) * (t - t₀)))
  exact hasFDerivAt_flow_of_defect_isLittleO hA hΦ' h0' hΦ h0 x₀ ht0 hDnn hdefect' hDo

open Asymptotics Filter in
/-- **The flow map is differentiable at the base point** from a vanishing uniform oscillation
modulus (the consumer-facing corollary of `hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero`):
`DifferentiableAt ℝ (fun z => Φ z t) x₀`. -/
theorem differentiableAt_flow_of_uniform_oscillation_tendsto_zero
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {C : E → ℝ} (hCnn : ∀ z, 0 ≤ C z) (hCto : Tendsto C (𝓝 x₀) (𝓝 0))
    (hdefect : ∀ z, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖
        ≤ C z * (Real.exp ((K : ℝ) * |s - t₀|) * ‖z - x₀‖)) :
    DifferentiableAt ℝ (fun z => Φ z t) x₀ :=
  (hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero hA hΦ' h0' hΦ h0 x₀ ht0 hCnn hCto
    hdefect).differentiableAt

open Asymptotics Filter in
/-- **The Fréchet derivative of the flow map is the resolvent** from a vanishing uniform
oscillation modulus:
`fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution … t = D_x Φ_t`. -/
theorem fderiv_flow_of_uniform_oscillation_tendsto_zero
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {C : E → ℝ} (hCnn : ∀ z, 0 ≤ C z) (hCto : Tendsto C (𝓝 x₀) (𝓝 0))
    (hdefect : ∀ z, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖
        ≤ C z * (Real.exp ((K : ℝ) * |s - t₀|) * ‖z - x₀‖)) :
    fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t :=
  (hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero hA hΦ' h0' hΦ h0 x₀ ht0 hCnn hCto
    hdefect).fderiv

/-!
### From defect modulus to derivative oscillation: the `C¹`-regularity hypothesis

The final composable reduction: `norm_flow_defect_le_of_segment_oscillation` turns a bound on the
*oscillation of the field's spatial derivative on the trajectory chord* into the per-time defect
bound consumed by `hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero`.  Composing the two, the
`C¹` dependence of the flow reduces to a single hypothesis phrased purely in terms of the field:
the chord-oscillation `‖Dv s ξ - A s‖` (uniform in `s ∈ [t₀, t]`, over `ξ` on the chord
`[Φ x₀ s, Φ z s]`) vanishes as `z → x₀`.  This is exactly the modulus-of-continuity input a genuine
`C¹` field supplies via Heine–Cantor on the compact trajectory tube. -/

open Asymptotics Filter in
/-- **`C¹` dependence of the flow from a vanishing derivative chord-oscillation.**  With `Φ`, `Φ'`
the nonlinear/variational flow families and `t ≥ t₀`, suppose the field `v s` has spatial
derivative `Dv s` on each trajectory chord `[Φ x₀ s, Φ z s]` (`s ∈ Ico t₀ t`), and a single
uniform modulus `C : E → ℝ` with `0 ≤ C z`, `C z → 0` as `z → x₀`, bounds the derivative
oscillation `‖Dv s ξ - A s‖ ≤ C z` there.  Then `x ↦ Φ x t` is Fréchet differentiable at `x₀` with
derivative the resolvent `fundamentalSolution … t = D_x Φ_t`.  The mean-value bound
`norm_flow_defect_le_of_segment_oscillation` converts the oscillation into the defect modulus of
`hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero`; the only residual input is the vanishing of
the derivative oscillation — a pure `C¹`-regularity statement about `v`. -/
theorem hasFDerivAt_flow_of_segment_oscillation_tendsto_zero
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {C : E → ℝ} (hCnn : ∀ z, 0 ≤ C z) (hCto : Tendsto C (𝓝 x₀) (𝓝 0))
    (hosc : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s), ‖Dv s ξ - A s‖ ≤ C z) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ := by
  have hdefect : ∀ z, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖
        ≤ C z * (Real.exp ((K : ℝ) * |s - t₀|) * ‖z - x₀‖) := fun z s hs =>
    norm_flow_defect_le_of_segment_oscillation hv hΦ h0 x₀ z s (hderiv z s hs) (hosc z s hs)
  exact hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero hA hΦ' h0' hΦ h0 x₀ ht0 hCnn hCto
    hdefect

open Asymptotics Filter in
/-- **The flow map is differentiable at the base point** from a vanishing derivative
chord-oscillation: `DifferentiableAt ℝ (fun z => Φ z t) x₀`. -/
theorem differentiableAt_flow_of_segment_oscillation_tendsto_zero
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {C : E → ℝ} (hCnn : ∀ z, 0 ≤ C z) (hCto : Tendsto C (𝓝 x₀) (𝓝 0))
    (hosc : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s), ‖Dv s ξ - A s‖ ≤ C z) :
    DifferentiableAt ℝ (fun z => Φ z t) x₀ :=
  (hasFDerivAt_flow_of_segment_oscillation_tendsto_zero hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hCnn
    hCto hosc).differentiableAt

open Asymptotics Filter in
/-- **The Fréchet derivative of the flow map is the resolvent** from a vanishing derivative
chord-oscillation: `fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution … t = D_x Φ_t`. -/
theorem fderiv_flow_of_segment_oscillation_tendsto_zero
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {C : E → ℝ} (hCnn : ∀ z, 0 ≤ C z) (hCto : Tendsto C (𝓝 x₀) (𝓝 0))
    (hosc : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s), ‖Dv s ξ - A s‖ ≤ C z) :
    fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t :=
  (hasFDerivAt_flow_of_segment_oscillation_tendsto_zero hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hCnn
    hCto hosc).fderiv

/-!
### Manufacturing the vanishing oscillation from a modulus of continuity

The final input to the `C¹` dependence tower is the *vanishing* of the derivative chord-oscillation.
For a `C¹` field this is furnished by a modulus of continuity `ω` of the spatial derivative
(uniform in `s ∈ [t₀, t]` on the compact trajectory tube, via Heine–Cantor): `ω` is nonnegative,
monotone, and vanishes at `0⁺`.  The two ingredients below turn such a modulus into the
hypotheses of `hasFDerivAt_flow_of_segment_oscillation_tendsto_zero`: the modulus composed with the
(exponentially controlled) flow separation still tends to `0`, and the chord-oscillation is bounded
by that composition. -/

open Filter in
/-- **A vanishing modulus composed with the vanishing scaled separation still vanishes.**  If
`ω → 0` along `𝓝[≥] 0` and `0 ≤ c`, then `z ↦ ω (c · ‖z - x₀‖)` tends to `0` as `z → x₀`.  The
"`C(z) → 0`" engine of the modulus-of-continuity route to `C¹` flow-dependence. -/
theorem tendsto_modulus_comp_norm_sub {ω : ℝ → ℝ} {c : ℝ} (x₀ : E)
    (hc : 0 ≤ c) (hω : Tendsto ω (𝓝[≥] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun z => ω (c * ‖z - x₀‖)) (𝓝 x₀) (𝓝 0) := by
  have hsep : Tendsto (fun z : E => c * ‖z - x₀‖) (𝓝 x₀) (𝓝[≥] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Filter.Eventually.of_forall fun z => Set.mem_Ici.mpr (mul_nonneg hc (norm_nonneg _))⟩
    have hnorm : Tendsto (fun z : E => ‖z - x₀‖) (𝓝 x₀) (𝓝 0) := by
      have hcont : Continuous fun z : E => ‖z - x₀‖ :=
        (continuous_id.sub continuous_const).norm
      simpa using hcont.tendsto x₀
    simpa using hnorm.const_mul c
  exact hω.comp hsep

open Asymptotics Filter in
/-- **`C¹` dependence of the flow from a uniform modulus of continuity of the spatial derivative.**
With `Φ`, `Φ'` the nonlinear/variational flow families and `t ≥ t₀`, suppose the field `v s` has
spatial derivative `Dv s` on each trajectory chord `[Φ x₀ s, Φ z s]` (`s ∈ Ico t₀ t`), and a single
nonnegative, monotone modulus `ω : ℝ → ℝ` vanishing at `0⁺` bounds the derivative oscillation there
by the distance to the anchor trajectory, `‖Dv s ξ - A s‖ ≤ ω (‖ξ - Φ x₀ s‖)`.  Then `x ↦ Φ x t`
is Fréchet differentiable at `x₀` with derivative the resolvent `fundamentalSolution … t = D_x Φ_t`.
The chord points lie within `exp (K |s - t₀|) · ‖z - x₀‖` of `Φ x₀ s` (`dist_flow_apply_le`), so the
monotone modulus caps the oscillation by `C z := ω (exp (K (t - t₀)) · ‖z - x₀‖) → 0`
(`tendsto_modulus_comp_norm_sub`), discharging the hypothesis of
`hasFDerivAt_flow_of_segment_oscillation_tendsto_zero`.  This is the `C¹`-regularity input in its
most usable form: a modulus of continuity for the field's spatial derivative. -/
theorem hasFDerivAt_flow_of_uniform_deriv_modulus
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {ω : ℝ → ℝ} (hωnn : ∀ r, 0 ≤ ω r) (hωmono : Monotone ω)
    (hω0 : Tendsto ω (𝓝[≥] (0 : ℝ)) (𝓝 0))
    (hmod : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ ω (‖ξ - Φ x₀ s‖)) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ := by
  set c : ℝ := Real.exp ((K : ℝ) * (t - t₀)) with hc
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  set C : E → ℝ := fun z => ω (c * ‖z - x₀‖) with hC
  have hCnn : ∀ z, 0 ≤ C z := fun z => hωnn _
  have hCto : Tendsto C (𝓝 x₀) (𝓝 0) := tendsto_modulus_comp_norm_sub x₀ hc0 hω0
  have hosc : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ C z := by
    intro z s hs ξ hξ
    have hle : ‖ξ - Φ x₀ s‖ ≤ c * ‖z - x₀‖ := by
      obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hξ
      have hq1 : q ≤ 1 := by linarith
      have heq : (p • Φ x₀ s + q • Φ z s) - Φ x₀ s = q • (Φ z s - Φ x₀ s) := by
        have hp1 : p = 1 - q := by linarith
        rw [hp1, sub_smul, one_smul, smul_sub]
        abel
      have hsep : ‖Φ z s - Φ x₀ s‖ ≤ ‖z - x₀‖ * Real.exp ((K : ℝ) * |s - t₀|) := by
        have h := dist_flow_apply_le hv hΦ h0 z x₀ s
        rwa [dist_eq_norm, dist_eq_norm] at h
      have hexp : Real.exp ((K : ℝ) * |s - t₀|) ≤ c := by
        rw [hc]
        refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ K.coe_nonneg)
        rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
        exact sub_le_sub_right hs.2.le t₀
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq]
      calc q * ‖Φ z s - Φ x₀ s‖ ≤ 1 * ‖Φ z s - Φ x₀ s‖ :=
            mul_le_mul_of_nonneg_right hq1 (norm_nonneg _)
        _ = ‖Φ z s - Φ x₀ s‖ := one_mul _
        _ ≤ ‖z - x₀‖ * Real.exp ((K : ℝ) * |s - t₀|) := hsep
        _ ≤ ‖z - x₀‖ * c := mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
        _ = c * ‖z - x₀‖ := mul_comm _ _
    calc ‖Dv s ξ - A s‖ ≤ ω (‖ξ - Φ x₀ s‖) := hmod z s hs ξ hξ
      _ ≤ ω (c * ‖z - x₀‖) := hωmono hle
      _ = C z := by simp only [hC]
  exact hasFDerivAt_flow_of_segment_oscillation_tendsto_zero hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv
    hCnn hCto hosc

open Asymptotics Filter in
/-- **The flow map is differentiable at the base point** from a uniform modulus of continuity of
the spatial derivative: `DifferentiableAt ℝ (fun z => Φ z t) x₀`. -/
theorem differentiableAt_flow_of_uniform_deriv_modulus
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {ω : ℝ → ℝ} (hωnn : ∀ r, 0 ≤ ω r) (hωmono : Monotone ω)
    (hω0 : Tendsto ω (𝓝[≥] (0 : ℝ)) (𝓝 0))
    (hmod : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ ω (‖ξ - Φ x₀ s‖)) :
    DifferentiableAt ℝ (fun z => Φ z t) x₀ :=
  (hasFDerivAt_flow_of_uniform_deriv_modulus hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hωnn hωmono hω0
    hmod).differentiableAt

open Asymptotics Filter in
/-- **The Fréchet derivative of the flow map is the resolvent** from a uniform modulus of
continuity of the spatial derivative:
`fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution … t = D_x Φ_t`. -/
theorem fderiv_flow_of_uniform_deriv_modulus
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {ω : ℝ → ℝ} (hωnn : ∀ r, 0 ≤ ω r) (hωmono : Monotone ω)
    (hω0 : Tendsto ω (𝓝[≥] (0 : ℝ)) (𝓝 0))
    (hmod : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ ω (‖ξ - Φ x₀ s‖)) :
    fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t :=
  (hasFDerivAt_flow_of_uniform_deriv_modulus hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hωnn hωmono hω0
    hmod).fderiv

/-!
### The `C^{1,1}` specialisation: a Lipschitz spatial derivative

The most directly usable entry point: when the field's spatial derivative is *Lipschitz* on the
trajectory chords (uniformly in `s`), i.e. `‖Dv s ξ - A s‖ ≤ L · ‖ξ - Φ x₀ s‖`, the linear modulus
`ω r = L · r⁺` (nonnegative, monotone, vanishing at `0⁺`) feeds
`hasFDerivAt_flow_of_uniform_deriv_modulus` directly.  This covers every smooth (`C^∞`) field — in
particular the intended Ricci-flow application, whose right-hand sides are smooth — so it is the
practical `C¹`-dependence theorem: no abstract modulus of continuity to supply, only a Lipschitz
constant for the derivative. -/

open Asymptotics Filter in
/-- **`C¹` dependence of the flow from a Lipschitz spatial derivative (`C^{1,1}`).**  If the field
`v s` has spatial derivative `Dv s` on each trajectory chord `[Φ x₀ s, Φ z s]` (`s ∈ Ico t₀ t`) and
the derivative oscillation there is Lipschitz in the distance to the anchor trajectory,
`‖Dv s ξ - A s‖ ≤ L · ‖ξ - Φ x₀ s‖` with `0 ≤ L` uniform in `s`, then `x ↦ Φ x t` is Fréchet
differentiable at `x₀` with derivative the resolvent `fundamentalSolution … t = D_x Φ_t`.  The linear
modulus `ω r = L · max r 0` discharges `hasFDerivAt_flow_of_uniform_deriv_modulus`. -/
theorem hasFDerivAt_flow_of_lipschitz_deriv
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ L * ‖ξ - Φ x₀ s‖) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ := by
  refine hasFDerivAt_flow_of_uniform_deriv_modulus hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv
    (ω := fun r => L * max r 0) (fun r => mul_nonneg hL (le_max_right r 0)) ?_ ?_ ?_
  · intro a b hab
    exact mul_le_mul_of_nonneg_left (max_le_max hab le_rfl) hL
  · have hbase : Tendsto (fun r : ℝ => L * r) (𝓝[≥] (0 : ℝ)) (𝓝 0) := by
      have h2 : Tendsto (fun r : ℝ => L * r) (𝓝 (0 : ℝ)) (𝓝 0) := by
        have hc : Continuous (fun r : ℝ => L * r) := by fun_prop
        simpa only [mul_zero] using hc.tendsto (0 : ℝ)
      exact h2.mono_left nhdsWithin_le_nhds
    refine hbase.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [max_eq_left (Set.mem_Ici.mp hr)]
  · intro z s hs ξ hξ
    simpa [max_eq_left (norm_nonneg (ξ - Φ x₀ s))] using hlip z s hs ξ hξ

open Asymptotics Filter in
/-- **The flow map is differentiable at the base point** from a Lipschitz spatial derivative:
`DifferentiableAt ℝ (fun z => Φ z t) x₀`. -/
theorem differentiableAt_flow_of_lipschitz_deriv
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ L * ‖ξ - Φ x₀ s‖) :
    DifferentiableAt ℝ (fun z => Φ z t) x₀ :=
  (hasFDerivAt_flow_of_lipschitz_deriv hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hL hlip).differentiableAt

open Asymptotics Filter in
/-- **The Fréchet derivative of the flow map is the resolvent** from a Lipschitz spatial
derivative: `fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution … t = D_x Φ_t`. -/
theorem fderiv_flow_of_lipschitz_deriv
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ L * ‖ξ - Φ x₀ s‖) :
    fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t :=
  (hasFDerivAt_flow_of_lipschitz_deriv hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hL hlip).fderiv

open Asymptotics Filter in
/-- **Global-derivative convenience form** of `hasFDerivAt_flow_of_lipschitz_deriv`.  Takes the
*global* Fréchet derivative `Dv s` of `v s` at every point (as a genuine `C¹` field provides,
`HasFDerivAt (v s) (Dv s ξ) ξ`) instead of the chord-restricted `HasFDerivWithinAt`; the chord
hypothesis follows by `HasFDerivAt.hasFDerivWithinAt`.  The single cleanest entry point to the
`C^1` flow-dependence tower for a smooth field with a spatially-Lipschitz derivative. -/
theorem hasFDerivAt_flow_of_lipschitz_deriv_of_hasFDerivAt
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ z, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ L * ‖ξ - Φ x₀ s‖) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ :=
  hasFDerivAt_flow_of_lipschitz_deriv hv hA hΦ' h0' hΦ h0 x₀ ht0
    (fun _ s _ ξ _ => (hderiv s ξ).hasFDerivWithinAt) hL hlip

/-!
### Local (`∀ᶠ z in 𝓝 x₀`) refinements of the `C¹` dependence tower

Fréchet differentiability of `x ↦ Φ x t` at the base point `x₀` is a **local** property, so the
defect / oscillation / derivative-existence hypotheses of the theorems above need only hold for
initial conditions `z` in a *neighbourhood* of `x₀`, not for every `z : E`.  The following variants
weaken the global `∀ z` hypotheses to `∀ᶠ z in 𝓝 x₀` (the nonnegativity of the modulus and the
structural flow-family hypotheses stay global, being harmless / non-analytic).

This is the honest form consumed by a genuine smooth field: its spatial derivative `D_x v` is only
*locally* Lipschitz, so the global Lipschitz-derivative bound of `hasFDerivAt_flow_of_lipschitz_deriv`
generally fails, whereas its local counterpart `hasFDerivAt_flow_of_lipschitz_deriv_eventually`
holds on the neighbourhood of `x₀` where the local Lipschitz estimate is available. -/

open Asymptotics Filter in
/-- **Local form of `hasFDerivAt_flow_of_defect_isLittleO`.**  The `C¹` dependence of the flow on
the initial condition, needing the defect bound `‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖
≤ D z` only for `z` in a neighbourhood of `x₀` (`∀ᶠ z in 𝓝 x₀`) rather than for every `z`.  Since
`HasFDerivAt` is determined by the behaviour of `z ↦ Φ z t` near `x₀`, the big-O numerator estimate
`numerator = O(D)` is an eventual (in `𝓝 x₀`) statement, so the eventual defect bound suffices. -/
theorem hasFDerivAt_flow_of_defect_isLittleO_eventually
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {D : E → ℝ} (hDnn : ∀ z, 0 ≤ D z)
    (hdefect : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ D z)
    (hDo : (fun z => D z) =o[𝓝 x₀] fun z => z - x₀) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ := by
  have hbig : (fun z => Φ z t - Φ x₀ t - fundamentalSolution hA hΦ' h0' t (z - x₀))
      =O[𝓝 x₀] fun z => D z := by
    rw [isBigO_iff]
    refine ⟨gronwallBound 0 (K : ℝ) 1 (t - t₀), ?_⟩
    filter_upwards [hdefect] with z hdefectz
    show ‖Φ z t - Φ x₀ t - fundamentalSolution hA hΦ' h0' t (z - x₀)‖
        ≤ gronwallBound 0 (K : ℝ) 1 (t - t₀) * ‖D z‖
    rw [Real.norm_eq_abs, abs_of_nonneg (hDnn z)]
    have hb := norm_flow_sub_fundamentalSolution_le_Icc hA hΦ' h0' hΦ h0 x₀ z
      hdefectz (Set.mem_Icc.mpr ⟨ht0, le_refl t⟩)
    rwa [gronwallBound_zero_left_mul, mul_comm (D z)] at hb
  exact HasFDerivAt.of_isLittleO (hbig.trans_isLittleO hDo)

open Asymptotics Filter in
/-- **The flow map is differentiable at the base point** (local defect-modulus form):
`DifferentiableAt ℝ (fun z => Φ z t) x₀`. -/
theorem differentiableAt_flow_of_defect_isLittleO_eventually
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {D : E → ℝ} (hDnn : ∀ z, 0 ≤ D z)
    (hdefect : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ D z)
    (hDo : (fun z => D z) =o[𝓝 x₀] fun z => z - x₀) :
    DifferentiableAt ℝ (fun z => Φ z t) x₀ :=
  (hasFDerivAt_flow_of_defect_isLittleO_eventually hA hΦ' h0' hΦ h0 x₀ ht0 hDnn hdefect
    hDo).differentiableAt

open Asymptotics Filter in
/-- **The Fréchet derivative of the flow map is the resolvent** (local defect-modulus form):
`fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t = D_x Φ_t`. -/
theorem fderiv_flow_of_defect_isLittleO_eventually
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {D : E → ℝ} (hDnn : ∀ z, 0 ≤ D z)
    (hdefect : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ D z)
    (hDo : (fun z => D z) =o[𝓝 x₀] fun z => z - x₀) :
    fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t :=
  (hasFDerivAt_flow_of_defect_isLittleO_eventually hA hΦ' h0' hΦ h0 x₀ ht0 hDnn hdefect
    hDo).fderiv

open Asymptotics Filter in
/-- **Local form of `hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero`.**  The per-time defect
bound `‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ C z · (exp (K |s - t₀|) · ‖z - x₀‖)`,
with `C z → 0`, is required only for `z` in a neighbourhood of `x₀`.  Reduces to
`hasFDerivAt_flow_of_defect_isLittleO_eventually` with `D z = C z · exp (K (t - t₀)) · ‖z - x₀‖`. -/
theorem hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero_eventually
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {C : E → ℝ} (hCnn : ∀ z, 0 ≤ C z) (hCto : Tendsto C (𝓝 x₀) (𝓝 0))
    (hdefect : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖
        ≤ C z * (Real.exp ((K : ℝ) * |s - t₀|) * ‖z - x₀‖)) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ := by
  set D : E → ℝ := fun z => C z * (Real.exp ((K : ℝ) * (t - t₀)) * ‖z - x₀‖) with hD
  have hDnn : ∀ z, 0 ≤ D z := fun z =>
    mul_nonneg (hCnn z) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
  have hdefect' : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ D z := by
    filter_upwards [hdefect] with z hdefectz
    intro s hs
    have hsle : |s - t₀| ≤ t - t₀ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
      exact sub_le_sub_right hs.2.le t₀
    have hexple : Real.exp ((K : ℝ) * |s - t₀|) ≤ Real.exp ((K : ℝ) * (t - t₀)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsle K.coe_nonneg)
    refine (hdefectz s hs).trans ?_
    simp only [hD]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hexple (norm_nonneg _)) (hCnn z)
  have hDo : (fun z => D z) =o[𝓝 x₀] fun z => z - x₀ := by
    refine isLittleO_of_norm_le_mul_of_tendsto_nhds_zero
      (g := fun z => C z * Real.exp ((K : ℝ) * (t - t₀))) ?_ ?_
    · refine Filter.Eventually.of_forall (fun z => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hDnn z)]
      refine le_of_eq ?_
      simp only [hD]
      ring
    · simpa using hCto.mul_const (Real.exp ((K : ℝ) * (t - t₀)))
  exact hasFDerivAt_flow_of_defect_isLittleO_eventually hA hΦ' h0' hΦ h0 x₀ ht0 hDnn hdefect' hDo

open Asymptotics Filter in
/-- Local form of `differentiableAt_flow_of_uniform_oscillation_tendsto_zero`. -/
theorem differentiableAt_flow_of_uniform_oscillation_tendsto_zero_eventually
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {C : E → ℝ} (hCnn : ∀ z, 0 ≤ C z) (hCto : Tendsto C (𝓝 x₀) (𝓝 0))
    (hdefect : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖
        ≤ C z * (Real.exp ((K : ℝ) * |s - t₀|) * ‖z - x₀‖)) :
    DifferentiableAt ℝ (fun z => Φ z t) x₀ :=
  (hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero_eventually hA hΦ' h0' hΦ h0 x₀ ht0 hCnn
    hCto hdefect).differentiableAt

open Asymptotics Filter in
/-- Local form of `fderiv_flow_of_uniform_oscillation_tendsto_zero`. -/
theorem fderiv_flow_of_uniform_oscillation_tendsto_zero_eventually
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {C : E → ℝ} (hCnn : ∀ z, 0 ≤ C z) (hCto : Tendsto C (𝓝 x₀) (𝓝 0))
    (hdefect : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖
        ≤ C z * (Real.exp ((K : ℝ) * |s - t₀|) * ‖z - x₀‖)) :
    fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t :=
  (hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero_eventually hA hΦ' h0' hΦ h0 x₀ ht0 hCnn
    hCto hdefect).fderiv

open Asymptotics Filter in
/-- **Local form of `hasFDerivAt_flow_of_segment_oscillation_tendsto_zero`.**  The derivative
existence on trajectory chords and the chord-oscillation bound `‖Dv s ξ - A s‖ ≤ C z` (with
`C z → 0`) are required only for `z` in a neighbourhood of `x₀`.  The mean-value bound
`norm_flow_defect_le_of_segment_oscillation` converts them (eventually) into the defect modulus of
`hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero_eventually`. -/
theorem hasFDerivAt_flow_of_segment_oscillation_tendsto_zero_eventually
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {C : E → ℝ} (hCnn : ∀ z, 0 ≤ C z) (hCto : Tendsto C (𝓝 x₀) (𝓝 0))
    (hosc : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ C z) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ := by
  have hdefect : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t,
      ‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖
        ≤ C z * (Real.exp ((K : ℝ) * |s - t₀|) * ‖z - x₀‖) := by
    filter_upwards [hderiv, hosc] with z hderivz hoscz
    intro s hs
    exact norm_flow_defect_le_of_segment_oscillation hv hΦ h0 x₀ z s (hderivz s hs) (hoscz s hs)
  exact hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero_eventually hA hΦ' h0' hΦ h0 x₀ ht0
    hCnn hCto hdefect

open Asymptotics Filter in
/-- Local form of `differentiableAt_flow_of_segment_oscillation_tendsto_zero`. -/
theorem differentiableAt_flow_of_segment_oscillation_tendsto_zero_eventually
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {C : E → ℝ} (hCnn : ∀ z, 0 ≤ C z) (hCto : Tendsto C (𝓝 x₀) (𝓝 0))
    (hosc : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ C z) :
    DifferentiableAt ℝ (fun z => Φ z t) x₀ :=
  (hasFDerivAt_flow_of_segment_oscillation_tendsto_zero_eventually hv hA hΦ' h0' hΦ h0 x₀ ht0
    hderiv hCnn hCto hosc).differentiableAt

open Asymptotics Filter in
/-- Local form of `fderiv_flow_of_segment_oscillation_tendsto_zero`. -/
theorem fderiv_flow_of_segment_oscillation_tendsto_zero_eventually
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {C : E → ℝ} (hCnn : ∀ z, 0 ≤ C z) (hCto : Tendsto C (𝓝 x₀) (𝓝 0))
    (hosc : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ C z) :
    fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t :=
  (hasFDerivAt_flow_of_segment_oscillation_tendsto_zero_eventually hv hA hΦ' h0' hΦ h0 x₀ ht0
    hderiv hCnn hCto hosc).fderiv

open Asymptotics Filter in
/-- **Local form of `hasFDerivAt_flow_of_uniform_deriv_modulus`.**  With a nonnegative, monotone
modulus `ω` vanishing at `0⁺`, the derivative existence on trajectory chords and the modulus bound
`‖Dv s ξ - A s‖ ≤ ω (‖ξ - Φ x₀ s‖)` are required only for `z` in a neighbourhood of `x₀`.  Same
proof as the global form (the chord points lie within `exp (K (t - t₀)) · ‖z - x₀‖` of the anchor,
so `C z := ω (exp (K (t - t₀)) · ‖z - x₀‖) → 0` caps the oscillation), feeding
`hasFDerivAt_flow_of_segment_oscillation_tendsto_zero_eventually`. -/
theorem hasFDerivAt_flow_of_uniform_deriv_modulus_eventually
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {ω : ℝ → ℝ} (hωnn : ∀ r, 0 ≤ ω r) (hωmono : Monotone ω)
    (hω0 : Tendsto ω (𝓝[≥] (0 : ℝ)) (𝓝 0))
    (hmod : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ ω (‖ξ - Φ x₀ s‖)) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ := by
  set c : ℝ := Real.exp ((K : ℝ) * (t - t₀)) with hc
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  set C : E → ℝ := fun z => ω (c * ‖z - x₀‖) with hC
  have hCnn : ∀ z, 0 ≤ C z := fun z => hωnn _
  have hCto : Tendsto C (𝓝 x₀) (𝓝 0) := tendsto_modulus_comp_norm_sub x₀ hc0 hω0
  have hosc : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ C z := by
    filter_upwards [hmod] with z hmodz
    intro s hs ξ hξ
    have hle : ‖ξ - Φ x₀ s‖ ≤ c * ‖z - x₀‖ := by
      obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hξ
      have hq1 : q ≤ 1 := by linarith
      have heq : (p • Φ x₀ s + q • Φ z s) - Φ x₀ s = q • (Φ z s - Φ x₀ s) := by
        have hp1 : p = 1 - q := by linarith
        rw [hp1, sub_smul, one_smul, smul_sub]
        abel
      have hsep : ‖Φ z s - Φ x₀ s‖ ≤ ‖z - x₀‖ * Real.exp ((K : ℝ) * |s - t₀|) := by
        have h := dist_flow_apply_le hv hΦ h0 z x₀ s
        rwa [dist_eq_norm, dist_eq_norm] at h
      have hexp : Real.exp ((K : ℝ) * |s - t₀|) ≤ c := by
        rw [hc]
        refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ K.coe_nonneg)
        rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
        exact sub_le_sub_right hs.2.le t₀
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq]
      calc q * ‖Φ z s - Φ x₀ s‖ ≤ 1 * ‖Φ z s - Φ x₀ s‖ :=
            mul_le_mul_of_nonneg_right hq1 (norm_nonneg _)
        _ = ‖Φ z s - Φ x₀ s‖ := one_mul _
        _ ≤ ‖z - x₀‖ * Real.exp ((K : ℝ) * |s - t₀|) := hsep
        _ ≤ ‖z - x₀‖ * c := mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
        _ = c * ‖z - x₀‖ := mul_comm _ _
    calc ‖Dv s ξ - A s‖ ≤ ω (‖ξ - Φ x₀ s‖) := hmodz s hs ξ hξ
      _ ≤ ω (c * ‖z - x₀‖) := hωmono hle
      _ = C z := by simp only [hC]
  exact hasFDerivAt_flow_of_segment_oscillation_tendsto_zero_eventually hv hA hΦ' h0' hΦ h0 x₀ ht0
    hderiv hCnn hCto hosc

open Asymptotics Filter in
/-- Local form of `differentiableAt_flow_of_uniform_deriv_modulus`. -/
theorem differentiableAt_flow_of_uniform_deriv_modulus_eventually
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {ω : ℝ → ℝ} (hωnn : ∀ r, 0 ≤ ω r) (hωmono : Monotone ω)
    (hω0 : Tendsto ω (𝓝[≥] (0 : ℝ)) (𝓝 0))
    (hmod : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ ω (‖ξ - Φ x₀ s‖)) :
    DifferentiableAt ℝ (fun z => Φ z t) x₀ :=
  (hasFDerivAt_flow_of_uniform_deriv_modulus_eventually hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hωnn
    hωmono hω0 hmod).differentiableAt

open Asymptotics Filter in
/-- Local form of `fderiv_flow_of_uniform_deriv_modulus`. -/
theorem fderiv_flow_of_uniform_deriv_modulus_eventually
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {ω : ℝ → ℝ} (hωnn : ∀ r, 0 ≤ ω r) (hωmono : Monotone ω)
    (hω0 : Tendsto ω (𝓝[≥] (0 : ℝ)) (𝓝 0))
    (hmod : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ ω (‖ξ - Φ x₀ s‖)) :
    fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t :=
  (hasFDerivAt_flow_of_uniform_deriv_modulus_eventually hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hωnn
    hωmono hω0 hmod).fderiv

/-!
### The local `C^{1,1}` entry point: a *locally* Lipschitz spatial derivative

The practical payoff of the localisation.  A genuine smooth field has a spatial derivative that is
only **locally** Lipschitz, so the global bound `‖Dv s ξ - A s‖ ≤ L · ‖ξ - Φ x₀ s‖` of
`hasFDerivAt_flow_of_lipschitz_deriv` need not hold for *all* `z`.  It does hold, however, for `z`
ranging over a neighbourhood of `x₀` (where the chord `[Φ x₀ s, Φ z s]` stays inside the region on
which the local Lipschitz estimate is valid).  These `_eventually` forms are exactly what such a
field supplies, giving unconditional `C¹` dependence of the flow on initial data for every smooth
field. -/

open Asymptotics Filter in
/-- **Local `C^{1,1}` `C¹`-dependence.**  If the derivative oscillation is Lipschitz in the distance
to the anchor trajectory, `‖Dv s ξ - A s‖ ≤ L · ‖ξ - Φ x₀ s‖`, for `z` in a neighbourhood of `x₀`,
then `x ↦ Φ x t` is Fréchet differentiable at `x₀` with derivative the resolvent.  The linear
modulus `ω r = L · max r 0` discharges `hasFDerivAt_flow_of_uniform_deriv_modulus_eventually`. -/
theorem hasFDerivAt_flow_of_lipschitz_deriv_eventually
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ L * ‖ξ - Φ x₀ s‖) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ := by
  refine hasFDerivAt_flow_of_uniform_deriv_modulus_eventually hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv
    (ω := fun r => L * max r 0) (fun r => mul_nonneg hL (le_max_right r 0)) ?_ ?_ ?_
  · intro a b hab
    exact mul_le_mul_of_nonneg_left (max_le_max hab le_rfl) hL
  · have hbase : Tendsto (fun r : ℝ => L * r) (𝓝[≥] (0 : ℝ)) (𝓝 0) := by
      have h2 : Tendsto (fun r : ℝ => L * r) (𝓝 (0 : ℝ)) (𝓝 0) := by
        have hc : Continuous (fun r : ℝ => L * r) := by fun_prop
        simpa only [mul_zero] using hc.tendsto (0 : ℝ)
      exact h2.mono_left nhdsWithin_le_nhds
    refine hbase.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [max_eq_left (Set.mem_Ici.mp hr)]
  · filter_upwards [hlip] with z hlipz
    intro s hs ξ hξ
    simpa [max_eq_left (norm_nonneg (ξ - Φ x₀ s))] using hlipz s hs ξ hξ

open Asymptotics Filter in
/-- Local form of `differentiableAt_flow_of_lipschitz_deriv`. -/
theorem differentiableAt_flow_of_lipschitz_deriv_eventually
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ L * ‖ξ - Φ x₀ s‖) :
    DifferentiableAt ℝ (fun z => Φ z t) x₀ :=
  (hasFDerivAt_flow_of_lipschitz_deriv_eventually hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hL
    hlip).differentiableAt

open Asymptotics Filter in
/-- Local form of `fderiv_flow_of_lipschitz_deriv`. -/
theorem fderiv_flow_of_lipschitz_deriv_eventually
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      HasFDerivWithinAt (v s) (Dv s ξ) (segment ℝ (Φ x₀ s) (Φ z s)) ξ)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ L * ‖ξ - Φ x₀ s‖) :
    fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t :=
  (hasFDerivAt_flow_of_lipschitz_deriv_eventually hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hL hlip).fderiv

open Asymptotics Filter in
/-- **Global-derivative convenience form** of `hasFDerivAt_flow_of_lipschitz_deriv_eventually`.
Takes the *global* Fréchet derivative `HasFDerivAt (v s) (Dv s ξ) ξ` at every point (as a genuine
`C¹` field provides) instead of the chord-restricted `HasFDerivWithinAt`, so only the *local*
Lipschitz-derivative bound (`∀ᶠ z in 𝓝 x₀`) need be supplied.  The single cleanest entry point to
the `C¹` flow-dependence tower for a smooth field whose derivative is *locally* Lipschitz. -/
theorem hasFDerivAt_flow_of_lipschitz_deriv_of_hasFDerivAt_eventually
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ‖Dv s ξ - A s‖ ≤ L * ‖ξ - Φ x₀ s‖) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ :=
  hasFDerivAt_flow_of_lipschitz_deriv_eventually hv hA hΦ' h0' hΦ h0 x₀ ht0
    (Filter.Eventually.of_forall (fun _ s _ ξ _ => (hderiv s ξ).hasFDerivWithinAt)) hL hlip

open Filter in
/-- **`C¹` dependence from a spatial derivative Lipschitz on a ball around the anchor trajectory.**
The most directly consumable entry point for a smooth field on a chart: `v s` has a global spatial
derivative `Dv s` (`HasFDerivAt (v s) (Dv s ξ) ξ`), and on the fixed radius-`r` ball around each
anchor point `Φ x₀ s` (`s ∈ Ico t₀ t`) the derivative oscillation is `L`-Lipschitz in the distance
to the anchor, `‖Dv s ξ - A s‖ ≤ L · ‖ξ - Φ x₀ s‖`.  Then `x ↦ Φ x t` is Fréchet differentiable at
`x₀` with derivative the resolvent.  A genuine `C^∞` field supplies exactly this — its derivative is
*locally* Lipschitz on balls — even when it is not *globally* Lipschitz-derivative.  The proof shows
that for `‖z - x₀‖ < r / exp (K (t - t₀))` every trajectory chord `[Φ x₀ s, Φ z s]` stays inside the
`r`-ball (flow separation `‖Φ z s - Φ x₀ s‖ ≤ exp (K (t - t₀)) ‖z - x₀‖`), so the ball estimate
supplies the *eventual* Lipschitz-derivative hypothesis of
`hasFDerivAt_flow_of_lipschitz_deriv_eventually`. -/
theorem hasFDerivAt_flow_of_lipschitz_deriv_on_ball
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    {r : ℝ} (hr : 0 < r) {L : ℝ} (hL : 0 ≤ L)
    (hlipball : ∀ s ∈ Ico t₀ t, ∀ ξ ∈ Metric.closedBall (Φ x₀ s) r,
      ‖Dv s ξ - A s‖ ≤ L * ‖ξ - Φ x₀ s‖) :
    HasFDerivAt (fun z => Φ z t) (fundamentalSolution hA hΦ' h0' t) x₀ := by
  set c : ℝ := Real.exp ((K : ℝ) * (t - t₀)) with hc
  have hc0 : 0 < c := Real.exp_pos _
  -- for `z` in the ball of radius `r / c`, every chord point stays in the `r`-ball around the anchor
  have hev : ∀ᶠ z in 𝓝 x₀, ∀ s ∈ Ico t₀ t, ∀ ξ ∈ segment ℝ (Φ x₀ s) (Φ z s),
      ξ ∈ Metric.closedBall (Φ x₀ s) r := by
    filter_upwards [Metric.ball_mem_nhds x₀ (by positivity : 0 < r / c)] with z hz
    intro s hs ξ hξ
    have hzlt : ‖z - x₀‖ < r / c := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hz
    have hle : ‖ξ - Φ x₀ s‖ ≤ c * ‖z - x₀‖ := by
      obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hξ
      have hq1 : q ≤ 1 := by linarith
      have heq : (p • Φ x₀ s + q • Φ z s) - Φ x₀ s = q • (Φ z s - Φ x₀ s) := by
        have hp1 : p = 1 - q := by linarith
        rw [hp1, sub_smul, one_smul, smul_sub]
        abel
      have hsep : ‖Φ z s - Φ x₀ s‖ ≤ ‖z - x₀‖ * Real.exp ((K : ℝ) * |s - t₀|) := by
        have h := dist_flow_apply_le hv hΦ h0 z x₀ s
        rwa [dist_eq_norm, dist_eq_norm] at h
      have hexp : Real.exp ((K : ℝ) * |s - t₀|) ≤ c := by
        rw [hc]
        refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ K.coe_nonneg)
        rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
        exact sub_le_sub_right hs.2.le t₀
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq]
      calc q * ‖Φ z s - Φ x₀ s‖ ≤ 1 * ‖Φ z s - Φ x₀ s‖ :=
            mul_le_mul_of_nonneg_right hq1 (norm_nonneg _)
        _ = ‖Φ z s - Φ x₀ s‖ := one_mul _
        _ ≤ ‖z - x₀‖ * Real.exp ((K : ℝ) * |s - t₀|) := hsep
        _ ≤ ‖z - x₀‖ * c := mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
        _ = c * ‖z - x₀‖ := mul_comm _ _
    have hcrc : c * (r / c) = r := by field_simp
    have hlt : c * ‖z - x₀‖ < r := by
      have h := mul_lt_mul_of_pos_left hzlt hc0
      rwa [hcrc] at h
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact le_of_lt (lt_of_le_of_lt hle hlt)
  refine hasFDerivAt_flow_of_lipschitz_deriv_eventually hv hA hΦ' h0' hΦ h0 x₀ ht0
    (Eventually.of_forall (fun _ s _ ξ _ => (hderiv s ξ).hasFDerivWithinAt)) hL ?_
  filter_upwards [hev] with z hzev
  intro s hs ξ hξ
  exact hlipball s hs ξ (hzev s hs ξ hξ)

open Filter in
/-- The flow map is differentiable at `x₀` from a ball-Lipschitz spatial derivative
(`hasFDerivAt_flow_of_lipschitz_deriv_on_ball`). -/
theorem differentiableAt_flow_of_lipschitz_deriv_on_ball
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    {r : ℝ} (hr : 0 < r) {L : ℝ} (hL : 0 ≤ L)
    (hlipball : ∀ s ∈ Ico t₀ t, ∀ ξ ∈ Metric.closedBall (Φ x₀ s) r,
      ‖Dv s ξ - A s‖ ≤ L * ‖ξ - Φ x₀ s‖) :
    DifferentiableAt ℝ (fun z => Φ z t) x₀ :=
  (hasFDerivAt_flow_of_lipschitz_deriv_on_ball hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hr hL
    hlipball).differentiableAt

open Filter in
/-- The Fréchet derivative of the flow map is the resolvent, from a ball-Lipschitz spatial
derivative (`hasFDerivAt_flow_of_lipschitz_deriv_on_ball`). -/
theorem fderiv_flow_of_lipschitz_deriv_on_ball
    (hv : ∀ τ, LipschitzWith K (v τ))
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    {r : ℝ} (hr : 0 < r) {L : ℝ} (hL : 0 ≤ L)
    (hlipball : ∀ s ∈ Ico t₀ t, ∀ ξ ∈ Metric.closedBall (Φ x₀ s) r,
      ‖Dv s ξ - A s‖ ≤ L * ‖ξ - Φ x₀ s‖) :
    fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution hA hΦ' h0' t :=
  (hasFDerivAt_flow_of_lipschitz_deriv_on_ball hv hA hΦ' h0' hΦ h0 x₀ ht0 hderiv hr hL
    hlipball).fderiv

/-!
### Continuous dependence of the resolvent on the coefficient field

The fundamental solution `D_x Φ_t` depends continuously — indeed Lipschitz-ly — on the coefficient
field `A`.  If two uniformly-`K`-bounded coefficients `A`, `A'` are uniformly `ε`-close,
`‖A s - A' s‖ ≤ ε`, then on a forward compact time interval `[t₀, T]` their resolvents differ in
operator norm by at most `ε · exp (K (T - t₀)) · gronwallBound 0 K 1 (t - t₀)`.  The linearised
perturbation `‖(A s - A' s) u‖ ≤ ε ‖u‖` is *not uniform* in `u`, so this is not a corollary of the
uniform-field-perturbation bound `dist_flow_perturb_le`; instead it uses the a-priori trajectory
growth `‖Φ₂ u₀ s‖ ≤ exp (K (T - t₀)) ‖u₀‖` (`norm_flow_variationalFieldVec_le`) to turn the
per-point linearisation defect into a *uniform* one on the compact interval, then feeds Mathlib's
approximate-trajectory Grönwall estimate `dist_le_of_approx_trajectories_ODE`.  This is the
operator-level continuous dependence of the linearised flow / resolvent on its coefficient — an
input to the `C²` regularity of the flow in initial data (where `A` itself varies with the base
point) and to the continuous dependence of the DeTurck flow on the metric. -/

/-- **Nonnegativity of the unit Grönwall bound.**  `0 ≤ gronwallBound 0 K 1 x` for `0 ≤ K` and
`0 ≤ x`: on the diagonal `δ = 0`, `ε = 1`, the bound is `x` (if `K = 0`) or `(exp (K x) - 1)/K ≥ 0`
(if `K > 0`). -/
theorem gronwallBound_zero_one_nonneg {K x : ℝ} (hK : 0 ≤ K) (hx : 0 ≤ x) :
    0 ≤ gronwallBound 0 K 1 x := by
  rcases eq_or_lt_of_le hK with hK0 | hK0
  · rw [← hK0]
    simp only [gronwallBound_K0]
    simpa using hx
  · rw [gronwallBound_of_K_ne_0 (ne_of_gt hK0)]
    have hexp : (1 : ℝ) ≤ Real.exp (K * x) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (mul_nonneg hK0.le hx)
    have h1 : (0 : ℝ) ≤ Real.exp (K * x) - 1 := by linarith
    have h2 : (0 : ℝ) ≤ 1 / K := by positivity
    simp only [zero_mul, zero_add]
    exact mul_nonneg h2 h1

/-- **Continuous dependence of the resolvent on the coefficient (directional form).**  For two
uniformly-`K`-bounded coefficient fields `A`, `A'` with variational flow families `Φ₁`, `Φ₂`, and
`‖A s - A' s‖ ≤ ε` for all `s`, the resolvents applied to a fixed direction `u₀` satisfy, on the
forward compact interval `[t₀, T]`,
`‖D_x Φ_t^A u₀ - D_x Φ_t^{A'} u₀‖ ≤ ε · exp (K (T - t₀)) · ‖u₀‖ · gronwallBound 0 K 1 (t - t₀)`.
The `A'`-column `s ↦ Φ₂ u₀ s` is treated as an approximate solution of the `A`-field, its
linearisation defect `‖(A' s - A s)(Φ₂ u₀ s)‖ ≤ ε · exp (K (T - t₀)) · ‖u₀‖` uniform on `[t₀, T]`. -/
theorem norm_fundamentalSolution_sub_apply_le_of_forall_le
    {A A' : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K) (hA' : ∀ s, ‖A' s‖₊ ≤ K)
    {Φ₁ Φ₂ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec A)) (h1 : ∀ x, Φ₁ x t₀ = x)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec A')) (h2 : ∀ x, Φ₂ x t₀ = x)
    {ε : ℝ} (hAA' : ∀ s, ‖A s - A' s‖ ≤ ε)
    (u₀ : E) {T t : ℝ} (ht : t ∈ Icc t₀ T) :
    ‖fundamentalSolution hA hΦ₁ h1 t u₀ - fundamentalSolution hA' hΦ₂ h2 t u₀‖
      ≤ ε * Real.exp ((K : ℝ) * (T - t₀)) * ‖u₀‖ * gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
  set εg : ℝ := ε * Real.exp ((K : ℝ) * (T - t₀)) * ‖u₀‖ with hεg
  have hgbound : ∀ s ∈ Ico t₀ T,
      dist (variationalFieldVec A' s (Φ₂ u₀ s)) (variationalFieldVec A s (Φ₂ u₀ s)) ≤ εg := by
    intro s hs
    have hsle : |s - t₀| ≤ T - t₀ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
      exact sub_le_sub_right hs.2.le t₀
    have hgnorm : ‖Φ₂ u₀ s‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) * ‖u₀‖ := by
      refine (norm_flow_variationalFieldVec_le hA' hΦ₂ h2 u₀ s).trans ?_
      exact mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsle K.coe_nonneg)) (norm_nonneg _)
    have hcoeff : ‖A' s - A s‖ ≤ ε := by
      rw [show A' s - A s = -(A s - A' s) by abel, norm_neg]; exact hAA' s
    calc dist (variationalFieldVec A' s (Φ₂ u₀ s)) (variationalFieldVec A s (Φ₂ u₀ s))
        = ‖(A' s - A s) (Φ₂ u₀ s)‖ := by
          simp only [variationalFieldVec, dist_eq_norm, ContinuousLinearMap.sub_apply]
      _ ≤ ‖A' s - A s‖ * ‖Φ₂ u₀ s‖ := (A' s - A s).le_opNorm _
      _ ≤ ε * (Real.exp ((K : ℝ) * (T - t₀)) * ‖u₀‖) :=
          mul_le_mul hcoeff hgnorm (norm_nonneg _) (le_trans (norm_nonneg _) hcoeff)
      _ = εg := by rw [hεg]; ring
  have key := dist_le_of_approx_trajectories_ODE
    (v := variationalFieldVec A) (a := t₀) (b := T)
    (f := fun s => Φ₁ u₀ s) (g := fun s => Φ₂ u₀ s)
    (f' := fun s => variationalFieldVec A s (Φ₁ u₀ s))
    (g' := fun s => variationalFieldVec A' s (Φ₂ u₀ s))
    (εf := 0) (εg := εg) (δ := 0) (K := K)
    (fun s => lipschitzWith_variationalFieldVec hA s)
    (hΦ₁ u₀).continuous.continuousOn
    (fun s _ => (hΦ₁ u₀ s).hasDerivWithinAt)
    (fun s _ => le_of_eq (dist_self _))
    (hΦ₂ u₀).continuous.continuousOn
    (fun s _ => (hΦ₂ u₀ s).hasDerivWithinAt)
    hgbound
    (by simp [h1, h2])
  have hb := key t ht
  rw [zero_add, gronwallBound_zero_left_mul] at hb
  rw [fundamentalSolution_apply, fundamentalSolution_apply, ← dist_eq_norm]
  exact hb

/-- **Operator-norm continuous dependence of the resolvent on the coefficient.**  Assembling the
directional bound `norm_fundamentalSolution_sub_apply_le_of_forall_le` over all unit directions:
for coefficient fields `A`, `A'` (both `≤ K`) with `‖A s - A' s‖ ≤ ε`, the resolvents satisfy
`‖D_x Φ_t^A - D_x Φ_t^{A'}‖ ≤ ε · exp (K (T - t₀)) · gronwallBound 0 K 1 (t - t₀)` on `[t₀, T]`.
The resolvent is thus a (locally) Lipschitz function of its coefficient field. -/
theorem norm_fundamentalSolution_sub_le_of_forall_le
    {A A' : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K) (hA' : ∀ s, ‖A' s‖₊ ≤ K)
    {Φ₁ Φ₂ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec A)) (h1 : ∀ x, Φ₁ x t₀ = x)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec A')) (h2 : ∀ x, Φ₂ x t₀ = x)
    {ε : ℝ} (hε : 0 ≤ ε) (hAA' : ∀ s, ‖A s - A' s‖ ≤ ε)
    {T t : ℝ} (ht : t ∈ Icc t₀ T) :
    ‖fundamentalSolution hA hΦ₁ h1 t - fundamentalSolution hA' hΦ₂ h2 t‖
      ≤ ε * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ (fun u₀ => ?_)
  · exact mul_nonneg (mul_nonneg hε (Real.exp_pos _).le)
      (gronwallBound_zero_one_nonneg K.coe_nonneg (sub_nonneg.mpr ht.1))
  · rw [ContinuousLinearMap.sub_apply]
    refine (norm_fundamentalSolution_sub_apply_le_of_forall_le hA hA' hΦ₁ h1 hΦ₂ h2 hAA' u₀ ht).trans
      (le_of_eq ?_)
    ring

/-- **Operator-norm local Lipschitz continuity of the resolvent in time.**  Beyond the
strong (fixed-direction) continuity `continuous_fundamentalSolution_apply`, the fundamental
solution is Lipschitz in time in the *operator* norm on every bounded time window: for any
two times `t₁`, `t₂`,
`‖D_x Φ_{t₂} - D_x Φ_{t₁}‖ ≤ K · exp (K · max |t₁ - t₀| |t₂ - t₀|) · |t₂ - t₁|`.  Each
resolvent column `s ↦ Φ u s` solves the variational ODE `u' = A s (u s)`, so the
one-dimensional mean-value inequality bounds its increment by the supremum over the time
window of `‖A s (Φ u s)‖ ≤ K · exp (K |s - t₀|) · ‖u‖`; the exponential is maximised at an
endpoint (`abs_le_max_abs_abs`), and taking the operator-norm supremum over unit directions
gives the stated bound.  This upgrades the resolvent path `t ↦ D_x Φ_t` from strongly
continuous to norm-continuous — an input to the `C^k` bootstrap (continuity of the resolvent
in time) and to Bochner integration of the resolvent in the parabolic theory. -/
theorem norm_fundamentalSolution_sub_le_time {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t₁ t₂ : ℝ) :
    ‖fundamentalSolution hA hΦ h0 t₂ - fundamentalSolution hA hΦ h0 t₁‖
      ≤ (K : ℝ) * Real.exp ((K : ℝ) * max |t₁ - t₀| |t₂ - t₀|) * |t₂ - t₁| := by
  set C : ℝ := (K : ℝ) * Real.exp ((K : ℝ) * max |t₁ - t₀| |t₂ - t₀|) with hCdef
  have hC0 : 0 ≤ C := mul_nonneg K.coe_nonneg (Real.exp_pos _).le
  have habs : ∀ σ ∈ Set.uIcc t₁ t₂, |σ - t₀| ≤ max |t₁ - t₀| |t₂ - t₀| := by
    intro σ hσ
    rcases le_total t₁ t₂ with h | h
    · rw [Set.uIcc_of_le h, Set.mem_Icc] at hσ
      obtain ⟨hσ1, hσ2⟩ := hσ
      exact abs_le_max_abs_abs (by linarith) (by linarith)
    · rw [Set.uIcc_of_ge h, Set.mem_Icc] at hσ
      obtain ⟨hσ1, hσ2⟩ := hσ
      rw [max_comm]
      exact abs_le_max_abs_abs (by linarith) (by linarith)
  have key : ∀ u : E, ‖Φ u t₂ - Φ u t₁‖ ≤ C * |t₂ - t₁| * ‖u‖ := by
    intro u
    have hderiv : ∀ σ ∈ Set.uIcc t₁ t₂,
        HasDerivWithinAt (Φ u) (A σ (Φ u σ)) (Set.uIcc t₁ t₂) σ :=
      fun σ _ => (hΦ u σ).hasDerivWithinAt
    have hbound : ∀ σ ∈ Set.uIcc t₁ t₂, ‖A σ (Φ u σ)‖ ≤ C * ‖u‖ := by
      intro σ hσ
      have hAσ : ‖A σ‖ ≤ (K : ℝ) := by exact_mod_cast hA σ
      have hexp : Real.exp ((K : ℝ) * |σ - t₀|)
          ≤ Real.exp ((K : ℝ) * max |t₁ - t₀| |t₂ - t₀|) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (habs σ hσ) K.coe_nonneg)
      have hΦσ : ‖Φ u σ‖ ≤ Real.exp ((K : ℝ) * max |t₁ - t₀| |t₂ - t₀|) * ‖u‖ :=
        (norm_flow_variationalFieldVec_le hA hΦ h0 u σ).trans
          (mul_le_mul_of_nonneg_right hexp (norm_nonneg u))
      calc ‖A σ (Φ u σ)‖ ≤ ‖A σ‖ * ‖Φ u σ‖ := (A σ).le_opNorm _
        _ ≤ (K : ℝ) * (Real.exp ((K : ℝ) * max |t₁ - t₀| |t₂ - t₀|) * ‖u‖) :=
            mul_le_mul hAσ hΦσ (norm_nonneg _) K.coe_nonneg
        _ = C * ‖u‖ := by rw [hCdef]; ring
    have hmv : ‖Φ u t₂ - Φ u t₁‖ ≤ C * ‖u‖ * |t₂ - t₁| := by
      have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
        (convex_uIcc t₁ t₂) left_mem_uIcc right_mem_uIcc
      rwa [Real.norm_eq_abs] at h
    calc ‖Φ u t₂ - Φ u t₁‖ ≤ C * ‖u‖ * |t₂ - t₁| := hmv
      _ = C * |t₂ - t₁| * ‖u‖ := by ring
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC0 (abs_nonneg _)) (fun u => ?_)
  simp only [ContinuousLinearMap.sub_apply, fundamentalSolution_apply]
  exact key u

/-- **The resolvent path is norm-continuous in time.**  `t ↦ D_x Φ_t` is a continuous curve in
the operator Banach space `E →L[ℝ] E`, not merely strongly (fixed-direction) continuous:
immediate from the operator-norm local-Lipschitz bound `norm_fundamentalSolution_sub_le_time` by
squeezing the distance `‖D_x Φ_a - D_x Φ_t‖` between `0` and the vanishing bound
`K · exp (K · max |t - t₀| |a - t₀|) · |a - t| → 0`.  This norm-continuity of the resolvent as a
curve of operators is the input consumed when Bochner-integrating the resolvent along time (the
Duhamel/variation-of-constants representation) in the parabolic theory. -/
theorem continuous_fundamentalSolution_time {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x) :
    Continuous (fun t => fundamentalSolution hA hΦ h0 t) := by
  rw [continuous_iff_continuousAt]
  intro t
  show Filter.Tendsto (fun a => fundamentalSolution hA hΦ h0 a) (𝓝 t)
    (𝓝 (fundamentalSolution hA hΦ h0 t))
  rw [tendsto_iff_dist_tendsto_zero]
  have hgcont : Continuous
      (fun a => (K : ℝ) * Real.exp ((K : ℝ) * max |t - t₀| |a - t₀|) * |a - t|) := by
    fun_prop
  have hgt : (K : ℝ) * Real.exp ((K : ℝ) * max |t - t₀| |t - t₀|) * |t - t| = 0 := by simp
  refine squeeze_zero (fun a => dist_nonneg) (fun a => ?_) (hgcont.tendsto' t 0 hgt)
  rw [dist_eq_norm]
  exact norm_fundamentalSolution_sub_le_time hA hΦ h0 t a

open Asymptotics Filter in
/-- **The fundamental solution solves the operator-valued variational ODE (`W' = A W`).**  For a
*norm-continuous* coefficient path `A` (`‖A t‖ ≤ K`), the resolvent `t ↦ D_x Φ_t` is
differentiable in the operator norm with
`d/dt (D_x Φ_t) = A t ∘ (D_x Φ_t)`.  This is genuine *operator-norm* (not merely strong)
differentiability: the linearisation-remainder is controlled uniformly over unit directions.
Proof: each column `s ↦ Φ u s` solves the vector ODE `u' = A s (u s)`, so the operator
Taylor remainder applied to `u` is, by the one-dimensional mean-value inequality, bounded by
`‖s - t‖ · (sup over the chord of ‖A σ ∘ D_x Φ_σ - A t ∘ D_x Φ_t‖) · ‖u‖`; the operator-norm
supremum over `u` and the norm-continuity of `σ ↦ A σ ∘ D_x Φ_σ`
(`continuous_fundamentalSolution_time` composed with `Continuous A`) drive the remainder to
`o(‖s - t‖)`. -/
theorem hasDerivAt_fundamentalSolution {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAcont : Continuous A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) :
    HasDerivAt (fun s => fundamentalSolution hA hΦ h0 s)
      ((A t).comp (fundamentalSolution hA hΦ h0 t)) t := by
  set W : ℝ → (E →L[ℝ] E) := fun s => fundamentalSolution hA hΦ h0 s with hWdef
  set H : ℝ → (E →L[ℝ] E) := fun σ => (A σ).comp (W σ) with hHdef
  have hHcont : Continuous H :=
    hAcont.clm_comp (continuous_fundamentalSolution_time hA hΦ h0)
  rw [hasDerivAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  have hUnhds : {σ : ℝ | ‖H σ - H t‖ < ε} ∈ 𝓝 t := by
    refine (isOpen_lt ((hHcont.sub continuous_const).norm) continuous_const).mem_nhds ?_
    change ‖H t - H t‖ < ε
    simpa only [sub_self, norm_zero] using hε
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hUnhds
  filter_upwards [Metric.ball_mem_nhds t hδ] with s hs
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hε.le (norm_nonneg _)) (fun u => ?_)
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply]
  have hderiv : ∀ σ ∈ Set.uIcc t s,
      HasDerivWithinAt (fun σ => W σ u - (σ - t) • (A t (W t u)))
        (A σ (W σ u) - A t (W t u)) (Set.uIcc t s) σ := by
    intro σ _
    have hcol : HasDerivAt (fun σ => W σ u) (A σ (W σ u)) σ :=
      isIntegralCurve_fundamentalSolution_apply hA hΦ h0 u σ
    have hlin : HasDerivAt (fun σ => (σ - t) • (A t (W t u))) (A t (W t u)) σ := by
      simpa using (((hasDerivAt_id σ).sub (hasDerivAt_const σ t)).smul_const (A t (W t u)))
    exact (hcol.sub hlin).hasDerivWithinAt
  have hbound : ∀ σ ∈ Set.uIcc t s, ‖A σ (W σ u) - A t (W t u)‖ ≤ ε * ‖u‖ := by
    intro σ hσ
    have hσδ : dist σ t < δ := by
      have h1 : dist σ t ≤ dist t s := Real.dist_le_of_mem_uIcc hσ left_mem_uIcc
      rw [dist_comm t s] at h1
      exact lt_of_le_of_lt h1 hs
    have hHσ : ‖H σ - H t‖ < ε := hball (Metric.mem_ball.mpr hσδ)
    have heq : A σ (W σ u) - A t (W t u) = (H σ - H t) u := by
      simp only [hHdef, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
    rw [heq]
    calc ‖(H σ - H t) u‖ ≤ ‖H σ - H t‖ * ‖u‖ := (H σ - H t).le_opNorm u
      _ ≤ ε * ‖u‖ := mul_le_mul_of_nonneg_right hHσ.le (norm_nonneg u)
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_uIcc t s) left_mem_uIcc right_mem_uIcc
  have hφeq : (fun σ => W σ u - (σ - t) • (A t (W t u))) s
      - (fun σ => W σ u - (σ - t) • (A t (W t u))) t
      = W s u - W t u - (s - t) • (A t (W t u)) := by
    simp only [sub_self, zero_smul, sub_zero]
    abel
  rw [hφeq] at hmv
  exact hmv.trans (le_of_eq (by ring))

open Filter in
/-- **The resolvent path is the operator integral curve of the variational field.**  Packaged
form of `hasDerivAt_fundamentalSolution`: for a norm-continuous `A`, the curve `t ↦ D_x Φ_t` is a
global integral curve of the operator variational field `variationalField A` (`W ↦ A t ∘ W`).
Together with `fundamentalSolution_anchor` (`D_x Φ_{t₀} = 1`) this is the full characterisation of
the fundamental solution as *the* solution of the operator ODE `W' = A W`, `W t₀ = 1` — the
statement `fundamentalSolution_eq_of_operator_isIntegralCurve` consumes hypothetically, now
discharged.  It also makes the operator resolvent's own dynamics available to the `C^k` bootstrap. -/
theorem isIntegralCurve_fundamentalSolution {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAcont : Continuous A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x) :
    IsIntegralCurve (fun t => fundamentalSolution hA hΦ h0 t) (variationalField A) :=
  fun t => hasDerivAt_fundamentalSolution hA hAcont hΦ h0 t

/-- **A priori velocity bound for the resolvent path.**  The time-derivative of the resolvent —
the right-hand side `A t ∘ D_x Φ_t` of the operator ODE `hasDerivAt_fundamentalSolution` — has
operator norm at most `K · exp (K · |t - t₀|)`: the resolvent curve moves through operator space
with speed controlled by the same exponential that bounds the resolvent itself.  Immediate from
submultiplicativity of the operator norm and `norm_fundamentalSolution_le`. -/
theorem norm_comp_fundamentalSolution_le {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) :
    ‖(A t).comp (fundamentalSolution hA hΦ h0 t)‖ ≤ (K : ℝ) * Real.exp ((K : ℝ) * |t - t₀|) := by
  refine (ContinuousLinearMap.opNorm_comp_le (A t) (fundamentalSolution hA hΦ h0 t)).trans ?_
  refine mul_le_mul ?_ (norm_fundamentalSolution_le hA hΦ h0 t) (norm_nonneg _) K.coe_nonneg
  exact_mod_cast hA t

open MeasureTheory intervalIntegral in
/-- **The fundamental solution satisfies the Volterra / Duhamel integral equation.**  For a
*norm-continuous* coefficient path `A` (`‖A t‖ ≤ K`), the resolvent `t ↦ D_x Φ_t` obeys the
integral form of the operator variational ODE `W' = A W`, `W t₀ = 1`:
`D_x Φ_t = 1 + ∫_{t₀}^{t} A σ ∘ D_x Φ_σ dσ`.  This is the fixed-point / Picard characterisation of
the fundamental solution: applying the fundamental theorem of calculus
(`intervalIntegral.integral_eq_sub_of_hasDerivAt`) to the operator ODE
`hasDerivAt_fundamentalSolution` — whose right-hand side `σ ↦ A σ ∘ D_x Φ_σ` is norm-continuous
(`hAcont.clm_comp continuous_fundamentalSolution_time`), hence interval-integrable — and folding in
the anchor `fundamentalSolution_anchor` (`D_x Φ_{t₀} = 1`) turns the differential equation into its
Volterra integral equation.  This is the operator-Duhamel identity underlying differentiable
dependence of the resolvent on its coefficient field (the second-order variational equation) toward
the `C^k` bootstrap. -/
theorem fundamentalSolution_eq_one_add_integral {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    [CompleteSpace E]
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAcont : Continuous A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) :
    fundamentalSolution hA hΦ h0 t
      = 1 + ∫ σ in t₀..t, (A σ).comp (fundamentalSolution hA hΦ h0 σ) := by
  have hHcont : Continuous (fun σ => (A σ).comp (fundamentalSolution hA hΦ h0 σ)) :=
    hAcont.clm_comp (continuous_fundamentalSolution_time hA hΦ h0)
  have hderiv : ∀ σ ∈ Set.uIcc t₀ t,
      HasDerivAt (fun s => fundamentalSolution hA hΦ h0 s)
        ((A σ).comp (fundamentalSolution hA hΦ h0 σ)) σ :=
    fun σ _ => hasDerivAt_fundamentalSolution hA hAcont hΦ h0 σ
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hHcont.intervalIntegrable t₀ t)
  rw [fundamentalSolution_anchor hA hΦ h0] at hint
  rw [hint, ← ContinuousLinearMap.one_def]
  abel

open MeasureTheory intervalIntegral in
/-- **The resolvent is close to the identity near the anchor.**  Quantitative "resolvent `≈ 1`"
bound: `‖D_x Φ_t - 1‖ ≤ K · exp (K · |t - t₀|) · |t - t₀|`, so the resolvent departs from the
identity operator at most linearly (times the exponential) in the elapsed time, vanishing as
`t → t₀`.  Immediate from the Volterra identity `fundamentalSolution_eq_one_add_integral`
(`D_x Φ_t - 1 = ∫_{t₀}^{t} A σ ∘ D_x Φ_σ dσ`) and the a-priori velocity bound
`norm_comp_fundamentalSolution_le` (`‖A σ ∘ D_x Φ_σ‖ ≤ K · exp (K · |σ - t₀|)`), whose integrand is
`≤ K · exp (K · |t - t₀|)` on the time window `Ι t₀ t` (`|σ - t₀| ≤ |t - t₀|`), integrated by
`intervalIntegral.norm_integral_le_of_norm_le_const`.  This is the operator-Duhamel short-time
estimate underlying the contraction/invertibility of the resolvent for small `|t - t₀|`. -/
theorem norm_fundamentalSolution_sub_one_le {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    [CompleteSpace E]
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAcont : Continuous A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) :
    ‖fundamentalSolution hA hΦ h0 t - 1‖
      ≤ (K : ℝ) * Real.exp ((K : ℝ) * |t - t₀|) * |t - t₀| := by
  rw [fundamentalSolution_eq_one_add_integral hA hAcont hΦ h0 t, add_sub_cancel_left]
  refine intervalIntegral.norm_integral_le_of_norm_le_const
    (C := (K : ℝ) * Real.exp ((K : ℝ) * |t - t₀|)) ?_
  intro σ hσ
  refine (norm_comp_fundamentalSolution_le hA hΦ h0 σ).trans ?_
  have hσle : |σ - t₀| ≤ |t - t₀| := by
    have hmem : σ ∈ Set.uIcc t₀ t := Set.uIoc_subset_uIcc hσ
    have := Real.dist_le_of_mem_uIcc hmem Set.left_mem_uIcc
    simpa [Real.dist_eq, abs_sub_comm] using this
  gcongr

/-- **The resolvent is invertible whenever it is within distance `1` of the identity.**  If
`‖D_x Φ_t - 1‖ < 1` then the resolvent `D_x Φ_t` is a unit of the operator ring `E →L[ℝ] E` (an
invertible bounded operator), by the Neumann-series openness of the units around `1`
(`Units.oneSub`).  This is the operator/inverse-function-theorem shadow of the bi-Lipschitz
embedding: on top of `fundamentalSolution_injective` (injectivity) it provides a genuine two-sided
operator inverse. -/
theorem isUnit_fundamentalSolution_of_norm_sub_one_lt {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    [CompleteSpace E]
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) (ht : ‖fundamentalSolution hA hΦ h0 t - 1‖ < 1) :
    IsUnit (fundamentalSolution hA hΦ h0 t) := by
  have h1 : ‖1 - fundamentalSolution hA hΦ h0 t‖ < 1 := by rwa [norm_sub_rev]
  exact sub_sub_self 1 (fundamentalSolution hA hΦ h0 t) ▸
    (Units.oneSub (1 - fundamentalSolution hA hΦ h0 t) h1).isUnit

/-- **Short-time invertibility of the resolvent.**  For a norm-continuous coefficient `A`, whenever
the elapsed-time bound `K · exp (K · |t - t₀|) · |t - t₀| < 1` holds the resolvent `D_x Φ_t` is a
unit of `E →L[ℝ] E`.  Combines the short-time closeness `norm_fundamentalSolution_sub_one_le`
(`‖D_x Φ_t - 1‖ ≤ K · exp (K · |t - t₀|) · |t - t₀|`) with the Neumann-series invertibility
`isUnit_fundamentalSolution_of_norm_sub_one_lt`; in particular the flow map `x ↦ Φ x t` is a linear
isomorphism for all `t` close enough to `t₀` — the local-diffeomorphism input for the compact
manifold gauge flow of Item 2. -/
theorem isUnit_fundamentalSolution_of_time_lt {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    [CompleteSpace E]
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAcont : Continuous A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) (ht : (K : ℝ) * Real.exp ((K : ℝ) * |t - t₀|) * |t - t₀| < 1) :
    IsUnit (fundamentalSolution hA hΦ h0 t) :=
  isUnit_fundamentalSolution_of_norm_sub_one_lt hA hΦ h0 t
    (lt_of_le_of_lt (norm_fundamentalSolution_sub_one_le hA hAcont hΦ h0 t) ht)

open MeasureTheory intervalIntegral in
/-- **Duhamel difference formula for the resolvent.**  For two norm-continuous coefficient fields
`A₁`, `A₂` (both `‖·‖ ≤ K`) with variational flow families `Φ₁`, `Φ₂`, the difference of the two
resolvents obeys the variation-of-parameters identity
`D_x Φ₁_t - D_x Φ₂_t = ∫_{t₀}^{t} A₁ σ ∘ (D_x Φ₁_σ - D_x Φ₂_σ) dσ + ∫_{t₀}^{t} (A₁ σ - A₂ σ) ∘ D_x Φ₂_σ dσ`.
Subtracting the two Volterra equations `fundamentalSolution_eq_one_add_integral` cancels the
identities, and the integrand difference `A₁ ∘ W₁ - A₂ ∘ W₂ = A₁ ∘ (W₁ - W₂) + (A₁ - A₂) ∘ W₂`
(bilinearity of composition, `comp_sub`/`sub_comp`) splits the single integral into the two Duhamel
terms — the "homogeneous propagation of the resolvent gap" plus the "source term from the coefficient
gap".  As `A₂ → A₁` the first term is `O(‖W₁ - W₂‖)` and the second is the leading `(A₁ - A₂)`
contribution, so this identity is the exact ancestor of the *differentiable* dependence of the
resolvent on its coefficient field (the second-order variational equation) toward the `C^k`
bootstrap. -/
theorem fundamentalSolution_sub_eq_integral {A₁ A₂ : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    [CompleteSpace E] {Φ₁ Φ₂ : E → ℝ → E}
    (hA₁ : ∀ t, ‖A₁ t‖₊ ≤ K) (hA₁cont : Continuous A₁)
    (hA₂ : ∀ t, ‖A₂ t‖₊ ≤ K) (hA₂cont : Continuous A₂)
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec A₁)) (h0₁ : ∀ x, Φ₁ x t₀ = x)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec A₂)) (h0₂ : ∀ x, Φ₂ x t₀ = x)
    (t : ℝ) :
    fundamentalSolution hA₁ hΦ₁ h0₁ t - fundamentalSolution hA₂ hΦ₂ h0₂ t
      = (∫ σ in t₀..t, (A₁ σ).comp
            (fundamentalSolution hA₁ hΦ₁ h0₁ σ - fundamentalSolution hA₂ hΦ₂ h0₂ σ))
        + ∫ σ in t₀..t, (A₁ σ - A₂ σ).comp (fundamentalSolution hA₂ hΦ₂ h0₂ σ) := by
  set W₁ := fundamentalSolution hA₁ hΦ₁ h0₁ with hW₁
  set W₂ := fundamentalSolution hA₂ hΦ₂ h0₂ with hW₂
  have hcW₁ : Continuous W₁ := continuous_fundamentalSolution_time hA₁ hΦ₁ h0₁
  have hcW₂ : Continuous W₂ := continuous_fundamentalSolution_time hA₂ hΦ₂ h0₂
  have hi1 : IntervalIntegrable (fun σ => (A₁ σ).comp (W₁ σ)) volume t₀ t :=
    (hA₁cont.clm_comp hcW₁).intervalIntegrable t₀ t
  have hi2 : IntervalIntegrable (fun σ => (A₂ σ).comp (W₂ σ)) volume t₀ t :=
    (hA₂cont.clm_comp hcW₂).intervalIntegrable t₀ t
  have hi3 : IntervalIntegrable (fun σ => (A₁ σ).comp (W₁ σ - W₂ σ)) volume t₀ t :=
    (hA₁cont.clm_comp (hcW₁.sub hcW₂)).intervalIntegrable t₀ t
  have hi4 : IntervalIntegrable (fun σ => (A₁ σ - A₂ σ).comp (W₂ σ)) volume t₀ t :=
    ((hA₁cont.sub hA₂cont).clm_comp hcW₂).intervalIntegrable t₀ t
  have hV₁ : W₁ t = 1 + ∫ σ in t₀..t, (A₁ σ).comp (W₁ σ) :=
    fundamentalSolution_eq_one_add_integral hA₁ hA₁cont hΦ₁ h0₁ t
  have hV₂ : W₂ t = 1 + ∫ σ in t₀..t, (A₂ σ).comp (W₂ σ) :=
    fundamentalSolution_eq_one_add_integral hA₂ hA₂cont hΦ₂ h0₂ t
  rw [hV₁, hV₂]
  have hlhs : (1 + ∫ σ in t₀..t, (A₁ σ).comp (W₁ σ))
      - (1 + ∫ σ in t₀..t, (A₂ σ).comp (W₂ σ))
      = (∫ σ in t₀..t, (A₁ σ).comp (W₁ σ)) - ∫ σ in t₀..t, (A₂ σ).comp (W₂ σ) := by abel
  rw [hlhs, ← intervalIntegral.integral_sub hi1 hi2,
    ← intervalIntegral.integral_add hi3 hi4]
  refine intervalIntegral.integral_congr (fun σ _ => ?_)
  simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
  abel

/-- **The time-derivative of the resolvent path is `A t ∘ D_x Φ_t`.**  The explicit `deriv` form of
the operator variational ODE `hasDerivAt_fundamentalSolution`: for a norm-continuous coefficient
`A`, `deriv (t ↦ D_x Φ_t) = A t ∘ D_x Φ_t`.  A convenience readout for regularity consumers that
work with `deriv` rather than `HasDerivAt`. -/
theorem deriv_fundamentalSolution {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAcont : Continuous A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (t : ℝ) :
    deriv (fun s => fundamentalSolution hA hΦ h0 s) t
      = (A t).comp (fundamentalSolution hA hΦ h0 t) :=
  (hasDerivAt_fundamentalSolution hA hAcont hΦ h0 t).deriv

/-- **The resolvent path is `C¹` in time as an operator-valued curve.**  For a norm-continuous
coefficient `A`, the curve `t ↦ D_x Φ_t ∈ E →L[ℝ] E` is continuously differentiable
(`ContDiff ℝ 1`): it is differentiable everywhere (`hasDerivAt_fundamentalSolution`) with derivative
`t ↦ A t ∘ D_x Φ_t`, which is norm-continuous
(`hAcont.clm_comp continuous_fundamentalSolution_time`).  The packaged regularity — as opposed to the
raw `HasDerivAt` + continuity pieces — is what higher-order (`C^k`) consumers compose against. -/
theorem contDiff_one_fundamentalSolution {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAcont : Continuous A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x) :
    ContDiff ℝ 1 (fun s => fundamentalSolution hA hΦ h0 s) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hasDerivAt_fundamentalSolution hA hAcont hΦ h0 t).differentiableAt, ?_⟩
  have hd : deriv (fun s => fundamentalSolution hA hΦ h0 s)
      = fun t => (A t).comp (fundamentalSolution hA hΦ h0 t) :=
    funext fun t => deriv_fundamentalSolution hA hAcont hΦ h0 t
  rw [hd]
  exact hAcont.clm_comp (continuous_fundamentalSolution_time hA hΦ h0)

open MeasureTheory intervalIntegral in
/-- **A priori bound on a resolvent-forcing integral (the Duhamel source term).**  For any
operator-valued path `B` with `‖B σ‖ ≤ ε` (`0 ≤ ε`),
`‖∫_{t₀}^{t} B σ ∘ D_x Φ_σ dσ‖ ≤ ε · exp (K · |t - t₀|) · |t - t₀|`.  Applied with `B = A₁ - A₂` this
bounds the inhomogeneous "source term" of the Duhamel difference formula
`fundamentalSolution_sub_eq_integral` — the leading-order response of the resolvent to a coefficient
perturbation of size `ε`.  Proof: pointwise `‖B σ ∘ D_x Φ_σ‖ ≤ ‖B σ‖ · ‖D_x Φ_σ‖ ≤ ε · exp (K · |σ -
t₀|) ≤ ε · exp (K · |t - t₀|)` (operator-norm submultiplicativity, `norm_fundamentalSolution_le`, and
`|σ - t₀| ≤ |t - t₀|` on the window `Ι t₀ t`), integrated by
`intervalIntegral.norm_integral_le_of_norm_le_const`. -/
theorem norm_integral_comp_fundamentalSolution_le {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0} {ε : ℝ}
    [CompleteSpace E]
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (hε : 0 ≤ ε) (B : ℝ → (E →L[ℝ] E)) (hB : ∀ σ, ‖B σ‖ ≤ ε) (t : ℝ) :
    ‖∫ σ in t₀..t, (B σ).comp (fundamentalSolution hA hΦ h0 σ)‖
      ≤ ε * Real.exp ((K : ℝ) * |t - t₀|) * |t - t₀| := by
  refine intervalIntegral.norm_integral_le_of_norm_le_const
    (C := ε * Real.exp ((K : ℝ) * |t - t₀|)) ?_
  intro σ hσ
  have hσle : |σ - t₀| ≤ |t - t₀| := by
    have hmem : σ ∈ Set.uIcc t₀ t := Set.uIoc_subset_uIcc hσ
    have := Real.dist_le_of_mem_uIcc hmem Set.left_mem_uIcc
    simpa [Real.dist_eq, abs_sub_comm] using this
  refine (ContinuousLinearMap.opNorm_comp_le (B σ) (fundamentalSolution hA hΦ h0 σ)).trans ?_
  refine (mul_le_mul (hB σ) (norm_fundamentalSolution_le hA hΦ h0 σ) (norm_nonneg _) hε).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by gcongr)) hε

/-- **Time-regularity bootstrap of the resolvent (finite order).**  If the coefficient path `A`
is `C^n` in time (`ContDiff ℝ n A`), then the resolvent curve `t ↦ D_x Φ_t ∈ E →L[ℝ] E` is
`C^{n+1}` in time.  Proof by induction on `n`: the base case (`n = 0`, i.e. norm-continuous `A`
⟹ `C¹` resolvent) is `contDiff_one_fundamentalSolution`; the inductive step reads the resolvent's
derivative off the operator ODE `deriv (t ↦ D_x Φ_t) = A t ∘ D_x Φ_t`
(`deriv_fundamentalSolution`) — a composition of the `C^{n+1}` field `A` with the (inductively)
`C^{n+1}` resolvent, hence itself `C^{n+1}` via `ContDiff.clm_comp`, so `deriv W ∈ C^{n+1}` and
therefore `W ∈ C^{n+2}` by `contDiff_succ_iff_deriv`.  This is the time-direction half of the
`C^k` resolvent regularity that the Ricci-flow / DeTurck `C^k` bootstrap consumes. -/
theorem contDiff_fundamentalSolution_time {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x) :
    ∀ n : ℕ, ContDiff ℝ (n : WithTop ℕ∞) A →
      ContDiff ℝ ((n : WithTop ℕ∞) + 1) (fun s => fundamentalSolution hA hΦ h0 s) := by
  intro n
  induction n with
  | zero =>
    intro hA0
    have hc : Continuous A := hA0.continuous
    simpa using contDiff_one_fundamentalSolution hA hc hΦ h0
  | succ n ih =>
    intro hAn1
    have hc : Continuous A := hAn1.continuous
    have hAn : ContDiff ℝ (n : WithTop ℕ∞) A :=
      hAn1.of_le (by exact_mod_cast Nat.le_succ n)
    have hWn : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (fun s => fundamentalSolution hA hΦ h0 s) := by
      rw [Nat.cast_add_one]; exact ih hAn
    rw [contDiff_succ_iff_deriv]
    refine ⟨fun t => (hasDerivAt_fundamentalSolution hA hc hΦ h0 t).differentiableAt, ?_, ?_⟩
    · simp
    · have hd : deriv (fun s => fundamentalSolution hA hΦ h0 s)
          = fun t => (A t).comp (fundamentalSolution hA hΦ h0 t) :=
        funext fun t => deriv_fundamentalSolution hA hc hΦ h0 t
      rw [hd]
      exact hAn1.clm_comp hWn

open scoped ContDiff in
/-- **Time-regularity of the resolvent: a smooth coefficient gives a smooth resolvent.**  If the
coefficient path `A` is `C^∞` in time, then so is the resolvent curve `t ↦ D_x Φ_t ∈ E →L[ℝ] E`.
`C^∞`-ness is tested order by order (`contDiff_infty`): for every `n`, `A ∈ C^n` (indeed `C^∞`),
so the finite bootstrap `contDiff_fundamentalSolution_time` gives `W ∈ C^{n+1} ⊆ C^n`. -/
theorem contDiff_infty_fundamentalSolution_time {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAsmooth : ContDiff ℝ ∞ A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x) :
    ContDiff ℝ ∞ (fun s => fundamentalSolution hA hΦ h0 s) := by
  rw [contDiff_infty]
  intro n
  exact (contDiff_fundamentalSolution_time hA hΦ h0 n (contDiff_infty.mp hAsmooth n)).of_le
    le_self_add

/-- **Time-regularity of the resolvent action (a pushforward of a fixed vector).**  For a `C^n`
coefficient path `A`, the resolvent *action* `t ↦ D_x Φ_t · u₀ = Φ u₀ t ∈ E` — the pushforward of a
fixed initial vector `u₀` along the flow — is `C^{n+1}` in time.  Immediate from the operator-level
bootstrap `contDiff_fundamentalSolution_time` composed with evaluation at `u₀` (a continuous linear
map, `ContDiff.clm_apply` against `contDiff_const`).  This is the form the tensor time-derivative
chain rule of Item 1 consumes for the pushforward legs `Φ_t · u`, `Φ_t · v`. -/
theorem contDiff_fundamentalSolution_apply_time {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (n : ℕ) (hAdiff : ContDiff ℝ (n : WithTop ℕ∞) A) (u₀ : E) :
    ContDiff ℝ ((n : WithTop ℕ∞) + 1) (fun s => fundamentalSolution hA hΦ h0 s u₀) :=
  (contDiff_fundamentalSolution_time hA hΦ h0 n hAdiff).clm_apply contDiff_const

open scoped ContDiff in
/-- **Smoothness of the resolvent action.**  If the coefficient path `A` is `C^∞` in time then so
is the resolvent action `t ↦ D_x Φ_t · u₀`. -/
theorem contDiff_infty_fundamentalSolution_apply_time {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAsmooth : ContDiff ℝ ∞ A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x) (u₀ : E) :
    ContDiff ℝ ∞ (fun s => fundamentalSolution hA hΦ h0 s u₀) :=
  (contDiff_infty_fundamentalSolution_time hA hAsmooth hΦ h0).clm_apply contDiff_const

/-- **The second-order time equation of the resolvent (its "acceleration").**  For a `C¹`
coefficient path `A` — supplied as `A' = deriv A`, `HasDerivAt A (A' t) t` — the velocity field of
the resolvent, `t ↦ A t ∘ D_x Φ_t` (`= deriv (t ↦ D_x Φ_t)` by `deriv_fundamentalSolution`), is
itself differentiable with
`d/dt (A t ∘ D_x Φ_t) = A' t ∘ D_x Φ_t + A t ∘ (A t ∘ D_x Φ_t)`.  This is the operator product
rule `HasDerivAt.clm_comp` applied to `A t ∘ D_x Φ_t`, using the first-order operator ODE
`hasDerivAt_fundamentalSolution` for the second factor; equivalently, the resolvent is `C²` in time
with this explicit second derivative — the `k = 2` instance of the `C^k` bootstrap made concrete. -/
theorem hasDerivAt_deriv_fundamentalSolution {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAcont : Continuous A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    {A' : ℝ → (E →L[ℝ] E)} (hA' : ∀ t, HasDerivAt A (A' t) t) (t : ℝ) :
    HasDerivAt (fun s => (A s).comp (fundamentalSolution hA hΦ h0 s))
      ((A' t).comp (fundamentalSolution hA hΦ h0 t)
        + (A t).comp ((A t).comp (fundamentalSolution hA hΦ h0 t))) t :=
  (hA' t).clm_comp (hasDerivAt_fundamentalSolution hA hAcont hΦ h0 t)

/-- **Explicit second time-derivative of the resolvent.**  The `deriv`-readout of
`hasDerivAt_deriv_fundamentalSolution`: for a `C¹` coefficient `A`,
`deriv (deriv (t ↦ D_x Φ_t)) t = A' t ∘ D_x Φ_t + A t ∘ (A t ∘ D_x Φ_t)`, the closed form of the
resolvent's second time derivative (the operator ODE differentiated once more). -/
theorem deriv_deriv_fundamentalSolution {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAcont : Continuous A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    {A' : ℝ → (E →L[ℝ] E)} (hA' : ∀ t, HasDerivAt A (A' t) t) (t : ℝ) :
    deriv (deriv (fun s => fundamentalSolution hA hΦ h0 s)) t
      = (A' t).comp (fundamentalSolution hA hΦ h0 t)
        + (A t).comp ((A t).comp (fundamentalSolution hA hΦ h0 t)) := by
  have hd : deriv (fun s => fundamentalSolution hA hΦ h0 s)
      = fun s => (A s).comp (fundamentalSolution hA hΦ h0 s) :=
    funext fun s => deriv_fundamentalSolution hA hAcont hΦ h0 s
  rw [hd]
  exact (hasDerivAt_deriv_fundamentalSolution hA hAcont hΦ h0 hA' t).deriv

/-- **Time-regularity of an integral curve.**  An integral curve `γ` of a field `v : ℝ → E → E`
that is jointly `C^n` in `(time, space)` (`ContDiff ℝ n (Function.uncurry v)`) is `C^{n+1}` in time.
Proof by induction on `n`: `γ` solves `γ'(t) = v t (γ t) = (↿v) (t, γ t)`, the composition of the
(inductively) `C^{n+1}` map `t ↦ (t, γ t)` with the `C^{n+1}` field `↿v`, hence itself `C^{n+1}`; so
`γ` is differentiable with a `C^{n+1}` derivative, i.e. `C^{n+2}` (`contDiff_succ_iff_deriv`).  The
base case is joint continuity of `↿v`, giving a `C¹` curve (`contDiff_one_iff_deriv`).  Unlike the
resolvent bootstrap this holds for a general (nonlinear) field, so it also delivers the
time-regularity of the *base* gauge flow `t ↦ Φ x t` that Item 2's compact-manifold flow uses. -/
theorem contDiff_of_isIntegralCurve {γ : ℝ → E} (hγ : IsIntegralCurve γ v) :
    ∀ n : ℕ, ContDiff ℝ (n : WithTop ℕ∞) (Function.uncurry v) →
      ContDiff ℝ ((n : WithTop ℕ∞) + 1) γ := by
  have hderiv : deriv γ = fun t => v t (γ t) := funext fun t => (hγ t).deriv
  have hdiff : Differentiable ℝ γ := fun t => (hγ t).differentiableAt
  intro n
  induction n with
  | zero =>
    intro hv0
    have hcont : ContDiff ℝ (1 : WithTop ℕ∞) γ := by
      rw [contDiff_one_iff_deriv]
      refine ⟨hdiff, ?_⟩
      rw [hderiv]
      exact hv0.continuous.comp (continuous_id.prodMk hγ.continuous)
    simpa using hcont
  | succ n ih =>
    intro hvn1
    have hvn : ContDiff ℝ (n : WithTop ℕ∞) (Function.uncurry v) :=
      hvn1.of_le (by exact_mod_cast Nat.le_succ n)
    have hγcn1 : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) γ := by
      rw [Nat.cast_add_one]; exact ih hvn
    rw [contDiff_succ_iff_deriv]
    refine ⟨hdiff, ?_, ?_⟩
    · simp
    · rw [hderiv]
      exact hvn1.comp (contDiff_id.prodMk hγcn1)

open scoped ContDiff in
/-- **Smoothness of an integral curve.**  An integral curve of a jointly-`C^∞` field is `C^∞` in
time (order-by-order via `contDiff_infty` and the finite bootstrap). -/
theorem contDiff_infty_of_isIntegralCurve {γ : ℝ → E} (hγ : IsIntegralCurve γ v)
    (huv : ContDiff ℝ ∞ (Function.uncurry v)) : ContDiff ℝ ∞ γ := by
  rw [contDiff_infty]
  intro n
  exact (contDiff_of_isIntegralCurve hγ n (contDiff_infty.mp huv n)).of_le le_self_add

/-- **Time-regularity of the base flow.**  Each trajectory `t ↦ Ψ x t` of a flow family of a
jointly-`C^n` field is `C^{n+1}` in time — the specialisation of `contDiff_of_isIntegralCurve` to a
flow family, the form Item 2's compact-manifold gauge flow consumes for the time direction. -/
theorem contDiff_flow_time {Ψ : E → ℝ → E} (hΨ : ∀ x, IsIntegralCurve (Ψ x) v)
    (n : ℕ) (huv : ContDiff ℝ (n : WithTop ℕ∞) (Function.uncurry v)) (x : E) :
    ContDiff ℝ ((n : WithTop ℕ∞) + 1) (fun t => Ψ x t) :=
  contDiff_of_isIntegralCurve (hΨ x) n huv

open scoped ContDiff in
/-- **Smoothness of the base flow.**  Each trajectory `t ↦ Ψ x t` of a flow family of a
jointly-`C^∞` field is `C^∞` in time. -/
theorem contDiff_infty_flow_time {Ψ : E → ℝ → E} (hΨ : ∀ x, IsIntegralCurve (Ψ x) v)
    (huv : ContDiff ℝ ∞ (Function.uncurry v)) (x : E) :
    ContDiff ℝ ∞ (fun t => Ψ x t) :=
  contDiff_infty_of_isIntegralCurve (hΨ x) huv

/-- **Joint regularity of the resolvent action in (time, vector).**  For a `C^n` coefficient path
`A`, the pushforward map `(t, u₀) ↦ D_x Φ_t · u₀` is jointly `C^{n+1}` on `ℝ × E`.  The resolvent
operator curve `t ↦ D_x Φ_t` is `C^{n+1}` (`contDiff_fundamentalSolution_time`), pulled back along the
projection `Prod.fst`, then evaluated against the smooth `Prod.snd` through the bounded-bilinear
(hence smooth) evaluation map (`ContDiff.clm_apply`).  So the flow pushforward is regular jointly in
the flow time and the pushed vector. -/
theorem contDiff_fundamentalSolution_apply_joint {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x)
    (n : ℕ) (hAdiff : ContDiff ℝ (n : WithTop ℕ∞) A) :
    ContDiff ℝ ((n : WithTop ℕ∞) + 1)
      (fun p : ℝ × E => fundamentalSolution hA hΦ h0 p.1 p.2) :=
  ((contDiff_fundamentalSolution_time hA hΦ h0 n hAdiff).comp contDiff_fst).clm_apply contDiff_snd

open scoped ContDiff in
/-- **Joint smoothness of the resolvent action.**  For a `C^∞` coefficient `A`, the pushforward
`(t, u₀) ↦ D_x Φ_t · u₀` is jointly `C^∞` on `ℝ × E`. -/
theorem contDiff_infty_fundamentalSolution_apply_joint {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) (hAsmooth : ContDiff ℝ ∞ A)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec A)) (h0 : ∀ x, Φ x t₀ = x) :
    ContDiff ℝ ∞ (fun p : ℝ × E => fundamentalSolution hA hΦ h0 p.1 p.2) :=
  ((contDiff_infty_fundamentalSolution_time hA hAsmooth hΦ h0).comp contDiff_fst).clm_apply
    contDiff_snd

/-!
### Differentiable dependence of the resolvent on its coefficient field

The Duhamel difference formula `fundamentalSolution_sub_eq_integral` is the *integral* form of the
equation governing the resolvent gap `W₁ - W₂` of two coefficient fields.  Its *differential* form —
the inhomogeneous operator ODE for the gap — starts the second-order variational analysis:
*differentiable* dependence of the resolvent on its coefficient field. -/

/-- **Differential form of the Duhamel gap equation.**  For norm-continuous coefficient fields `A₁`,
`A₂` (`‖·‖ ≤ K`) with variational flow families and resolvents `W₁ = D_x Φ₁`, `W₂ = D_x Φ₂`, the gap
`t ↦ W₁ t - W₂ t` solves the inhomogeneous operator ODE
`d/dt (W₁ - W₂) = A₁ ∘ (W₁ - W₂) + (A₁ - A₂) ∘ W₂`.  This is the differential (`HasDerivAt`) form of
the integral identity `fundamentalSolution_sub_eq_integral`: subtract the two operator ODEs
`W₁' = A₁ ∘ W₁`, `W₂' = A₂ ∘ W₂` (`hasDerivAt_fundamentalSolution`) and regroup via bilinearity of
composition, `A₁ ∘ W₁ - A₂ ∘ W₂ = A₁ ∘ (W₁ - W₂) + (A₁ - A₂) ∘ W₂`.  The homogeneous part
`A₁ ∘ (W₁ - W₂)` propagates the gap; the source `(A₁ - A₂) ∘ W₂` is the leading
coefficient-perturbation forcing — the second-order variational equation is built on this. -/
theorem hasDerivAt_fundamentalSolution_sub {A₁ A₂ : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    {Φ₁ Φ₂ : E → ℝ → E}
    (hA₁ : ∀ t, ‖A₁ t‖₊ ≤ K) (hA₁cont : Continuous A₁)
    (hA₂ : ∀ t, ‖A₂ t‖₊ ≤ K) (hA₂cont : Continuous A₂)
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec A₁)) (h0₁ : ∀ x, Φ₁ x t₀ = x)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec A₂)) (h0₂ : ∀ x, Φ₂ x t₀ = x)
    (t : ℝ) :
    HasDerivAt (fun s => fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s)
      ((A₁ t).comp (fundamentalSolution hA₁ hΦ₁ h0₁ t - fundamentalSolution hA₂ hΦ₂ h0₂ t)
        + (A₁ t - A₂ t).comp (fundamentalSolution hA₂ hΦ₂ h0₂ t)) t := by
  have h1 := hasDerivAt_fundamentalSolution hA₁ hA₁cont hΦ₁ h0₁ t
  have h2 := hasDerivAt_fundamentalSolution hA₂ hA₂cont hΦ₂ h0₂ t
  have heq : (A₁ t).comp (fundamentalSolution hA₁ hΦ₁ h0₁ t - fundamentalSolution hA₂ hΦ₂ h0₂ t)
        + (A₁ t - A₂ t).comp (fundamentalSolution hA₂ hΦ₂ h0₂ t)
      = (A₁ t).comp (fundamentalSolution hA₁ hΦ₁ h0₁ t)
        - (A₂ t).comp (fundamentalSolution hA₂ hΦ₂ h0₂ t) := by
    simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
    abel
  rw [heq]
  exact h1.sub h2

/-- **Second-order variational estimate — quantitative differentiability of the resolvent in its
coefficient field.**  Let `A₁`, `A₂` be norm-continuous coefficient fields (`‖·‖ ≤ K`) with
resolvents `W₁ = D_x Φ₁`, `W₂ = D_x Φ₂`, and let the coefficient gap be `ε`-small,
`‖A₁ s - A₂ s‖ ≤ ε`.  If `V` is the *first variation* — a solution of the inhomogeneous operator ODE
`V' = A₂ ∘ V + (A₁ - A₂) ∘ W₂` anchored at `V t₀ = 0` (the leading linear response of the resolvent
to the coefficient perturbation `A₁ - A₂`) — then the resolvent gap agrees with its linear prediction
`V` to **second order**:
`‖(W₁ t - W₂ t) - V t‖ ≤ ε² · exp (K (T - t₀)) · (gronwallBound 0 K 1 (T - t₀))²` on `[t₀, T]`.

Proof: the remainder `R := (W₁ - W₂) - V` satisfies the *homogeneous* variational ODE with a
quadratically-small forcing, `R' = A₂ ∘ R + (A₁ - A₂) ∘ (W₁ - W₂)`, obtained by subtracting the
first-variation ODE from the gap ODE `hasDerivAt_fundamentalSolution_sub` — the two `(A₁ - A₂) ∘ W₂`
source terms cancel — with `R t₀ = 0`.  The forcing is `O(ε²)` since
`‖(A₁ - A₂) ∘ (W₁ - W₂)‖ ≤ ε · ‖W₁ - W₂‖` and the gap is itself `O(ε)` by the first-order Lipschitz
bound `norm_fundamentalSolution_sub_le_of_forall_le`.  Grönwall's inequality
(`norm_le_gronwallBound_of_norm_deriv_right_le`) then bounds `‖R t‖` by
`gronwallBound 0 K Γ (t - t₀) = Γ · gronwallBound 0 K 1 (t - t₀)` with the `O(ε²)` forcing constant
`Γ`.  This is the second-order variational equation underlying *differentiable* dependence of the
resolvent on its coefficient field — the base-point `C²`/`C^k` bootstrap for the flow. -/
theorem norm_fundamentalSolution_sub_sub_variation_le
    {A₁ A₂ : ℝ → (E →L[ℝ] E)} {K : ℝ≥0} {Φ₁ Φ₂ : E → ℝ → E}
    (hA₁ : ∀ t, ‖A₁ t‖₊ ≤ K) (hA₁cont : Continuous A₁)
    (hA₂ : ∀ t, ‖A₂ t‖₊ ≤ K) (hA₂cont : Continuous A₂)
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec A₁)) (h0₁ : ∀ x, Φ₁ x t₀ = x)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec A₂)) (h0₂ : ∀ x, Φ₂ x t₀ = x)
    {ε : ℝ} (hε : 0 ≤ ε) (hAA' : ∀ s, ‖A₁ s - A₂ s‖ ≤ ε)
    {V : ℝ → (E →L[ℝ] E)}
    (hVderiv : ∀ s, HasDerivAt V
      ((A₂ s).comp (V s) + (A₁ s - A₂ s).comp (fundamentalSolution hA₂ hΦ₂ h0₂ s)) s)
    (hV0 : V t₀ = 0)
    {T t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ‖(fundamentalSolution hA₁ hΦ₁ h0₁ t - fundamentalSolution hA₂ hΦ₂ h0₂ t) - V t‖
      ≤ ε ^ 2 * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀) ^ 2 := by
  have hKr : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  have ht0T : t₀ ≤ T := le_trans ht.1 ht.2
  have hg0 : 0 ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
    gronwallBound_zero_one_nonneg hKr (sub_nonneg.mpr ht0T)
  set R : ℝ → (E →L[ℝ] E) :=
    fun s => (fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s) - V s
    with hRdef
  have hcR : Continuous R := by
    rw [hRdef]
    exact ((continuous_fundamentalSolution_time hA₁ hΦ₁ h0₁).sub
      (continuous_fundamentalSolution_time hA₂ hΦ₂ h0₂)).sub
      (continuous_iff_continuousAt.mpr (fun s => (hVderiv s).continuousAt))
  have hR0 : R t₀ = 0 := by
    rw [hRdef]
    simp [fundamentalSolution_anchor hA₁ hΦ₁ h0₁, fundamentalSolution_anchor hA₂ hΦ₂ h0₂, hV0]
  set Γ : ℝ := ε ^ 2 * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀)
    with hΓdef
  have hΓ0 : 0 ≤ Γ := by
    rw [hΓdef]; exact mul_nonneg (mul_nonneg (sq_nonneg ε) (Real.exp_pos _).le) hg0
  have hgap : ∀ s ∈ Set.Icc t₀ T,
      ‖fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s‖
        ≤ ε * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀) := by
    intro s hs
    refine (norm_fundamentalSolution_sub_le_of_forall_le hA₁ hA₂ hΦ₁ h0₁ hΦ₂ h0₂ hε hAA' hs).trans ?_
    exact mul_le_mul_of_nonneg_left
      (gronwallBound_mono (le_refl (0 : ℝ)) zero_le_one hKr (by linarith [hs.2]))
      (mul_nonneg hε (Real.exp_pos _).le)
  have hRderiv : ∀ s, HasDerivAt R
      ((A₂ s).comp (R s) + (A₁ s - A₂ s).comp
        (fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s)) s := by
    intro s
    have hgs := (hasDerivAt_fundamentalSolution_sub hA₁ hA₁cont hA₂ hA₂cont hΦ₁ h0₁ hΦ₂ h0₂ s).sub
      (hVderiv s)
    have hval :
        (A₁ s).comp (fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s)
          + (A₁ s - A₂ s).comp (fundamentalSolution hA₂ hΦ₂ h0₂ s)
        - ((A₂ s).comp (V s)
          + (A₁ s - A₂ s).comp (fundamentalSolution hA₂ hΦ₂ h0₂ s))
        = (A₂ s).comp (R s) + (A₁ s - A₂ s).comp
          (fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s) := by
      rw [hRdef]
      simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
      abel
    rwa [hval] at hgs
  have ha : ‖R t₀‖ ≤ 0 := by simp [hR0]
  have hbound : ∀ s ∈ Set.Ico t₀ t,
      ‖(A₂ s).comp (R s) + (A₁ s - A₂ s).comp
        (fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s)‖
        ≤ (K : ℝ) * ‖R s‖ + Γ := by
    intro s hs
    have hsIcc : s ∈ Set.Icc t₀ T := ⟨hs.1, le_trans hs.2.le ht.2⟩
    have hA₂s : ‖A₂ s‖ ≤ (K : ℝ) := by exact_mod_cast hA₂ s
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · calc ‖(A₂ s).comp (R s)‖ ≤ ‖A₂ s‖ * ‖R s‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (K : ℝ) * ‖R s‖ := mul_le_mul_of_nonneg_right hA₂s (norm_nonneg _)
    · calc ‖(A₁ s - A₂ s).comp
              (fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s)‖
            ≤ ‖A₁ s - A₂ s‖
              * ‖fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ε * (ε * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀)) :=
            mul_le_mul (hAA' s) (hgap s hsIcc) (norm_nonneg _) hε
        _ = Γ := by rw [hΓdef]; ring
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le (a := t₀) (b := t)
    hcR.continuousOn (fun x _ => (hRderiv x).hasDerivWithinAt) ha hbound t ⟨ht.1, le_rfl⟩
  calc ‖(fundamentalSolution hA₁ hΦ₁ h0₁ t - fundamentalSolution hA₂ hΦ₂ h0₂ t) - V t‖
      = ‖R t‖ := by rw [hRdef]
    _ ≤ gronwallBound 0 (K : ℝ) Γ (t - t₀) := hgron
    _ = Γ * gronwallBound 0 (K : ℝ) 1 (t - t₀) := gronwallBound_zero_left_mul _ _ _
    _ ≤ Γ * gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
        mul_le_mul_of_nonneg_left
          (gronwallBound_mono (le_refl (0 : ℝ)) zero_le_one hKr (by linarith [ht.2])) hΓ0
    _ = ε ^ 2 * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀) ^ 2 := by
        rw [hΓdef]; ring

/-- **A-priori `O(ε)` bound on the first variation of the resolvent.**  The first variation `V` — the
solution of the inhomogeneous operator ODE `V' = A₂ ∘ V + (A₁ - A₂) ∘ W₂`, `V t₀ = 0`, i.e. the
leading linear response of the resolvent `W₂ = D_x Φ₂` to a coefficient perturbation `A₁ - A₂` of
size `ε` — is itself `O(ε)`:
`‖V t‖ ≤ ε · exp (K (T - t₀)) · gronwallBound 0 K 1 (t - t₀)` on `[t₀, T]`.  Together with the
second-order estimate `norm_fundamentalSolution_sub_sub_variation_le` (`‖(W₁ - W₂) - V‖ = O(ε²)`)
this exhibits the resolvent gap as `W₁ - W₂ = V + O(ε²)` with linear leading term `V = O(ε)` — so `V`
is genuinely the (Gateaux) derivative of the resolvent in the coefficient direction `A₁ - A₂`.  Proof:
the forcing `(A₁ - A₂) ∘ W₂` has norm `≤ ε · ‖W₂ s‖ ≤ ε · exp (K (T - t₀))` (operator
submultiplicativity, `norm_fundamentalSolution_le`, and `|s - t₀| ≤ T - t₀`), whence
`‖V' s‖ ≤ K · ‖V s‖ + ε · exp (K (T - t₀))`, and Grönwall
(`norm_le_gronwallBound_of_norm_deriv_right_le`) closes it. -/
theorem norm_fundamentalSolution_variation_le
    {A₁ A₂ : ℝ → (E →L[ℝ] E)} {K : ℝ≥0} {Φ₂ : E → ℝ → E}
    (hA₂ : ∀ t, ‖A₂ t‖₊ ≤ K)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec A₂)) (h0₂ : ∀ x, Φ₂ x t₀ = x)
    {ε : ℝ} (hε : 0 ≤ ε) (hAA' : ∀ s, ‖A₁ s - A₂ s‖ ≤ ε)
    {V : ℝ → (E →L[ℝ] E)}
    (hVderiv : ∀ s, HasDerivAt V
      ((A₂ s).comp (V s) + (A₁ s - A₂ s).comp (fundamentalSolution hA₂ hΦ₂ h0₂ s)) s)
    (hV0 : V t₀ = 0)
    {T t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ‖V t‖ ≤ ε * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
  have hKr : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  have hcV : Continuous V := continuous_iff_continuousAt.mpr (fun s => (hVderiv s).continuousAt)
  have ha : ‖V t₀‖ ≤ 0 := by simp [hV0]
  have hbound : ∀ s ∈ Set.Ico t₀ t,
      ‖(A₂ s).comp (V s) + (A₁ s - A₂ s).comp (fundamentalSolution hA₂ hΦ₂ h0₂ s)‖
        ≤ (K : ℝ) * ‖V s‖ + ε * Real.exp ((K : ℝ) * (T - t₀)) := by
    intro s hs
    have hA₂s : ‖A₂ s‖ ≤ (K : ℝ) := by exact_mod_cast hA₂ s
    have hexp : Real.exp ((K : ℝ) * |s - t₀|) ≤ Real.exp ((K : ℝ) * (T - t₀)) := by
      apply Real.exp_le_exp.mpr
      rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
      exact mul_le_mul_of_nonneg_left (by linarith [hs.2, ht.2]) hKr
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · calc ‖(A₂ s).comp (V s)‖ ≤ ‖A₂ s‖ * ‖V s‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (K : ℝ) * ‖V s‖ := mul_le_mul_of_nonneg_right hA₂s (norm_nonneg _)
    · calc ‖(A₁ s - A₂ s).comp (fundamentalSolution hA₂ hΦ₂ h0₂ s)‖
            ≤ ‖A₁ s - A₂ s‖ * ‖fundamentalSolution hA₂ hΦ₂ h0₂ s‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ε * Real.exp ((K : ℝ) * (T - t₀)) :=
            mul_le_mul (hAA' s)
              ((norm_fundamentalSolution_le hA₂ hΦ₂ h0₂ s).trans hexp) (norm_nonneg _) hε
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le (a := t₀) (b := t)
    hcV.continuousOn (fun x _ => (hVderiv x).hasDerivWithinAt) ha hbound t ⟨ht.1, le_rfl⟩
  calc ‖V t‖
      ≤ gronwallBound 0 (K : ℝ) (ε * Real.exp ((K : ℝ) * (T - t₀))) (t - t₀) := hgron
    _ = ε * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (t - t₀) :=
        gronwallBound_zero_left_mul _ _ _

/-!
### Linearity and uniqueness of the first variation

The second-order variational estimates above (`norm_fundamentalSolution_sub_sub_variation_le`,
`norm_fundamentalSolution_variation_le`) take the *first variation* `V` — a solution of the
inhomogeneous operator ODE `V' = A ∘ V + F` anchored at `V t₀ = 0` — as a hypothesis.  Here `F` is
the coefficient-perturbation forcing `(A₁ - A₂) ∘ W₂`, *linear* in the perturbation `A₁ - A₂`.  The
lemmas below establish that the map `F ↦ V` (equivalently `perturbation ↦ V`) is a genuine
**linear** and **single-valued** assignment: the inhomogeneous variational ODE is linear, so its
solution set is closed under addition and scalar multiplication (superposition), and Grönwall
uniqueness pins the anchored solution down.  This is exactly the linearity-in-perturbation that
upgrades the Gateaux estimate `W₁ - W₂ = V + O(ε²)` toward an honest *bounded linear* Gateaux/Fréchet
derivative of the resolvent `A ↦ D_x Φ_t` in its coefficient field — the algebraic backbone of the
base-point `C^k` bootstrap. -/

/-- **Superposition (additivity) for the inhomogeneous variational ODE.**  If `V₁` solves
`V₁' = A ∘ V₁ + F₁` and `V₂` solves `V₂' = A ∘ V₂ + F₂` (the first-variation ODEs with forcings
`F₁`, `F₂`), then their sum solves the ODE with the summed forcing,
`(V₁ + V₂)' = A ∘ (V₁ + V₂) + (F₁ + F₂)`.  Linearity of the operator ODE: add the two `HasDerivAt`
statements and regroup via bilinearity of composition (`comp_add`). -/
theorem hasDerivAt_inhomogVariation_add {A F₁ F₂ V₁ V₂ : ℝ → (E →L[ℝ] E)}
    (hV₁ : ∀ s, HasDerivAt V₁ ((A s).comp (V₁ s) + F₁ s) s)
    (hV₂ : ∀ s, HasDerivAt V₂ ((A s).comp (V₂ s) + F₂ s) s)
    (s : ℝ) :
    HasDerivAt (fun r => V₁ r + V₂ r)
      ((A s).comp (V₁ s + V₂ s) + (F₁ s + F₂ s)) s := by
  have h := (hV₁ s).add (hV₂ s)
  have heq : (A s).comp (V₁ s) + F₁ s + ((A s).comp (V₂ s) + F₂ s)
      = (A s).comp (V₁ s + V₂ s) + (F₁ s + F₂ s) := by
    rw [ContinuousLinearMap.comp_add]; abel
  rwa [heq] at h

/-- **Homogeneity (scalar multiplication) for the inhomogeneous variational ODE.**  If `V` solves
`V' = A ∘ V + F`, then `c • V` solves the ODE with the scaled forcing,
`(c • V)' = A ∘ (c • V) + c • F`.  Linearity of the operator ODE: scale the `HasDerivAt` statement
and use `A ∘ (c • V) = c • (A ∘ V)` (`comp_smul`). -/
theorem hasDerivAt_inhomogVariation_smul {A F V : ℝ → (E →L[ℝ] E)} (c : ℝ)
    (hV : ∀ s, HasDerivAt V ((A s).comp (V s) + F s) s)
    (s : ℝ) :
    HasDerivAt (fun r => c • V r) ((A s).comp (c • V s) + c • F s) s := by
  have h := (hV s).const_smul c
  have heq : c • ((A s).comp (V s) + F s) = (A s).comp (c • V s) + c • F s := by
    rw [smul_add, ContinuousLinearMap.comp_smul]
  rwa [heq] at h

/-- **Uniqueness of the first variation.**  Two solutions `V₁`, `V₂` of the *same* inhomogeneous
variational ODE `V' = A ∘ V + F` (with `‖A s‖ ≤ K`) that agree at one time `t₀` agree everywhere.
Proof: the difference `D = V₁ - V₂` solves the *homogeneous* variational ODE `D' = A ∘ D` (the
forcings cancel) with `D t₀ = 0`, hence equals the zero solution by Grönwall uniqueness
(`variational_eq_of_isIntegralCurve`).  Together with existence this makes the first variation a
*single-valued* (well-defined) function of the forcing. -/
theorem inhomogVariation_unique {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ s, ‖A s‖₊ ≤ K) {F V₁ V₂ : ℝ → (E →L[ℝ] E)}
    (hV₁ : ∀ s, HasDerivAt V₁ ((A s).comp (V₁ s) + F s) s)
    (hV₂ : ∀ s, HasDerivAt V₂ ((A s).comp (V₂ s) + F s) s)
    (h0 : V₁ t₀ = V₂ t₀) (t : ℝ) : V₁ t = V₂ t := by
  have hDcurve : IsIntegralCurve (fun s => V₁ s - V₂ s) (variationalField A) := by
    intro s
    have h := (hV₁ s).sub (hV₂ s)
    have heq : (A s).comp (V₁ s) + F s - ((A s).comp (V₂ s) + F s)
        = variationalField A s (V₁ s - V₂ s) := by
      simp only [variationalField, ContinuousLinearMap.comp_sub]; abel
    rwa [heq] at h
  have hZcurve : IsIntegralCurve (fun _ : ℝ => (0 : E →L[ℝ] E)) (variationalField A) := by
    intro s
    simpa [variationalField] using hasDerivAt_const s (0 : E →L[ℝ] E)
  have hD0 : (fun s => V₁ s - V₂ s) t₀ = (fun _ : ℝ => (0 : E →L[ℝ] E)) t₀ :=
    sub_eq_zero.mpr h0
  have hfin := variational_eq_of_isIntegralCurve hA hDcurve hZcurve hD0 t
  have hzero : V₁ t - V₂ t = 0 := hfin
  exact sub_eq_zero.mp hzero

/-- **The first variation is additive in the coefficient perturbation.**  With a fixed background
resolvent `W` (e.g. `W = D_x Φ₂ = fundamentalSolution hA₂ hΦ₂ h0₂`), the forcing of the
first-variation ODE is `B ∘ W`, *linear* in the perturbation `B = A₁ - A₂`.  Hence if `V₁` is the
first variation for perturbation `B₁` and `V₂` for `B₂`, their sum `V₁ + V₂` is the first variation
for `B₁ + B₂`:
`(V₁ + V₂)' = A₂ ∘ (V₁ + V₂) + (B₁ + B₂) ∘ W`.  (Superposition
`hasDerivAt_inhomogVariation_add` composed with linearity of `B ↦ B ∘ W`, `add_comp`.) -/
theorem hasDerivAt_firstVariation_perturbation_add
    {A₂ W B₁ B₂ V₁ V₂ : ℝ → (E →L[ℝ] E)}
    (hV₁ : ∀ s, HasDerivAt V₁ ((A₂ s).comp (V₁ s) + (B₁ s).comp (W s)) s)
    (hV₂ : ∀ s, HasDerivAt V₂ ((A₂ s).comp (V₂ s) + (B₂ s).comp (W s)) s)
    (s : ℝ) :
    HasDerivAt (fun r => V₁ r + V₂ r)
      ((A₂ s).comp (V₁ s + V₂ s) + (B₁ s + B₂ s).comp (W s)) s := by
  have h := hasDerivAt_inhomogVariation_add hV₁ hV₂ s
  rwa [← ContinuousLinearMap.add_comp] at h

/-- **The first variation is homogeneous in the coefficient perturbation.**  With a fixed background
resolvent `W`, if `V` is the first variation for perturbation `B`, then `c • V` is the first
variation for `c • B`:
`(c • V)' = A₂ ∘ (c • V) + (c • B) ∘ W`.  (Homogeneity `hasDerivAt_inhomogVariation_smul` composed
with linearity of `B ↦ B ∘ W`, `smul_comp`.)  Together with additivity this exhibits the first
variation as a *linear* function of the coefficient perturbation. -/
theorem hasDerivAt_firstVariation_perturbation_smul
    {A₂ W B V : ℝ → (E →L[ℝ] E)} (c : ℝ)
    (hV : ∀ s, HasDerivAt V ((A₂ s).comp (V s) + (B s).comp (W s)) s)
    (s : ℝ) :
    HasDerivAt (fun r => c • V r)
      ((A₂ s).comp (c • V s) + (c • B s).comp (W s)) s := by
  have h := hasDerivAt_inhomogVariation_smul c hV s
  rwa [← ContinuousLinearMap.smul_comp] at h

/-- **General a-priori size bound for the inhomogeneous variational ODE.**  Forcing-agnostic
Grönwall estimate: if `V` solves `V' = A ∘ V + F` (with `‖A s‖ ≤ K`) anchored at `V t₀ = 0`, and the
forcing is bounded by `M ≥ 0` on `[t₀, T]` (`‖F s‖ ≤ M`), then
`‖V t‖ ≤ M · gronwallBound 0 K 1 (t - t₀)` on `[t₀, T]`.  Proof: `‖V' s‖ ≤ K · ‖V s‖ + M` (operator
submultiplicativity of `A ∘ V` and the forcing bound), and Grönwall
(`norm_le_gronwallBound_of_norm_deriv_right_le`) closes it, with `gronwallBound_zero_left_mul`
factoring the linear response `M`.  This is the general first-variation size estimate of which
`norm_fundamentalSolution_variation_le` (specialised to the coefficient-perturbation forcing
`F = (A₁ - A₂) ∘ W₂`, `M = ε · exp (K (T - t₀))`) is the leading instance. -/
theorem norm_inhomogVariation_le {A F V : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ s, ‖A s‖₊ ≤ K)
    (hVderiv : ∀ s, HasDerivAt V ((A s).comp (V s) + F s) s)
    (hV0 : V t₀ = 0) {M : ℝ} {T : ℝ} (hFbound : ∀ s ∈ Set.Icc t₀ T, ‖F s‖ ≤ M)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ‖V t‖ ≤ M * gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
  have hcV : Continuous V := continuous_iff_continuousAt.mpr (fun s => (hVderiv s).continuousAt)
  have ha : ‖V t₀‖ ≤ 0 := by simp [hV0]
  have hbound : ∀ s ∈ Set.Ico t₀ t,
      ‖(A s).comp (V s) + F s‖ ≤ (K : ℝ) * ‖V s‖ + M := by
    intro s hs
    have hsIcc : s ∈ Set.Icc t₀ T := ⟨hs.1, le_trans hs.2.le ht.2⟩
    have hAs : ‖A s‖ ≤ (K : ℝ) := by exact_mod_cast hA s
    refine (norm_add_le _ _).trans (add_le_add ?_ (hFbound s hsIcc))
    calc ‖(A s).comp (V s)‖ ≤ ‖A s‖ * ‖V s‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (K : ℝ) * ‖V s‖ := mul_le_mul_of_nonneg_right hAs (norm_nonneg _)
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le (a := t₀) (b := t)
    hcV.continuousOn (fun x _ => (hVderiv x).hasDerivWithinAt) ha hbound t ⟨ht.1, le_rfl⟩
  calc ‖V t‖ ≤ gronwallBound 0 (K : ℝ) M (t - t₀) := hgron
    _ = M * gronwallBound 0 (K : ℝ) 1 (t - t₀) := gronwallBound_zero_left_mul _ _ _

/-- **Zero forcing gives the zero first variation.**  The first variation for a vanishing
perturbation is identically zero: if `V' = A ∘ V + F` with `F ≡ 0` and `V t₀ = 0`, then `V ≡ 0`.
(Uniqueness `inhomogVariation_unique` against the zero solution.)  This is the value at the origin of
the *linear* first-variation map `perturbation ↦ V` — a linear map sends `0` to `0` — consistent with
`hasDerivAt_firstVariation_perturbation_add/smul`. -/
theorem inhomogVariation_eq_zero_of_forcing_zero {A F V : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ s, ‖A s‖₊ ≤ K)
    (hVderiv : ∀ s, HasDerivAt V ((A s).comp (V s) + F s) s)
    (hF : ∀ s, F s = 0) (hV0 : V t₀ = 0) (t : ℝ) : V t = 0 := by
  have hZderiv : ∀ s, HasDerivAt (fun _ : ℝ => (0 : E →L[ℝ] E))
      ((A s).comp ((fun _ : ℝ => (0 : E →L[ℝ] E)) s) + F s) s := by
    intro s
    have hz : (A s).comp ((fun _ : ℝ => (0 : E →L[ℝ] E)) s) + F s = 0 := by simp [hF s]
    rw [hz]
    exact hasDerivAt_const s 0
  have hfin := inhomogVariation_unique hA hVderiv hZderiv hV0 t
  exact hfin

/-- **Superposition (subtraction) for the inhomogeneous variational ODE.**  If `V₁` solves
`V₁' = A ∘ V₁ + F₁` and `V₂` solves `V₂' = A ∘ V₂ + F₂`, then their difference solves the ODE with
the subtracted forcing, `(V₁ - V₂)' = A ∘ (V₁ - V₂) + (F₁ - F₂)`.  (Linearity of the operator ODE;
`comp_sub`.) -/
theorem hasDerivAt_inhomogVariation_sub {A F₁ F₂ V₁ V₂ : ℝ → (E →L[ℝ] E)}
    (hV₁ : ∀ s, HasDerivAt V₁ ((A s).comp (V₁ s) + F₁ s) s)
    (hV₂ : ∀ s, HasDerivAt V₂ ((A s).comp (V₂ s) + F₂ s) s)
    (s : ℝ) :
    HasDerivAt (fun r => V₁ r - V₂ r)
      ((A s).comp (V₁ s - V₂ s) + (F₁ s - F₂ s)) s := by
  have h := (hV₁ s).sub (hV₂ s)
  have heq : (A s).comp (V₁ s) + F₁ s - ((A s).comp (V₂ s) + F₂ s)
      = (A s).comp (V₁ s - V₂ s) + (F₁ s - F₂ s) := by
    rw [ContinuousLinearMap.comp_sub]; abel
  rwa [heq] at h

/-- **The first variation is subtractive in the coefficient perturbation.**  With a fixed background
resolvent `W`, if `V₁` is the first variation for perturbation `B₁` and `V₂` for `B₂`, their
difference `V₁ - V₂` is the first variation for `B₁ - B₂`:
`(V₁ - V₂)' = A₂ ∘ (V₁ - V₂) + (B₁ - B₂) ∘ W`.  (Superposition `hasDerivAt_inhomogVariation_sub`
composed with linearity of `B ↦ B ∘ W`, `sub_comp`.)  This is the differential input to the Lipschitz
dependence of the first variation on the perturbation. -/
theorem hasDerivAt_firstVariation_perturbation_sub
    {A₂ W B₁ B₂ V₁ V₂ : ℝ → (E →L[ℝ] E)}
    (hV₁ : ∀ s, HasDerivAt V₁ ((A₂ s).comp (V₁ s) + (B₁ s).comp (W s)) s)
    (hV₂ : ∀ s, HasDerivAt V₂ ((A₂ s).comp (V₂ s) + (B₂ s).comp (W s)) s)
    (s : ℝ) :
    HasDerivAt (fun r => V₁ r - V₂ r)
      ((A₂ s).comp (V₁ s - V₂ s) + (B₁ s - B₂ s).comp (W s)) s := by
  have h := hasDerivAt_inhomogVariation_sub hV₁ hV₂ s
  rwa [← ContinuousLinearMap.sub_comp] at h

/-- **Lipschitz dependence of the first variation on the coefficient perturbation.**  With a fixed
background resolvent `W` bounded by `C` on `[t₀, T]` (`‖W s‖ ≤ C`), the first variation depends
Lipschitz-continuously on the perturbation: if `V₁`, `V₂` are the (anchored) first variations for
perturbations `B₁`, `B₂` with `‖B₁ s - B₂ s‖ ≤ ε`, then
`‖V₁ t - V₂ t‖ ≤ (ε · C) · gronwallBound 0 K 1 (t - t₀)` on `[t₀, T]`.  Proof: `V₁ - V₂` is the first
variation for `B₁ - B₂` (`hasDerivAt_firstVariation_perturbation_sub`) with forcing bounded by
`‖(B₁ - B₂) ∘ W‖ ≤ ε · C`, and the general a-priori bound `norm_inhomogVariation_le` closes it.
Taking `ε → 0` this is the *continuity* of the Gateaux-derivative map `perturbation ↦ V`; together
with additivity/homogeneity (`hasDerivAt_firstVariation_perturbation_add/smul`) it exhibits the first
variation as a genuinely *bounded linear* map of the coefficient perturbation — the honest
Gateaux/Fréchet derivative of the resolvent `A ↦ D_x Φ_t`. -/
theorem norm_firstVariation_perturbation_sub_le
    {A₂ W B₁ B₂ V₁ V₂ : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA₂ : ∀ s, ‖A₂ s‖₊ ≤ K)
    (hV₁ : ∀ s, HasDerivAt V₁ ((A₂ s).comp (V₁ s) + (B₁ s).comp (W s)) s)
    (hV₂ : ∀ s, HasDerivAt V₂ ((A₂ s).comp (V₂ s) + (B₂ s).comp (W s)) s)
    (hV₁0 : V₁ t₀ = 0) (hV₂0 : V₂ t₀ = 0)
    {ε C T : ℝ} (hε : 0 ≤ ε)
    (hB : ∀ s ∈ Set.Icc t₀ T, ‖B₁ s - B₂ s‖ ≤ ε)
    (hW : ∀ s ∈ Set.Icc t₀ T, ‖W s‖ ≤ C)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ‖V₁ t - V₂ t‖ ≤ (ε * C) * gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
  have hDderiv := hasDerivAt_firstVariation_perturbation_sub hV₁ hV₂
  have hD0 : (fun r => V₁ r - V₂ r) t₀ = 0 := by simp [hV₁0, hV₂0]
  have hFbound : ∀ s ∈ Set.Icc t₀ T, ‖(B₁ s - B₂ s).comp (W s)‖ ≤ ε * C := by
    intro s hs
    calc ‖(B₁ s - B₂ s).comp (W s)‖
        ≤ ‖B₁ s - B₂ s‖ * ‖W s‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ε * C := mul_le_mul (hB s hs) (hW s hs) (norm_nonneg _) hε
  exact norm_inhomogVariation_le hA₂ hDderiv hD0 hFbound ht

/-- **The first-variation map is additive.**  Combining superposition
(`hasDerivAt_firstVariation_perturbation_add`) with Grönwall uniqueness (`inhomogVariation_unique`):
the *unique* anchored first variation `V₁₂` for the summed perturbation `B₁ + B₂` equals the sum of
the individual first variations, `V₁₂ t = V₁ t + V₂ t`.  This is the honest *map-level* additivity of
the coefficient-derivative assignment `perturbation ↦ V` (not merely closure of the solution set
under addition). -/
theorem firstVariation_perturbation_add_eq
    {A₂ W B₁ B₂ V₁ V₂ V₁₂ : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA₂ : ∀ s, ‖A₂ s‖₊ ≤ K)
    (hV₁ : ∀ s, HasDerivAt V₁ ((A₂ s).comp (V₁ s) + (B₁ s).comp (W s)) s)
    (hV₂ : ∀ s, HasDerivAt V₂ ((A₂ s).comp (V₂ s) + (B₂ s).comp (W s)) s)
    (hV₁₂ : ∀ s, HasDerivAt V₁₂ ((A₂ s).comp (V₁₂ s) + (B₁ s + B₂ s).comp (W s)) s)
    (hV₁0 : V₁ t₀ = 0) (hV₂0 : V₂ t₀ = 0) (hV₁₂0 : V₁₂ t₀ = 0)
    (t : ℝ) : V₁₂ t = V₁ t + V₂ t := by
  have hsum := hasDerivAt_firstVariation_perturbation_add hV₁ hV₂
  have h0 : V₁₂ t₀ = (fun r => V₁ r + V₂ r) t₀ := by simp [hV₁₂0, hV₁0, hV₂0]
  exact inhomogVariation_unique hA₂ hV₁₂ hsum h0 t

/-- **The first-variation map is homogeneous.**  Combining homogeneity
(`hasDerivAt_firstVariation_perturbation_smul`) with Grönwall uniqueness: the unique anchored first
variation `Vc` for the scaled perturbation `c • B` equals the scaled first variation,
`Vc t = c • V t`.  Together with `firstVariation_perturbation_add_eq` and
`inhomogVariation_eq_zero_of_forcing_zero` this makes `perturbation ↦ V` a genuine *linear map*. -/
theorem firstVariation_perturbation_smul_eq
    {A₂ W B V Vc : ℝ → (E →L[ℝ] E)} {K : ℝ≥0} (c : ℝ)
    (hA₂ : ∀ s, ‖A₂ s‖₊ ≤ K)
    (hV : ∀ s, HasDerivAt V ((A₂ s).comp (V s) + (B s).comp (W s)) s)
    (hVc : ∀ s, HasDerivAt Vc ((A₂ s).comp (Vc s) + (c • B s).comp (W s)) s)
    (hV0 : V t₀ = 0) (hVc0 : Vc t₀ = 0)
    (t : ℝ) : Vc t = c • V t := by
  have hsmul := hasDerivAt_firstVariation_perturbation_smul c hV
  have h0 : Vc t₀ = (fun r => c • V r) t₀ := by simp [hVc0, hV0]
  exact inhomogVariation_unique hA₂ hVc hsmul h0 t

/-- **Volterra (integral) form of the first variation.**  The anchored solution of the inhomogeneous
variational ODE `V' = A ∘ V + F` (`V t₀ = 0`) satisfies the fixed-point integral equation
`V t = ∫_{t₀}^{t} (A σ ∘ V σ + F σ) dσ`.  Immediate from the fundamental theorem of calculus
(`intervalIntegral.integral_eq_sub_of_hasDerivAt`) with the anchor `V t₀ = 0`, the integrand being
continuous (`A`, `F` continuous, `V` continuous from `HasDerivAt`) hence interval-integrable.  This is
the Volterra/Picard equation whose iteration constructs the first variation — the integral-equation
starting point for the *existence* of the first variation (the remaining, continuation-flavoured half
of the linearity-and-existence target), companion to `fundamentalSolution_eq_one_add_integral` for
the homogeneous resolvent. -/
theorem inhomogVariation_eq_integral [CompleteSpace E]
    {A F V : ℝ → (E →L[ℝ] E)}
    (hAcont : Continuous A) (hFcont : Continuous F)
    (hVderiv : ∀ s, HasDerivAt V ((A s).comp (V s) + F s) s)
    (hV0 : V t₀ = 0) (t : ℝ) :
    V t = ∫ σ in t₀..t, ((A σ).comp (V σ) + F σ) := by
  have hVcont : Continuous V :=
    continuous_iff_continuousAt.mpr (fun s => (hVderiv s).continuousAt)
  have hHcont : Continuous (fun σ => (A σ).comp (V σ) + F σ) :=
    (hAcont.clm_comp hVcont).add hFcont
  have hderiv : ∀ σ ∈ Set.uIcc t₀ t, HasDerivAt V ((A σ).comp (V σ) + F σ) σ :=
    fun σ _ => hVderiv σ
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hHcont.intervalIntegrable t₀ t)
  rw [hV0, sub_zero] at hint
  exact hint.symm

/-!
### Existence of the first variation via the augmented homogeneous flow

The linearity/uniqueness/bound lemmas above take the first variation `V` — a solution of the
*inhomogeneous* operator ODE `V' = A ∘ V + F` anchored at `V t₀ = 0` — as a hypothesis.  Here we
reduce the *existence* of such a `V` to the existence of a genuine **homogeneous** linear flow, by
the classical homogenisation of an affine ODE.

On the augmented Banach space `(E →L[ℝ] E) × ℝ` consider the *linear* (homogeneous) field
`ℳ(s)(V, c) = (A s ∘ V + c • F s, 0)`.  An integral curve `z = (V, c)` of `ℳ` through `(0, 1)` has a
constant scalar coordinate `c ≡ 1` (its derivative is `0`), so the operator coordinate `V` satisfies
`V' = A ∘ V + 1 • F = A ∘ V + F` with `V t₀ = 0`: it *is* the first variation.  Thus the inhomogeneous
first variation is a component of a homogeneous resolvent — the operator-ODE shadow of Duhamel's
principle — and its existence follows from the very same flow-existence input this file consumes for
`variationalFieldVec`.  No new analysis is required beyond homogeneous flow existence. -/

/-- The **augmented (homogenised) variational field** on `(E →L[ℝ] E) × ℝ` associated to an operator
path `A` and a forcing path `F`: `(V, c) ↦ (A s ∘ V + c • F s, 0)`.  It is linear (homogeneous) in
`(V, c)`; an integral curve through `(0, 1)` carries the first variation of the inhomogeneous
variational ODE `V' = A ∘ V + F` in its operator coordinate. -/
def augmentedVariationalField (A F : ℝ → (E →L[ℝ] E)) :
    ℝ → ((E →L[ℝ] E) × ℝ) → ((E →L[ℝ] E) × ℝ) :=
  fun s p => ((A s).comp p.1 + p.2 • F s, 0)

/-- **The augmented variational field is uniformly Lipschitz.**  Under uniform bounds `‖A s‖ ≤ K` and
`‖F s‖ ≤ M`, the linear augmented field `(V, c) ↦ (A s ∘ V + c • F s, 0)` on `(E →L[ℝ] E) × ℝ` is
`(K + M)`-Lipschitz in `(V, c)`, with the constant independent of `s`.  (Sup-norm on the product,
submultiplicativity of `A s ∘ ·`, and `‖c • F s‖ ≤ ‖c‖ · M`; the two component gaps are each bounded
by the product-norm gap.)  This places the augmented homogeneous flow squarely in the uniformly
Lipschitz regime handled by the `C⁰`/`C¹` dependence theory above — so the flow-existence input
required by `hasDerivAt_inhomogVariation_of_augmented` is of exactly the same well-posed kind consumed
throughout this file for `variationalFieldVec`. -/
theorem lipschitzWith_augmentedVariationalField {A F : ℝ → (E →L[ℝ] E)} {K M : ℝ≥0}
    (hA : ∀ s, ‖A s‖₊ ≤ K) (hF : ∀ s, ‖F s‖₊ ≤ M) (s : ℝ) :
    LipschitzWith (K + M) (augmentedVariationalField A F s) := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  have hAs : ‖A s‖ ≤ (K : ℝ) := by exact_mod_cast hA s
  have hFs : ‖F s‖ ≤ (M : ℝ) := by exact_mod_cast hF s
  have hfst : ‖p.1 - q.1‖ ≤ ‖p - q‖ := norm_fst_le (p - q)
  have hsnd : ‖p.2 - q.2‖ ≤ ‖p - q‖ := norm_snd_le (p - q)
  rw [dist_eq_norm, dist_eq_norm]
  have hnorm : ‖augmentedVariationalField A F s p - augmentedVariationalField A F s q‖
      = ‖(A s).comp (p.1 - q.1) + (p.2 - q.2) • F s‖ := by
    rw [Prod.norm_def]
    have e1 : (augmentedVariationalField A F s p - augmentedVariationalField A F s q).1
        = (A s).comp (p.1 - q.1) + (p.2 - q.2) • F s := by
      show ((A s).comp p.1 + p.2 • F s) - ((A s).comp q.1 + q.2 • F s)
          = (A s).comp (p.1 - q.1) + (p.2 - q.2) • F s
      rw [ContinuousLinearMap.comp_sub, sub_smul]; abel
    have e2 : (augmentedVariationalField A F s p - augmentedVariationalField A F s q).2 = 0 := by
      show (0 : ℝ) - 0 = 0
      simp
    rw [e1, e2, norm_zero, max_eq_left (norm_nonneg _)]
  rw [hnorm]
  have h1 : ‖(A s).comp (p.1 - q.1)‖ ≤ (K : ℝ) * ‖p - q‖ :=
    calc ‖(A s).comp (p.1 - q.1)‖
        ≤ ‖A s‖ * ‖p.1 - q.1‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (K : ℝ) * ‖p - q‖ := mul_le_mul hAs hfst (norm_nonneg _) (by positivity)
  have h2 : ‖(p.2 - q.2) • F s‖ ≤ ‖p - q‖ * (M : ℝ) := by
    rw [norm_smul]
    exact mul_le_mul hsnd hFs (norm_nonneg _) (norm_nonneg _)
  calc ‖(A s).comp (p.1 - q.1) + (p.2 - q.2) • F s‖
      ≤ ‖(A s).comp (p.1 - q.1)‖ + ‖(p.2 - q.2) • F s‖ := norm_add_le _ _
    _ ≤ (K : ℝ) * ‖p - q‖ + ‖p - q‖ * (M : ℝ) := add_le_add h1 h2
    _ = ((K + M : ℝ≥0) : ℝ) * ‖p - q‖ := by push_cast; ring

/-- **The scalar coordinate of the augmented flow has zero derivative.**  For any integral curve `z`
of `augmentedVariationalField A F`, the scalar component `s ↦ (z s).2` has derivative `0` everywhere
(the second slot of the augmented field is identically `0`); obtained by post-composing with the
continuous linear projection `snd`. -/
theorem hasDerivAt_augmentedVariationalField_snd {A F : ℝ → (E →L[ℝ] E)}
    {z : ℝ → ((E →L[ℝ] E) × ℝ)}
    (hz : ∀ s, HasDerivAt z (augmentedVariationalField A F s (z s)) s) (s : ℝ) :
    HasDerivAt (fun r => (z r).2) 0 s := by
  have h := (ContinuousLinearMap.snd ℝ (E →L[ℝ] E) ℝ).hasFDerivAt.comp_hasDerivAt s (hz s)
  simpa [augmentedVariationalField, ContinuousLinearMap.coe_snd', Function.comp_def] using h

/-- **The scalar coordinate of the augmented flow through `(0, 1)` is constantly `1`.**  Its
derivative vanishes everywhere (`hasDerivAt_augmentedVariationalField_snd`) and it starts at `1`, so
it is constant equal to `1` by `is_const_of_deriv_eq_zero`. -/
theorem augmentedVariationalField_snd_eq_one {A F : ℝ → (E →L[ℝ] E)}
    {z : ℝ → ((E →L[ℝ] E) × ℝ)}
    (hz : ∀ s, HasDerivAt z (augmentedVariationalField A F s (z s)) s)
    (hz0 : z t₀ = (0, 1)) (s : ℝ) : (z s).2 = 1 := by
  have hderiv := hasDerivAt_augmentedVariationalField_snd hz
  have hdiff : Differentiable ℝ (fun r => (z r).2) := fun r => (hderiv r).differentiableAt
  have hzero : ∀ r, deriv (fun r => (z r).2) r = 0 := fun r => (hderiv r).deriv
  have hconst : (z s).2 = (z t₀).2 := is_const_of_deriv_eq_zero hdiff hzero s t₀
  rw [hconst, hz0]

/-- **Existence of the first variation via the augmented homogeneous flow.**  If `z` is an integral
curve of the homogeneous augmented field `augmentedVariationalField A F` through `(0, 1)`, then its
operator coordinate `V = (z ·).1` solves the *inhomogeneous* variational ODE `V' = A ∘ V + F`.  (The
scalar coordinate is constantly `1`, so the forcing `c • F` reduces to `F`.)  This reduces existence
of the first variation to homogeneous flow existence — the operator-ODE Duhamel principle — supplying
the `HasDerivAt V (A ∘ V + F)` hypothesis consumed by the linearity/uniqueness/bound lemmas above. -/
theorem hasDerivAt_inhomogVariation_of_augmented {A F : ℝ → (E →L[ℝ] E)}
    {z : ℝ → ((E →L[ℝ] E) × ℝ)}
    (hz : ∀ s, HasDerivAt z (augmentedVariationalField A F s (z s)) s)
    (hz0 : z t₀ = (0, 1)) (s : ℝ) :
    HasDerivAt (fun r => (z r).1) ((A s).comp ((z s).1) + F s) s := by
  have hone : (z s).2 = 1 := augmentedVariationalField_snd_eq_one hz hz0 s
  have h := (ContinuousLinearMap.fst ℝ (E →L[ℝ] E) ℝ).hasFDerivAt.comp_hasDerivAt s (hz s)
  simpa [augmentedVariationalField, ContinuousLinearMap.coe_fst', Function.comp_def, hone] using h

/-- **The augmented first variation is anchored at `0`.**  The operator coordinate of the augmented
flow through `(0, 1)` vanishes at the anchor time: `V t₀ = 0`.  Together with
`hasDerivAt_inhomogVariation_of_augmented` this delivers the full anchored first variation `V`, whose
existence is thereby reduced to that of the augmented homogeneous flow. -/
theorem inhomogVariation_of_augmented_anchor
    {z : ℝ → ((E →L[ℝ] E) × ℝ)} (hz0 : z t₀ = (0, 1)) :
    (fun r => (z r).1) t₀ = (0 : E →L[ℝ] E) := by
  show (z t₀).1 = 0
  rw [hz0]

/-- **Existence and a-priori bound of the first variation from the augmented flow.**  The operator
coordinate `V = (z ·).1` of an integral curve `z` of `augmentedVariationalField A F` through `(0, 1)`
is the anchored first variation of `V' = A ∘ V + F` (`hasDerivAt_inhomogVariation_of_augmented`,
`inhomogVariation_of_augmented_anchor`), so it inherits the general Grönwall a-priori bound: with
`‖A s‖ ≤ K` and `‖F s‖ ≤ M` on `[t₀, T]`, `‖V t‖ ≤ M · gronwallBound 0 K 1 (t - t₀)` there.  This is
the capstone of the augmented-flow reduction: existence *and* the exponential size control of the
first variation follow from homogeneous flow existence alone, delivering the complete first-variation
data (existence, anchoring, size bound) consumed by the second-variation estimates. -/
theorem norm_inhomogVariation_of_augmented_le {A F : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ s, ‖A s‖₊ ≤ K) {z : ℝ → ((E →L[ℝ] E) × ℝ)}
    (hz : ∀ s, HasDerivAt z (augmentedVariationalField A F s (z s)) s)
    (hz0 : z t₀ = (0, 1)) {M T : ℝ} (hFbound : ∀ s ∈ Set.Icc t₀ T, ‖F s‖ ≤ M)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ‖(z t).1‖ ≤ M * gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
  have hV := hasDerivAt_inhomogVariation_of_augmented hz hz0
  have hV0 : (fun r => (z r).1) t₀ = 0 := inhomogVariation_of_augmented_anchor hz0
  exact norm_inhomogVariation_le hA hV hV0 hFbound ht

/-- **Well-definedness of the augmented first variation.**  Any two integral curves `z₁, z₂` of the
augmented field `augmentedVariationalField A F` through `(0, 1)` carry the *same* operator coordinate:
`(z₁ t).1 = (z₂ t).1`.  Both operator coordinates solve the anchored inhomogeneous ODE
`V' = A ∘ V + F`, `V t₀ = 0` (`hasDerivAt_inhomogVariation_of_augmented`,
`inhomogVariation_of_augmented_anchor`), so Grönwall uniqueness (`inhomogVariation_unique`) pins them
together.  Thus the first variation extracted by the augmented-flow reduction is a canonical,
flow-independent object — it depends only on `A` and `F`, not on the particular augmented flow. -/
theorem augmentedVariationalField_fst_unique {A F : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ s, ‖A s‖₊ ≤ K) {z₁ z₂ : ℝ → ((E →L[ℝ] E) × ℝ)}
    (hz₁ : ∀ s, HasDerivAt z₁ (augmentedVariationalField A F s (z₁ s)) s)
    (hz₂ : ∀ s, HasDerivAt z₂ (augmentedVariationalField A F s (z₂ s)) s)
    (hz₁0 : z₁ t₀ = (0, 1)) (hz₂0 : z₂ t₀ = (0, 1)) (t : ℝ) :
    (z₁ t).1 = (z₂ t).1 := by
  have hV₁ := hasDerivAt_inhomogVariation_of_augmented hz₁ hz₁0
  have hV₂ := hasDerivAt_inhomogVariation_of_augmented hz₂ hz₂0
  have h0 : (fun r => (z₁ r).1) t₀ = (fun r => (z₂ r).1) t₀ := by
    rw [inhomogVariation_of_augmented_anchor hz₁0, inhomogVariation_of_augmented_anchor hz₂0]
  exact inhomogVariation_unique hA hV₁ hV₂ h0 t

/-!
### Gluing integral curves across a junction (the continuation primitive)

Mathlib v4.29.1 supplies *local* existence of integral curves (Picard–Lindelöf on a compact
interval) but no way to **glue** integral curves that meet at a common time into a single curve valid
on the union.  The two lemmas here provide that missing continuation primitive.

The payoff is `isIntegralCurve_of_isIntegralCurveOn_Iic_Ici`: a curve which is an integral curve on
the left half-line `Iic b` and on the right half-line `Ici b` is a **global** integral curve.  This
is exactly the shape (`IsIntegralCurve` — a genuine two-sided derivative at *every* time) consumed by
every flow-existence hypothesis in this file (`hΦ : ∀ x, IsIntegralCurve (Φ x) …`, and the augmented
homogeneous flow `∀ s, HasDerivAt z …` of `hasDerivAt_inhomogVariation_of_augmented`).  Thus a global
integral curve can be assembled from a forward local solution on `[b, ∞)` and a backward local
solution on `(-∞, b]` glued at the anchor `b` — reducing global existence to one-sided existence.

`isIntegralCurve_glue_Iic_Ici` is the constructive companion: it *builds* the glued curve
`fun t => if t ≤ b then γ₁ t else γ₂ t` from two one-sided integral curves that agree at the junction
`γ₁ b = γ₂ b`, and shows it is a global integral curve.  Only Mathlib's Banach-level within-set
derivative calculus is used — no PDE or manifold content. -/

/-- **Half-line gluing to a global integral curve.**  If `γ` is an integral curve of `v` on the left
half-line `Iic b` *and* on the right half-line `Ici b`, then it is a *global* integral curve of `v`.
At a time `t < b` the set `Iic b` is a neighbourhood of `t`, so the within-`Iic b` derivative upgrades
to a two-sided `HasDerivAt`; symmetrically for `t > b` using `Ici b`; and at the junction `t = b` the
two one-sided within-set derivatives combine via `HasDerivWithinAt.union` over `Iic b ∪ Ici b = univ`
into the two-sided derivative.  This is the continuation primitive that turns one-sided existence into
the global `IsIntegralCurve` consumed throughout this file. -/
theorem isIntegralCurve_of_isIntegralCurveOn_Iic_Ici {b : ℝ}
    (h₁ : IsIntegralCurveOn γ v (Set.Iic b)) (h₂ : IsIntegralCurveOn γ v (Set.Ici b)) :
    IsIntegralCurve γ v := by
  intro t
  rcases lt_trichotomy t b with hlt | heq | hgt
  · have hd := h₁ t (le_of_lt hlt)
    have hnhd : Set.Iic b ∈ 𝓝 t :=
      Filter.mem_of_superset (isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hlt)) Set.Iio_subset_Iic_self
    exact hd.hasDerivAt hnhd
  · rw [heq]
    have hd1 := h₁ b (Set.mem_Iic.mpr le_rfl)
    have hd2 := h₂ b (Set.mem_Ici.mpr le_rfl)
    have hu := hd1.union hd2
    rw [Set.Iic_union_Ici] at hu
    exact hasDerivWithinAt_univ.mp hu
  · have hd := h₂ t (le_of_lt hgt)
    have hnhd : Set.Ici b ∈ 𝓝 t :=
      Filter.mem_of_superset (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hgt)) Set.Ioi_subset_Ici_self
    exact hd.hasDerivAt hnhd

/-- **Constructive continuation: gluing two one-sided integral curves into a global one.**  Given a
left integral curve `γ₁` on `Iic b` and a right integral curve `γ₂` on `Ici b` that agree at the
junction (`γ₁ b = γ₂ b`), the piecewise curve `fun t => if t ≤ b then γ₁ t else γ₂ t` is a *global*
integral curve of `v`.  The glued curve agrees with `γ₁` on `Iic b` and with `γ₂` on `Ici b` (the
junction value being pinned by `γ₁ b = γ₂ b`), so each one-sided integral-curve property transfers by
`HasDerivWithinAt.congr`, and `isIntegralCurve_of_isIntegralCurveOn_Iic_Ici` assembles them into the
global curve.  This is the concrete tool for continuing a solution past a time `b` — the operational
heart of extending local ODE solutions to global ones. -/
theorem isIntegralCurve_glue_Iic_Ici {b : ℝ} {γ₁ γ₂ : ℝ → E}
    (h₁ : IsIntegralCurveOn γ₁ v (Set.Iic b)) (h₂ : IsIntegralCurveOn γ₂ v (Set.Ici b))
    (hmatch : γ₁ b = γ₂ b) :
    IsIntegralCurve (fun t => if t ≤ b then γ₁ t else γ₂ t) v := by
  set γ := fun t => if t ≤ b then γ₁ t else γ₂ t with hγdef
  have hEq1 : Set.EqOn γ γ₁ (Set.Iic b) := by
    intro x hx
    simp only [hγdef]
    rw [if_pos (Set.mem_Iic.mp hx)]
  have hEq2 : Set.EqOn γ γ₂ (Set.Ici b) := by
    intro x hx
    have hbx : b ≤ x := Set.mem_Ici.mp hx
    rcases hbx.lt_or_eq with h | h
    · simp only [hγdef]
      rw [if_neg (not_le.mpr h)]
    · subst h
      simp only [hγdef]
      rw [if_pos le_rfl]
      exact hmatch
  have step1 : IsIntegralCurveOn γ v (Set.Iic b) := by
    intro x hx
    have hgx : γ x = γ₁ x := hEq1 hx
    rw [hgx]
    exact (h₁ x hx).congr (fun y hy => hEq1 hy) hgx
  have step2 : IsIntegralCurveOn γ v (Set.Ici b) := by
    intro x hx
    have hgx : γ x = γ₂ x := hEq2 hx
    rw [hgx]
    exact (h₂ x hx).congr (fun y hy => hEq2 hy) hgx
  exact isIntegralCurve_of_isIntegralCurveOn_Iic_Ici step1 step2

/-- **Closed-interval gluing.**  If `γ` is an integral curve of `v` on `Icc a b` and on `Icc b c`
(with `a ≤ b ≤ c`), then it is an integral curve on the whole interval `Icc a c`.  Away from the
junction `b` the relevant closed subinterval is a within-`Icc a c` neighbourhood of the point, so the
subinterval derivative transports to `Icc a c` by `HasDerivWithinAt.mono_of_mem_nhdsWithin`; at the
junction the two one-sided within-derivatives combine via `HasDerivWithinAt.union` over
`Icc a b ∪ Icc b c = Icc a c`.  This is the finite-interval companion of
`isIntegralCurve_of_isIntegralCurveOn_Iic_Ici`, used to concatenate successive local solutions. -/
theorem isIntegralCurveOn_Icc_union {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (h₁ : IsIntegralCurveOn γ v (Set.Icc a b)) (h₂ : IsIntegralCurveOn γ v (Set.Icc b c)) :
    IsIntegralCurveOn γ v (Set.Icc a c) := by
  rw [← Set.Icc_union_Icc_eq_Icc hab hbc]
  intro t ht
  rcases lt_trichotomy t b with hlt | heq | hgt
  · have htab : t ∈ Set.Icc a b := by
      rcases ht with h | h
      · exact h
      · exact absurd h.1 (not_le.mpr hlt)
    have hd := h₁ t htab
    apply hd.mono_of_mem_nhdsWithin
    rw [Set.Icc_union_Icc_eq_Icc hab hbc, mem_nhdsWithin]
    exact ⟨Set.Iio b, isOpen_Iio, Set.mem_Iio.mpr hlt,
      fun x hx => ⟨hx.2.1, le_of_lt (Set.mem_Iio.mp hx.1)⟩⟩
  · rw [heq]
    have hd1 := h₁ b (Set.mem_Icc.mpr ⟨hab, le_rfl⟩)
    have hd2 := h₂ b (Set.mem_Icc.mpr ⟨le_rfl, hbc⟩)
    exact hd1.union hd2
  · have htbc : t ∈ Set.Icc b c := by
      rcases ht with h | h
      · exact absurd h.2 (not_le.mpr hgt)
      · exact h
    have hd := h₂ t htbc
    apply hd.mono_of_mem_nhdsWithin
    rw [Set.Icc_union_Icc_eq_Icc hab hbc, mem_nhdsWithin]
    exact ⟨Set.Ioi b, isOpen_Ioi, Set.mem_Ioi.mpr hgt,
      fun x hx => ⟨le_of_lt (Set.mem_Ioi.mp hx.1), hx.2.2⟩⟩

/-- **Constructive closed-interval continuation.**  Given a left integral curve `γ₁` on `Icc a b` and
a right integral curve `γ₂` on `Icc b c` (with `a ≤ b ≤ c`) that agree at the junction `γ₁ b = γ₂ b`,
the piecewise curve `fun t => if t ≤ b then γ₁ t else γ₂ t` is an integral curve of `v` on `Icc a c`.
The glued curve agrees with `γ₁` on `Icc a b` and with `γ₂` on `Icc b c`, so each subinterval
integral-curve property transfers by `HasDerivWithinAt.congr` and `isIntegralCurveOn_Icc_union` fuses
them.  Iterating this over a chain `a = t₀ ≤ t₁ ≤ ⋯ ≤ tₙ = c` concatenates finitely many local
Picard–Lindelöf solutions into one solution on the whole span — the finite-continuation building
block toward global existence. -/
theorem isIntegralCurveOn_glue_Icc {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) {γ₁ γ₂ : ℝ → E}
    (h₁ : IsIntegralCurveOn γ₁ v (Set.Icc a b)) (h₂ : IsIntegralCurveOn γ₂ v (Set.Icc b c))
    (hmatch : γ₁ b = γ₂ b) :
    IsIntegralCurveOn (fun t => if t ≤ b then γ₁ t else γ₂ t) v (Set.Icc a c) := by
  set γ := fun t => if t ≤ b then γ₁ t else γ₂ t with hγdef
  have hEq1 : Set.EqOn γ γ₁ (Set.Icc a b) := by
    intro x hx
    simp only [hγdef]
    rw [if_pos hx.2]
  have hEq2 : Set.EqOn γ γ₂ (Set.Icc b c) := by
    intro x hx
    rcases hx.1.lt_or_eq with h | h
    · simp only [hγdef]
      rw [if_neg (not_le.mpr h)]
    · subst h
      simp only [hγdef]
      rw [if_pos le_rfl]
      exact hmatch
  have step1 : IsIntegralCurveOn γ v (Set.Icc a b) := by
    intro x hx
    have hgx : γ x = γ₁ x := hEq1 hx
    rw [hgx]
    exact (h₁ x hx).congr (fun y hy => hEq1 hy) hgx
  have step2 : IsIntegralCurveOn γ v (Set.Icc b c) := by
    intro x hx
    have hgx : γ x = γ₂ x := hEq2 hx
    rw [hgx]
    exact (h₂ x hx).congr (fun y hy => hEq2 hy) hgx
  exact isIntegralCurveOn_Icc_union hab hbc step1 step2

/-- **Exhaustion: global integral curve from a countable family of bounded-interval solutions.**  If
`γ` is an integral curve of `v` on every symmetric closed interval `Icc (t₀ - n) (t₀ + n)`, `n : ℕ`,
then it is a *global* integral curve of `v`.  Any time `t` lies in the open interior of some
`Icc (t₀ - n) (t₀ + n)` (Archimedean: choose `n > |t - t₀|`), where that interval is a genuine
neighbourhood of `t`, so the within-interval derivative upgrades to a two-sided `HasDerivAt`.  This is
the countable-exhaustion counterpart of `isIntegralCurve_of_isIntegralCurveOn_Iic_Ici`: it reduces
global existence to solving on a growing sequence of compact intervals — the natural target of
iterating `isIntegralCurveOn_glue_Icc` over local Picard–Lindelöf solutions. -/
theorem isIntegralCurve_of_forall_mem_Icc {t₀ : ℝ}
    (h : ∀ n : ℕ, IsIntegralCurveOn γ v (Set.Icc (t₀ - n) (t₀ + n))) :
    IsIntegralCurve γ v := by
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (|t - t₀|)
  obtain ⟨hl, hr⟩ := abs_lt.mp hn
  have hmem : t ∈ Set.Icc (t₀ - (n : ℝ)) (t₀ + (n : ℝ)) :=
    Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  have hnhd : Set.Icc (t₀ - (n : ℝ)) (t₀ + (n : ℝ)) ∈ 𝓝 t :=
    Icc_mem_nhds (by linarith) (by linarith)
  exact (h n t hmem).hasDerivAt hnhd

/-- **Finite-chain concatenation of consecutive-interval solutions.**  If `a : ℕ → ℝ` is monotone and
`γ` is an integral curve of `v` on every consecutive interval `Icc (a i) (a (i+1))`, then `γ` is an
integral curve on the whole span `Icc (a 0) (a (N+1))` for every `N`.  Proved by induction on `N`,
fusing one more interval at each step with `isIntegralCurveOn_Icc_union`.  This lifts the two-interval
gluing to arbitrarily many pieces — the induction that turns a sequence of local Picard–Lindelöf
solutions (arranged to share endpoints) into a single solution on an arbitrarily long interval, the
main input to the exhaustion lemma `isIntegralCurve_of_forall_mem_Icc`. -/
theorem isIntegralCurveOn_Icc_chain {a : ℕ → ℝ} (hmono : Monotone a)
    (h : ∀ i, IsIntegralCurveOn γ v (Set.Icc (a i) (a (i + 1)))) :
    ∀ N : ℕ, IsIntegralCurveOn γ v (Set.Icc (a 0) (a (N + 1))) := by
  intro N
  induction N with
  | zero => exact h 0
  | succ n ih =>
      exact isIntegralCurveOn_Icc_union
        (hmono (Nat.zero_le (n + 1))) (hmono (Nat.le_succ (n + 1))) ih (h (n + 1))

/-- **Right half-line from a growing family of forward compact-interval solutions.**  If `γ` is an
integral curve of `v` on every forward interval `Icc t₀ (t₀ + N)`, `N : ℕ`, then it is an integral
curve on the whole right half-line `Ici t₀`.  Any `t ≥ t₀` lies in `Icc t₀ (t₀ + N)` for large `N`
(Archimedean), and that interval is a within-`Ici t₀` neighbourhood of `t`, so the within-interval
derivative transports to `Ici t₀` by `HasDerivWithinAt.mono_of_mem_nhdsWithin`. -/
theorem isIntegralCurveOn_Ici_of_forall_Icc {t₀ : ℝ}
    (h : ∀ N : ℕ, IsIntegralCurveOn γ v (Set.Icc t₀ (t₀ + N))) :
    IsIntegralCurveOn γ v (Set.Ici t₀) := by
  intro t ht
  obtain ⟨N, hN⟩ := exists_nat_gt (t - t₀)
  have htmem : t ∈ Set.Icc t₀ (t₀ + (N : ℝ)) :=
    Set.mem_Icc.mpr ⟨Set.mem_Ici.mp ht, by linarith⟩
  have hd := h N t htmem
  apply hd.mono_of_mem_nhdsWithin
  rw [mem_nhdsWithin]
  exact ⟨Set.Iio (t₀ + (N : ℝ)), isOpen_Iio, Set.mem_Iio.mpr (by linarith),
    fun x hx => Set.mem_Icc.mpr ⟨Set.mem_Ici.mp hx.2, le_of_lt (Set.mem_Iio.mp hx.1)⟩⟩

/-- **Left half-line from a growing family of backward compact-interval solutions.**  The mirror of
`isIntegralCurveOn_Ici_of_forall_Icc`: integral-curve data on every backward interval
`Icc (t₀ - N) t₀`, `N : ℕ`, yields an integral curve on the whole left half-line `Iic t₀`. -/
theorem isIntegralCurveOn_Iic_of_forall_Icc {t₀ : ℝ}
    (h : ∀ N : ℕ, IsIntegralCurveOn γ v (Set.Icc (t₀ - N) t₀)) :
    IsIntegralCurveOn γ v (Set.Iic t₀) := by
  intro t ht
  obtain ⟨N, hN⟩ := exists_nat_gt (t₀ - t)
  have htmem : t ∈ Set.Icc (t₀ - (N : ℝ)) t₀ :=
    Set.mem_Icc.mpr ⟨by linarith, Set.mem_Iic.mp ht⟩
  have hd := h N t htmem
  apply hd.mono_of_mem_nhdsWithin
  rw [mem_nhdsWithin]
  exact ⟨Set.Ioi (t₀ - (N : ℝ)), isOpen_Ioi, Set.mem_Ioi.mpr (by linarith),
    fun x hx => Set.mem_Icc.mpr ⟨le_of_lt (Set.mem_Ioi.mp hx.1), Set.mem_Iic.mp hx.2⟩⟩

/-- **Global integral curve from forward and backward families of compact-interval solutions.**  If
`γ` is an integral curve of `v` on every forward interval `Icc t₀ (t₀ + N)` *and* on every backward
interval `Icc (t₀ - N) t₀`, then it is a *global* integral curve of `v`.  The two families give
integral-curve data on the right half-line `Ici t₀` and the left half-line `Iic t₀`
(`isIntegralCurveOn_Ici_of_forall_Icc`, `isIntegralCurveOn_Iic_of_forall_Icc`), and these glue at the
anchor `t₀` via `isIntegralCurve_of_isIntegralCurveOn_Iic_Ici`.  This is the end of the continuation
chain assembled in this section: it reduces *global* existence of an integral curve to solving the ODE
on the two growing families of compact intervals around the anchor — precisely the output produced by
iterating `isIntegralCurveOn_Icc_chain` over local Picard–Lindelöf solutions.  It discharges the
global-flow hypothesis shape `IsIntegralCurve` consumed throughout this file to the compact-interval
local theory that Mathlib v4.29.1 does supply. -/
theorem isIntegralCurve_of_forall_Icc_Ici_Iic {t₀ : ℝ}
    (hf : ∀ N : ℕ, IsIntegralCurveOn γ v (Set.Icc t₀ (t₀ + N)))
    (hb : ∀ N : ℕ, IsIntegralCurveOn γ v (Set.Icc (t₀ - N) t₀)) :
    IsIntegralCurve γ v :=
  isIntegralCurve_of_isIntegralCurveOn_Iic_Ici
    (isIntegralCurveOn_Iic_of_forall_Icc hb) (isIntegralCurveOn_Ici_of_forall_Icc hf)

/-- **Time reversal of an interval integral curve (the `IsIntegralCurveOn` companion of
`isIntegralCurve_comp_neg`).**  If `f` is an integral curve of `v` on a set `s`, then the reflected
curve `t ↦ f (-t)` is an integral curve of the time-reversed field `(t, x) ↦ -(v (-t) x)` on the
reflected set `Neg.neg ⁻¹' s`.  Proved by the within-set scalar chain rule (`HasDerivWithinAt.scomp`)
composing with the reparametrisation `Neg.neg` (whose within-derivative is `-1`), the `MapsTo` datum
being `Set.mapsTo_preimage`.  Since `Neg.neg ⁻¹' (Ici a) = Iic (-a)` and `Neg.neg ⁻¹' (Iic a) =
Ici (-a)`, this converts a *forward* half-line solution of the reflected field into a *backward*
half-line solution of `v`: it lets the backward family required by
`isIntegralCurve_of_forall_Icc_Ici_Iic` be supplied by a forward solver applied to the reflected
field, reducing global existence to *forward* local existence alone. -/
theorem isIntegralCurveOn_comp_neg {f : ℝ → E} {v : ℝ → E → E} {s : Set ℝ}
    (hf : IsIntegralCurveOn f v s) :
    IsIntegralCurveOn (fun t => f (-t)) (fun t x => -(v (-t) x)) (Neg.neg ⁻¹' s) := by
  intro t ht
  have hmem : -t ∈ s := ht
  have hcomp := (hf (-t) hmem).scomp t (hasDerivWithinAt_neg t (Neg.neg ⁻¹' s))
    (Set.mapsTo_preimage Neg.neg s)
  simpa only [Function.comp_def, neg_one_smul] using hcomp

/-!
### Local existence of integral curves (Picard–Lindelöf, uniform step)

The continuation stack above (`isIntegralCurveOn_Icc_union`, `isIntegralCurveOn_Icc_chain`,
`isIntegralCurve_of_forall_Icc_Ici_Iic`) reduces *global* existence of an integral curve to
*compact-interval* `IsIntegralCurveOn` data, and the augmented-flow reduction
(`hasDerivAt_inhomogVariation_of_augmented`) reduces existence of the first variation to existence of
a global integral curve of the Lipschitz field `augmentedVariationalField A F`.  The one remaining
input is *local* existence — which is exactly what Mathlib v4.29.1 supplies, via Picard–Lindelöf
(`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`) on a complete Banach space.

For a field that is **uniformly (in time) `K`-Lipschitz in state**, the local solution can be produced
on a time interval of a *uniform* half-length `lipschitzFlowStep K`, independent of the anchor
`(t₀, x₀)`.  The mechanism: on a closed ball of radius `a` the field is bounded by `K·a + C₀` (with
`C₀` a time-sup of `‖v · x₀‖`), so Picard–Lindelöf yields a solution of length `a/(K·a + C₀) → 1/K`
as `a → ∞`; choosing `a` large (depending on `C₀`) makes the length reach the fixed target
`lipschitzFlowStep K`.  This uniform lower bound on the step is what allows the local solutions to be
*chained* (via `isIntegralCurveOn_Icc_chain`) across an arbitrarily long compact interval — the
crucial property a merely-local existence statement would lack. -/

/-- The **uniform local-existence half-step** for a uniformly `K`-Lipschitz vector field: the
anchor-independent time radius `min 1 (1 / (2 (K + 1)))` on which a local integral curve is guaranteed
to exist (`exists_isIntegralCurveOn_Icc_of_lipschitzWith`).  It lies in `(0, 1]` and satisfies
`K · lipschitzFlowStep K ≤ 1/2`, the inequality that makes the Picard–Lindelöf interval-length
constraint solvable with a fixed step. -/
def lipschitzFlowStep (K : ℝ≥0) : ℝ := min 1 (1 / (2 * ((K : ℝ) + 1)))

/-- The uniform local-existence half-step is positive. -/
theorem lipschitzFlowStep_pos (K : ℝ≥0) : 0 < lipschitzFlowStep K := by
  refine lt_min one_pos ?_
  positivity

/-- The uniform local-existence half-step is at most `1`. -/
theorem lipschitzFlowStep_le_one (K : ℝ≥0) : lipschitzFlowStep K ≤ 1 := min_le_left _ _

/-- The defining inequality of the half-step: `K · lipschitzFlowStep K ≤ 1/2`.  (Since
`lipschitzFlowStep K ≤ 1 / (2 (K + 1))` and `K ≤ K + 1`.)  This is the bound that makes the
Picard–Lindelöf time-length constraint `L · h ≤ a` solvable with a *fixed* step `h`. -/
theorem lipschitzFlowStep_mul_le (K : ℝ≥0) : (K : ℝ) * lipschitzFlowStep K ≤ 1 / 2 := by
  have hK : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  have hstep : lipschitzFlowStep K ≤ 1 / (2 * ((K : ℝ) + 1)) := min_le_right _ _
  have hpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  calc (K : ℝ) * lipschitzFlowStep K
      ≤ (K : ℝ) * (1 / (2 * ((K : ℝ) + 1))) := by gcongr
    _ = (K : ℝ) / (2 * ((K : ℝ) + 1)) := by rw [mul_one_div]
    _ ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * ((K : ℝ) + 1))]
        nlinarith [hK]

/-- **Local existence of an integral curve, uniform step (Picard–Lindelöf).**  For a vector field
`v : ℝ → E → E` on a complete real Banach space that is uniformly (in time) `K`-Lipschitz in the state
(`∀ t, LipschitzWith K (v t)`) and continuous in time at every fixed state (`∀ x, Continuous (v · x)`),
and for any anchor `(t₀, x₀)`, there is an integral curve `γ` of `v` through `x₀` on the symmetric
closed interval of the *uniform* half-length `lipschitzFlowStep K` — a radius depending only on `K`,
**not** on the anchor `(t₀, x₀)`.

This is the local-existence input the continuation stack (`isIntegralCurveOn_Icc_chain`,
`isIntegralCurve_of_forall_Icc_Ici_Iic`) and the augmented-flow reduction
(`hasDerivAt_inhomogVariation_of_augmented`) consume — the one piece Mathlib supplies directly, here
packaged from `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`.  The uniform lower bound
on the step is essential: it lets the finitely many local solutions be chained across an arbitrarily
long compact interval.

Construction: on the closed ball `closedBall x₀ a` the field is bounded by `L = K·a + C₀` where
`C₀ = sup_{[t₀-h, t₀+h]} ‖v · x₀‖` (finite by compactness), so `IsPicardLindelof` holds on the
interval as soon as `L·h ≤ a`.  Taking `a = 2·h·(C₀+1) + 1` with `h = lipschitzFlowStep K` (whence
`K·h ≤ 1/2`) makes `L·h ≤ a/2 + (a-1)/2 = a - 1/2 ≤ a`. -/
theorem exists_isIntegralCurveOn_Icc_of_lipschitzWith [CompleteSpace E]
    {v : ℝ → E → E} {K : ℝ≥0}
    (hlip : ∀ t, LipschitzWith K (v t)) (hcont : ∀ x, Continuous fun t => v t x)
    (t₀ : ℝ) (x₀ : E) :
    ∃ γ : ℝ → E, γ t₀ = x₀ ∧
      IsIntegralCurveOn γ v (Set.Icc (t₀ - lipschitzFlowStep K) (t₀ + lipschitzFlowStep K)) := by
  set h : ℝ := lipschitzFlowStep K with hh_def
  have hh0 : 0 < h := by rw [hh_def]; exact lipschitzFlowStep_pos K
  have hKh : (K : ℝ) * h ≤ 1 / 2 := by rw [hh_def]; exact lipschitzFlowStep_mul_le K
  have hmem : t₀ ∈ Set.Icc (t₀ - h) (t₀ + h) := Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  -- time-sup of ‖v · x₀‖ on the compact interval
  have hcontOn : ContinuousOn (fun t => v t x₀) (Set.Icc (t₀ - h) (t₀ + h)) := (hcont x₀).continuousOn
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcontOn
  have hC₀0 : 0 ≤ C₀ := le_trans (norm_nonneg _) (hC₀ t₀ hmem)
  -- ball radius and field bound
  set a : ℝ := 2 * h * (C₀ + 1) + 1 with ha_def
  have ha0 : 0 < a := by rw [ha_def]; positivity
  set L : ℝ := (K : ℝ) * a + C₀ + 1 with hL_def
  have hL0 : 0 < L := by rw [hL_def]; positivity
  -- the Picard–Lindelöf interval-length inequality  L·h ≤ a
  have hLh : L * h ≤ a := by
    have e1 : (K : ℝ) * a * h ≤ a / 2 := by
      have h' : (K : ℝ) * a * h = a * ((K : ℝ) * h) := by ring
      rw [h']
      calc a * ((K : ℝ) * h) ≤ a * (1 / 2) := by gcongr
        _ = a / 2 := by ring
    have e2 : (C₀ + 1) * h = (a - 1) / 2 := by rw [ha_def]; ring
    have expand : L * h = (K : ℝ) * a * h + (C₀ + 1) * h := by rw [hL_def]; ring
    rw [expand, e2]; linarith [e1]
  -- build the Picard–Lindelöf datum on [t₀-h, t₀+h]
  have hpl : IsPicardLindelof v (⟨t₀, hmem⟩ : Set.Icc (t₀ - h) (t₀ + h)) x₀
      ⟨a, le_of_lt ha0⟩ 0 ⟨L, le_of_lt hL0⟩ K := by
    refine ⟨fun t _ => (hlip t).lipschitzOnWith, fun x _ => (hcont x).continuousOn,
      fun t ht x hx => ?_, ?_⟩
    · -- norm bound on the ball
      have hxa : dist x x₀ ≤ a := by
        have := Metric.mem_closedBall.mp hx
        change dist x x₀ ≤ a at this
        exact this
      have h_first : ‖v t x - v t x₀‖ ≤ (K : ℝ) * a := by
        rw [← dist_eq_norm]
        refine le_trans ((hlip t).dist_le_mul x x₀) ?_
        gcongr
      have h_second : ‖v t x₀‖ ≤ C₀ := hC₀ t ht
      have hle : ‖v t x‖ ≤ (K : ℝ) * a + C₀ := by
        have htri : ‖v t x‖ ≤ ‖v t x - v t x₀‖ + ‖v t x₀‖ := by
          simpa using norm_add_le (v t x - v t x₀) (v t x₀)
        calc ‖v t x‖ ≤ ‖v t x - v t x₀‖ + ‖v t x₀‖ := htri
          _ ≤ (K : ℝ) * a + C₀ := add_le_add h_first h_second
      calc ‖v t x‖ ≤ (K : ℝ) * a + C₀ := hle
        _ ≤ L := by rw [hL_def]; linarith
    · -- interval-length inequality
      show (L : ℝ) * max ((t₀ + h) - t₀) (t₀ - (t₀ - h)) ≤ a - ((0 : ℝ≥0) : ℝ)
      have hmax : max ((t₀ + h) - t₀) (t₀ - (t₀ - h)) = h := by
        rw [show (t₀ + h) - t₀ = h by ring, show t₀ - (t₀ - h) = h by ring, max_self]
      rw [hmax, NNReal.coe_zero, sub_zero]
      exact hLh
  obtain ⟨γ, hγ0, hγd⟩ :=
    IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ hpl
  exact ⟨γ, hγ0, fun t ht => hγd t ht⟩

/-- **Local existence of an integral curve at a point (Picard–Lindelöf).**  The
`IsIntegralCurveAt` form of `exists_isIntegralCurveOn_Icc_of_lipschitzWith`: a uniformly (in time)
`K`-Lipschitz, time-continuous vector field on a complete real Banach space admits, through any anchor
`(t₀, x₀)`, a local integral curve valid in a neighbourhood of `t₀`.  Obtained by upgrading the
solution on `Icc (t₀ - lipschitzFlowStep K) (t₀ + lipschitzFlowStep K)` to `IsIntegralCurveAt` at the
interior point `t₀` (the interval is a neighbourhood of `t₀` since `lipschitzFlowStep K > 0`), via
`IsIntegralCurveOn.isIntegralCurveAt`. -/
theorem exists_isIntegralCurveAt_of_lipschitzWith [CompleteSpace E]
    {v : ℝ → E → E} {K : ℝ≥0}
    (hlip : ∀ t, LipschitzWith K (v t)) (hcont : ∀ x, Continuous fun t => v t x)
    (t₀ : ℝ) (x₀ : E) :
    ∃ γ : ℝ → E, γ t₀ = x₀ ∧ IsIntegralCurveAt γ v t₀ := by
  obtain ⟨γ, hγ0, hγon⟩ := exists_isIntegralCurveOn_Icc_of_lipschitzWith hlip hcont t₀ x₀
  have hpos := lipschitzFlowStep_pos K
  exact ⟨γ, hγ0, hγon.isIntegralCurveAt (Icc_mem_nhds (by linarith) (by linarith))⟩

/-- **Forward existence on an arbitrary compact interval (continuation).**  A uniformly (in time)
`K`-Lipschitz, time-continuous vector field on a complete real Banach space admits, through any anchor
`(t₀, x₀)`, an integral curve on *every* forward compact interval `Icc t₀ T` (`t₀ ≤ T`).  Local
existence (`exists_isIntegralCurveOn_Icc_of_lipschitzWith`) supplies a solution over one uniform step
`lipschitzFlowStep K`; the constructive gluing `isIntegralCurveOn_glue_Icc` concatenates successive
steps.  The *uniform* step (independent of the anchor) is what guarantees finitely many steps reach
any `T` — the property that fails for a merely-local existence statement (a globally Lipschitz field
cannot blow up in finite time, so its trajectories extend to all times).

Proof: an induction shows `∃ γ, γ t₀ = x₀ ∧ IsIntegralCurveOn γ v (Icc t₀ (t₀ + n · step))` for every
`n : ℕ` (base = local existence restricted to `{t₀}`; step = extend the length-`n` solution by one
more local solution anchored at its right endpoint `(t₀ + n·step, γ (t₀ + n·step))`, glued at the
junction where the two curves agree by construction).  Choosing `n` with `t₀ + n·step ≥ T`
(Archimedean, `step > 0`) and restricting gives the claim.  (No hypothesis `t₀ ≤ T` is needed: for
`T < t₀` the interval `Icc t₀ T` is empty and the claim is vacuous.) -/
theorem exists_isIntegralCurveOn_Icc_forward_of_lipschitzWith [CompleteSpace E]
    {v : ℝ → E → E} {K : ℝ≥0}
    (hlip : ∀ t, LipschitzWith K (v t)) (hcont : ∀ x, Continuous fun t => v t x)
    (t₀ : ℝ) (x₀ : E) (T : ℝ) :
    ∃ γ : ℝ → E, γ t₀ = x₀ ∧ IsIntegralCurveOn γ v (Set.Icc t₀ T) := by
  set h : ℝ := lipschitzFlowStep K with hh_def
  have hh0 : 0 < h := by rw [hh_def]; exact lipschitzFlowStep_pos K
  -- `n`-step forward existence by induction on the number of uniform steps
  have hstep : ∀ n : ℕ, ∃ γ : ℝ → E, γ t₀ = x₀ ∧
      IsIntegralCurveOn γ v (Set.Icc t₀ (t₀ + (n : ℝ) * h)) := by
    intro n
    induction n with
    | zero =>
        obtain ⟨γ, hγ0, hγon⟩ := exists_isIntegralCurveOn_Icc_of_lipschitzWith hlip hcont t₀ x₀
        rw [← hh_def] at hγon
        refine ⟨γ, hγ0, ?_⟩
        simp only [Nat.cast_zero, zero_mul, add_zero]
        exact hγon.mono (Set.Icc_subset_Icc (by linarith) (by linarith))
    | succ n ih =>
        obtain ⟨γ, hγ0, hγon⟩ := ih
        have hb : t₀ + (↑(n + 1) : ℝ) * h = (t₀ + (n : ℝ) * h) + h := by push_cast; ring
        set b : ℝ := t₀ + (n : ℝ) * h with hb_def
        have hbb : t₀ ≤ b := by
          rw [hb_def]; have := mul_nonneg (Nat.cast_nonneg n) hh0.le; linarith
        obtain ⟨δ, hδ0, hδon⟩ := exists_isIntegralCurveOn_Icc_of_lipschitzWith hlip hcont b (γ b)
        rw [← hh_def] at hδon
        have hδon2 : IsIntegralCurveOn δ v (Set.Icc b (b + h)) :=
          hδon.mono (Set.Icc_subset_Icc (by linarith) (le_refl _))
        have hmatch : γ b = δ b := hδ0.symm
        have hconv : b + h = t₀ + (↑(n + 1) : ℝ) * h := by rw [hb]
        refine ⟨fun t => if t ≤ b then γ t else δ t, ?_, ?_⟩
        · show (if t₀ ≤ b then γ t₀ else δ t₀) = x₀
          rw [if_pos hbb]; exact hγ0
        · have hglue := isIntegralCurveOn_glue_Icc hbb (by linarith) hγon hδon2 hmatch
          rwa [hconv] at hglue
  -- pick enough steps to reach `T`, then restrict
  obtain ⟨n, hn⟩ := exists_nat_gt ((T - t₀) / h)
  have hTn : T ≤ t₀ + (n : ℝ) * h := by
    rw [div_lt_iff₀ hh0] at hn
    linarith
  obtain ⟨γ, hγ0, hγon⟩ := hstep n
  exact ⟨γ, hγ0, hγon.mono (Set.Icc_subset_Icc (le_refl _) hTn)⟩

/-- **Backward existence on an arbitrary compact interval (time reversal).**  A uniformly (in time)
`K`-Lipschitz, time-continuous vector field on a complete real Banach space admits, through any anchor
`(t₀, x₀)`, an integral curve on *every* backward compact interval `Icc T t₀`.  Obtained from the
forward result (`exists_isIntegralCurveOn_Icc_forward_of_lipschitzWith`) applied to the time-reversed
field `w t x = -(v (-t) x)` — itself uniformly `K`-Lipschitz (negation is `1`-Lipschitz) and
time-continuous — at the reflected anchor `(-t₀, x₀)`, then reflected back with
`isIntegralCurveOn_comp_neg`.  Since `-(w (-t) x) = v t x` and `Neg.neg ⁻¹' Icc (-t₀) (-T) = Icc T t₀`,
the reflected curve `t ↦ η (-t)` is an integral curve of `v` on `Icc T t₀`. -/
theorem exists_isIntegralCurveOn_Icc_backward_of_lipschitzWith [CompleteSpace E]
    {v : ℝ → E → E} {K : ℝ≥0}
    (hlip : ∀ t, LipschitzWith K (v t)) (hcont : ∀ x, Continuous fun t => v t x)
    (t₀ : ℝ) (x₀ : E) (T : ℝ) :
    ∃ γ : ℝ → E, γ t₀ = x₀ ∧ IsIntegralCurveOn γ v (Set.Icc T t₀) := by
  set w : ℝ → E → E := fun t x => -(v (-t) x) with hw_def
  have hlipW : ∀ t, LipschitzWith K (w t) := fun t => (hlip (-t)).neg
  have hcontW : ∀ x, Continuous fun t => w t x := fun x => ((hcont x).comp continuous_neg).neg
  obtain ⟨η, hη0, hηon⟩ :=
    exists_isIntegralCurveOn_Icc_forward_of_lipschitzWith hlipW hcontW (-t₀) x₀ (-T)
  have hcomp := isIntegralCurveOn_comp_neg hηon
  have e1 : (fun t x => -(w (-t) x)) = v := by
    funext t x; simp only [hw_def, neg_neg]
  have e2 : (Neg.neg ⁻¹' Set.Icc (-t₀) (-T)) = Set.Icc T t₀ := by
    ext s
    simp only [Set.mem_preimage, Set.mem_Icc, neg_le_neg_iff]
    tauto
  rw [e1, e2] at hcomp
  exact ⟨fun t => η (-t), hη0, hcomp⟩

/-- **Existence on an arbitrary compact interval containing the anchor.**  Combining the forward and
backward continuations: for a uniformly (in time) `K`-Lipschitz, time-continuous vector field on a
complete real Banach space and any anchor `(t₀, x₀)`, and any compact interval `Icc a b` with
`a ≤ t₀ ≤ b`, there is a *single* integral curve `γ` of `v` through `x₀` on all of `Icc a b`.  The
backward solution on `Icc a t₀` and the forward solution on `Icc t₀ b` (both through `x₀` at `t₀`)
agree at the junction `t₀` and are fused by `isIntegralCurveOn_glue_Icc`.  This is the compact-interval
existence the exhaustion lemmas (`isIntegralCurve_of_forall_mem_Icc`,
`isIntegralCurve_of_forall_Icc_Ici_Iic`) consume toward a global integral curve. -/
theorem exists_isIntegralCurveOn_Icc_of_lipschitzWith_containing [CompleteSpace E]
    {v : ℝ → E → E} {K : ℝ≥0}
    (hlip : ∀ t, LipschitzWith K (v t)) (hcont : ∀ x, Continuous fun t => v t x)
    (t₀ : ℝ) (x₀ : E) {a b : ℝ} (ha : a ≤ t₀) (hb : t₀ ≤ b) :
    ∃ γ : ℝ → E, γ t₀ = x₀ ∧ IsIntegralCurveOn γ v (Set.Icc a b) := by
  obtain ⟨γf, hγf0, hγfon⟩ :=
    exists_isIntegralCurveOn_Icc_forward_of_lipschitzWith hlip hcont t₀ x₀ b
  obtain ⟨γb, hγb0, hγbon⟩ :=
    exists_isIntegralCurveOn_Icc_backward_of_lipschitzWith hlip hcont t₀ x₀ a
  have hmatch : γb t₀ = γf t₀ := by rw [hγb0, hγf0]
  refine ⟨fun t => if t ≤ t₀ then γb t else γf t, ?_, ?_⟩
  · show (if t₀ ≤ t₀ then γb t₀ else γf t₀) = x₀
    rw [if_pos le_rfl]; exact hγb0
  · exact isIntegralCurveOn_glue_Icc ha hb hγbon hγfon hmatch

/-- **Interval uniqueness of integral curves.**  Two integral curves of a uniformly (in time)
`K`-Lipschitz vector field on a compact interval `Icc a b` that agree at a single *interior* point
`t₁ ∈ Ioo a b` agree on all of `Icc a b`.  This is Mathlib's Grönwall ODE uniqueness
(`ODE_solution_unique_of_mem_Icc`, with the trivial state constraint `s ≡ univ`): the `IsIntegralCurveOn`
within-interval derivatives upgrade to genuine `HasDerivAt` on the open interior (where `Icc a b` is a
neighbourhood), and `IsIntegralCurveOn.continuousOn` supplies the endpoint continuity.  It is the tool
that reconciles the per-window compact-interval solutions into a single global integral curve. -/
theorem eqOn_of_isIntegralCurveOn_Icc
    {v : ℝ → E → E} {K : ℝ≥0} (hlip : ∀ t, LipschitzWith K (v t))
    {a b t₁ : ℝ} (ht₁ : t₁ ∈ Set.Ioo a b) {γ₁ γ₂ : ℝ → E}
    (h₁ : IsIntegralCurveOn γ₁ v (Set.Icc a b)) (h₂ : IsIntegralCurveOn γ₂ v (Set.Icc a b))
    (heq : γ₁ t₁ = γ₂ t₁) : Set.EqOn γ₁ γ₂ (Set.Icc a b) :=
  ODE_solution_unique_of_mem_Icc (s := fun _ => Set.univ)
    (fun t _ => (hlip t).lipschitzOnWith) ht₁
    h₁.continuousOn
    (fun t ht => (h₁ t (Set.Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (fun _ _ => Set.mem_univ _)
    h₂.continuousOn
    (fun t ht => (h₂ t (Set.Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (fun _ _ => Set.mem_univ _) heq

/-- **Global existence of an integral curve (globally Lipschitz field).**  A vector field on a
complete real Banach space that is uniformly (in time) `K`-Lipschitz in state and continuous in time
admits, through any anchor `(t₀, x₀)`, a *global* integral curve `γ` (a genuine two-sided
`HasDerivAt` at every time).  This is the capstone of the existence tower for a globally Lipschitz
field: such fields never blow up in finite time, so their trajectories extend to all of `ℝ`.

Assembly: `exists_isIntegralCurveOn_Icc_of_lipschitzWith_containing` supplies, for each `n`, a solution
`Γ n` on the window `Icc (t₀ - (n+1)) (t₀ + (n+1))` through `x₀`.  By interval uniqueness
(`eqOn_of_isIntegralCurveOn_Icc`) these windows agree on overlaps, so the pointwise-selected curve
`γ t = Γ ⌊|t - t₀|⌋₊ t` (choosing the smallest window whose interior contains `t`) is unambiguous, and
on every symmetric compact interval `Icc (t₀ - m) (t₀ + m)` it coincides with the single solution
`Γ m`.  The countable-exhaustion lemma `isIntegralCurve_of_forall_mem_Icc` then upgrades this to a
global integral curve.  Feeding the augmented field `augmentedVariationalField A F` (uniformly
Lipschitz by `lipschitzWith_augmentedVariationalField`) into this result discharges the flow-existence
hypothesis of `hasDerivAt_inhomogVariation_of_augmented`, delivering the first variation. -/
theorem exists_isIntegralCurve_of_lipschitzWith [CompleteSpace E]
    {v : ℝ → E → E} {K : ℝ≥0}
    (hlip : ∀ t, LipschitzWith K (v t)) (hcont : ∀ x, Continuous fun t => v t x)
    (t₀ : ℝ) (x₀ : E) :
    ∃ γ : ℝ → E, γ t₀ = x₀ ∧ IsIntegralCurve γ v := by
  -- a solution on every symmetric window strictly containing the anchor
  have hex : ∀ n : ℕ, ∃ γ : ℝ → E, γ t₀ = x₀ ∧
      IsIntegralCurveOn γ v (Set.Icc (t₀ - ((n : ℝ) + 1)) (t₀ + ((n : ℝ) + 1))) := by
    intro n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    exact exists_isIntegralCurveOn_Icc_of_lipschitzWith_containing hlip hcont t₀ x₀
      (by linarith) (by linarith)
  choose Γ hΓ0 hΓon using hex
  set γ : ℝ → E := fun t => Γ ⌊|t - t₀|⌋₊ t with hγ_def
  -- windows agree: on the interior of window `k`, the selection equals `Γ m` whenever `k ≤ m`
  have hglobal_eq : ∀ (m : ℕ) (t : ℝ), |t - t₀| < (m : ℝ) + 1 → Γ ⌊|t - t₀|⌋₊ t = Γ m t := by
    intro m t htm
    set k := ⌊|t - t₀|⌋₊ with hk_def
    have hkm : k ≤ m := by
      have h1 : k < m + 1 := by
        rw [hk_def, Nat.floor_lt (abs_nonneg _)]; exact_mod_cast htm
      omega
    have hkmR : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
    have hltk : |t - t₀| < (k : ℝ) + 1 := by rw [hk_def]; exact Nat.lt_floor_add_one _
    have htk : t ∈ Set.Ioo (t₀ - ((k : ℝ) + 1)) (t₀ + ((k : ℝ) + 1)) := by
      rw [Set.mem_Ioo]; rw [abs_lt] at hltk; constructor <;> linarith
    have ht₀int : t₀ ∈ Set.Ioo (t₀ - ((k : ℝ) + 1)) (t₀ + ((k : ℝ) + 1)) := by
      rw [Set.mem_Ioo]; have := Nat.cast_nonneg (α := ℝ) k; constructor <;> linarith
    have hmsub : Set.Icc (t₀ - ((k : ℝ) + 1)) (t₀ + ((k : ℝ) + 1)) ⊆
        Set.Icc (t₀ - ((m : ℝ) + 1)) (t₀ + ((m : ℝ) + 1)) :=
      Set.Icc_subset_Icc (by linarith) (by linarith)
    have huniq : Set.EqOn (Γ k) (Γ m) (Set.Icc (t₀ - ((k : ℝ) + 1)) (t₀ + ((k : ℝ) + 1))) :=
      eqOn_of_isIntegralCurveOn_Icc hlip ht₀int (hΓon k) ((hΓon m).mono hmsub)
        (by rw [hΓ0 k, hΓ0 m])
    exact huniq (Set.Ioo_subset_Icc_self htk)
  refine ⟨γ, ?_, ?_⟩
  · show Γ ⌊|t₀ - t₀|⌋₊ t₀ = x₀
    simp only [sub_self, abs_zero, Nat.floor_zero]
    exact hΓ0 0
  · apply isIntegralCurve_of_forall_mem_Icc
    intro m t ht
    have htmem : |t - t₀| < (m : ℝ) + 1 := by
      rw [Set.mem_Icc] at ht; rw [abs_lt]; constructor <;> linarith
    have hgt : γ t = Γ m t := hglobal_eq m t htmem
    rw [hgt]
    have hmsub2 : Set.Icc (t₀ - (m : ℝ)) (t₀ + (m : ℝ)) ⊆
        Set.Icc (t₀ - ((m : ℝ) + 1)) (t₀ + ((m : ℝ) + 1)) :=
      Set.Icc_subset_Icc (by linarith) (by linarith)
    refine (((hΓon m).mono hmsub2) t ht).congr (fun y hy => ?_) hgt
    have hymem : |y - t₀| < (m : ℝ) + 1 := by
      rw [Set.mem_Icc] at hy; rw [abs_lt]; constructor <;> linarith
    exact hglobal_eq m y hymem

/-- **Existence of the first variation (the operator-ODE Duhamel existence, capstone).**  For
norm-bounded, continuous operator paths `A, F : ℝ → (E →L[ℝ] E)` on a complete real Banach space
(`‖A s‖₊ ≤ K`, `‖F s‖₊ ≤ M`, `Continuous A`, `Continuous F`) and any anchor time `t₀`, the anchored
*inhomogeneous variational ODE* `V' = A ∘ V + F`, `V t₀ = 0` has a (global) solution `V`.

This closes the **existence half** of the first-variation target that the whole
`augmentedVariationalField` / continuation apparatus was built for.  The homogenised augmented field
`augmentedVariationalField A F` on `(E →L[ℝ] E) × ℝ` is uniformly `(K + M)`-Lipschitz
(`lipschitzWith_augmentedVariationalField`) and continuous in time (composition/scalar-multiplication
continuity of `A`, `F`), so — the augmented state space `(E →L[ℝ] E) × ℝ` being complete — the global
existence theorem `exists_isIntegralCurve_of_lipschitzWith` produces an integral curve `z` through
`(0, 1)`.  Its operator coordinate `V = (z ·).1` solves the inhomogeneous variational ODE by
`hasDerivAt_inhomogVariation_of_augmented`.  Combined with the uniqueness
(`inhomogVariation_unique`), linearity (`firstVariation_perturbation_add_eq`, …) and a-priori bounds
(`norm_inhomogVariation_le`) already established, the first variation of the resolvent is now a fully
constructed object — the Gateaux/Fréchet derivative datum for the spatial `C^k` bootstrap of the flow
that Items 1 and 2 consume. -/
theorem exists_hasDerivAt_inhomogVariation [CompleteSpace E]
    {A F : ℝ → (E →L[ℝ] E)} {K M : ℝ≥0}
    (hA : ∀ s, ‖A s‖₊ ≤ K) (hF : ∀ s, ‖F s‖₊ ≤ M)
    (hAc : Continuous A) (hFc : Continuous F) (t₀ : ℝ) :
    ∃ V : ℝ → (E →L[ℝ] E), V t₀ = 0 ∧
      ∀ s, HasDerivAt V ((A s).comp (V s) + F s) s := by
  have hlipW : ∀ s, LipschitzWith (K + M) (augmentedVariationalField A F s) :=
    fun s => lipschitzWith_augmentedVariationalField hA hF s
  have hcontW : ∀ p : (E →L[ℝ] E) × ℝ,
      Continuous fun s => augmentedVariationalField A F s p := by
    intro p
    show Continuous fun s => ((A s).comp p.1 + p.2 • F s, (0 : ℝ))
    exact (Continuous.add (hAc.clm_comp continuous_const) (hFc.const_smul p.2)).prodMk
      continuous_const
  obtain ⟨z, hz0, hzcurve⟩ :=
    exists_isIntegralCurve_of_lipschitzWith hlipW hcontW t₀ ((0 : E →L[ℝ] E), (1 : ℝ))
  refine ⟨fun s => (z s).1, ?_, fun s => ?_⟩
  · show (z t₀).1 = 0
    rw [hz0]
  · exact hasDerivAt_inhomogVariation_of_augmented hzcurve hz0 s

/-- **Existence of the resolvent / fundamental solution (homogeneous operator ODE).**  For a
norm-bounded (`‖A s‖₊ ≤ K`), continuous operator path `A : ℝ → (E →L[ℝ] E)` on a complete real Banach
space and any anchor `t₀`, the *homogeneous* operator ODE `W' = A ∘ W` with identity initial condition
`W t₀ = 1` has a global solution `W : ℝ → (E →L[ℝ] E)`.  The right-composition field
`W ↦ (A s) ∘ W` is `K`-Lipschitz (submultiplicativity `‖(A s) ∘ (W₁ - W₂)‖ ≤ ‖A s‖ · ‖W₁ - W₂‖`) and
continuous in time (`Continuous.clm_comp`), so `exists_isIntegralCurve_of_lipschitzWith` on the
complete space `E →L[ℝ] E` supplies the curve.

This is the unconditional existence of the object the file's `fundamentalSolution` theory
(`hasDerivAt_fundamentalSolution`, `fundamentalSolution_eq_one_add_integral`, …) axiomatises as "given
a flow family": it discharges that flow-family hypothesis directly from the coefficient bound and
continuity, so the resolvent `D_x Φ_t` — the spatial derivative of the base flow — is now a
constructed object.  (Take `F = 0` in `exists_hasDerivAt_inhomogVariation` for the anchored-at-`0`
inhomogeneous sibling; here the anchor is the identity `1`, giving the genuine resolvent.) -/
theorem exists_hasDerivAt_resolvent [CompleteSpace E]
    {A : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ s, ‖A s‖₊ ≤ K) (hAc : Continuous A) (t₀ : ℝ) :
    ∃ W : ℝ → (E →L[ℝ] E), W t₀ = 1 ∧ ∀ s, HasDerivAt W ((A s).comp (W s)) s := by
  have hlip : ∀ s, LipschitzWith K (fun W : E →L[ℝ] E => (A s).comp W) := by
    intro s
    refine LipschitzWith.of_dist_le_mul fun W₁ W₂ => ?_
    have hAs : ‖A s‖ ≤ (K : ℝ) := by exact_mod_cast hA s
    rw [dist_eq_norm, dist_eq_norm, ← ContinuousLinearMap.comp_sub]
    calc ‖(A s).comp (W₁ - W₂)‖
        ≤ ‖A s‖ * ‖W₁ - W₂‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (K : ℝ) * ‖W₁ - W₂‖ := by gcongr
  have hcont : ∀ W : E →L[ℝ] E, Continuous fun s => (A s).comp W :=
    fun W => hAc.clm_comp continuous_const
  obtain ⟨W, hW0, hWcurve⟩ :=
    exists_isIntegralCurve_of_lipschitzWith hlip hcont t₀ (1 : E →L[ℝ] E)
  exact ⟨W, hW0, fun s => hWcurve s⟩

/-!
### Existence of the flow family (and the variational flow family)

The global existence theorem `exists_isIntegralCurve_of_lipschitzWith` produces, for *one* initial
value, a global integral curve.  Choosing such a curve for *every* initial value assembles a **flow
family** `Φ : E → ℝ → E` with `Φ z t₀ = z` and `IsIntegralCurve (Φ z) v` for all `z` — exactly the
`(hΦ, h0)` datum that the entire conditional dependence tower
(`hasFDerivAt_flow_of_defect_isLittleO`, `hasFDerivAt_flow_of_lipschitz_deriv`, …) takes as a
hypothesis.  Specialising to the vector variational field `variationalFieldVec A` (`K`-Lipschitz and,
for a continuous coefficient `A`, time-continuous) yields the **variational flow family** `Φ'` — the
`(hΦ', h0')` datum, from which the resolvent `fundamentalSolution hA hΦ' h0'` is built.  These two
existence lemmas discharge the flow-family hypotheses of the tower from field-level data alone. -/

/-- **Existence of the flow family.**  For a uniformly `K`-Lipschitz (`∀ t, LipschitzWith K (v t)`),
time-continuous (`∀ x, Continuous (v · x)`) field on a complete Banach space, there is a *family* of
global integral curves `Φ : E → ℝ → E` anchored at the identity, `Φ z t₀ = z`, with `Φ z` a global
integral curve of `v` for every initial value `z`.  Assembled by `choose`-ing an integral curve
through each `(t₀, z)` out of the global existence theorem `exists_isIntegralCurve_of_lipschitzWith`.
This is the `(hΦ, h0)` flow-family datum consumed by the whole `C¹`-dependence tower. -/
theorem exists_flow_family [CompleteSpace E]
    (hlip : ∀ t, LipschitzWith K (v t)) (hcont : ∀ x, Continuous fun t => v t x) :
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) := by
  choose Φ hΦ0 hΦcurve using
    fun z => exists_isIntegralCurve_of_lipschitzWith hlip hcont t₀ z
  exact ⟨Φ, hΦ0, hΦcurve⟩

/-- **Existence of the variational flow family.**  For a norm-bounded (`‖A s‖₊ ≤ K`), continuous
operator path `A : ℝ → (E →L[ℝ] E)` on a complete Banach space, there is a family of global integral
curves `Φ' : E → ℝ → E` of the vector variational field `variationalFieldVec A` (`u ↦ A · u`), anchored
`Φ' z t₀ = z`.  The field is `K`-Lipschitz (`lipschitzWith_variationalFieldVec`) and time-continuous
(evaluation of the continuous path `A` on a fixed direction, `Continuous.clm_apply`), so this is the
`variationalFieldVec` specialisation of `exists_flow_family`.  It is the `(hΦ', h0')` datum from which
the resolvent `fundamentalSolution hA hΦ' h0'` is constructed. -/
theorem exists_variationalFlowFamily [CompleteSpace E]
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K) (hAc : Continuous A) :
    ∃ Φ' : E → ℝ → E, (∀ z, Φ' z t₀ = z) ∧
      (∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A)) := by
  have hlip : ∀ s, LipschitzWith K (variationalFieldVec A s) :=
    fun s => lipschitzWith_variationalFieldVec hA s
  have hcont : ∀ x, Continuous fun s => variationalFieldVec A s x := by
    intro x
    simpa only [variationalFieldVec] using hAc.clm_apply continuous_const
  exact exists_flow_family hlip hcont

/-!
### Unconditional differentiable dependence on initial data for a `C^{1,1}` field

Assembling the flow-family existence with the `C^{1,1}` conditional theorem
`hasFDerivAt_flow_of_lipschitz_deriv` gives a fully **unconditional** differentiable-dependence
statement from *field-level* data only: a uniformly `K`-Lipschitz, time-continuous field whose spatial
Fréchet derivative `Dv` exists everywhere, is jointly continuous, and is (uniformly in time)
`L`-Lipschitz in space.  No flow family, no coefficient path, no resolvent need be supplied — they are
all constructed internally.  This is the Banach-level smooth-dependence-on-initial-data result that
Items 1 and 2 consume: the spatial derivative `x₀ ↦ D_x Φ_t` of the base flow exists and is the
resolvent. -/

/-- **Unconditional `C¹` dependence of the flow on initial data (`C^{1,1}` field).**  Let `v` be a
uniformly `K`-Lipschitz (`∀ τ, LipschitzWith K (v τ)`), time-continuous (`∀ x, Continuous (v · x)`)
field on a complete Banach space, whose spatial Fréchet derivative `Dv s x` exists at every `(s, x)`
(`hderiv`), is jointly continuous (`hDvc`), and is `L`-Lipschitz in the spatial variable uniformly in
time (`hDvlip`).  Then for every base point `x₀` and forward time `t ≥ t₀` there exist a flow family
`Φ` of `v` (anchored `Φ z t₀ = z`) and a bounded operator `D` (the resolvent
`fundamentalSolution … t = D_x Φ_t`) such that the flow map `z ↦ Φ z t` is **Fréchet differentiable**
at `x₀` with derivative `D`.

Proof: `exists_flow_family` builds `Φ`; the coefficient `A s := Dv s (Φ x₀ s)` (linearisation along the
reference trajectory) is norm-`≤ K` (`HasFDerivAt.le_of_lipschitz`, the derivative of a `K`-Lipschitz
map has norm `≤ K`) and continuous (`Dv` jointly continuous ∘ the continuous reference trajectory), so
`exists_variationalFlowFamily` builds the variational flow family `Φ'` and hence the resolvent `D`;
finally `hasFDerivAt_flow_of_lipschitz_deriv` closes the differentiability, its segment-wise derivative
hypothesis discharged by `HasFDerivAt.hasFDerivWithinAt` and its Lipschitz-defect hypothesis
`‖Dv s ξ - A s‖ = ‖Dv s ξ - Dv s (Φ x₀ s)‖ ≤ L‖ξ - Φ x₀ s‖` by `hDvlip`. -/
theorem exists_hasFDerivAt_flow_of_lipschitz_deriv [CompleteSpace E]
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ s x, HasFDerivAt (v s) (Dv s x) x)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    {L : ℝ≥0} (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (x₀ : E) {t : ℝ} (ht0 : t₀ ≤ t) :
    ∃ (Φ : E → ℝ → E) (D : E →L[ℝ] E),
      (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) ∧
        HasFDerivAt (fun z => Φ z t) D x₀ := by
  obtain ⟨Φ, h0, hΦ⟩ := exists_flow_family hv hvc
  -- coefficient `A s = Dv s (Φ x₀ s)`: norm-bounded (derivative of a `K`-Lipschitz map) …
  have hAnorm : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K := by
    intro s
    have h : ‖Dv s (Φ x₀ s)‖ ≤ (K : ℝ) := (hderiv s (Φ x₀ s)).le_of_lipschitz (hv s)
    exact_mod_cast h
  -- … and continuous (jointly continuous `Dv` along the continuous reference trajectory)
  have hAcont : Continuous fun s => Dv s (Φ x₀ s) := by
    have hpair : Continuous fun s : ℝ => (s, Φ x₀ s) :=
      continuous_id.prodMk (hΦ x₀).continuous
    exact hDvc.comp hpair
  obtain ⟨Φ', h0', hΦ'⟩ := exists_variationalFlowFamily hAnorm hAcont
  refine ⟨Φ, fundamentalSolution hAnorm hΦ' h0' t, h0, hΦ, ?_⟩
  refine hasFDerivAt_flow_of_lipschitz_deriv hv hAnorm hΦ' h0' hΦ h0 x₀ ht0
    (Dv := Dv) (L := (L : ℝ)) ?_ L.coe_nonneg ?_
  · intro z s _ ξ _
    exact (hderiv s ξ).hasFDerivWithinAt
  · intro z s _ ξ _
    have hlip := (hDvlip s).dist_le_mul ξ (Φ x₀ s)
    rw [dist_eq_norm, dist_eq_norm] at hlip
    exact hlip

/-- **The time-`t` flow map is differentiable in the initial condition everywhere (`C^{1,1}`
field).**  Strengthening `exists_hasFDerivAt_flow_of_lipschitz_deriv` to a *single* flow family that
is differentiable at *every* base point: under the same field-level hypotheses (uniformly
`K`-Lipschitz, time-continuous `v` with everywhere-defined, jointly continuous, spatially
`L`-Lipschitz derivative `Dv`), there is one flow family `Φ` of `v` (anchored `Φ z t₀ = z`) whose
forward time-`t` slice `z ↦ Φ z t` is `Differentiable ℝ` — i.e. Fréchet differentiable at every
initial value.  Proof: build `Φ` once with `exists_flow_family`, then at each base point `x₀` supply
the derivative via `exists_hasFDerivAt_flow_of_lipschitz_deriv`'s internal construction (coefficient
`Dv s (Φ x₀ s)`, variational flow family, resolvent) and read off `.differentiableAt`.  This is the
"`C¹` in initial data" regularity statement consumed by the spatial bootstrap of Items 1 and 2. -/
theorem exists_flow_differentiable_of_lipschitz_deriv [CompleteSpace E]
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ s x, HasFDerivAt (v s) (Dv s x) x)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    {L : ℝ≥0} (hDvlip : ∀ s, LipschitzWith L (Dv s))
    {t : ℝ} (ht0 : t₀ ≤ t) :
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) ∧
        Differentiable ℝ (fun z => Φ z t) := by
  obtain ⟨Φ, h0, hΦ⟩ := exists_flow_family hv hvc
  refine ⟨Φ, h0, hΦ, ?_⟩
  intro x₀
  have hAnorm : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K := by
    intro s
    have h : ‖Dv s (Φ x₀ s)‖ ≤ (K : ℝ) := (hderiv s (Φ x₀ s)).le_of_lipschitz (hv s)
    exact_mod_cast h
  have hAcont : Continuous fun s => Dv s (Φ x₀ s) := by
    have hpair : Continuous fun s : ℝ => (s, Φ x₀ s) :=
      continuous_id.prodMk (hΦ x₀).continuous
    exact hDvc.comp hpair
  obtain ⟨Φ', h0', hΦ'⟩ := exists_variationalFlowFamily hAnorm hAcont
  refine (hasFDerivAt_flow_of_lipschitz_deriv hv hAnorm hΦ' h0' hΦ h0 x₀ ht0
    (Dv := Dv) (L := (L : ℝ)) ?_ L.coe_nonneg ?_).differentiableAt
  · intro z s _ ξ _
    exact (hderiv s ξ).hasFDerivWithinAt
  · intro z s _ ξ _
    have hlip := (hDvlip s).dist_le_mul ξ (Φ x₀ s)
    rw [dist_eq_norm, dist_eq_norm] at hlip
    exact hlip

/-!
### Coefficient regularity for the base-point `C²` bootstrap

The `C¹` bootstrap (`hasFDerivAt_flow_of_lipschitz_deriv`, …) produces the resolvent
`R s = D_x Φ_s` as the Fréchet derivative of the flow in its initial value.  The next layer — the
base-point `C²`/`C^k` bootstrap — differentiates `x₀ ↦ R(x₀) s = fundamentalSolution … s` once more,
via the second-order variational estimates `norm_fundamentalSolution_sub_sub_variation_le` /
`norm_fundamentalSolution_variation_le`.  Its coefficient is the linearisation of the field along the
reference trajectory, `A(x₀) s = Dv s (Φ x₀ s)`, so the `C²` step consumes two facts about how this
coefficient depends on the base point `x₀`:

* its **Fréchet derivative** — the chain rule `∂/∂x₀ [Dv s (Φ x₀ s)] = D²v s (Φ x₀ s) ∘ D_x Φ_s`,
  requiring the field's *second* spatial derivative `D²v` and the already-established flow derivative
  `D_x Φ` (`hasFDerivAt_derivField_apply_flow`);
* its **size** — a Lipschitz-in-`x₀` bound making the coefficient perturbation
  `‖A(x₀+h) s - A(x₀) s‖ = O(‖h‖)`, *uniformly* on the compact time tube, the `ε`-datum
  (`hAA'`/`hε`) of the second-order variational estimates
  (`lipschitzWith_derivField_apply_flow`, `..._of_abs_le`, `norm_derivField_apply_flow_sub_le`).

Together with the **uniform-in-time first-order flow remainder**
`norm_flow_sub_fundamentalSolution_le_uniform` (the interval bound
`norm_flow_sub_fundamentalSolution_le_Icc` upgraded to a single Grönwall factor over `[t₀, T]`), these
are the coefficient-side inputs of the base-point `C²` bootstrap.  Everything below is proved from
field-level data (second spatial derivative of `v`, Lipschitz derivative, flow-family data); no PDE
or manifold content is used. -/

/-- **Chain rule for the linearised coefficient (`∂A/∂x₀`).**  If the time-`s` flow map `z ↦ Φ z s`
is Fréchet differentiable at `x₀` with derivative `R` (the resolvent `D_x Φ_s` supplied by the `C¹`
bootstrap) and the field's spatial derivative `Dv s` is itself Fréchet differentiable at the
trajectory point `Φ x₀ s` with derivative `D2` (the second spatial derivative `D²v s (Φ x₀ s)`), then
the linearised coefficient `z ↦ Dv s (Φ z s) = A(z) s` is Fréchet differentiable at `x₀` with
derivative `D2.comp R = D²v s (Φ x₀ s) ∘ D_x Φ_s`.  Pure chain rule (`HasFDerivAt.comp`); the `∂A/∂x₀`
ingredient with which the base-point `C²` bootstrap linearises the coefficient perturbation. -/
theorem hasFDerivAt_derivField_apply_flow
    {Dv : ℝ → E → (E →L[ℝ] E)} {Φ : E → ℝ → E} {x₀ : E} {s : ℝ}
    {R : E →L[ℝ] E} {D2 : E →L[ℝ] (E →L[ℝ] E)}
    (hΦ : HasFDerivAt (fun z => Φ z s) R x₀)
    (hDv : HasFDerivAt (Dv s) D2 (Φ x₀ s)) :
    HasFDerivAt (fun z => Dv s (Φ z s)) (D2.comp R) x₀ :=
  hDv.comp x₀ hΦ

/-- **Differentiability form of the coefficient chain rule.**  Under the hypotheses of
`hasFDerivAt_derivField_apply_flow`, the linearised coefficient `z ↦ Dv s (Φ z s)` is
`DifferentiableAt ℝ` at `x₀`. -/
theorem differentiableAt_derivField_apply_flow
    {Dv : ℝ → E → (E →L[ℝ] E)} {Φ : E → ℝ → E} {x₀ : E} {s : ℝ}
    {R : E →L[ℝ] E} {D2 : E →L[ℝ] (E →L[ℝ] E)}
    (hΦ : HasFDerivAt (fun z => Φ z s) R x₀)
    (hDv : HasFDerivAt (Dv s) D2 (Φ x₀ s)) :
    DifferentiableAt ℝ (fun z => Dv s (Φ z s)) x₀ :=
  (hasFDerivAt_derivField_apply_flow hΦ hDv).differentiableAt

/-- **The linearised coefficient is Lipschitz in the base point.**  If the field's spatial derivative
`Dv s` is `L`-Lipschitz and the time-`s` flow map `z ↦ Φ z s` is `C`-Lipschitz, then the linearised
coefficient `z ↦ Dv s (Φ z s) = A(z) s` is `L · C`-Lipschitz.  Composition of Lipschitz maps
(`LipschitzWith.comp`). -/
theorem lipschitzWith_derivField_apply_flow
    {Dv : ℝ → E → (E →L[ℝ] E)} {Φ : E → ℝ → E} {s : ℝ} {L C : ℝ≥0}
    (hDv : LipschitzWith L (Dv s))
    (hΦ : LipschitzWith C (fun z => Φ z s)) :
    LipschitzWith (L * C) (fun z => Dv s (Φ z s)) :=
  hDv.comp hΦ

/-- **Uniform Lipschitz-in-base-point bound for the linearised coefficient on a compact time tube.**
For a uniformly `K`-Lipschitz field `v` with `L`-Lipschitz spatial derivative `Dv s`, and a flow
family `Φ` of `v` anchored at `Φ x t₀ = x`, the linearised coefficient `z ↦ Dv s (Φ z s)` is
Lipschitz with the single constant `L · exp (K T)` for every time `s` with `|s - t₀| ≤ T`.  Combines
`lipschitzWith_derivField_apply_flow` with the uniform flow-Lipschitz bound
`lipschitzWith_flow_apply_of_abs_le` (`exp (K T)`, uniform in `s` on `[t₀ - T, t₀ + T]`). -/
theorem lipschitzWith_derivField_apply_flow_of_abs_le
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {L : ℝ≥0} {s T : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (hDv : LipschitzWith L (Dv s)) (hsT : |s - t₀| ≤ T) :
    LipschitzWith (L * (Real.exp ((K : ℝ) * T)).toNNReal) (fun z => Dv s (Φ z s)) :=
  lipschitzWith_derivField_apply_flow hDv (lipschitzWith_flow_apply_of_abs_le hv hΦ h0 hsT)

/-- **Coefficient-perturbation size datum for the second-order variational estimates.**  Under the
hypotheses of `lipschitzWith_derivField_apply_flow_of_abs_le`, the coefficient perturbation is
`O(‖z - w‖)` uniformly in `s` on the compact time tube:
`‖Dv s (Φ z s) - Dv s (Φ w s)‖ ≤ L · exp (K T) · ‖z - w‖` for `|s - t₀| ≤ T`.  This is exactly the
`hAA'`/`ε` input of `norm_fundamentalSolution_sub_sub_variation_le` and
`norm_fundamentalSolution_variation_le` (with `ε = L · exp (K T) · ‖z - w‖`), the leading-order size
of the coefficient response to a base-point increment `z - w`. -/
theorem norm_derivField_apply_flow_sub_le
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {L : ℝ≥0} {s T : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (hDv : LipschitzWith L (Dv s)) (hsT : |s - t₀| ≤ T) (z w : E) :
    ‖Dv s (Φ z s) - Dv s (Φ w s)‖ ≤ (L : ℝ) * Real.exp ((K : ℝ) * T) * ‖z - w‖ := by
  have hd := (lipschitzWith_derivField_apply_flow_of_abs_le hv hΦ h0 hDv hsT).dist_le_mul z w
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mul,
    Real.coe_toNNReal _ (Real.exp_pos _).le] at hd
  exact hd

/-- **Uniform-in-time linearisation remainder of the flow.**  The pointwise interval bound
`norm_flow_sub_fundamentalSolution_le_Icc` made uniform over the whole forward tube `[t₀, T]`: with a
single defect bound `δ` on `Ico t₀ T`, the linearisation remainder
`(Φ y t - Φ x t) - D_x Φ_t (y - x)` is bounded by `δ · gronwallBound 0 K 1 (T - t₀)` for *every*
`t ∈ [t₀, T]` — the `t`-dependent Grönwall factor `gronwallBound 0 K 1 (t - t₀)` is replaced by its
endpoint value at `T` (monotonicity `gronwallBound_mono`).  The uniform-in-`s` first-order remainder
consumed by the forcing analysis of the base-point `C²` bootstrap. -/
theorem norm_flow_sub_fundamentalSolution_le_uniform
    {A : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K)
    {Φ' : E → ℝ → E} (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec A))
    (h0' : ∀ z, Φ' z t₀ = z)
    {Φ : E → ℝ → E} (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (x y : E) {δ T : ℝ} (hδ : 0 ≤ δ)
    (hdefect : ∀ s ∈ Ico t₀ T,
      ‖v s (Φ y s) - v s (Φ x s) - A s (Φ y s - Φ x s)‖ ≤ δ)
    {t : ℝ} (ht : t ∈ Icc t₀ T) :
    ‖(Φ y t - Φ x t) - fundamentalSolution hA hΦ' h0' t (y - x)‖
      ≤ δ * gronwallBound 0 (K : ℝ) 1 (T - t₀) := by
  have hb := norm_flow_sub_fundamentalSolution_le_Icc hA hΦ' h0' hΦ h0 x y hdefect ht
  rw [gronwallBound_zero_left_mul] at hb
  refine hb.trans (mul_le_mul_of_nonneg_left ?_ hδ)
  exact gronwallBound_mono (le_refl (0 : ℝ)) zero_le_one K.coe_nonneg
    (show t - t₀ ≤ T - t₀ by linarith [ht.2])

/-- **Quadratic (`C^{1,1}`) Taylor remainder bound.**  If `g : E → F` is everywhere Fréchet
differentiable with derivative `g'` and `g'` is `M`-Lipschitz, then the first-order Taylor remainder
is *quadratically* small: `‖g b - g a - g' a (b - a)‖ ≤ M · ‖b - a‖²`.  Proof: on the segment `[a, b]`
the derivative deviation is `‖g' ξ - g' a‖ ≤ M ‖ξ - a‖ ≤ M ‖b - a‖` (Lipschitz `g'`, and
`‖ξ - a‖ ≤ ‖b - a‖` on the segment via `segment_eq_image'`), so the linearised mean-value inequality
`Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'` bounds the remainder by `(M ‖b - a‖) · ‖b - a‖`.
The pure-calculus second-order estimate the base-point `C²` bootstrap applies to the field's spatial
derivative to control the quadratic part of the coefficient perturbation. -/
theorem norm_sub_fderiv_le_mul_sq_of_lipschitz
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} {g' : E → (E →L[ℝ] F)} {M : ℝ≥0}
    (hg : ∀ ξ, HasFDerivAt g (g' ξ) ξ) (hg'lip : LipschitzWith M g') (a b : E) :
    ‖g b - g a - g' a (b - a)‖ ≤ (M : ℝ) * ‖b - a‖ ^ 2 := by
  have hseg : ∀ ξ ∈ segment ℝ a b, ‖ξ - a‖ ≤ ‖b - a‖ := by
    intro ξ hξ
    rw [segment_eq_image' ℝ a b] at hξ
    obtain ⟨θ, hθ, rfl⟩ := hξ
    have hsub : a + θ • (b - a) - a = θ • (b - a) := by abel
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
    have hm := mul_le_mul_of_nonneg_right hθ.2 (norm_nonneg (b - a))
    rwa [one_mul] at hm
  have hbound : ∀ ξ ∈ segment ℝ a b, ‖g' ξ - g' a‖ ≤ (M : ℝ) * ‖b - a‖ := by
    intro ξ hξ
    have h1 : ‖g' ξ - g' a‖ ≤ (M : ℝ) * ‖ξ - a‖ := by
      have hd := hg'lip.dist_le_mul ξ a
      rwa [dist_eq_norm, dist_eq_norm] at hd
    exact h1.trans (mul_le_mul_of_nonneg_left (hseg ξ hξ) M.coe_nonneg)
  have hmvt := (convex_segment a b).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := g) (f' := g') (φ := g' a)
    (fun ξ _ => (hg ξ).hasFDerivWithinAt) hbound
    (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
  calc ‖g b - g a - g' a (b - a)‖
      ≤ (M : ℝ) * ‖b - a‖ * ‖b - a‖ := hmvt
    _ = (M : ℝ) * ‖b - a‖ ^ 2 := by ring

/-- **Second-order (quadratic) part of the coefficient perturbation.**  Specialising
`norm_sub_fderiv_le_mul_sq_of_lipschitz` to the field's spatial derivative `g = Dv s`, `g' = D²v s`
(the second spatial derivative, `M`-Lipschitz): the trajectory-linearised coefficient's Taylor
remainder is quadratic in the trajectory separation,
`‖Dv s b - Dv s a - D²v s a (b - a)‖ ≤ M · ‖b - a‖²`.  With `a = Φ x₀ s`, `b = Φ (x₀+h) s`
(separation `≤ exp (K T) · ‖h‖` by `dist_flow_apply_le`), this is the `O(‖h‖²)` bracket of the
base-point `C²` coefficient expansion `A(x₀+h) s - A(x₀) s - (D²v s (Φ x₀ s) ∘ D_x Φ_s) h`; the
complementary bracket is `D²v s (Φ x₀ s)` applied to the uniform-in-time flow remainder
`norm_flow_sub_fundamentalSolution_le_uniform`. -/
theorem norm_derivField_sub_sub_secondDeriv_le
    {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))} {M : ℝ≥0} {s : ℝ}
    (hDv : ∀ ξ, HasFDerivAt (Dv s) (D2v s ξ) ξ) (hD2vlip : LipschitzWith M (D2v s)) (a b : E) :
    ‖Dv s b - Dv s a - D2v s a (b - a)‖ ≤ (M : ℝ) * ‖b - a‖ ^ 2 :=
  norm_sub_fderiv_le_mul_sq_of_lipschitz hDv hD2vlip a b

/-- **Flow-tube quadratic bound for the field's linearisation defect.**  For a `C^{1,1}` field `v`
(spatial derivative `Dv s`, `L`-Lipschitz), the defect of the trajectory linearisation is quadratic in
the initial separation, uniformly on the compact time tube:
`‖v s (Φ z s) - v s (Φ x s) - Dv s (Φ x s) (Φ z s - Φ x s)‖ ≤ L · exp (2 K T) · ‖z - x‖²` whenever
`|s - t₀| ≤ T`.  Combines the pure Taylor bound `norm_sub_fderiv_le_mul_sq_of_lipschitz` (applied to
`g = v s`, `g' = Dv s`, `a = Φ x s`, `b = Φ z s`) with the exponential flow-separation bound
`dist_flow_apply_le` (`‖Φ z s - Φ x s‖ ≤ exp (K T) ‖z - x‖`, whence the square is
`≤ exp (2 K T) ‖z - x‖²`).  This is the `δ = O(‖z - x‖²)` datum that, fed to
`norm_flow_sub_fundamentalSolution_le_uniform`, upgrades the qualitative `C¹` dependence of the flow to
a quantitative `C^{1,1}` (quadratic-remainder) rate. -/
theorem norm_field_linearizationDefect_flow_le
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {L : ℝ≥0} {s T : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x)
    (hDv : ∀ ξ, HasFDerivAt (v s) (Dv s ξ) ξ) (hDvlip : LipschitzWith L (Dv s))
    (hsT : |s - t₀| ≤ T) (x z : E) :
    ‖v s (Φ z s) - v s (Φ x s) - Dv s (Φ x s) (Φ z s - Φ x s)‖
      ≤ (L : ℝ) * Real.exp (2 * (K : ℝ) * T) * ‖z - x‖ ^ 2 := by
  have htaylor := norm_sub_fderiv_le_mul_sq_of_lipschitz hDv hDvlip (Φ x s) (Φ z s)
  refine htaylor.trans ?_
  have hexp : Real.exp ((K : ℝ) * |s - t₀|) ≤ Real.exp ((K : ℝ) * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsT K.coe_nonneg)
  have hsep : ‖Φ z s - Φ x s‖ ≤ Real.exp ((K : ℝ) * T) * ‖z - x‖ := by
    have hd := dist_flow_apply_le hv hΦ h0 z x s
    rw [dist_eq_norm, dist_eq_norm] at hd
    calc ‖Φ z s - Φ x s‖ ≤ ‖z - x‖ * Real.exp ((K : ℝ) * |s - t₀|) := hd
      _ ≤ ‖z - x‖ * Real.exp ((K : ℝ) * T) := mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
      _ = Real.exp ((K : ℝ) * T) * ‖z - x‖ := mul_comm _ _
  have hsq : ‖Φ z s - Φ x s‖ ^ 2 ≤ (Real.exp ((K : ℝ) * T) * ‖z - x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hsep 2
  have hexp2 : Real.exp ((K : ℝ) * T) ^ 2 = Real.exp (2 * (K : ℝ) * T) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  calc (L : ℝ) * ‖Φ z s - Φ x s‖ ^ 2
      ≤ (L : ℝ) * (Real.exp ((K : ℝ) * T) * ‖z - x‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq L.coe_nonneg
    _ = (L : ℝ) * Real.exp (2 * (K : ℝ) * T) * ‖z - x‖ ^ 2 := by rw [mul_pow, hexp2]; ring

/-- **Quantitative `C^{1,1}` dependence of the flow on the initial condition.**  For a `C^{1,1}` field
`v` (uniformly `K`-Lipschitz, spatial derivative `Dv s` everywhere-defined and `L`-Lipschitz), the
flow's first-order Taylor remainder in the initial value is *quadratically* small, uniformly on the
forward compact time tube `[t₀, T]`:
`‖Φ z t - Φ x₀ t - D_x Φ_t (z - x₀)‖ ≤ L · exp (2 K (T - t₀)) · gronwallBound 0 K 1 (T - t₀) · ‖z - x₀‖²`
for every `t ∈ [t₀, T]`, where `D_x Φ_t = fundamentalSolution … t` is the resolvent (linearised
coefficient `A s = Dv s (Φ x₀ s)`).  This strengthens the qualitative `C¹` statement
`hasFDerivAt_flow_of_lipschitz_deriv` (remainder `o(‖z - x₀‖)`) to an explicit second-order
(`O(‖z - x₀‖²)`) rate.  Proof: the field's trajectory-linearisation defect is `O(‖z - x₀‖²)` uniformly
in `s` (`norm_field_linearizationDefect_flow_le`), which is exactly the defect datum `δ` fed to the
uniform-in-time flow remainder `norm_flow_sub_fundamentalSolution_le_uniform`. -/
theorem norm_flow_sub_fundamentalSolution_le_sq
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {L : ℝ≥0}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ) (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    (z : E) {T t : ℝ} (ht : t ∈ Icc t₀ T) :
    ‖Φ z t - Φ x₀ t - fundamentalSolution hA hΦ' h0' t (z - x₀)‖
      ≤ (L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
          * gronwallBound 0 (K : ℝ) 1 (T - t₀) * ‖z - x₀‖ ^ 2 := by
  have hdefect : ∀ s ∈ Ico t₀ T,
      ‖v s (Φ z s) - v s (Φ x₀ s) - Dv s (Φ x₀ s) (Φ z s - Φ x₀ s)‖
        ≤ (L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀)) * ‖z - x₀‖ ^ 2 := by
    intro s hs
    have hsT : |s - t₀| ≤ T - t₀ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
    exact norm_field_linearizationDefect_flow_le hv hΦ h0 (hDv s) (hDvlip s) hsT x₀ z
  have hδ0 : (0 : ℝ) ≤ (L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀)) * ‖z - x₀‖ ^ 2 := by positivity
  have hmain := norm_flow_sub_fundamentalSolution_le_uniform hA hΦ' h0' hΦ h0 x₀ z hδ0 hdefect ht
  refine hmain.trans_eq ?_
  ring

/-- **Flow-separation square bound on the compact time tube.**  `‖Φ z s - Φ x s‖² ≤ exp (2 K T) ‖z - x‖²`
whenever `|s - t₀| ≤ T`; the square of the exponential flow-Lipschitz bound `dist_flow_apply_le`.  A
reusable factor for the quadratic (`C^{1,1}`/`C²`) remainder estimates, where a `‖b - a‖²` Taylor term
with `a = Φ x s`, `b = Φ z s` must be re-expressed in the initial separation `‖z - x‖`. -/
theorem norm_flow_sub_sq_le
    {Φ : E → ℝ → E} {s T : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hsT : |s - t₀| ≤ T) (x z : E) :
    ‖Φ z s - Φ x s‖ ^ 2 ≤ Real.exp (2 * (K : ℝ) * T) * ‖z - x‖ ^ 2 := by
  have hexp : Real.exp ((K : ℝ) * |s - t₀|) ≤ Real.exp ((K : ℝ) * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsT K.coe_nonneg)
  have hsep : ‖Φ z s - Φ x s‖ ≤ Real.exp ((K : ℝ) * T) * ‖z - x‖ := by
    have hd := dist_flow_apply_le hv hΦ h0 z x s
    rw [dist_eq_norm, dist_eq_norm] at hd
    calc ‖Φ z s - Φ x s‖ ≤ ‖z - x‖ * Real.exp ((K : ℝ) * |s - t₀|) := hd
      _ ≤ ‖z - x‖ * Real.exp ((K : ℝ) * T) := mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
      _ = Real.exp ((K : ℝ) * T) * ‖z - x‖ := mul_comm _ _
  have hexp2 : Real.exp ((K : ℝ) * T) ^ 2 = Real.exp (2 * (K : ℝ) * T) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  calc ‖Φ z s - Φ x s‖ ^ 2
      ≤ (Real.exp ((K : ℝ) * T) * ‖z - x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hsep 2
    _ = Real.exp (2 * (K : ℝ) * T) * ‖z - x‖ ^ 2 := by rw [mul_pow, hexp2]

/-- **Quadratic (`C²`) Taylor bound for the trajectory-linearised coefficient.**  For a `C^{2,1}`
field `v` (uniformly `K`-Lipschitz; spatial derivative `Dv s` everywhere-defined and `L`-Lipschitz;
second spatial derivative `D²v s` everywhere-defined, `M`-Lipschitz, and bounded by `C'` along the
reference trajectory `s ↦ Φ x₀ s`), the coefficient `A(x₀) s = Dv s (Φ x₀ s)` has a *quadratically
small* Taylor remainder in the base point, uniformly on the compact time tube `[t₀, T]`:
`‖Dv s (Φ z s) - Dv s (Φ x₀ s) - (D²v s (Φ x₀ s) ∘ D_x Φ_s) (z - x₀)‖`
`  ≤ (M · e + C' · (L · e · g)) · ‖z - x₀‖²`, where `e = exp (2 K (T - t₀))`,
`g = gronwallBound 0 K 1 (T - t₀)`, and `D_x Φ_s = fundamentalSolution … s` is the resolvent.  The
linear map `D²v s (Φ x₀ s) ∘ D_x Φ_s` is precisely `∂/∂x₀ [Dv s (Φ x₀ s)]`
(`hasFDerivAt_derivField_apply_flow`), so this is a *quantitative Fréchet* statement: the coefficient is
`C^{1,1}` in the base point with an `O(‖z - x₀‖²)` remainder.  Proof: split the remainder into the pure
`C^{1,1}` Taylor remainder of `Dv s` (`norm_derivField_sub_sub_secondDeriv_le` + `norm_flow_sub_sq_le`)
plus `D²v s (Φ x₀ s)` applied to the flow's own quadratic remainder
(`norm_flow_sub_fundamentalSolution_le_sq`, bounded via `‖D²v s (Φ x₀ s)‖ ≤ C'`).  This is the
coefficient-side second-order estimate feeding the second-order variational estimate
`norm_fundamentalSolution_sub_sub_variation_le` in the base-point `C²` bootstrap. -/
theorem norm_derivField_sub_sub_comp_fundamentalSolution_le_sq
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {L M : ℝ≥0} {C' : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ) (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2v : ∀ s ξ, HasFDerivAt (Dv s) (D2v s ξ) ξ) (hD2vlip : ∀ s, LipschitzWith M (D2v s))
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hC'0 : 0 ≤ C') (hC' : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ C')
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    (z : E) {T s : ℝ} (hs : s ∈ Icc t₀ T) :
    ‖Dv s (Φ z s) - Dv s (Φ x₀ s)
        - (D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) (z - x₀)‖
      ≤ ((M : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
          + C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
              * gronwallBound 0 (K : ℝ) 1 (T - t₀))) * ‖z - x₀‖ ^ 2 := by
  have hsT : |s - t₀| ≤ T - t₀ := by
    rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
  rw [ContinuousLinearMap.comp_apply]
  have hms : D2v s (Φ x₀ s) ((Φ z s - Φ x₀ s) - fundamentalSolution hA hΦ' h0' s (z - x₀))
      = D2v s (Φ x₀ s) (Φ z s - Φ x₀ s)
        - D2v s (Φ x₀ s) (fundamentalSolution hA hΦ' h0' s (z - x₀)) :=
    (D2v s (Φ x₀ s)).map_sub _ _
  have hsplit :
      Dv s (Φ z s) - Dv s (Φ x₀ s) - D2v s (Φ x₀ s) (fundamentalSolution hA hΦ' h0' s (z - x₀))
        = (Dv s (Φ z s) - Dv s (Φ x₀ s) - D2v s (Φ x₀ s) (Φ z s - Φ x₀ s))
          + D2v s (Φ x₀ s) ((Φ z s - Φ x₀ s) - fundamentalSolution hA hΦ' h0' s (z - x₀)) := by
    rw [hms]; abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hb1 : ‖Dv s (Φ z s) - Dv s (Φ x₀ s) - D2v s (Φ x₀ s) (Φ z s - Φ x₀ s)‖
      ≤ (M : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀)) * ‖z - x₀‖ ^ 2 := by
    have htay := norm_derivField_sub_sub_secondDeriv_le (hD2v s) (hD2vlip s) (Φ x₀ s) (Φ z s)
    have hfs := norm_flow_sub_sq_le hv hΦ h0 hsT x₀ z
    calc ‖Dv s (Φ z s) - Dv s (Φ x₀ s) - D2v s (Φ x₀ s) (Φ z s - Φ x₀ s)‖
        ≤ (M : ℝ) * ‖Φ z s - Φ x₀ s‖ ^ 2 := htay
      _ ≤ (M : ℝ) * (Real.exp (2 * (K : ℝ) * (T - t₀)) * ‖z - x₀‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hfs M.coe_nonneg
      _ = (M : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀)) * ‖z - x₀‖ ^ 2 := by ring
  have hb2 : ‖D2v s (Φ x₀ s) ((Φ z s - Φ x₀ s) - fundamentalSolution hA hΦ' h0' s (z - x₀))‖
      ≤ C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
          * gronwallBound 0 (K : ℝ) 1 (T - t₀)) * ‖z - x₀‖ ^ 2 := by
    have hflow := norm_flow_sub_fundamentalSolution_le_sq hv hΦ h0 hDv hDvlip x₀ hA hΦ' h0' z hs
    calc ‖D2v s (Φ x₀ s) ((Φ z s - Φ x₀ s) - fundamentalSolution hA hΦ' h0' s (z - x₀))‖
        ≤ ‖D2v s (Φ x₀ s)‖
            * ‖(Φ z s - Φ x₀ s) - fundamentalSolution hA hΦ' h0' s (z - x₀)‖ :=
          (D2v s (Φ x₀ s)).le_opNorm _
      _ ≤ C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
            * gronwallBound 0 (K : ℝ) 1 (T - t₀) * ‖z - x₀‖ ^ 2) :=
          mul_le_mul (hC' s) hflow (norm_nonneg _) hC'0
      _ = C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
            * gronwallBound 0 (K : ℝ) 1 (T - t₀)) * ‖z - x₀‖ ^ 2 := by ring
  exact (add_le_add hb1 hb2).trans_eq (by ring)

/-- **Second-order agreement of the resolvent's first variation with its linearised (chain-rule)
form.**  Fix the base point `x₀` with reference coefficient `A₀ s = Dv s (Φ x₀ s)` and resolvent
`W₀ s = D_x Φ_s = fundamentalSolution hA hΦ' h0' s`.  For a nearby base point `z`, let

* `Vz` be the *true* first variation — the anchored solution of
  `Vz' = A₀ ∘ Vz + (A_z - A₀) ∘ W₀` (`A_z s = Dv s (Φ z s)`), the leading response of the resolvent
  to the actual coefficient perturbation `A_z - A₀`; and
* `Vlin` be the *linearised* first variation — the anchored solution of
  `Vlin' = A₀ ∘ Vlin + (∂A₀/∂x₀ · (z - x₀)) ∘ W₀`, whose forcing uses the *chain-rule* coefficient
  derivative `∂A₀/∂x₀ = D²v(Φ x₀ s) ∘ W₀` (`hasFDerivAt_derivField_apply_flow`) evaluated on the
  base-point increment `z - x₀`.

Then the two first variations agree to *second order* in the increment, uniformly on `[t₀, T]`:
`‖Vz t - Vlin t‖ ≤ Cquad · exp (K (T - t₀)) · gronwallBound 0 K 1 (t - t₀) · ‖z - x₀‖²`, where
`Cquad = M · e + C' · (L · e · g)` (`e = exp (2 K (T - t₀))`, `g = gronwallBound 0 K 1 (T - t₀)`) is
the coefficient Taylor constant of `norm_derivField_sub_sub_comp_fundamentalSolution_le_sq`.  Proof:
the difference `Vz - Vlin` is (`hasDerivAt_firstVariation_perturbation_sub`) the first variation for
the perturbation `(A_z - A₀) - ∂A₀/∂x₀ · (z - x₀)`, whose forcing is bounded by
`(Cquad ‖z - x₀‖²) · ‖W₀ s‖ ≤ Cquad ‖z - x₀‖² · exp (K (T - t₀))` (the coefficient Taylor bound
`norm_derivField_sub_sub_comp_fundamentalSolution_le_sq` times the resolvent bound
`norm_fundamentalSolution_le`); the general a-priori first-variation bound `norm_inhomogVariation_le`
closes it.  This is the second-order term of the base-point `C²` bootstrap: since `Vlin` is *linear*
in `z - x₀`, it identifies the Fréchet derivative of the resolvent in the base point, with an
`O(‖z - x₀‖²)` remainder. -/
theorem norm_firstVariation_sub_linearVariation_le_sq
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {L M : ℝ≥0} {C' : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ) (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2v : ∀ s ξ, HasFDerivAt (Dv s) (D2v s ξ) ξ) (hD2vlip : ∀ s, LipschitzWith M (D2v s))
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hC'0 : 0 ≤ C') (hC' : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ C')
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    (z : E) {T : ℝ}
    {Vz Vlin : ℝ → (E →L[ℝ] E)}
    (hVz : ∀ s, HasDerivAt Vz
      ((Dv s (Φ x₀ s)).comp (Vz s)
        + (Dv s (Φ z s) - Dv s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s)) s)
    (hVz0 : Vz t₀ = 0)
    (hVlin : ∀ s, HasDerivAt Vlin
      ((Dv s (Φ x₀ s)).comp (Vlin s)
        + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) (z - x₀)).comp
            (fundamentalSolution hA hΦ' h0' s)) s)
    (hVlin0 : Vlin t₀ = 0)
    {t : ℝ} (ht : t ∈ Icc t₀ T) :
    ‖Vz t - Vlin t‖
      ≤ ((M : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
          + C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
              * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
        * Real.exp ((K : ℝ) * (T - t₀))
        * gronwallBound 0 (K : ℝ) 1 (t - t₀)
        * ‖z - x₀‖ ^ 2 := by
  set Cquad : ℝ := (M : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
      + C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
          * gronwallBound 0 (K : ℝ) 1 (T - t₀)) with hCquad
  set expT : ℝ := Real.exp ((K : ℝ) * (T - t₀)) with hexpT
  have hCquad0 : 0 ≤ Cquad := by
    rw [hCquad]
    refine add_nonneg (mul_nonneg M.coe_nonneg (Real.exp_pos _).le) ?_
    refine mul_nonneg hC'0 (mul_nonneg (mul_nonneg L.coe_nonneg (Real.exp_pos _).le) ?_)
    exact gronwallBound_zero_one_nonneg K.coe_nonneg (sub_nonneg.mpr (le_trans ht.1 ht.2))
  -- The difference `Vz - Vlin` is the first variation for the residual coefficient perturbation.
  have hVd := hasDerivAt_firstVariation_perturbation_sub hVz hVlin
  -- Bound the residual forcing by `Cquad · ‖z - x₀‖² · expT` on the tube `[t₀, T]`.
  have hFbound : ∀ s ∈ Icc t₀ T,
      ‖((Dv s (Φ z s) - Dv s (Φ x₀ s))
          - (D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) (z - x₀)).comp
            (fundamentalSolution hA hΦ' h0' s)‖
        ≤ Cquad * ‖z - x₀‖ ^ 2 * expT := by
    intro s hs
    have htaylor := norm_derivField_sub_sub_comp_fundamentalSolution_le_sq
      hv hΦ h0 hDv hDvlip hD2v hD2vlip x₀ hA hC'0 hC' hΦ' h0' z hs
    have hWbound : ‖fundamentalSolution hA hΦ' h0' s‖ ≤ expT := by
      refine (norm_fundamentalSolution_le hA hΦ' h0' s).trans ?_
      rw [hexpT]
      refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ K.coe_nonneg)
      rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
    calc ‖((Dv s (Φ z s) - Dv s (Φ x₀ s))
              - (D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) (z - x₀)).comp
                (fundamentalSolution hA hΦ' h0' s)‖
        ≤ ‖(Dv s (Φ z s) - Dv s (Φ x₀ s))
              - (D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) (z - x₀)‖
            * ‖fundamentalSolution hA hΦ' h0' s‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (Cquad * ‖z - x₀‖ ^ 2) * expT :=
          mul_le_mul htaylor hWbound (norm_nonneg _)
            (mul_nonneg hCquad0 (sq_nonneg _))
      _ = Cquad * ‖z - x₀‖ ^ 2 * expT := by ring
  have hV0 : (fun r => Vz r - Vlin r) t₀ = 0 := by simp [hVz0, hVlin0]
  have hbound := norm_inhomogVariation_le hA hVd hV0 hFbound ht
  calc ‖Vz t - Vlin t‖
      = ‖(fun r => Vz r - Vlin r) t‖ := by rfl
    _ ≤ Cquad * ‖z - x₀‖ ^ 2 * expT * gronwallBound 0 (K : ℝ) 1 (t - t₀) := hbound
    _ = Cquad * expT * gronwallBound 0 (K : ℝ) 1 (t - t₀) * ‖z - x₀‖ ^ 2 := by ring

/-- **Interval-restricted directional resolvent-coefficient bound.**  The variant of
`norm_fundamentalSolution_sub_apply_le_of_forall_le` whose coefficient-gap hypothesis
`‖A s - A' s‖ ≤ ε` is required only on the compact tube `[t₀, T]` (the proof only ever evaluates the
gap there).  This is the form the base-point `C²` bootstrap needs: the trajectory-linearised
coefficients `A₀ s = Dv s (Φ x₀ s)` and `A_z s = Dv s (Φ z s)` are close *only on compact time
intervals* (their difference `≤ L · exp (K (T - t₀)) · ‖z - x₀‖` grows with the tube), never
globally. -/
theorem norm_fundamentalSolution_sub_apply_le_of_forall_le_Icc
    {A A' : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K) (hA' : ∀ s, ‖A' s‖₊ ≤ K)
    {Φ₁ Φ₂ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec A)) (h1 : ∀ x, Φ₁ x t₀ = x)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec A')) (h2 : ∀ x, Φ₂ x t₀ = x)
    {ε : ℝ} {T : ℝ} (hAA' : ∀ s ∈ Icc t₀ T, ‖A s - A' s‖ ≤ ε)
    (u₀ : E) {t : ℝ} (ht : t ∈ Icc t₀ T) :
    ‖fundamentalSolution hA hΦ₁ h1 t u₀ - fundamentalSolution hA' hΦ₂ h2 t u₀‖
      ≤ ε * Real.exp ((K : ℝ) * (T - t₀)) * ‖u₀‖ * gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
  set εg : ℝ := ε * Real.exp ((K : ℝ) * (T - t₀)) * ‖u₀‖ with hεg
  have hgbound : ∀ s ∈ Ico t₀ T,
      dist (variationalFieldVec A' s (Φ₂ u₀ s)) (variationalFieldVec A s (Φ₂ u₀ s)) ≤ εg := by
    intro s hs
    have hsle : |s - t₀| ≤ T - t₀ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
      exact sub_le_sub_right hs.2.le t₀
    have hgnorm : ‖Φ₂ u₀ s‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) * ‖u₀‖ := by
      refine (norm_flow_variationalFieldVec_le hA' hΦ₂ h2 u₀ s).trans ?_
      exact mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsle K.coe_nonneg)) (norm_nonneg _)
    have hcoeff : ‖A' s - A s‖ ≤ ε := by
      rw [show A' s - A s = -(A s - A' s) by abel, norm_neg]
      exact hAA' s ⟨hs.1, hs.2.le⟩
    calc dist (variationalFieldVec A' s (Φ₂ u₀ s)) (variationalFieldVec A s (Φ₂ u₀ s))
        = ‖(A' s - A s) (Φ₂ u₀ s)‖ := by
          simp only [variationalFieldVec, dist_eq_norm, ContinuousLinearMap.sub_apply]
      _ ≤ ‖A' s - A s‖ * ‖Φ₂ u₀ s‖ := (A' s - A s).le_opNorm _
      _ ≤ ε * (Real.exp ((K : ℝ) * (T - t₀)) * ‖u₀‖) :=
          mul_le_mul hcoeff hgnorm (norm_nonneg _) (le_trans (norm_nonneg _) hcoeff)
      _ = εg := by rw [hεg]; ring
  have key := dist_le_of_approx_trajectories_ODE
    (v := variationalFieldVec A) (a := t₀) (b := T)
    (f := fun s => Φ₁ u₀ s) (g := fun s => Φ₂ u₀ s)
    (f' := fun s => variationalFieldVec A s (Φ₁ u₀ s))
    (g' := fun s => variationalFieldVec A' s (Φ₂ u₀ s))
    (εf := 0) (εg := εg) (δ := 0) (K := K)
    (fun s => lipschitzWith_variationalFieldVec hA s)
    (hΦ₁ u₀).continuous.continuousOn
    (fun s _ => (hΦ₁ u₀ s).hasDerivWithinAt)
    (fun s _ => le_of_eq (dist_self _))
    (hΦ₂ u₀).continuous.continuousOn
    (fun s _ => (hΦ₂ u₀ s).hasDerivWithinAt)
    hgbound
    (by simp [h1, h2])
  have hb := key t ht
  rw [zero_add, gronwallBound_zero_left_mul] at hb
  rw [fundamentalSolution_apply, fundamentalSolution_apply, ← dist_eq_norm]
  exact hb

/-- **Interval-restricted operator-norm resolvent-coefficient bound.**  The variant of
`norm_fundamentalSolution_sub_le_of_forall_le` with the coefficient-gap hypothesis required only on
the tube `[t₀, T]` (assembled over unit directions from
`norm_fundamentalSolution_sub_apply_le_of_forall_le_Icc`).  For coefficients `A`, `A'` (both `≤ K`)
with `‖A s - A' s‖ ≤ ε` on `[t₀, T]`,
`‖D_x Φ_t^A - D_x Φ_t^{A'}‖ ≤ ε · exp (K (T - t₀)) · gronwallBound 0 K 1 (t - t₀)` there. -/
theorem norm_fundamentalSolution_sub_le_of_forall_le_Icc
    {A A' : ℝ → (E →L[ℝ] E)} (hA : ∀ s, ‖A s‖₊ ≤ K) (hA' : ∀ s, ‖A' s‖₊ ≤ K)
    {Φ₁ Φ₂ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec A)) (h1 : ∀ x, Φ₁ x t₀ = x)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec A')) (h2 : ∀ x, Φ₂ x t₀ = x)
    {ε : ℝ} {T : ℝ} (hε : 0 ≤ ε) (hAA' : ∀ s ∈ Icc t₀ T, ‖A s - A' s‖ ≤ ε)
    {t : ℝ} (ht : t ∈ Icc t₀ T) :
    ‖fundamentalSolution hA hΦ₁ h1 t - fundamentalSolution hA' hΦ₂ h2 t‖
      ≤ ε * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ (fun u₀ => ?_)
  · exact mul_nonneg (mul_nonneg hε (Real.exp_pos _).le)
      (gronwallBound_zero_one_nonneg K.coe_nonneg (sub_nonneg.mpr ht.1))
  · rw [ContinuousLinearMap.sub_apply]
    refine (norm_fundamentalSolution_sub_apply_le_of_forall_le_Icc
      hA hA' hΦ₁ h1 hΦ₂ h2 hAA' u₀ ht).trans (le_of_eq ?_)
    ring

/-- **Interval-restricted second-order variational estimate.**  The variant of
`norm_fundamentalSolution_sub_sub_variation_le` whose coefficient-gap hypothesis
`‖A₁ s - A₂ s‖ ≤ ε` is required only on the compact tube `[t₀, T]` (the proof evaluates the gap only
there — through `norm_fundamentalSolution_sub_le_of_forall_le_Icc` and directly on `Ico t₀ t`).  This
is the form the base-point `C²` bootstrap consumes: the trajectory-linearised coefficients
`A₁ s = Dv s (Φ z s)`, `A₂ s = Dv s (Φ x₀ s)` are `ε`-close only on `[t₀, T]`.  Given the first
variation `V` (`V' = A₂ ∘ V + (A₁ - A₂) ∘ W₂`, `V t₀ = 0`), the resolvent gap agrees with `V` to
second order there:
`‖(W₁ t - W₂ t) - V t‖ ≤ ε² · exp (K (T - t₀)) · gronwallBound 0 K 1 (T - t₀)²`. -/
theorem norm_fundamentalSolution_sub_sub_variation_le_Icc
    {A₁ A₂ : ℝ → (E →L[ℝ] E)} {K : ℝ≥0} {Φ₁ Φ₂ : E → ℝ → E}
    (hA₁ : ∀ t, ‖A₁ t‖₊ ≤ K) (hA₁cont : Continuous A₁)
    (hA₂ : ∀ t, ‖A₂ t‖₊ ≤ K) (hA₂cont : Continuous A₂)
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec A₁)) (h0₁ : ∀ x, Φ₁ x t₀ = x)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec A₂)) (h0₂ : ∀ x, Φ₂ x t₀ = x)
    {ε : ℝ} {T : ℝ} (hε : 0 ≤ ε) (hAA' : ∀ s ∈ Icc t₀ T, ‖A₁ s - A₂ s‖ ≤ ε)
    {V : ℝ → (E →L[ℝ] E)}
    (hVderiv : ∀ s, HasDerivAt V
      ((A₂ s).comp (V s) + (A₁ s - A₂ s).comp (fundamentalSolution hA₂ hΦ₂ h0₂ s)) s)
    (hV0 : V t₀ = 0)
    {t : ℝ} (ht : t ∈ Icc t₀ T) :
    ‖(fundamentalSolution hA₁ hΦ₁ h0₁ t - fundamentalSolution hA₂ hΦ₂ h0₂ t) - V t‖
      ≤ ε ^ 2 * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀) ^ 2 := by
  have hKr : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
  have ht0T : t₀ ≤ T := le_trans ht.1 ht.2
  have hg0 : 0 ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
    gronwallBound_zero_one_nonneg hKr (sub_nonneg.mpr ht0T)
  set R : ℝ → (E →L[ℝ] E) :=
    fun s => (fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s) - V s
    with hRdef
  have hcR : Continuous R := by
    rw [hRdef]
    exact ((continuous_fundamentalSolution_time hA₁ hΦ₁ h0₁).sub
      (continuous_fundamentalSolution_time hA₂ hΦ₂ h0₂)).sub
      (continuous_iff_continuousAt.mpr (fun s => (hVderiv s).continuousAt))
  have hR0 : R t₀ = 0 := by
    rw [hRdef]
    simp [fundamentalSolution_anchor hA₁ hΦ₁ h0₁, fundamentalSolution_anchor hA₂ hΦ₂ h0₂, hV0]
  set Γ : ℝ := ε ^ 2 * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀)
    with hΓdef
  have hΓ0 : 0 ≤ Γ := by
    rw [hΓdef]; exact mul_nonneg (mul_nonneg (sq_nonneg ε) (Real.exp_pos _).le) hg0
  have hgap : ∀ s ∈ Icc t₀ T,
      ‖fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s‖
        ≤ ε * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀) := by
    intro s hs
    refine (norm_fundamentalSolution_sub_le_of_forall_le_Icc
      hA₁ hA₂ hΦ₁ h0₁ hΦ₂ h0₂ hε hAA' hs).trans ?_
    exact mul_le_mul_of_nonneg_left
      (gronwallBound_mono (le_refl (0 : ℝ)) zero_le_one hKr (by linarith [hs.2]))
      (mul_nonneg hε (Real.exp_pos _).le)
  have hRderiv : ∀ s, HasDerivAt R
      ((A₂ s).comp (R s) + (A₁ s - A₂ s).comp
        (fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s)) s := by
    intro s
    have hgs := (hasDerivAt_fundamentalSolution_sub hA₁ hA₁cont hA₂ hA₂cont hΦ₁ h0₁ hΦ₂ h0₂ s).sub
      (hVderiv s)
    have hval :
        (A₁ s).comp (fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s)
          + (A₁ s - A₂ s).comp (fundamentalSolution hA₂ hΦ₂ h0₂ s)
        - ((A₂ s).comp (V s)
          + (A₁ s - A₂ s).comp (fundamentalSolution hA₂ hΦ₂ h0₂ s))
        = (A₂ s).comp (R s) + (A₁ s - A₂ s).comp
          (fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s) := by
      rw [hRdef]
      simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
      abel
    rwa [hval] at hgs
  have ha : ‖R t₀‖ ≤ 0 := by simp [hR0]
  have hbound : ∀ s ∈ Ico t₀ t,
      ‖(A₂ s).comp (R s) + (A₁ s - A₂ s).comp
        (fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s)‖
        ≤ (K : ℝ) * ‖R s‖ + Γ := by
    intro s hs
    have hsIcc : s ∈ Icc t₀ T := ⟨hs.1, le_trans hs.2.le ht.2⟩
    have hA₂s : ‖A₂ s‖ ≤ (K : ℝ) := by exact_mod_cast hA₂ s
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · calc ‖(A₂ s).comp (R s)‖ ≤ ‖A₂ s‖ * ‖R s‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (K : ℝ) * ‖R s‖ := mul_le_mul_of_nonneg_right hA₂s (norm_nonneg _)
    · calc ‖(A₁ s - A₂ s).comp
              (fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s)‖
            ≤ ‖A₁ s - A₂ s‖
              * ‖fundamentalSolution hA₁ hΦ₁ h0₁ s - fundamentalSolution hA₂ hΦ₂ h0₂ s‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ε * (ε * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀)) :=
            mul_le_mul (hAA' s hsIcc) (hgap s hsIcc) (norm_nonneg _) hε
        _ = Γ := by rw [hΓdef]; ring
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le (a := t₀) (b := t)
    hcR.continuousOn (fun x _ => (hRderiv x).hasDerivWithinAt) ha hbound t ⟨ht.1, le_rfl⟩
  calc ‖(fundamentalSolution hA₁ hΦ₁ h0₁ t - fundamentalSolution hA₂ hΦ₂ h0₂ t) - V t‖
      = ‖R t‖ := by rw [hRdef]
    _ ≤ gronwallBound 0 (K : ℝ) Γ (t - t₀) := hgron
    _ = Γ * gronwallBound 0 (K : ℝ) 1 (t - t₀) := gronwallBound_zero_left_mul _ _ _
    _ ≤ Γ * gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
        mul_le_mul_of_nonneg_left
          (gronwallBound_mono (le_refl (0 : ℝ)) zero_le_one hKr (by linarith [ht.2])) hΓ0
    _ = ε ^ 2 * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀) ^ 2 := by
        rw [hΓdef]; ring

/-- **Second-order Taylor remainder of the resolvent in the base point.**  Fix `x₀` with reference
coefficient `A₀ s = Dv s (Φ x₀ s)`, variational flow family `Φ'` and resolvent
`W₀ s = fundamentalSolution hA hΦ' h0' s = D_x Φ_s`.  For a nearby base point `z` with coefficient
`A_z s = Dv s (Φ z s)`, variational flow family `Φ₁` and resolvent `W_z s = fundamentalSolution hAz
hΦ₁ h0₁ s`, the resolvent gap `W_z t - W₀ t` agrees to *second order* in the increment `z - x₀` with
the *linearised* first variation `Vlin` — the anchored solution of
`Vlin' = A₀ ∘ Vlin + (∂A₀/∂x₀ · (z - x₀)) ∘ W₀` whose forcing is the chain-rule coefficient
derivative `∂A₀/∂x₀ = D²v(Φ x₀ s) ∘ W₀` (`hasFDerivAt_derivField_apply_flow`) applied to `z - x₀`:
`‖(W_z t - W₀ t) - Vlin t‖ ≤ (L² e₁³ g² + Cquad e₁ g) · ‖z - x₀‖²` uniformly on `[t₀, T]`, where
`e₁ = exp (K (T - t₀))`, `g = gronwallBound 0 K 1 (T - t₀)`, `Cquad = M e₂ + C' L e₂ g`
(`e₂ = exp (2 K (T - t₀))`).  Proof: triangle inequality across the *true* first variation `Vz`,
* `‖(W_z t - W₀ t) - Vz t‖ ≤ ε² e₁ g²` (the interval second-order variational estimate
  `norm_fundamentalSolution_sub_sub_variation_le_Icc`, with `ε = L e₁ ‖z - x₀‖` the coefficient gap
  from `norm_derivField_apply_flow_sub_le`), and
* `‖Vz t - Vlin t‖ ≤ Cquad e₁ g ‖z - x₀‖²` (`norm_firstVariation_sub_linearVariation_le_sq`).

Since `Vlin` is *linear* in `z - x₀`, this identifies the Fréchet derivative of `x₀ ↦ D_x Φ_t` in the
base point with an `O(‖z - x₀‖²)` remainder — the spatial `C²` numerator of the base-point bootstrap
(the exact resolvent analogue of the `C¹` numerator `norm_flow_sub_fundamentalSolution_le_sq`). -/
theorem norm_fundamentalSolution_sub_sub_linearVariation_le_sq
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {L M : ℝ≥0} {C' : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ) (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2v : ∀ s ξ, HasFDerivAt (Dv s) (D2v s ξ) ξ) (hD2vlip : ∀ s, LipschitzWith M (D2v s))
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K) (hAcont : Continuous (fun s => Dv s (Φ x₀ s)))
    (hC'0 : 0 ≤ C') (hC' : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ C')
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    (z : E) (hAz : ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K) (hAzcont : Continuous (fun s => Dv s (Φ z s)))
    {Φ₁ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h0₁ : ∀ x, Φ₁ x t₀ = x)
    {T : ℝ}
    {Vz Vlin : ℝ → (E →L[ℝ] E)}
    (hVz : ∀ s, HasDerivAt Vz
      ((Dv s (Φ x₀ s)).comp (Vz s)
        + (Dv s (Φ z s) - Dv s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s)) s)
    (hVz0 : Vz t₀ = 0)
    (hVlin : ∀ s, HasDerivAt Vlin
      ((Dv s (Φ x₀ s)).comp (Vlin s)
        + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) (z - x₀)).comp
            (fundamentalSolution hA hΦ' h0' s)) s)
    (hVlin0 : Vlin t₀ = 0)
    {t : ℝ} (ht : t ∈ Icc t₀ T) :
    ‖(fundamentalSolution hAz hΦ₁ h0₁ t - fundamentalSolution hA hΦ' h0' t) - Vlin t‖
      ≤ ((L : ℝ) ^ 2 * Real.exp ((K : ℝ) * (T - t₀)) ^ 3
            * gronwallBound 0 (K : ℝ) 1 (T - t₀) ^ 2
          + ((M : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
              + C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                  * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
            * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀))
        * ‖z - x₀‖ ^ 2 := by
  -- The coefficient gap `ε = L · exp (K (T - t₀)) · ‖z - x₀‖`, valid on the tube `[t₀, T]`.
  have hε : (0 : ℝ) ≤ (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖ :=
    mul_nonneg (mul_nonneg L.coe_nonneg (Real.exp_pos _).le) (norm_nonneg _)
  have hAA' : ∀ s ∈ Icc t₀ T,
      ‖Dv s (Φ z s) - Dv s (Φ x₀ s)‖
        ≤ (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖ := by
    intro s hs
    have hsabs : |s - t₀| ≤ T - t₀ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
    exact norm_derivField_apply_flow_sub_le hv hΦ h0 (hDvlip s) hsabs z x₀
  -- Piece 1: the true first variation `Vz` predicts the resolvent gap to `O(ε²)`.
  have hp1 := norm_fundamentalSolution_sub_sub_variation_le_Icc
    hAz hAzcont hA hAcont hΦ₁ h0₁ hΦ' h0' hε hAA' hVz hVz0 ht
  -- Piece 2: the linearised first variation `Vlin` agrees with `Vz` to `O(‖z - x₀‖²)`.
  have hp2 := norm_firstVariation_sub_linearVariation_le_sq
    hv hΦ h0 hDv hDvlip hD2v hD2vlip x₀ hA hC'0 hC' hΦ' h0' z hVz hVz0 hVlin hVlin0 ht
  -- Grönwall monotonicity, to replace the `t`-window factor by its endpoint value at `T`.
  have hgt : gronwallBound 0 (K : ℝ) 1 (t - t₀) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
    gronwallBound_mono (le_refl (0 : ℝ)) zero_le_one K.coe_nonneg (by linarith [ht.2])
  have hCq0 : (0 : ℝ) ≤ (M : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
      + C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
          * gronwallBound 0 (K : ℝ) 1 (T - t₀)) := by
    refine add_nonneg (mul_nonneg M.coe_nonneg (Real.exp_pos _).le) ?_
    refine mul_nonneg hC'0 (mul_nonneg (mul_nonneg L.coe_nonneg (Real.exp_pos _).le) ?_)
    exact gronwallBound_zero_one_nonneg K.coe_nonneg (sub_nonneg.mpr (le_trans ht.1 ht.2))
  -- Bound Piece 2's `t`-window factor by the endpoint value.
  have hp2' :
      ((M : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
          + C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
              * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
        * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (t - t₀) * ‖z - x₀‖ ^ 2
      ≤ ((M : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
          + C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
              * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
        * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀) * ‖z - x₀‖ ^ 2 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgt (mul_nonneg hCq0 (Real.exp_pos _).le)) (sq_nonneg _)
  -- Reshape both pieces to their clean `· * ‖z - x₀‖²` forms.
  have hp1' :
      ‖(fundamentalSolution hAz hΦ₁ h0₁ t - fundamentalSolution hA hΦ' h0' t) - Vz t‖
        ≤ (L : ℝ) ^ 2 * Real.exp ((K : ℝ) * (T - t₀)) ^ 3
            * gronwallBound 0 (K : ℝ) 1 (T - t₀) ^ 2 * ‖z - x₀‖ ^ 2 := by
    refine hp1.trans (le_of_eq ?_); ring
  have hp2'' :
      ‖Vz t - Vlin t‖
        ≤ ((M : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
            + C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
          * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀) * ‖z - x₀‖ ^ 2 :=
    hp2.trans hp2'
  -- Triangle inequality across `Vz`, then combine the two second-order bounds.
  have htri : (fundamentalSolution hAz hΦ₁ h0₁ t - fundamentalSolution hA hΦ' h0' t) - Vlin t
      = ((fundamentalSolution hAz hΦ₁ h0₁ t - fundamentalSolution hA hΦ' h0' t) - Vz t)
        + (Vz t - Vlin t) := by abel
  rw [htri]
  refine (norm_add_le _ _).trans ((add_le_add hp1' hp2'').trans_eq ?_)
  ring

/-- **Additivity of the linearised first variation in the direction.**  The linearised first
variation `Vlin^h` (the anchored solution of `V' = A₀ ∘ V + (∂A₀/∂x₀ · h) ∘ W₀`, `V t₀ = 0`, with the
chain-rule forcing `∂A₀/∂x₀ · h = (D²v(Φ x₀ s) ∘ W₀) h` for the base direction `h`) is *additive* in
`h`: `Vlin^{h₁ + h₂} t = Vlin^{h₁} t + Vlin^{h₂} t`.  This is the additive half of packaging the
candidate spatial `C²` derivative `h ↦ Vlin^h t` as a bounded linear map.  Proof: the forcing
`(D²v(Φ x₀ s) ∘ W₀)` is a *bounded linear map* of `h`, so its value at `h₁ + h₂` splits (`map_add`);
the first-variation additivity `firstVariation_perturbation_add_eq` then pins `Vlin^{h₁+h₂}` to the
sum. -/
theorem linearVariation_perturbation_add_eq
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    (h₁ h₂ : E) {V₁ V₂ V₁₂ : ℝ → (E →L[ℝ] E)}
    (hV₁ : ∀ s, HasDerivAt V₁ ((Dv s (Φ x₀ s)).comp (V₁ s)
      + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h₁).comp
          (fundamentalSolution hA hΦ' h0' s)) s)
    (hV₂ : ∀ s, HasDerivAt V₂ ((Dv s (Φ x₀ s)).comp (V₂ s)
      + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h₂).comp
          (fundamentalSolution hA hΦ' h0' s)) s)
    (hV₁₂ : ∀ s, HasDerivAt V₁₂ ((Dv s (Φ x₀ s)).comp (V₁₂ s)
      + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) (h₁ + h₂)).comp
          (fundamentalSolution hA hΦ' h0' s)) s)
    (hV₁0 : V₁ t₀ = 0) (hV₂0 : V₂ t₀ = 0) (hV₁₂0 : V₁₂ t₀ = 0)
    (t : ℝ) : V₁₂ t = V₁ t + V₂ t := by
  have hV₁₂' : ∀ s, HasDerivAt V₁₂ ((Dv s (Φ x₀ s)).comp (V₁₂ s)
      + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h₁)
          + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h₂)).comp
          (fundamentalSolution hA hΦ' h0' s)) s := by
    intro s
    have hmap : (D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) (h₁ + h₂)
        = (D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h₁
          + (D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h₂ :=
      map_add _ h₁ h₂
    have := hV₁₂ s
    rwa [hmap] at this
  exact firstVariation_perturbation_add_eq hA hV₁ hV₂ hV₁₂' hV₁0 hV₂0 hV₁₂0 t

/-- **Homogeneity of the linearised first variation in the direction.**  The linearised first
variation `Vlin^h` is *homogeneous* in `h`: `Vlin^{c • h} t = c • Vlin^h t`.  This is the homogeneous
half of packaging the candidate spatial `C²` derivative `h ↦ Vlin^h t` as a bounded linear map.
Proof: the chain-rule forcing `(D²v(Φ x₀ s) ∘ W₀)` is linear, so its value at `c • h` scales
(`map_smul`); the first-variation homogeneity `firstVariation_perturbation_smul_eq` closes it. -/
theorem linearVariation_perturbation_smul_eq
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    (c : ℝ) (h : E) {V Vc : ℝ → (E →L[ℝ] E)}
    (hV : ∀ s, HasDerivAt V ((Dv s (Φ x₀ s)).comp (V s)
      + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp
          (fundamentalSolution hA hΦ' h0' s)) s)
    (hVc : ∀ s, HasDerivAt Vc ((Dv s (Φ x₀ s)).comp (Vc s)
      + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) (c • h)).comp
          (fundamentalSolution hA hΦ' h0' s)) s)
    (hV0 : V t₀ = 0) (hVc0 : Vc t₀ = 0)
    (t : ℝ) : Vc t = c • V t := by
  have hVc' : ∀ s, HasDerivAt Vc ((Dv s (Φ x₀ s)).comp (Vc s)
      + (c • ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h)).comp
          (fundamentalSolution hA hΦ' h0' s)) s := by
    intro s
    have hmap : (D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) (c • h)
        = c • ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h) :=
      map_smul _ c h
    have := hVc s
    rwa [hmap] at this
  exact firstVariation_perturbation_smul_eq c hA hV hVc' hV0 hVc0 t

/-!
### Existence of the first variation for a *time-unbounded* (locally bounded) forcing

The base-point `C²` bootstrap needs the true / linearised first variations `Vz`, `Vlin` whose
forcings — `(A_z − A₀) ∘ W₀`, `(D²v(Φ x₀ s) ∘ W₀ · h) ∘ W₀` — are only *continuous*, growing like
`exp (K |s − t₀|)` in `s` and hence never globally norm-bounded.  The globally-bounded existence
`exists_hasDerivAt_inhomogVariation` (whose homogenised `augmentedVariationalField` folds `F` into the
state via a scalar coordinate, forcing `‖F s‖ ≤ M`) therefore does not apply.

The key observation is that the **direct** inhomogeneous variation field
`inhomogVariationalField A F s W = (A s) ∘ W + F s` is *uniformly* `K`-Lipschitz *in the state* `W`
whenever `A` is globally `K`-bounded — the forcing `F s` cancels in the state-difference
`g s W₁ − g s W₂ = (A s) ∘ (W₁ − W₂)`, so its (possibly unbounded) size never enters the Lipschitz
constant.  Global existence of `V` with `V t₀ = 0`, `V' = A ∘ V + F` therefore follows *directly*
from the uniform-Lipschitz global existence `exists_isIntegralCurve_of_lipschitzWith` — no augmented
scalar coordinate, no truncation, no global bound on `F`. -/

/-- The **direct inhomogeneous variation field** `W ↦ (A t) ∘ W + F t` on `E →L[ℝ] E`, whose integral
curves solve the inhomogeneous variational ODE `V' = A ∘ V + F`.  (Compare `variationalField`, the
homogeneous `F = 0` case.) -/
def inhomogVariationalField (A F : ℝ → (E →L[ℝ] E)) :
    ℝ → (E →L[ℝ] E) → (E →L[ℝ] E) :=
  fun t W => (A t).comp W + F t

/-- **The direct inhomogeneous variation field is `K`-Lipschitz in the state**, with `K` the operator
bound of `A` alone — *independently of the size of the forcing* `F`.  The forcing is a state-constant
translation, so it cancels in the state-difference `(A t) ∘ W₁ + F t − ((A t) ∘ W₂ + F t) =
(A t) ∘ (W₁ − W₂)`; submultiplicativity then gives `≤ ‖A t‖ ‖W₁ − W₂‖ ≤ K ‖W₁ − W₂‖`.  This is what
lets a *time-unbounded* (but continuous) forcing still feed the uniform-Lipschitz global existence. -/
theorem lipschitzWith_inhomogVariationalField {A F : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ t, ‖A t‖₊ ≤ K) (t : ℝ) :
    LipschitzWith K (inhomogVariationalField A F t) := by
  refine LipschitzWith.of_dist_le_mul fun W₁ W₂ => ?_
  simp only [inhomogVariationalField, dist_eq_norm]
  have hsub : (A t).comp W₁ + F t - ((A t).comp W₂ + F t) = (A t).comp (W₁ - W₂) := by
    rw [ContinuousLinearMap.comp_sub]; abel
  rw [hsub]
  calc ‖(A t).comp (W₁ - W₂)‖
      ≤ ‖A t‖ * ‖W₁ - W₂‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (K : ℝ) * ‖W₁ - W₂‖ := by
        gcongr
        exact_mod_cast hA t

/-- **Existence of the first variation for a merely-continuous (time-unbounded) forcing.**  For a
norm-bounded (`‖A s‖₊ ≤ K`), continuous operator path `A` and *any* continuous forcing
`F : ℝ → (E →L[ℝ] E)` — **no global bound on `F` required** — the anchored inhomogeneous variational
ODE `V' = A ∘ V + F`, `V t₀ = 0` has a global solution `V`.

Proof: the direct field `inhomogVariationalField A F` is uniformly `K`-Lipschitz in the state
(`lipschitzWith_inhomogVariationalField`, the forcing cancels) and continuous in time
(`s ↦ (A s) ∘ W + F s` via `Continuous.clm_comp` + `Continuous.add`), so — the operator space
`E →L[ℝ] E` being complete (`E` complete) — the uniform-Lipschitz global existence
`exists_isIntegralCurve_of_lipschitzWith` supplies an integral curve `V` through `(t₀, 0)`, i.e.
`∀ s, HasDerivAt V ((A s) ∘ V s + F s) s`.  This is the piece the globally-bounded
`exists_hasDerivAt_inhomogVariation` could not supply — the existence half of the *time-unbounded*
first variations `Vz`, `Vlin` that the base-point `C²` bootstrap consumes. -/
theorem exists_hasDerivAt_inhomogVariation_of_continuous [CompleteSpace E]
    {A F : ℝ → (E →L[ℝ] E)} {K : ℝ≥0}
    (hA : ∀ s, ‖A s‖₊ ≤ K) (hAc : Continuous A) (hFc : Continuous F) (t₀ : ℝ) :
    ∃ V : ℝ → (E →L[ℝ] E), V t₀ = 0 ∧
      ∀ s, HasDerivAt V ((A s).comp (V s) + F s) s := by
  have hlip : ∀ s, LipschitzWith K (inhomogVariationalField A F s) :=
    fun s => lipschitzWith_inhomogVariationalField hA s
  have hcont : ∀ W : E →L[ℝ] E, Continuous fun s => inhomogVariationalField A F s W := by
    intro W
    show Continuous fun s => (A s).comp W + F s
    exact (hAc.clm_comp continuous_const).add hFc
  obtain ⟨V, hV0, hVcurve⟩ :=
    exists_isIntegralCurve_of_lipschitzWith hlip hcont t₀ (0 : E →L[ℝ] E)
  refine ⟨V, hV0, fun s => ?_⟩
  simpa only [inhomogVariationalField] using hVcurve s

/-- **Existence of the true first variation `Vz`.**  For the base-point `C²` bootstrap: given the
reference base point `x₀`, its trajectory-linearised coefficient `A₀ s = Dv s (Φ x₀ s)`
(`K`-bounded, continuous), the associated resolvent `W₀ = fundamentalSolution hA hΦ' h0'`, and a
second point `z` whose coefficient `A_z s = Dv s (Φ z s)` is continuous, the anchored *true first
variation* ODE `Vz' = A₀ ∘ Vz + (A_z − A₀) ∘ W₀`, `Vz t₀ = 0` has a global solution.

The forcing `(A_z − A₀) ∘ W₀` grows like `exp (K |s − t₀|)` and is *never* globally bounded, so the
globally-bounded `exists_hasDerivAt_inhomogVariation` does not apply; the merely-continuous existence
`exists_hasDerivAt_inhomogVariation_of_continuous` closes it (`A₀` is `K`-bounded and continuous, the
forcing is continuous by `Continuous.clm_comp` of `A_z − A₀` with `continuous_fundamentalSolution_time`).
Produces exactly the `hVz`/`hVz0` datum consumed by
`norm_fundamentalSolution_sub_sub_linearVariation_le_sq`. -/
theorem exists_hasDerivAt_firstVariation_true [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {K : ℝ≥0}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hAcont : Continuous (fun s => Dv s (Φ x₀ s)))
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    (z : E) (hAzcont : Continuous (fun s => Dv s (Φ z s))) :
    ∃ Vz : ℝ → (E →L[ℝ] E), Vz t₀ = 0 ∧
      ∀ s, HasDerivAt Vz
        ((Dv s (Φ x₀ s)).comp (Vz s)
          + (Dv s (Φ z s) - Dv s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s)) s := by
  have hFc : Continuous fun s =>
      (Dv s (Φ z s) - Dv s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) :=
    (hAzcont.sub hAcont).clm_comp (continuous_fundamentalSolution_time hA hΦ' h0')
  exact exists_hasDerivAt_inhomogVariation_of_continuous hA hAcont hFc t₀

/-- **Existence of the linearised first variation `Vlin`.**  The companion of
`exists_hasDerivAt_firstVariation_true` for the *linearised* (chain-rule) forcing: given the base
point `x₀`, its coefficient `A₀ s = Dv s (Φ x₀ s)` (`K`-bounded, continuous) with second derivative
`D2v` whose along-trajectory value `s ↦ D²v s (Φ x₀ s)` is continuous, the resolvent
`W₀ = fundamentalSolution hA hΦ' h0'`, and a direction increment `z − x₀`, the anchored *linearised
first variation* ODE `Vlin' = A₀ ∘ Vlin + (D²v(Φ x₀ s) ∘ W₀ · (z − x₀)) ∘ W₀`, `Vlin t₀ = 0` has a
global solution.

The chain-rule forcing `(D²v(Φ x₀ s) ∘ W₀ · (z − x₀)) ∘ W₀` again grows like `exp (2K |s − t₀|)` and
is never globally bounded, so `exists_hasDerivAt_inhomogVariation_of_continuous` is what closes it
(continuity by `Continuous.clm_comp`/`Continuous.clm_apply` of `D²v(Φ x₀ ·)` with the continuous
resolvent).  Produces exactly the `hVlin`/`hVlin0` datum consumed by
`norm_fundamentalSolution_sub_sub_linearVariation_le_sq` — completing the existence half of piece (i).
-/
theorem exists_hasDerivAt_firstVariation_linearised [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))} {K : ℝ≥0}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hAcont : Continuous (fun s => Dv s (Φ x₀ s)))
    (hD2cont : Continuous (fun s => D2v s (Φ x₀ s)))
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    (z : E) :
    ∃ Vlin : ℝ → (E →L[ℝ] E), Vlin t₀ = 0 ∧
      ∀ s, HasDerivAt Vlin
        ((Dv s (Φ x₀ s)).comp (Vlin s)
          + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) (z - x₀)).comp
              (fundamentalSolution hA hΦ' h0' s)) s := by
  have hW : Continuous (fun s => fundamentalSolution hA hΦ' h0' s) :=
    continuous_fundamentalSolution_time hA hΦ' h0'
  have hFc : Continuous fun s =>
      ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) (z - x₀)).comp
        (fundamentalSolution hA hΦ' h0' s) :=
    ((hD2cont.clm_comp hW).clm_apply continuous_const).clm_comp hW
  exact exists_hasDerivAt_inhomogVariation_of_continuous hA hAcont hFc t₀

/-- **Operator-norm bound for the linearised first variation, linear in the direction.**  The
boundedness datum for packaging `h ↦ Vlin^h t` as a bounded linear map.  If `Vlin` solves the
linearised (chain-rule) first-variation ODE for direction `h`,
`Vlin' = A₀ ∘ Vlin + (D²v(Φ x₀ s) ∘ W₀ · h) ∘ W₀`, `Vlin t₀ = 0` (`A₀ s = Dv s (Φ x₀ s)`,
`W₀ = fundamentalSolution hA hΦ' h0'`), then on `[t₀, T]`
`‖Vlin t‖ ≤ C' · exp (2K(T − t₀)) · ‖h‖ · gronwallBound 0 K 1 (t − t₀)`, with the constant
*independent of `h`* — so the map `h ↦ Vlin^h t` is bounded with operator norm
`≤ C' · exp (2K(T − t₀)) · gronwallBound 0 K 1 (t − t₀)`.

Proof: the forcing `((D²v(Φ x₀ s) ∘ W₀) h) ∘ W₀` is bounded by
`‖D²v(Φ x₀ s)‖ · ‖W₀ s‖ · ‖h‖ · ‖W₀ s‖ ≤ C' · exp(2K(T − t₀)) · ‖h‖` on `[t₀, T]` (operator
submultiplicativity `opNorm_comp_le`/`le_opNorm`, the resolvent bound `norm_fundamentalSolution_le`,
and the `D²v` bound), and the general a-priori estimate `norm_inhomogVariation_le` closes it. -/
theorem norm_linearisedFirstVariation_le
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))} {K : ℝ≥0}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    {C' : ℝ} (hC'0 : 0 ≤ C') (hC' : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ C')
    (h : E) {Vlin : ℝ → (E →L[ℝ] E)}
    (hVlin : ∀ s, HasDerivAt Vlin
      ((Dv s (Φ x₀ s)).comp (Vlin s)
        + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp
            (fundamentalSolution hA hΦ' h0' s)) s)
    (hVlin0 : Vlin t₀ = 0)
    {T : ℝ} {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ‖Vlin t‖
      ≤ C' * Real.exp (2 * (K : ℝ) * (T - t₀)) * ‖h‖
          * gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
  have hexp2 : Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
      = Real.exp (2 * (K : ℝ) * (T - t₀)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hFbound : ∀ s ∈ Set.Icc t₀ T,
      ‖((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp
          (fundamentalSolution hA hΦ' h0' s)‖
        ≤ C' * Real.exp (2 * (K : ℝ) * (T - t₀)) * ‖h‖ := by
    intro s hs
    have hsabs : |s - t₀| ≤ T - t₀ := by
      rw [abs_of_nonneg (by linarith [hs.1] : (0 : ℝ) ≤ s - t₀)]; linarith [hs.2]
    have hWle : ‖fundamentalSolution hA hΦ' h0' s‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) :=
      (norm_fundamentalSolution_le hA hΦ' h0' s).trans
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsabs K.coe_nonneg))
    calc ‖((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp
            (fundamentalSolution hA hΦ' h0' s)‖
        ≤ ‖(D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h‖
            * ‖fundamentalSolution hA hΦ' h0' s‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖(D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s)‖ * ‖h‖
            * ‖fundamentalSolution hA hΦ' h0' s‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ ‖D2v s (Φ x₀ s)‖ * ‖fundamentalSolution hA hΦ' h0' s‖ * ‖h‖
            * ‖fundamentalSolution hA hΦ' h0' s‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
            (norm_nonneg _)
      _ ≤ C' * Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖ * Real.exp ((K : ℝ) * (T - t₀)) := by
          gcongr
          exact hC' s
      _ = C' * Real.exp (2 * (K : ℝ) * (T - t₀)) * ‖h‖ := by rw [← hexp2]; ring
  exact norm_inhomogVariation_le hA hVlin hVlin0 hFbound ht

/-- **Existence of the linearised first variation, keyed on the direction `h`.**  The
direction-parameterised form of `exists_hasDerivAt_firstVariation_linearised` (with the increment a
free vector `h` rather than `z − x₀`), so the solution family `h ↦ Vlin^h` can be assembled into a
map of `h`.  Same proof: `exists_hasDerivAt_inhomogVariation_of_continuous` on the (continuous,
time-unbounded) chain-rule forcing `((D²v(Φ x₀ s) ∘ W₀) h) ∘ W₀`. -/
theorem exists_hasDerivAt_firstVariation_linearised_dir [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))} {K : ℝ≥0}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hAcont : Continuous (fun s => Dv s (Φ x₀ s)))
    (hD2cont : Continuous (fun s => D2v s (Φ x₀ s)))
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    (h : E) :
    ∃ Vlin : ℝ → (E →L[ℝ] E), Vlin t₀ = 0 ∧
      ∀ s, HasDerivAt Vlin
        ((Dv s (Φ x₀ s)).comp (Vlin s)
          + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp
              (fundamentalSolution hA hΦ' h0' s)) s := by
  have hW : Continuous (fun s => fundamentalSolution hA hΦ' h0' s) :=
    continuous_fundamentalSolution_time hA hΦ' h0'
  have hFc : Continuous fun s =>
      ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp
        (fundamentalSolution hA hΦ' h0' s) :=
    ((hD2cont.clm_comp hW).clm_apply continuous_const).clm_comp hW
  exact exists_hasDerivAt_inhomogVariation_of_continuous hA hAcont hFc t₀

/-- **The candidate spatial `C²` derivative as a bounded operator** `D₂ = ∂/∂x₀ (D_x Φ_t)`.  Packaging
piece (ii) of the base-point `C²` bootstrap: there is a *bounded linear map*
`D₂ : E →L[ℝ] (E →L[ℝ] E)` whose value on a direction `h` equals the time-`t` value of **any**
solution `Vlin` of the linearised first-variation ODE for direction `h`
(`Vlin' = A₀ ∘ Vlin + (D²v(Φ x₀ s) ∘ W₀ · h) ∘ W₀`, `Vlin t₀ = 0`, `A₀ s = Dv s (Φ x₀ s)`,
`W₀ = fundamentalSolution hA hΦ' h0'`).

The map is `h ↦ Vlin^h t` for the canonical solution `Vlin^h` (chosen from
`exists_hasDerivAt_firstVariation_linearised_dir`); it is additive and homogeneous
(`linearVariation_perturbation_add_eq`/`_smul_eq`) and bounded with operator norm
`≤ C' · exp (2K(T − t₀)) · gronwallBound 0 K 1 (t − t₀)` (`norm_linearisedFirstVariation_le`), so
`LinearMap.mkContinuous` yields the bounded operator; the value is independent of the chosen solution
by the linear-ODE uniqueness `inhomogVariation_unique`.  This is the operator `D₂` that, fed with the
second-order Taylor remainder `norm_fundamentalSolution_sub_sub_linearVariation_le_sq`, will give
`HasFDerivAt (fun z => D_x Φ_t^{A(z)}) D₂ x₀` — the spatial `C²` regularity (piece (iii)). -/
theorem exists_continuousLinearMap_linearisedVariation [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))} {K : ℝ≥0}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hAcont : Continuous (fun s => Dv s (Φ x₀ s)))
    (hD2cont : Continuous (fun s => D2v s (Φ x₀ s)))
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    {C' : ℝ} (hC'0 : 0 ≤ C') (hC' : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ C')
    {T : ℝ} {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ∃ D₂ : E →L[ℝ] (E →L[ℝ] E),
      ∀ (h : E) (Vlin : ℝ → (E →L[ℝ] E)), Vlin t₀ = 0 →
        (∀ s, HasDerivAt Vlin
          ((Dv s (Φ x₀ s)).comp (Vlin s)
            + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp
                (fundamentalSolution hA hΦ' h0' s)) s) →
        D₂ h = Vlin t := by
  choose Vsol hVsol0 hVsolderiv using fun h =>
    exists_hasDerivAt_firstVariation_linearised_dir x₀ hA hAcont hD2cont hΦ' h0' h
  have hadd : ∀ h₁ h₂ : E, Vsol (h₁ + h₂) t = Vsol h₁ t + Vsol h₂ t := fun h₁ h₂ =>
    linearVariation_perturbation_add_eq x₀ hA hΦ' h0' h₁ h₂
      (hVsolderiv h₁) (hVsolderiv h₂) (hVsolderiv (h₁ + h₂))
      (hVsol0 h₁) (hVsol0 h₂) (hVsol0 (h₁ + h₂)) t
  have hsmul : ∀ (c : ℝ) (h : E), Vsol (c • h) t = c • Vsol h t := fun c h =>
    linearVariation_perturbation_smul_eq x₀ hA hΦ' h0' c h
      (hVsolderiv h) (hVsolderiv (c • h)) (hVsol0 h) (hVsol0 (c • h)) t
  have hbound : ∀ h : E,
      ‖Vsol h t‖
        ≤ C' * Real.exp (2 * (K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (t - t₀) * ‖h‖ :=
    fun h => by
      have hle := norm_linearisedFirstVariation_le x₀ hA hΦ' h0' hC'0 hC' h
        (hVsolderiv h) (hVsol0 h) ht
      calc ‖Vsol h t‖
          ≤ C' * Real.exp (2 * (K : ℝ) * (T - t₀)) * ‖h‖
              * gronwallBound 0 (K : ℝ) 1 (t - t₀) := hle
        _ = C' * Real.exp (2 * (K : ℝ) * (T - t₀))
              * gronwallBound 0 (K : ℝ) 1 (t - t₀) * ‖h‖ := by ring
  refine ⟨LinearMap.mkContinuous
    { toFun := fun h => Vsol h t
      map_add' := hadd
      map_smul' := fun c h => by simpa using hsmul c h }
    (C' * Real.exp (2 * (K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (t - t₀)) hbound, ?_⟩
  intro h Vlin hVlin0 hVlinderiv
  have huniq : Vsol h t = Vlin t :=
    inhomogVariation_unique hA (hVsolderiv h) hVlinderiv (by rw [hVsol0 h, hVlin0]) t
  simpa using huniq

open Asymptotics Filter in
/-- **`HasFDerivAt` from a quadratic (`O(‖z − x₀‖²)`) linearisation error.**  If the linearisation
error `f z − f x₀ − f'(z − x₀)` is bounded by `C · ‖z − x₀‖²` for `z` near `x₀`, then `f` is Fréchet
differentiable at `x₀` with derivative `f'`.  (The quadratic error is `o(‖z − x₀‖)` since the scalar
modulus `C · ‖z − x₀‖ → 0`.)  The reusable analytic bridge from a *second-order Taylor remainder* to
differentiability: the exact shape produced by
`norm_fundamentalSolution_sub_sub_linearVariation_le_sq` (with `f' = D₂` the packaged operator of
`exists_continuousLinearMap_linearisedVariation`), feeding the spatial `C²` regularity assembly
(remaining piece (iii)). -/
theorem hasFDerivAt_of_eventually_norm_sub_sub_le_sq
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F → G} {f' : F →L[ℝ] G} {x₀ : F} {C : ℝ}
    (h : ∀ᶠ z in 𝓝 x₀, ‖f z - f x₀ - f' (z - x₀)‖ ≤ C * ‖z - x₀‖ ^ 2) :
    HasFDerivAt f f' x₀ := by
  refine HasFDerivAt.of_isLittleO ?_
  refine isLittleO_of_norm_le_mul_of_tendsto_nhds_zero (g := fun z => C * ‖z - x₀‖) ?_ ?_
  · filter_upwards [h] with z hz
    refine hz.trans_eq ?_
    show C * ‖z - x₀‖ ^ 2 = C * ‖z - x₀‖ * ‖z - x₀‖
    ring
  · have hcont : Continuous (fun z : F => ‖z - x₀‖) :=
      (continuous_id.sub continuous_const).norm
    have hnorm : Tendsto (fun z : F => ‖z - x₀‖) (𝓝 x₀) (𝓝 0) := by
      simpa using hcont.tendsto x₀
    simpa using hnorm.const_mul C

/-- **Differentiability from a quadratic linearisation error** (the `DifferentiableAt` corollary of
`hasFDerivAt_of_eventually_norm_sub_sub_le_sq`). -/
theorem differentiableAt_of_eventually_norm_sub_sub_le_sq
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F → G} {f' : F →L[ℝ] G} {x₀ : F} {C : ℝ}
    (h : ∀ᶠ z in 𝓝 x₀, ‖f z - f x₀ - f' (z - x₀)‖ ≤ C * ‖z - x₀‖ ^ 2) :
    DifferentiableAt ℝ f x₀ :=
  (hasFDerivAt_of_eventually_norm_sub_sub_le_sq h).differentiableAt

/-- **The Fréchet derivative is `f'`** (the `fderiv` corollary of
`hasFDerivAt_of_eventually_norm_sub_sub_le_sq`): a quadratic linearisation error identifies the
derivative. -/
theorem fderiv_of_eventually_norm_sub_sub_le_sq
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F → G} {f' : F →L[ℝ] G} {x₀ : F} {C : ℝ}
    (h : ∀ᶠ z in 𝓝 x₀, ‖f z - f x₀ - f' (z - x₀)‖ ≤ C * ‖z - x₀‖ ^ 2) :
    fderiv ℝ f x₀ = f' :=
  (hasFDerivAt_of_eventually_norm_sub_sub_le_sq h).fderiv

/-- **Spatial `C²` regularity of the flow's resolvent** (base-point `C²` bootstrap, piece (iii) —
assembly).  For a `C^{2,1}` field `v` (uniformly `K`-Lipschitz, everywhere Fréchet differentiable with
`L`-Lipschitz spatial derivative `Dv` and `M`-Lipschitz second derivative `D2v`) with a flow family
`Φ` (`Φ z t₀ = z`), the resolvent map `z ↦ D_x Φ_t^{A(z)} = fundamentalSolution … t` — the time-`t`
fundamental solution of the *linearised* ODE with coefficient `A(z) s = Dv s (Φ z s)`, packaged over a
uniform variational flow family `Ψ` — is Fréchet differentiable at the base point `x₀`, with derivative
the packaged linearised-first-variation operator `D₂ = ∂/∂x₀(D_x Φ_t)`.

This is the assembly of the base-point `C²` bootstrap:
* `exists_continuousLinearMap_linearisedVariation` packages the candidate derivative `D₂` and pins
  `D₂ (z − x₀) = Vlin^{z−x₀} t` (the time-`t` value of the linearised first variation);
* `exists_hasDerivAt_firstVariation_true` / `..._linearised` supply the variations `Vz`, `Vlin` for
  each `z` (their forcings are time-unbounded, so continuity — not a global bound — is what closes
  existence);
* `norm_fundamentalSolution_sub_sub_linearVariation_le_sq` bounds the linearisation error
  `‖(W_z t − W₀ t) − Vlin t‖ ≤ C · ‖z − x₀‖²` with `C` *uniform in `z`* (the second-order Taylor
  remainder of the resolvent in the base point);
* substituting `Vlin t = D₂ (z − x₀)` turns this into the quadratic error `∀ z`, and
  `hasFDerivAt_of_eventually_norm_sub_sub_le_sq` upgrades the `O(‖z − x₀‖²)` error to `HasFDerivAt`.

The spatial `C²` layer of the smooth-dependence tower unblocking Items 1 & 2; everything is proved
from field-level data, no PDE or manifold content. -/
theorem exists_hasFDerivAt_fundamentalSolution_baseCurve [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {L M : ℝ≥0} {C' : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ) (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2v : ∀ s ξ, HasFDerivAt (Dv s) (D2v s ξ) ξ) (hD2vlip : ∀ s, LipschitzWith M (D2v s))
    (x₀ : E)
    (hAfun : ∀ z, ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K)
    (hAcontfun : ∀ z, Continuous (fun s => Dv s (Φ z s)))
    (hD2cont : Continuous (fun s => D2v s (Φ x₀ s)))
    (hC'0 : 0 ≤ C') (hC' : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ C')
    {Ψ : E → E → ℝ → E}
    (hΨ : ∀ z, ∀ x, IsIntegralCurve (Ψ z x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h0Ψ : ∀ z, ∀ x, Ψ z x t₀ = x)
    {T : ℝ} {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ∃ D₂ : E →L[ℝ] (E →L[ℝ] E),
      HasFDerivAt (fun z => fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) t) D₂ x₀ := by
  -- The packaged candidate spatial `C²` derivative `D₂ = ∂/∂x₀(D_x Φ_t)`, with the
  -- characterisation `D₂ h = Vlin^h t` for any linearised first variation of direction `h`.
  obtain ⟨D₂, hD₂⟩ := exists_continuousLinearMap_linearisedVariation
    x₀ (hAfun x₀) (hAcontfun x₀) hD2cont (hΨ x₀) (h0Ψ x₀) hC'0 hC' ht
  refine ⟨D₂, ?_⟩
  refine hasFDerivAt_of_eventually_norm_sub_sub_le_sq (C :=
    (L : ℝ) ^ 2 * Real.exp ((K : ℝ) * (T - t₀)) ^ 3
        * gronwallBound 0 (K : ℝ) 1 (T - t₀) ^ 2
      + ((M : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
          + C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
              * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
        * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀)) ?_
  refine Filter.Eventually.of_forall (fun z => ?_)
  -- Existence of the true / linearised first variations for the increment `z − x₀`.
  obtain ⟨Vz, hVz0, hVz⟩ := exists_hasDerivAt_firstVariation_true
    x₀ (hAfun x₀) (hAcontfun x₀) (hΨ x₀) (h0Ψ x₀) z (hAcontfun z)
  obtain ⟨Vlin, hVlin0, hVlin⟩ := exists_hasDerivAt_firstVariation_linearised
    x₀ (hAfun x₀) (hAcontfun x₀) hD2cont (hΨ x₀) (h0Ψ x₀) z
  -- The second-order Taylor remainder of the resolvent, with a constant uniform in `z`.
  have hrem := norm_fundamentalSolution_sub_sub_linearVariation_le_sq
    hv hΦ h0 hDv hDvlip hD2v hD2vlip x₀ (hAfun x₀) (hAcontfun x₀) hC'0 hC'
    (hΨ x₀) (h0Ψ x₀) z (hAfun z) (hAcontfun z) (hΨ z) (h0Ψ z) hVz hVz0 hVlin hVlin0 ht
  -- The packaged operator agrees with the linearised first variation: `D₂ (z − x₀) = Vlin t`.
  have hval : D₂ (z - x₀) = Vlin t := hD₂ (z - x₀) Vlin hVlin0 hVlin
  -- Rewrite the linearisation error into the Taylor-remainder shape and conclude.
  rw [hval]
  exact hrem

/-- **Spatial `C²` regularity of the resolvent — the `DifferentiableAt` corollary.**  The resolvent
map `z ↦ D_x Φ_t^{A(z)} = fundamentalSolution … t` is Fréchet differentiable at the base point `x₀`.
Immediate from `exists_hasFDerivAt_fundamentalSolution_baseCurve` via `HasFDerivAt.differentiableAt`. -/
theorem differentiableAt_fundamentalSolution_baseCurve [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {L M : ℝ≥0} {C' : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ) (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2v : ∀ s ξ, HasFDerivAt (Dv s) (D2v s ξ) ξ) (hD2vlip : ∀ s, LipschitzWith M (D2v s))
    (x₀ : E)
    (hAfun : ∀ z, ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K)
    (hAcontfun : ∀ z, Continuous (fun s => Dv s (Φ z s)))
    (hD2cont : Continuous (fun s => D2v s (Φ x₀ s)))
    (hC'0 : 0 ≤ C') (hC' : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ C')
    {Ψ : E → E → ℝ → E}
    (hΨ : ∀ z, ∀ x, IsIntegralCurve (Ψ z x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h0Ψ : ∀ z, ∀ x, Ψ z x t₀ = x)
    {T : ℝ} {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    DifferentiableAt ℝ (fun z => fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) t) x₀ := by
  obtain ⟨D₂, hD₂⟩ := exists_hasFDerivAt_fundamentalSolution_baseCurve
    hv hΦ h0 hDv hDvlip hD2v hD2vlip x₀ hAfun hAcontfun hD2cont hC'0 hC' hΨ h0Ψ ht
  exact hD₂.differentiableAt

/-- **The flow map has a second spatial derivative at the base point (`C²` in initial data,
`C^{2,1}` field).**  Field-level, self-contained assembly of the base-point `C²` bootstrap: from a
uniformly `K`-Lipschitz, time-continuous field `v` whose spatial derivative `Dv` exists everywhere, is
jointly continuous and `L`-Lipschitz in space, and whose *second* spatial derivative `D2v` exists
everywhere, is jointly continuous and `M`-Lipschitz, there is a flow family `Φ` of `v` (anchored) such
that the **resolvent map** `z ↦ D_x Φ_t = fderiv ℝ (fun w => Φ w t) z` — the first spatial derivative
of the flow — is *itself* Fréchet differentiable at every base point `x₀`, i.e. the flow map
`z ↦ Φ z t` is twice Fréchet differentiable at `x₀`.

Proof: `exists_flow_family` builds `Φ`; the coefficient `A(z) s = Dv s (Φ z s)` is norm-`≤ K`
(`HasFDerivAt.le_of_lipschitz`) and continuous along each (continuous) trajectory, so
`exists_variationalFlowFamily` supplies the per-`z` variational families `Ψ z`.  The `C¹` bootstrap
`hasFDerivAt_flow_of_lipschitz_deriv` identifies the resolvent with the flow's spatial derivative,
`fderiv ℝ (fun w => Φ w t) z = fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) t`; and the base-point
`C²` result `exists_hasFDerivAt_fundamentalSolution_baseCurve` (with `C' = L`, the `D2v` bound from the
`L`-Lipschitz `Dv`) differentiates that resolvent map in the base point.  The self-contained spatial
`C²` layer unblocking Items 1 & 2. -/
theorem exists_hasFDerivAt_fderiv_flow_of_lipschitz_secondDeriv [CompleteSpace E]
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    {L : ℝ≥0} (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2v : ∀ s ξ, HasFDerivAt (Dv s) (D2v s ξ) ξ)
    (hD2vc : Continuous fun p : ℝ × E => D2v p.1 p.2)
    {M : ℝ≥0} (hD2vlip : ∀ s, LipschitzWith M (D2v s))
    (x₀ : E) {T : ℝ} {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ∃ (Φ : E → ℝ → E) (D₂ : E →L[ℝ] (E →L[ℝ] E)),
      (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) ∧
        HasFDerivAt (fun z => fderiv ℝ (fun w => Φ w t) z) D₂ x₀ := by
  obtain ⟨Φ, h0, hΦ⟩ := exists_flow_family hv hvc
  -- coefficient data at every base point: norm bound and continuity along the trajectory
  have hAfun : ∀ z, ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K := fun z s => by
    have h : ‖Dv s (Φ z s)‖ ≤ (K : ℝ) := (hDv s (Φ z s)).le_of_lipschitz (hv s)
    exact_mod_cast h
  have hAcontfun : ∀ z, Continuous (fun s => Dv s (Φ z s)) := fun z =>
    hDvc.comp (continuous_id.prodMk (hΦ z).continuous)
  have hD2cont : Continuous (fun s => D2v s (Φ x₀ s)) :=
    hD2vc.comp (continuous_id.prodMk (hΦ x₀).continuous)
  -- the second derivative is bounded by `L` (it is the derivative of the `L`-Lipschitz `Dv`)
  have hC' : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ (L : ℝ) := fun s =>
    (hD2v s (Φ x₀ s)).le_of_lipschitz (hDvlip s)
  -- per-base-point variational flow families
  choose Ψ h0Ψ hΨ using fun z => exists_variationalFlowFamily (hAfun z) (hAcontfun z)
  -- the resolvent equals the flow's spatial derivative at every base point (`C¹` bootstrap)
  have hres : ∀ z, HasFDerivAt (fun w => Φ w t)
      (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) t) z := fun z =>
    hasFDerivAt_flow_of_lipschitz_deriv hv (hAfun z) (hΨ z) (h0Ψ z) hΦ h0 z ht.1
      (Dv := Dv) (fun _ s _ ξ _ => (hDv s ξ).hasFDerivWithinAt) L.coe_nonneg
      (fun _ s _ ξ _ => by
        have hlip := (hDvlip s).dist_le_mul ξ (Φ z s)
        rw [dist_eq_norm, dist_eq_norm] at hlip
        exact hlip)
  have hfeq : (fun z => fderiv ℝ (fun w => Φ w t) z)
      = (fun z => fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) t) :=
    funext fun z => (hres z).fderiv
  obtain ⟨D₂, hD₂⟩ := exists_hasFDerivAt_fundamentalSolution_baseCurve
    hv hΦ h0 hDv hDvlip hD2v hD2vlip x₀ hAfun hAcontfun hD2cont L.coe_nonneg hC' hΨ h0Ψ ht
  exact ⟨Φ, D₂, h0, hΦ, hfeq ▸ hD₂⟩

/-- **The flow's spatial derivative is everywhere differentiable (`C²` in initial data at every base
point, `C^{2,1}` field).**  Strengthening `exists_hasFDerivAt_fderiv_flow_of_lipschitz_secondDeriv` to
a *single* flow family whose resolvent map is differentiable at *every* base point: under the same
field-level hypotheses there is one flow family `Φ` of `v` (anchored `Φ z t₀ = z`) whose resolvent map
`z ↦ fderiv ℝ (fun w => Φ w t) z` — the first spatial derivative of the time-`t` flow — is
`Differentiable ℝ`, i.e. Fréchet differentiable at every initial value.  Thus `z ↦ Φ z t` is twice
Fréchet differentiable everywhere.

Proof: build `Φ` and the per-`z` variational families `Ψ` once; the `C¹` bootstrap identifies the
resolvent map with `fderiv ℝ (fun w => Φ w t)` uniformly, and at each base point
`differentiableAt_fundamentalSolution_baseCurve` supplies the derivative (coefficient bound `C' = L`).
The "`C²` in initial data" regularity statement — everywhere — for the spatial bootstrap of Items 1
and 2. -/
theorem exists_flow_fderiv_differentiable_of_lipschitz_secondDeriv [CompleteSpace E]
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    {L : ℝ≥0} (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2v : ∀ s ξ, HasFDerivAt (Dv s) (D2v s ξ) ξ)
    (hD2vc : Continuous fun p : ℝ × E => D2v p.1 p.2)
    {M : ℝ≥0} (hD2vlip : ∀ s, LipschitzWith M (D2v s))
    {T : ℝ} {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) ∧
        Differentiable ℝ (fun z => fderiv ℝ (fun w => Φ w t) z) := by
  obtain ⟨Φ, h0, hΦ⟩ := exists_flow_family hv hvc
  have hAfun : ∀ z, ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K := fun z s => by
    have h : ‖Dv s (Φ z s)‖ ≤ (K : ℝ) := (hDv s (Φ z s)).le_of_lipschitz (hv s)
    exact_mod_cast h
  have hAcontfun : ∀ z, Continuous (fun s => Dv s (Φ z s)) := fun z =>
    hDvc.comp (continuous_id.prodMk (hΦ z).continuous)
  choose Ψ h0Ψ hΨ using fun z => exists_variationalFlowFamily (hAfun z) (hAcontfun z)
  -- the resolvent map equals `fderiv` of the flow, uniformly in the base point (`C¹` bootstrap)
  have hres : ∀ z, HasFDerivAt (fun w => Φ w t)
      (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) t) z := fun z =>
    hasFDerivAt_flow_of_lipschitz_deriv hv (hAfun z) (hΨ z) (h0Ψ z) hΦ h0 z ht.1
      (Dv := Dv) (fun _ s _ ξ _ => (hDv s ξ).hasFDerivWithinAt) L.coe_nonneg
      (fun _ s _ ξ _ => by
        have hlip := (hDvlip s).dist_le_mul ξ (Φ z s)
        rw [dist_eq_norm, dist_eq_norm] at hlip
        exact hlip)
  have hfeq : (fun z => fderiv ℝ (fun w => Φ w t) z)
      = (fun z => fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) t) :=
    funext fun z => (hres z).fderiv
  refine ⟨Φ, h0, hΦ, ?_⟩
  rw [hfeq]
  intro x₀
  have hD2cont : Continuous (fun s => D2v s (Φ x₀ s)) :=
    hD2vc.comp (continuous_id.prodMk (hΦ x₀).continuous)
  have hC' : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ (L : ℝ) := fun s =>
    (hD2v s (Φ x₀ s)).le_of_lipschitz (hDvlip s)
  exact differentiableAt_fundamentalSolution_baseCurve
    hv hΦ h0 hDv hDvlip hD2v hD2vlip x₀ hAfun hAcontfun hD2cont L.coe_nonneg hC' hΨ h0Ψ ht

/-!
### Continuous differentiability of the flow in the initial data (`C¹` in the strong Mathlib sense)

The unconditional differentiable-dependence result `exists_flow_differentiable_of_lipschitz_deriv`
only produces a *differentiable* flow map; the honest `C¹` regularity consumed by the compact-manifold
gauge flow of Item 2 (a *diffeomorphism* family, whose derivatives must vary continuously) is
`ContDiff ℝ 1` — differentiability **plus norm-continuity of the derivative**.  The missing piece is
that the resolvent map `z ↦ D_x Φ_t = fderiv ℝ (fun w => Φ w t) z` depends continuously on the base
point `z`.  This is supplied by the operator-norm continuous dependence of the resolvent on its
coefficient (`norm_fundamentalSolution_sub_le_of_forall_le_Icc`) composed with the Lipschitz-in-base
control of the linearised coefficient along the reference trajectory
(`norm_derivField_apply_flow_sub_le`): the coefficient `A(z) s = Dv s (Φ z s)` moves by at most
`L · exp (K (t − t₀)) · ‖z − z₀‖` on the tube `[t₀, t]`, hence the resolvent moves by at most
`L · exp (K (t − t₀))² · gronwallBound 0 K 1 (t − t₀) · ‖z − z₀‖`.  The resolvent map is therefore
(globally) Lipschitz in the base point, in particular continuous.  This upgrades the `C¹`-in-initial
-data dependence from *differentiable* to *continuously differentiable* — the `ContDiff ℝ 1` interface
that Items 1 and 2 actually consume. -/

/-- **The flow map is `C¹`-with-continuous-derivative in the initial data (`C^{1,1}` field): the
resolvent varies continuously with the base point.**  Strengthening
`exists_flow_differentiable_of_lipschitz_deriv`: under the same field-level hypotheses (uniformly
`K`-Lipschitz, time-continuous `v` with everywhere-defined, jointly continuous, spatially
`L`-Lipschitz derivative `Dv`) there is one flow family `Φ` of `v` (anchored `Φ z t₀ = z`) whose
forward time-`t` slice `z ↦ Φ z t` is `Differentiable ℝ` **and** whose derivative map
`z ↦ fderiv ℝ (fun w => Φ w t) z` — the resolvent `D_x Φ_t` — is `Continuous`.

Proof: build `Φ` once; the `C¹` bootstrap `hasFDerivAt_flow_of_lipschitz_deriv` identifies the resolvent
map with `fderiv ℝ (fun w => Φ w t)`, so it remains to show `z ↦ fundamentalSolution (A(z)) t` is
continuous.  Two base points `z`, `z₀` have coefficients `A(z) s = Dv s (Φ z s)` differing by at most
`ε = L · exp (K (t − t₀)) · ‖z − z₀‖` on `[t₀, t]` (`norm_derivField_apply_flow_sub_le`), so the
resolvent gap is `≤ ε · exp (K (t − t₀)) · gronwallBound 0 K 1 (t − t₀)`
(`norm_fundamentalSolution_sub_le_of_forall_le_Icc`); this is a fixed multiple of `‖z − z₀‖`, i.e. the
resolvent map is Lipschitz, hence continuous. -/
theorem exists_flow_fderiv_continuous_of_lipschitz_deriv [CompleteSpace E]
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ s x, HasFDerivAt (v s) (Dv s x) x)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    {L : ℝ≥0} (hDvlip : ∀ s, LipschitzWith L (Dv s))
    {t : ℝ} (ht0 : t₀ ≤ t) :
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) ∧
        Differentiable ℝ (fun z => Φ z t) ∧
        Continuous (fun z => fderiv ℝ (fun w => Φ w t) z) := by
  obtain ⟨Φ, h0, hΦ⟩ := exists_flow_family hv hvc
  have hAfun : ∀ z, ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K := fun z s => by
    have h : ‖Dv s (Φ z s)‖ ≤ (K : ℝ) := (hderiv s (Φ z s)).le_of_lipschitz (hv s)
    exact_mod_cast h
  have hAcontfun : ∀ z, Continuous (fun s => Dv s (Φ z s)) := fun z =>
    hDvc.comp (continuous_id.prodMk (hΦ z).continuous)
  choose Ψ h0Ψ hΨ using fun z => exists_variationalFlowFamily (hAfun z) (hAcontfun z)
  -- the `C¹` bootstrap identifies the resolvent map with `fderiv` at every base point
  have hres : ∀ z, HasFDerivAt (fun w => Φ w t)
      (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) t) z := fun z =>
    hasFDerivAt_flow_of_lipschitz_deriv hv (hAfun z) (hΨ z) (h0Ψ z) hΦ h0 z ht0
      (Dv := Dv) (fun _ s _ ξ _ => (hderiv s ξ).hasFDerivWithinAt) L.coe_nonneg
      (fun _ s _ ξ _ => by
        have hlip := (hDvlip s).dist_le_mul ξ (Φ z s)
        rw [dist_eq_norm, dist_eq_norm] at hlip
        exact hlip)
  have hfeq : (fun z => fderiv ℝ (fun w => Φ w t) z)
      = (fun z => fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) t) :=
    funext fun z => (hres z).fderiv
  refine ⟨Φ, h0, hΦ, fun z => (hres z).differentiableAt, ?_⟩
  rw [hfeq]
  -- the resolvent map is Lipschitz in the base point, hence continuous
  have hg0 : 0 ≤ gronwallBound 0 (K : ℝ) 1 (t - t₀) :=
    gronwallBound_zero_one_nonneg K.coe_nonneg (sub_nonneg.mpr ht0)
  have hC0 : (0 : ℝ) ≤ (L : ℝ) * Real.exp ((K : ℝ) * (t - t₀)) ^ 2
      * gronwallBound 0 (K : ℝ) 1 (t - t₀) :=
    mul_nonneg (by positivity) hg0
  apply LipschitzWith.continuous
    (K := ((L : ℝ) * Real.exp ((K : ℝ) * (t - t₀)) ^ 2
      * gronwallBound 0 (K : ℝ) 1 (t - t₀)).toNNReal)
  apply LipschitzWith.of_dist_le_mul
  intro z z₀
  rw [Real.coe_toNNReal _ hC0, dist_eq_norm, dist_eq_norm]
  have hgap : ∀ s ∈ Icc t₀ t, ‖Dv s (Φ z s) - Dv s (Φ z₀ s)‖
      ≤ (L : ℝ) * Real.exp ((K : ℝ) * (t - t₀)) * ‖z - z₀‖ := fun s hs => by
    have hsT : |s - t₀| ≤ t - t₀ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
    exact norm_derivField_apply_flow_sub_le hv hΦ h0 (hDvlip s) hsT z z₀
  have key := norm_fundamentalSolution_sub_le_of_forall_le_Icc
    (hAfun z) (hAfun z₀) (hΨ z) (h0Ψ z) (hΨ z₀) (h0Ψ z₀)
    (by positivity : (0 : ℝ) ≤ (L : ℝ) * Real.exp ((K : ℝ) * (t - t₀)) * ‖z - z₀‖)
    hgap ⟨ht0, le_refl t⟩
  calc ‖fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) t
          - fundamentalSolution (hAfun z₀) (hΨ z₀) (h0Ψ z₀) t‖
      ≤ (L : ℝ) * Real.exp ((K : ℝ) * (t - t₀)) * ‖z - z₀‖
          * Real.exp ((K : ℝ) * (t - t₀)) * gronwallBound 0 (K : ℝ) 1 (t - t₀) := key
    _ = (L : ℝ) * Real.exp ((K : ℝ) * (t - t₀)) ^ 2
          * gronwallBound 0 (K : ℝ) 1 (t - t₀) * ‖z - z₀‖ := by ring

/-- **The flow map is `ContDiff ℝ 1` in the initial data (`C^{1,1}` field).**  The Mathlib-`ContDiff`
packaging of `exists_flow_fderiv_continuous_of_lipschitz_deriv`: under the same field-level hypotheses
there is one flow family `Φ` of `v` (anchored `Φ z t₀ = z`) whose forward time-`t` slice
`z ↦ Φ z t` is `ContDiff ℝ 1` — continuously (Fréchet) differentiable in the initial value.  This is
the honest "`C¹` in initial data" statement (differentiable with continuous derivative), in the
`ContDiff` vocabulary that the compact-manifold gauge flow (Item 2) and the tensor time-derivative
chain rule (Item 1) consume, obtained from the differentiability and resolvent-continuity halves via
`contDiff_one_iff_fderiv`. -/
theorem exists_flow_contDiff_one_of_lipschitz_deriv [CompleteSpace E]
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)}
    (hderiv : ∀ s x, HasFDerivAt (v s) (Dv s x) x)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    {L : ℝ≥0} (hDvlip : ∀ s, LipschitzWith L (Dv s))
    {t : ℝ} (ht0 : t₀ ≤ t) :
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) ∧
        ContDiff ℝ 1 (fun z => Φ z t) := by
  obtain ⟨Φ, h0, hΦ, hdiff, hcont⟩ :=
    exists_flow_fderiv_continuous_of_lipschitz_deriv hv hvc hderiv hDvc hDvlip ht0
  exact ⟨Φ, h0, hΦ, contDiff_one_iff_fderiv.mpr ⟨hdiff, hcont⟩⟩

/-!
### Continuous dependence of the inhomogeneous variation on its coefficient and forcing

The base-point `C²` bootstrap packages the second fundamental solution `D₂(x₀)` as the time-`t` value
of the *linearised first variation* `Vlin` — the anchored solution of an inhomogeneous linear ODE
`V' = A(x₀) ∘ V + F(x₀)` whose coefficient `A(x₀) s = Dv s (Φ x₀ s)` and chain-rule forcing
`F(x₀) s = (D²v(Φ x₀ s) ∘ W(x₀,s) · h) ∘ W(x₀,s)` both depend on the base point `x₀`.  Establishing
that `x₀ ↦ D₂(x₀)` is *continuous* — the missing ingredient for the honest `ContDiff ℝ 2` regularity of
the flow in the initial data — therefore reduces to the continuous (in fact Lipschitz) dependence of
the inhomogeneous variation's time-`t` value on the pair `(A, F)`.  The following primitive isolates
that dependence, allowing the two coefficient fields to differ (unlike the same-coefficient
subtraction `hasDerivAt_inhomogVariation_sub`): the difference `V₁ - V₂` solves the inhomogeneous ODE
with coefficient `A₁` and the *residual* forcing `(A₁ - A₂) ∘ V₂ + (F₁ - F₂)`, whose size is
controlled by the coefficient gap `α`, the second-solution bound `N`, and the forcing gap `β`. -/

/-- **Lipschitz dependence of the inhomogeneous variation on the coefficient and forcing.**  Let `V₁`,
`V₂` be the anchored solutions (`V t₀ = 0`) of the inhomogeneous variational ODEs
`V₁' = A₁ ∘ V₁ + F₁` and `V₂' = A₂ ∘ V₂ + F₂`, with `A₁` norm-bounded by `K`.  If, on the compact tube
`[t₀, T]`, the coefficients differ by at most `α` (`‖A₁ s − A₂ s‖ ≤ α`), the second solution is bounded
by `N` (`‖V₂ s‖ ≤ N`), and the forcings differ by at most `β` (`‖F₁ s − F₂ s‖ ≤ β`), then
`‖V₁ t − V₂ t‖ ≤ (α · N + β) · gronwallBound 0 K 1 (t − t₀)` for every `t ∈ [t₀, T]`.

Proof: the difference `R = V₁ − V₂` solves the inhomogeneous ODE with coefficient `A₁` and residual
forcing `G = (A₁ − A₂) ∘ V₂ + (F₁ − F₂)` (rearranging `A₁ ∘ V₁ + F₁ − (A₂ ∘ V₂ + F₂)` via
`comp_sub`/`sub_comp`), anchored `R t₀ = 0`.  On `[t₀, T]` the forcing satisfies
`‖G s‖ ≤ ‖A₁ s − A₂ s‖ · ‖V₂ s‖ + ‖F₁ s − F₂ s‖ ≤ α · N + β` (submultiplicativity of the operator
norm), and the general a-priori bound `norm_inhomogVariation_le` closes it.  Taking `α, β → 0` this is
the continuity of `(A, F) ↦ V(t)`; specialised to the trajectory-linearised coefficient and chain-rule
forcing it drives the continuity of the second fundamental solution `x₀ ↦ D₂(x₀)`. -/
theorem norm_inhomogVariation_sub_le_of_gap
    {A₁ A₂ F₁ F₂ V₁ V₂ : ℝ → (E →L[ℝ] E)}
    (hA₁ : ∀ s, ‖A₁ s‖₊ ≤ K)
    (hV₁ : ∀ s, HasDerivAt V₁ ((A₁ s).comp (V₁ s) + F₁ s) s) (hV₁0 : V₁ t₀ = 0)
    (hV₂ : ∀ s, HasDerivAt V₂ ((A₂ s).comp (V₂ s) + F₂ s) s) (hV₂0 : V₂ t₀ = 0)
    {α β N T : ℝ}
    (hAgap : ∀ s ∈ Icc t₀ T, ‖A₁ s - A₂ s‖ ≤ α)
    (hV₂bound : ∀ s ∈ Icc t₀ T, ‖V₂ s‖ ≤ N)
    (hFgap : ∀ s ∈ Icc t₀ T, ‖F₁ s - F₂ s‖ ≤ β)
    (hα : 0 ≤ α) {t : ℝ} (ht : t ∈ Icc t₀ T) :
    ‖V₁ t - V₂ t‖ ≤ (α * N + β) * gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
  -- `R = V₁ - V₂` solves `R' = A₁ ∘ R + G`, `G = (A₁ - A₂) ∘ V₂ + (F₁ - F₂)`
  have hRderiv : ∀ s, HasDerivAt (fun r => V₁ r - V₂ r)
      ((A₁ s).comp (V₁ s - V₂ s)
        + ((A₁ s - A₂ s).comp (V₂ s) + (F₁ s - F₂ s))) s := by
    intro s
    have h := (hV₁ s).sub (hV₂ s)
    have heq : (A₁ s).comp (V₁ s) + F₁ s - ((A₂ s).comp (V₂ s) + F₂ s)
        = (A₁ s).comp (V₁ s - V₂ s)
          + ((A₁ s - A₂ s).comp (V₂ s) + (F₁ s - F₂ s)) := by
      rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]; abel
    rwa [heq] at h
  have hR0 : (fun r => V₁ r - V₂ r) t₀ = 0 := by simp [hV₁0, hV₂0]
  have hGbound : ∀ s ∈ Icc t₀ T,
      ‖(A₁ s - A₂ s).comp (V₂ s) + (F₁ s - F₂ s)‖ ≤ α * N + β := by
    intro s hs
    refine (norm_add_le _ _).trans (add_le_add ?_ (hFgap s hs))
    calc ‖(A₁ s - A₂ s).comp (V₂ s)‖
        ≤ ‖A₁ s - A₂ s‖ * ‖V₂ s‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ α * N := mul_le_mul (hAgap s hs) (hV₂bound s hs) (norm_nonneg _) hα
  exact norm_inhomogVariation_le hA₁ hRderiv hR0 hGbound ht

/-- **Uniform Lipschitz-in-base-point bound for the second derivative field along the flow.**  The
second-derivative analogue of `norm_derivField_apply_flow_sub_le`: for a uniformly `K`-Lipschitz field
`v` with `M`-Lipschitz *second* spatial derivative `D²v s`, and a flow family `Φ` of `v` anchored at
`Φ x t₀ = x`, the second-derivative field along the flow `z ↦ D²v s (Φ z s)` moves by at most
`M · exp (K T) · ‖z − w‖` for every time `s` with `|s − t₀| ≤ T`.  Composes the `M`-Lipschitz `D²v s`
with the uniform flow-Lipschitz bound `lipschitzWith_flow_apply_of_abs_le` (`exp (K T)`), exactly as
`norm_derivField_apply_flow_sub_le` does for the first derivative.  This is the size datum for the
`D²v`-gap term in the chain-rule forcing perturbation of the base-point `C³`/`ContDiff ℝ 2` bootstrap
(continuity of the second fundamental solution). -/
theorem norm_secondDerivField_apply_flow_sub_le
    {Φ : E → ℝ → E} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))} {M : ℝ≥0} {s T : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (hD2v : LipschitzWith M (D2v s)) (hsT : |s - t₀| ≤ T) (z w : E) :
    ‖D2v s (Φ z s) - D2v s (Φ w s)‖ ≤ (M : ℝ) * Real.exp ((K : ℝ) * T) * ‖z - w‖ := by
  have hlip : LipschitzWith (M * (Real.exp ((K : ℝ) * T)).toNNReal) (fun z => D2v s (Φ z s)) :=
    hD2v.comp (lipschitzWith_flow_apply_of_abs_le hv hΦ h0 hsT)
  have hd := hlip.dist_le_mul z w
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mul, Real.coe_toNNReal _ (Real.exp_pos _).le] at hd
  exact hd

/-- **The resolvent is Lipschitz in the base point along the flow.**  Packaging the base-point
continuous dependence of the first fundamental solution used inside
`exists_flow_fderiv_continuous_of_lipschitz_deriv` as a standalone quantitative estimate.  For two
base points `z`, `w`, the trajectory-linearised coefficients `A(z) s = Dv s (Φ z s)`,
`A(w) s = Dv s (Φ w s)` (both `≤ K`) with their variational flow families `Φ₁`, `Φ₂`, the resolvents
at time `t` satisfy
`‖D_x Φ_t^{A(z)} − D_x Φ_t^{A(w)}‖ ≤ L · exp (K (T − t₀)) · ‖z − w‖ · exp (K (T − t₀)) · gronwallBound 0 K 1 (t − t₀)`
for `t ∈ [t₀, T]`.  Proof: the coefficient gap is `≤ L · exp (K (T − t₀)) · ‖z − w‖` on `[t₀, T]`
(`norm_derivField_apply_flow_sub_le`), fed to the resolvent-in-coefficient bound
`norm_fundamentalSolution_sub_le_of_forall_le_Icc`.  This is the `dw` datum (the size of the resolvent
response to a base-point increment, uniformly over the tube) consumed by the chain-rule forcing
perturbation of the base-point `ContDiff ℝ 2` bootstrap (continuity of the second fundamental
solution). -/
theorem norm_fundamentalSolution_baseCurve_sub_le
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {L : ℝ≥0}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hDvlip : ∀ s, LipschitzWith L (Dv s)) (z w : E)
    (hAz : ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K) (hAw : ∀ s, ‖Dv s (Φ w s)‖₊ ≤ K)
    {Φ₁ Φ₂ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h1 : ∀ x, Φ₁ x t₀ = x)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec (fun s => Dv s (Φ w s))))
    (h2 : ∀ x, Φ₂ x t₀ = x)
    {T t : ℝ} (ht : t ∈ Icc t₀ T) :
    ‖fundamentalSolution hAz hΦ₁ h1 t - fundamentalSolution hAw hΦ₂ h2 t‖
      ≤ (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - w‖
          * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
  have hgap : ∀ s ∈ Icc t₀ T, ‖Dv s (Φ z s) - Dv s (Φ w s)‖
      ≤ (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - w‖ := fun s hs => by
    have hsT : |s - t₀| ≤ T - t₀ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
    exact norm_derivField_apply_flow_sub_le hv hΦ h0 (hDvlip s) hsT z w
  exact norm_fundamentalSolution_sub_le_of_forall_le_Icc hAz hAw hΦ₁ h1 hΦ₂ h2
    (by positivity) hgap ht

/-- **Perturbation estimate for the chain-rule forcing operator.**  The chain-rule forcing of the
linearised first-variation ODE has, at each time, the shape `((P ∘ W) h) ∘ W` where `P = D²v(Φ z s)`
and `W = D_x Φ_s^{A(z)}` is the resolvent (so `(P ∘ W) h ∘ W = (D²v(Φ z s) ∘ W · h) ∘ W`).  This
lemma bounds its response to a joint perturbation of `P` and `W`: for `‖P₁‖ ≤ p`, `‖W₁‖, ‖W₂‖ ≤ w`,
`‖P₁ − P₂‖ ≤ dp`, `‖W₁ − W₂‖ ≤ dw`,
`‖((P₁ ∘ W₁) h) ∘ W₁ − ((P₂ ∘ W₂) h) ∘ W₂‖ ≤ (dp · w² + 2 · p · w · dw) · ‖h‖`.

Proof: telescoping the composition (`comp_sub`/`sub_comp`), `((P₁∘W₁)h)∘W₁ − ((P₂∘W₂)h)∘W₂ =
a ∘ (W₁ − W₂) + (a − b) ∘ W₂` with `a = (P₁∘W₁)h`, `b = (P₂∘W₂)h`; then `‖a‖ ≤ p·w·‖h‖`,
`‖a − b‖ ≤ (p·dw + dp·w)·‖h‖` (a second telescoping of `P₁∘W₁ − P₂∘W₂`), and submultiplicativity of
the operator norm.  This is the algebraic core of the forcing-gap `β` in the chain-rule forcing
perturbation of the base-point `ContDiff ℝ 2` bootstrap: fed the flow bounds (`‖D²v‖ ≤ L = p`,
`‖W‖ ≤ exp (K(T−t₀)) = w`, `dp` from `norm_secondDerivField_apply_flow_sub_le`, `dw` from
`norm_fundamentalSolution_baseCurve_sub_le`) it bounds the forcing response to a base-point increment,
which `norm_inhomogVariation_sub_le_of_gap` turns into the continuity of the second fundamental
solution. -/
theorem norm_chainRuleForcing_sub_le
    {P₁ P₂ : E →L[ℝ] (E →L[ℝ] E)} {W₁ W₂ : E →L[ℝ] E} (h : E)
    {p w dp dw : ℝ}
    (hP₁ : ‖P₁‖ ≤ p) (hW₁ : ‖W₁‖ ≤ w) (hW₂ : ‖W₂‖ ≤ w)
    (hPd : ‖P₁ - P₂‖ ≤ dp) (hWd : ‖W₁ - W₂‖ ≤ dw)
    (hp : 0 ≤ p) (hw : 0 ≤ w) (hdp : 0 ≤ dp) (hdw : 0 ≤ dw) :
    ‖((P₁.comp W₁) h).comp W₁ - ((P₂.comp W₂) h).comp W₂‖
      ≤ (dp * w ^ 2 + 2 * p * w * dw) * ‖h‖ := by
  -- `‖(P₁ ∘ W₁) h‖ ≤ p · w · ‖h‖`
  have hanorm : ‖(P₁.comp W₁) h‖ ≤ p * w * ‖h‖ := by
    calc ‖(P₁.comp W₁) h‖ ≤ ‖P₁.comp W₁‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖P₁‖ * ‖W₁‖ * ‖h‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
      _ ≤ p * w * ‖h‖ := by gcongr
  -- `‖P₁ ∘ W₁ − P₂ ∘ W₂‖ ≤ p · dw + dp · w`
  have hPWd : ‖P₁.comp W₁ - P₂.comp W₂‖ ≤ p * dw + dp * w := by
    have hsplit : P₁.comp W₁ - P₂.comp W₂
        = P₁.comp (W₁ - W₂) + (P₁ - P₂).comp W₂ := by
      rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]; abel
    calc ‖P₁.comp W₁ - P₂.comp W₂‖
        = ‖P₁.comp (W₁ - W₂) + (P₁ - P₂).comp W₂‖ := by rw [hsplit]
      _ ≤ ‖P₁.comp (W₁ - W₂)‖ + ‖(P₁ - P₂).comp W₂‖ :=
          norm_add_le (P₁.comp (W₁ - W₂)) ((P₁ - P₂).comp W₂)
      _ ≤ ‖P₁‖ * ‖W₁ - W₂‖ + ‖P₁ - P₂‖ * ‖W₂‖ :=
          add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
            (ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ p * dw + dp * w := by gcongr
  -- `‖(P₁ ∘ W₁) h − (P₂ ∘ W₂) h‖ ≤ (p · dw + dp · w) · ‖h‖`
  have habd : ‖(P₁.comp W₁) h - (P₂.comp W₂) h‖ ≤ (p * dw + dp * w) * ‖h‖ := by
    have hab : (P₁.comp W₁) h - (P₂.comp W₂) h = (P₁.comp W₁ - P₂.comp W₂) h := by
      rw [ContinuousLinearMap.sub_apply]
    calc ‖(P₁.comp W₁) h - (P₂.comp W₂) h‖ = ‖(P₁.comp W₁ - P₂.comp W₂) h‖ := by rw [hab]
      _ ≤ ‖P₁.comp W₁ - P₂.comp W₂‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (p * dw + dp * w) * ‖h‖ := by gcongr
  -- telescope: `G₁ − G₂ = (P₁∘W₁)h ∘ (W₁ − W₂) + ((P₁∘W₁)h − (P₂∘W₂)h) ∘ W₂`
  have hGsplit : ((P₁.comp W₁) h).comp W₁ - ((P₂.comp W₂) h).comp W₂
      = ((P₁.comp W₁) h).comp (W₁ - W₂)
        + ((P₁.comp W₁) h - (P₂.comp W₂) h).comp W₂ := by
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]; abel
  have hpw : (0 : ℝ) ≤ p * w * ‖h‖ := by positivity
  have hpdw : (0 : ℝ) ≤ (p * dw + dp * w) * ‖h‖ := by positivity
  calc ‖((P₁.comp W₁) h).comp W₁ - ((P₂.comp W₂) h).comp W₂‖
      = ‖((P₁.comp W₁) h).comp (W₁ - W₂)
          + ((P₁.comp W₁) h - (P₂.comp W₂) h).comp W₂‖ := by rw [hGsplit]
    _ ≤ ‖((P₁.comp W₁) h).comp (W₁ - W₂)‖
          + ‖((P₁.comp W₁) h - (P₂.comp W₂) h).comp W₂‖ :=
        norm_add_le (((P₁.comp W₁) h).comp (W₁ - W₂))
          (((P₁.comp W₁) h - (P₂.comp W₂) h).comp W₂)
    _ ≤ ‖(P₁.comp W₁) h‖ * ‖W₁ - W₂‖
          + ‖(P₁.comp W₁) h - (P₂.comp W₂) h‖ * ‖W₂‖ :=
        add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
          (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ (p * w * ‖h‖) * dw + ((p * dw + dp * w) * ‖h‖) * w :=
        add_le_add (mul_le_mul hanorm hWd (norm_nonneg _) hpw)
          (mul_le_mul habd hW₂ (norm_nonneg _) hpdw)
    _ = (dp * w ^ 2 + 2 * p * w * dw) * ‖h‖ := by ring

/-- **The flow map is `ContDiff ℝ 2` in the initial data (`C^{2,1}` field).**  The honest "flow is `C²`
in initial data" milestone in Mathlib's `ContDiff` vocabulary: from a uniformly `K`-Lipschitz,
time-continuous field `v` with everywhere-defined, jointly continuous, spatially `L`-Lipschitz first
derivative `Dv` and everywhere-defined, jointly continuous, `M`-Lipschitz second derivative `D²v`,
there is one flow family `Φ` of `v` (anchored `Φ z t₀ = z`) whose forward time-`t` slice
`z ↦ Φ z t` is `ContDiff ℝ 2` — twice continuously (Fréchet) differentiable in the initial value.

Proof: build `Φ` and the per-`z` variational families `Ψ z`.  The `C¹` bootstrap identifies the
resolvent map with `fderiv ℝ (fun w => Φ w t)`, and the base-point `C²` bootstrap
(`exists_hasFDerivAt_fundamentalSolution_baseCurve`, replicated with the packaged operator `D₂ z` of
`exists_continuousLinearMap_linearisedVariation`) identifies its derivative with `D₂ z`, so
`fderiv ℝ (fderiv ℝ (fun w => Φ w t)) = D₂`.  Continuity of the second fundamental solution
`z ↦ D₂ z` — the new ingredient — is the Lipschitz bound `‖D₂ z − D₂ z₀‖ ≤ C · ‖z − z₀‖`: for a unit
direction `h`, `D₂ z h − D₂ z₀ h = Vlin^{z,h} t − Vlin^{z₀,h} t` (operator characterisation), and the
two linearised variations solve inhomogeneous ODEs whose coefficient gap
(`norm_derivField_apply_flow_sub_le`) and chain-rule forcing gap
(`norm_chainRuleForcing_sub_le`, fed the `D²v`-gap `norm_secondDerivField_apply_flow_sub_le` and the
resolvent gap `norm_fundamentalSolution_baseCurve_sub_le`) are `O(‖z − z₀‖)`, so
`norm_inhomogVariation_sub_le_of_gap` gives `‖Vlin^{z,h} t − Vlin^{z₀,h} t‖ ≤ C · ‖z − z₀‖ · ‖h‖`.
Packaged as `ContDiff ℝ 2` via `contDiff_one_iff_fderiv` and `contDiff_succ_iff_fderiv`.  The
self-contained `C²`-in-initial-data layer consumed by the compact-manifold gauge flow (Item 2) and the
tensor time-derivative chain rule (Item 1). -/
theorem exists_flow_contDiff_two_of_lipschitz_secondDeriv [CompleteSpace E]
    (hv : ∀ τ, LipschitzWith K (v τ)) (hvc : ∀ x, Continuous fun s => v s x)
    {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ)
    (hDvc : Continuous fun p : ℝ × E => Dv p.1 p.2)
    {L : ℝ≥0} (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2v : ∀ s ξ, HasFDerivAt (Dv s) (D2v s ξ) ξ)
    (hD2vc : Continuous fun p : ℝ × E => D2v p.1 p.2)
    {M : ℝ≥0} (hD2vlip : ∀ s, LipschitzWith M (D2v s))
    {t : ℝ} (ht0 : t₀ ≤ t) :
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) ∧
        ContDiff ℝ 2 (fun z => Φ z t) := by
  obtain ⟨Φ, h0, hΦ⟩ := exists_flow_family hv hvc
  have hAfun : ∀ z, ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K := fun z s => by
    have h : ‖Dv s (Φ z s)‖ ≤ (K : ℝ) := (hDv s (Φ z s)).le_of_lipschitz (hv s)
    exact_mod_cast h
  have hAcontfun : ∀ z, Continuous (fun s => Dv s (Φ z s)) := fun z =>
    hDvc.comp (continuous_id.prodMk (hΦ z).continuous)
  have hD2contfun : ∀ z, Continuous (fun s => D2v s (Φ z s)) := fun z =>
    hD2vc.comp (continuous_id.prodMk (hΦ z).continuous)
  have hCz : ∀ z, ∀ s, ‖D2v s (Φ z s)‖ ≤ (L : ℝ) := fun z s =>
    (hD2v s (Φ z s)).le_of_lipschitz (hDvlip s)
  choose Ψ h0Ψ hΨ using fun z => exists_variationalFlowFamily (hAfun z) (hAcontfun z)
  have htmem : t ∈ Set.Icc t₀ t := ⟨ht0, le_refl t⟩
  have hg0 : (0 : ℝ) ≤ gronwallBound 0 (K : ℝ) 1 (t - t₀) :=
    gronwallBound_zero_one_nonneg K.coe_nonneg (sub_nonneg.mpr ht0)
  -- the packaged second fundamental solution operators, with their linearised-variation characterisation
  choose D₂ hD₂char using fun z => exists_continuousLinearMap_linearisedVariation
    z (hAfun z) (hAcontfun z) (hD2contfun z) (hΨ z) (h0Ψ z) L.coe_nonneg (hCz z) htmem
  -- `C¹` bootstrap: the resolvent map is the flow's spatial derivative
  have hres : ∀ z, HasFDerivAt (fun w => Φ w t)
      (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) t) z := fun z =>
    hasFDerivAt_flow_of_lipschitz_deriv hv (hAfun z) (hΨ z) (h0Ψ z) hΦ h0 z ht0
      (Dv := Dv) (fun _ s _ ξ _ => (hDv s ξ).hasFDerivWithinAt) L.coe_nonneg
      (fun _ s _ ξ _ => by
        have hlip := (hDvlip s).dist_le_mul ξ (Φ z s)
        rw [dist_eq_norm, dist_eq_norm] at hlip
        exact hlip)
  have hfeq : fderiv ℝ (fun w => Φ w t)
      = fun z => fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) t :=
    funext fun z => (hres z).fderiv
  -- base-point `C²` bootstrap with the *packaged* operator `D₂ z` (replicating
  -- `exists_hasFDerivAt_fundamentalSolution_baseCurve` so that `fderiv` is identified with `D₂ z`)
  have hD2has : ∀ z, HasFDerivAt
      (fun z' => fundamentalSolution (hAfun z') (hΨ z') (h0Ψ z') t) (D₂ z) z := by
    intro z
    refine hasFDerivAt_of_eventually_norm_sub_sub_le_sq (C :=
        (L : ℝ) ^ 2 * Real.exp ((K : ℝ) * (t - t₀)) ^ 3
            * gronwallBound 0 (K : ℝ) 1 (t - t₀) ^ 2
          + ((M : ℝ) * Real.exp (2 * (K : ℝ) * (t - t₀))
              + (L : ℝ) * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (t - t₀))
                  * gronwallBound 0 (K : ℝ) 1 (t - t₀)))
            * Real.exp ((K : ℝ) * (t - t₀)) * gronwallBound 0 (K : ℝ) 1 (t - t₀))
      (Filter.Eventually.of_forall (fun z' => ?_))
    obtain ⟨Vz, hVz0, hVz⟩ := exists_hasDerivAt_firstVariation_true
      z (hAfun z) (hAcontfun z) (hΨ z) (h0Ψ z) z' (hAcontfun z')
    obtain ⟨Vlin, hVlin0, hVlin⟩ := exists_hasDerivAt_firstVariation_linearised
      z (hAfun z) (hAcontfun z) (hD2contfun z) (hΨ z) (h0Ψ z) z'
    have hrem := norm_fundamentalSolution_sub_sub_linearVariation_le_sq
      hv hΦ h0 hDv hDvlip hD2v hD2vlip z (hAfun z) (hAcontfun z) L.coe_nonneg (hCz z)
      (hΨ z) (h0Ψ z) z' (hAfun z') (hAcontfun z') (hΨ z') (h0Ψ z') hVz hVz0 hVlin hVlin0 htmem
    have hval : D₂ z (z' - z) = Vlin t := hD₂char z (z' - z) Vlin hVlin0 hVlin
    rw [hval]; exact hrem
  have hfeq2 : fderiv ℝ (fun z => fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) t) = D₂ :=
    funext fun z => (hD2has z).fderiv
  -- **continuity of the second fundamental solution** `z ↦ D₂ z` (the new ingredient)
  have hcont_D₂ : Continuous D₂ := by
    have hClip0 : (0 : ℝ) ≤ (((L : ℝ) * Real.exp ((K : ℝ) * (t - t₀)))
          * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (t - t₀))
              * gronwallBound 0 (K : ℝ) 1 (t - t₀))
        + ((M : ℝ) * Real.exp ((K : ℝ) * (t - t₀)) ^ 3
            + 2 * (L : ℝ) ^ 2 * Real.exp ((K : ℝ) * (t - t₀)) ^ 3
                * gronwallBound 0 (K : ℝ) 1 (t - t₀)))
        * gronwallBound 0 (K : ℝ) 1 (t - t₀) :=
      mul_nonneg (add_nonneg
        (mul_nonneg (by positivity) (mul_nonneg (by positivity) hg0))
        (add_nonneg (by positivity) (mul_nonneg (by positivity) hg0))) hg0
    have hkey : ∀ z z₀ : E, ‖D₂ z - D₂ z₀‖
        ≤ (((L : ℝ) * Real.exp ((K : ℝ) * (t - t₀)))
              * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (t - t₀))
                  * gronwallBound 0 (K : ℝ) 1 (t - t₀))
            + ((M : ℝ) * Real.exp ((K : ℝ) * (t - t₀)) ^ 3
                + 2 * (L : ℝ) ^ 2 * Real.exp ((K : ℝ) * (t - t₀)) ^ 3
                    * gronwallBound 0 (K : ℝ) 1 (t - t₀)))
            * gronwallBound 0 (K : ℝ) 1 (t - t₀) * ‖z - z₀‖ := by
      intro z z₀
      refine ContinuousLinearMap.opNorm_le_bound _
        (mul_nonneg hClip0 (norm_nonneg _)) (fun h => ?_)
      rw [ContinuousLinearMap.sub_apply]
      obtain ⟨V1, hV10, hV1⟩ := exists_hasDerivAt_firstVariation_linearised_dir
        z (hAfun z) (hAcontfun z) (hD2contfun z) (hΨ z) (h0Ψ z) h
      obtain ⟨V2, hV20, hV2⟩ := exists_hasDerivAt_firstVariation_linearised_dir
        z₀ (hAfun z₀) (hAcontfun z₀) (hD2contfun z₀) (hΨ z₀) (h0Ψ z₀) h
      rw [hD₂char z h V1 hV10 hV1, hD₂char z₀ h V2 hV20 hV2]
      -- coefficient gap `α`
      have hAgap : ∀ s ∈ Set.Icc t₀ t, ‖Dv s (Φ z s) - Dv s (Φ z₀ s)‖
          ≤ (L : ℝ) * Real.exp ((K : ℝ) * (t - t₀)) * ‖z - z₀‖ := by
        intro s hs
        have hsT : |s - t₀| ≤ t - t₀ := by
          rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
        exact norm_derivField_apply_flow_sub_le hv hΦ h0 (hDvlip s) hsT z z₀
      -- second-solution bound `N`
      have hV₂bound : ∀ s ∈ Set.Icc t₀ t, ‖V2 s‖
          ≤ (L : ℝ) * Real.exp (2 * (K : ℝ) * (t - t₀)) * ‖h‖
              * gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
        intro s hs
        refine (norm_linearisedFirstVariation_le z₀ (hAfun z₀) (hΨ z₀) (h0Ψ z₀)
          L.coe_nonneg (hCz z₀) h hV2 hV20 hs).trans ?_
        apply mul_le_mul_of_nonneg_left
          (gronwallBound_mono le_rfl zero_le_one K.coe_nonneg (by linarith [hs.2]))
        positivity
      -- forcing gap `β`
      have hFgap : ∀ s ∈ Set.Icc t₀ t,
          ‖((D2v s (Φ z s)).comp (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s) h).comp
                (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s)
            - ((D2v s (Φ z₀ s)).comp (fundamentalSolution (hAfun z₀) (hΨ z₀) (h0Ψ z₀) s) h).comp
                (fundamentalSolution (hAfun z₀) (hΨ z₀) (h0Ψ z₀) s)‖
          ≤ ((M : ℝ) * Real.exp ((K : ℝ) * (t - t₀)) * ‖z - z₀‖
                  * Real.exp ((K : ℝ) * (t - t₀)) ^ 2
                + 2 * (L : ℝ) * Real.exp ((K : ℝ) * (t - t₀))
                    * ((L : ℝ) * Real.exp ((K : ℝ) * (t - t₀)) ^ 2
                        * gronwallBound 0 (K : ℝ) 1 (t - t₀) * ‖z - z₀‖))
              * ‖h‖ := by
        intro s hs
        have hsT : |s - t₀| ≤ t - t₀ := by
          rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
        have hW1 : ‖fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s‖
            ≤ Real.exp ((K : ℝ) * (t - t₀)) :=
          (norm_fundamentalSolution_le (hAfun z) (hΨ z) (h0Ψ z) s).trans
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsT K.coe_nonneg))
        have hW2 : ‖fundamentalSolution (hAfun z₀) (hΨ z₀) (h0Ψ z₀) s‖
            ≤ Real.exp ((K : ℝ) * (t - t₀)) :=
          (norm_fundamentalSolution_le (hAfun z₀) (hΨ z₀) (h0Ψ z₀) s).trans
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsT K.coe_nonneg))
        have hWd : ‖fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s
              - fundamentalSolution (hAfun z₀) (hΨ z₀) (h0Ψ z₀) s‖
            ≤ (L : ℝ) * Real.exp ((K : ℝ) * (t - t₀)) ^ 2
                * gronwallBound 0 (K : ℝ) 1 (t - t₀) * ‖z - z₀‖ := by
          refine (norm_fundamentalSolution_baseCurve_sub_le hv hΦ h0 hDvlip z z₀
            (hAfun z) (hAfun z₀) (hΨ z) (h0Ψ z) (hΨ z₀) (h0Ψ z₀) (T := t) hs).trans ?_
          calc (L : ℝ) * Real.exp ((K : ℝ) * (t - t₀)) * ‖z - z₀‖
                  * Real.exp ((K : ℝ) * (t - t₀)) * gronwallBound 0 (K : ℝ) 1 (s - t₀)
              = (L : ℝ) * Real.exp ((K : ℝ) * (t - t₀)) ^ 2 * ‖z - z₀‖
                  * gronwallBound 0 (K : ℝ) 1 (s - t₀) := by ring
            _ ≤ (L : ℝ) * Real.exp ((K : ℝ) * (t - t₀)) ^ 2 * ‖z - z₀‖
                  * gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
                apply mul_le_mul_of_nonneg_left
                  (gronwallBound_mono le_rfl zero_le_one K.coe_nonneg (by linarith [hs.2]))
                positivity
            _ = (L : ℝ) * Real.exp ((K : ℝ) * (t - t₀)) ^ 2
                  * gronwallBound 0 (K : ℝ) 1 (t - t₀) * ‖z - z₀‖ := by ring
        exact norm_chainRuleForcing_sub_le h (hCz z s) hW1 hW2
          (norm_secondDerivField_apply_flow_sub_le hv hΦ h0 (hD2vlip s) hsT z z₀) hWd
          L.coe_nonneg (Real.exp_pos _).le (by positivity) (by positivity)
      -- assemble via the inhomogeneous-variation dependence bound
      refine (norm_inhomogVariation_sub_le_of_gap (hAfun z) hV1 hV10 hV2 hV20
        hAgap hV₂bound hFgap (by positivity) htmem).trans_eq ?_
      ring
    have hlip : LipschitzWith ((((L : ℝ) * Real.exp ((K : ℝ) * (t - t₀)))
          * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (t - t₀))
              * gronwallBound 0 (K : ℝ) 1 (t - t₀))
        + ((M : ℝ) * Real.exp ((K : ℝ) * (t - t₀)) ^ 3
            + 2 * (L : ℝ) ^ 2 * Real.exp ((K : ℝ) * (t - t₀)) ^ 3
                * gronwallBound 0 (K : ℝ) 1 (t - t₀)))
        * gronwallBound 0 (K : ℝ) 1 (t - t₀)).toNNReal D₂ := by
      refine LipschitzWith.of_dist_le_mul (fun z z₀ => ?_)
      rw [Real.coe_toNNReal _ hClip0, dist_eq_norm, dist_eq_norm]
      exact hkey z z₀
    exact hlip.continuous
  -- assemble `ContDiff ℝ 2`
  refine ⟨Φ, h0, hΦ, ?_⟩
  have hdiff_df : Differentiable ℝ (fderiv ℝ (fun w => Φ w t)) := by
    rw [hfeq]; exact fun z => (hD2has z).differentiableAt
  have hcont_ddf : Continuous (fderiv ℝ (fderiv ℝ (fun w => Φ w t))) := by
    rw [hfeq, hfeq2]; exact hcont_D₂
  have hone : ContDiff ℝ 1 (fderiv ℝ (fun w => Φ w t)) :=
    contDiff_one_iff_fderiv.mpr ⟨hdiff_df, hcont_ddf⟩
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_fderiv]
  exact ⟨fun z => (hres z).differentiableAt, by rintro ⟨⟩, hone⟩

/-- **Uniform Lipschitz-in-base-point bound for a derivative field along the flow (any order).**  The
codomain-generic form of `norm_secondDerivField_apply_flow_sub_le`: for a uniformly `K`-Lipschitz field
`v`, a flow family `Φ` of `v` anchored at `Φ x t₀ = x`, and *any* seminormed target `F` carrying an
`N`-Lipschitz field `DF s : E → F` (typically an iterated spatial derivative of `v`), the field along
the flow `z ↦ DF s (Φ z s)` moves by at most `N · exp (K T) · ‖z − w‖` for every time `s` with
`|s − t₀| ≤ T`.  Composes the `N`-Lipschitz `DF s` with the uniform flow-Lipschitz bound
`lipschitzWith_flow_apply_of_abs_le` (`exp (K T)`), exactly as `norm_secondDerivField_apply_flow_sub_le`
does for the second derivative.  Specialising `F := E →L[ℝ] (E →L[ℝ] E)` recovers
`norm_secondDerivField_apply_flow_sub_le`; specialising `F` to the third-derivative target
`ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E` gives `norm_thirdDerivField_apply_flow_sub_le`, the
`D³v`-gap size datum of the base-point `ContDiff ℝ 3` bootstrap. -/
theorem norm_field_apply_flow_sub_le
    {F : Type*} [SeminormedAddCommGroup F]
    {Φ : E → ℝ → E} {DF : ℝ → E → F} {N : ℝ≥0} {s T : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (hDF : LipschitzWith N (DF s)) (hsT : |s - t₀| ≤ T) (z w : E) :
    ‖DF s (Φ z s) - DF s (Φ w s)‖ ≤ (N : ℝ) * Real.exp ((K : ℝ) * T) * ‖z - w‖ := by
  have hlip : LipschitzWith (N * (Real.exp ((K : ℝ) * T)).toNNReal) (fun z => DF s (Φ z s)) :=
    hDF.comp (lipschitzWith_flow_apply_of_abs_le hv hΦ h0 hsT)
  have hd := hlip.dist_le_mul z w
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mul, Real.coe_toNNReal _ (Real.exp_pos _).le] at hd
  exact hd

/-- **Uniform Lipschitz-in-base-point bound for the third derivative field along the flow.**  The
third-derivative specialisation of `norm_field_apply_flow_sub_le` (and the third-order analogue of
`norm_secondDerivField_apply_flow_sub_le`): for a uniformly `K`-Lipschitz field `v` with `N`-Lipschitz
*third* spatial derivative `D³v s`, and a flow family `Φ` of `v` anchored at `Φ x t₀ = x`, the
third-derivative field along the flow `z ↦ D³v s (Φ z s)` moves by at most `N · exp (K T) · ‖z − w‖`
for every time `s` with `|s − t₀| ≤ T`.  The third spatial derivative is represented by the canonical
`iteratedFDeriv`-target `ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E`; the curried triple
`E →L[ℝ] E →L[ℝ] E →L[ℝ] E` carries no operator-norm instance in Mathlib v4.29.1.  This is the size
datum for the `D³v`-gap term in the chain-rule forcing perturbation of the base-point
`C⁴`/`ContDiff ℝ 3` bootstrap (continuity of the third fundamental solution). -/
theorem norm_thirdDerivField_apply_flow_sub_le
    {Φ : E → ℝ → E} {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E}
    {N : ℝ≥0} {s T : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (hD3v : LipschitzWith N (D3v s)) (hsT : |s - t₀| ≤ T) (z w : E) :
    ‖D3v s (Φ z s) - D3v s (Φ w s)‖ ≤ (N : ℝ) * Real.exp ((K : ℝ) * T) * ‖z - w‖ :=
  norm_field_apply_flow_sub_le hv hΦ h0 hD3v hsT z w

/-- **Perturbation estimate for the asymmetric composition-forcing operator.**  The higher variational
ODEs produce forcing terms of the shape `((P ∘ A) h) ∘ B` where `P : E →L[ℝ] (E →L[ℝ] E)` is a spatial
derivative of the field and `A`, `B` are resolvent-type operators, *possibly different* — e.g.
`A = D₂` the second fundamental solution and `B = W` the resolvent in the third-variation forcing.
This lemma bounds its response to a joint perturbation of `P`, `A`, `B`: for `‖P₁‖ ≤ p`,
`‖A₁‖, ‖A₂‖ ≤ a`, `‖B₂‖ ≤ b`, `‖P₁ − P₂‖ ≤ dp`, `‖A₁ − A₂‖ ≤ da`, `‖B₁ − B₂‖ ≤ db`,
`‖((P₁ ∘ A₁) h) ∘ B₁ − ((P₂ ∘ A₂) h) ∘ B₂‖ ≤ (dp · a · b + p · da · b + p · a · db) · ‖h‖`.
Specialising `A₁ = B₁ = W₁`, `A₂ = B₂ = W₂` (so `a = b = w`, `da = db = dw`) recovers exactly
`norm_chainRuleForcing_sub_le` (`(dp · w² + 2 · p · w · dw) · ‖h‖`).  Proof: telescope the outer
composition (`comp_sub`/`sub_comp`) into `((P₁∘A₁)h) ∘ (B₁ − B₂) + ((P₁∘A₁)h − (P₂∘A₂)h) ∘ B₂`, then
telescope the inner one `P₁∘A₁ − P₂∘A₂ = P₁∘(A₁−A₂) + (P₁−P₂)∘A₂`, everywhere using
submultiplicativity of the operator norm. -/
theorem norm_bilinearCompForcing_sub_le
    {P₁ P₂ : E →L[ℝ] (E →L[ℝ] E)} {A₁ A₂ B₁ B₂ : E →L[ℝ] E} (h : E)
    {p a b dp da db : ℝ}
    (hP₁ : ‖P₁‖ ≤ p) (hA₁ : ‖A₁‖ ≤ a) (hA₂ : ‖A₂‖ ≤ a) (hB₂ : ‖B₂‖ ≤ b)
    (hPd : ‖P₁ - P₂‖ ≤ dp) (hAd : ‖A₁ - A₂‖ ≤ da) (hBd : ‖B₁ - B₂‖ ≤ db)
    (hp : 0 ≤ p) (ha : 0 ≤ a) (hdp : 0 ≤ dp) (hda : 0 ≤ da) :
    ‖((P₁.comp A₁) h).comp B₁ - ((P₂.comp A₂) h).comp B₂‖
      ≤ (dp * a * b + p * da * b + p * a * db) * ‖h‖ := by
  -- `‖(P₁ ∘ A₁) h‖ ≤ p · a · ‖h‖`
  have hcnorm : ‖(P₁.comp A₁) h‖ ≤ p * a * ‖h‖ := by
    calc ‖(P₁.comp A₁) h‖ ≤ ‖P₁.comp A₁‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖P₁‖ * ‖A₁‖ * ‖h‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
      _ ≤ p * a * ‖h‖ := by gcongr
  -- `‖P₁ ∘ A₁ − P₂ ∘ A₂‖ ≤ p · da + dp · a`
  have hPAd : ‖P₁.comp A₁ - P₂.comp A₂‖ ≤ p * da + dp * a := by
    have hsplit : P₁.comp A₁ - P₂.comp A₂ = P₁.comp (A₁ - A₂) + (P₁ - P₂).comp A₂ := by
      rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]; abel
    calc ‖P₁.comp A₁ - P₂.comp A₂‖
        = ‖P₁.comp (A₁ - A₂) + (P₁ - P₂).comp A₂‖ := by rw [hsplit]
      _ ≤ ‖P₁.comp (A₁ - A₂)‖ + ‖(P₁ - P₂).comp A₂‖ :=
          norm_add_le (P₁.comp (A₁ - A₂)) ((P₁ - P₂).comp A₂)
      _ ≤ ‖P₁‖ * ‖A₁ - A₂‖ + ‖P₁ - P₂‖ * ‖A₂‖ :=
          add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
            (ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ p * da + dp * a := by gcongr
  -- `‖(P₁ ∘ A₁) h − (P₂ ∘ A₂) h‖ ≤ (p · da + dp · a) · ‖h‖`
  have hcd : ‖(P₁.comp A₁) h - (P₂.comp A₂) h‖ ≤ (p * da + dp * a) * ‖h‖ := by
    have hc : (P₁.comp A₁) h - (P₂.comp A₂) h = (P₁.comp A₁ - P₂.comp A₂) h := by
      rw [ContinuousLinearMap.sub_apply]
    calc ‖(P₁.comp A₁) h - (P₂.comp A₂) h‖ = ‖(P₁.comp A₁ - P₂.comp A₂) h‖ := by rw [hc]
      _ ≤ ‖P₁.comp A₁ - P₂.comp A₂‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (p * da + dp * a) * ‖h‖ := by gcongr
  -- telescope the outer composition
  have hGsplit : ((P₁.comp A₁) h).comp B₁ - ((P₂.comp A₂) h).comp B₂
      = ((P₁.comp A₁) h).comp (B₁ - B₂)
        + ((P₁.comp A₁) h - (P₂.comp A₂) h).comp B₂ := by
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]; abel
  have hpa : (0 : ℝ) ≤ p * a * ‖h‖ := by positivity
  have hpda : (0 : ℝ) ≤ (p * da + dp * a) * ‖h‖ := by positivity
  calc ‖((P₁.comp A₁) h).comp B₁ - ((P₂.comp A₂) h).comp B₂‖
      = ‖((P₁.comp A₁) h).comp (B₁ - B₂)
          + ((P₁.comp A₁) h - (P₂.comp A₂) h).comp B₂‖ := by rw [hGsplit]
    _ ≤ ‖((P₁.comp A₁) h).comp (B₁ - B₂)‖
          + ‖((P₁.comp A₁) h - (P₂.comp A₂) h).comp B₂‖ :=
        norm_add_le (((P₁.comp A₁) h).comp (B₁ - B₂))
          (((P₁.comp A₁) h - (P₂.comp A₂) h).comp B₂)
    _ ≤ ‖(P₁.comp A₁) h‖ * ‖B₁ - B₂‖
          + ‖(P₁.comp A₁) h - (P₂.comp A₂) h‖ * ‖B₂‖ :=
        add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
          (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ (p * a * ‖h‖) * db + ((p * da + dp * a) * ‖h‖) * b :=
        add_le_add (mul_le_mul hcnorm hBd (norm_nonneg _) hpa)
          (mul_le_mul hcd hB₂ (norm_nonneg _) hpda)
    _ = (dp * a * b + p * da * b + p * a * db) * ‖h‖ := by ring

/-- **A-priori size bound for the composition-forcing operator.**  The magnitude companion of
`norm_bilinearCompForcing_sub_le`: the composition-forcing `((P ∘ A) h) ∘ B` of the higher variational
ODEs has operator norm `≤ ‖P‖ · ‖A‖ · ‖B‖ · ‖h‖`.  Proof: two applications of operator-norm
submultiplicativity (`opNorm_comp_le`) and the evaluation bound (`le_opNorm`).  Fed the flow bounds
(`‖D²v‖ ≤ C'`, `‖W‖, ‖D₂‖ ≤ …`) this is the size datum `N` of the third-variation forcing that, via the
a-priori estimate `norm_inhomogVariation_le`, bounds the (second) `D₃`-solution — the analogue of the
`‖D²v‖ · ‖W‖²`-bound used to bound the linearised first variation in `norm_linearisedFirstVariation_le`. -/
theorem norm_bilinearCompForcing_le
    (P : E →L[ℝ] (E →L[ℝ] E)) (A B : E →L[ℝ] E) (h : E) :
    ‖((P.comp A) h).comp B‖ ≤ ‖P‖ * ‖A‖ * ‖B‖ * ‖h‖ := by
  calc ‖((P.comp A) h).comp B‖
      ≤ ‖(P.comp A) h‖ * ‖B‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖P.comp A‖ * ‖h‖) * ‖B‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ (‖P‖ * ‖A‖ * ‖h‖) * ‖B‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
          (norm_nonneg _)
    _ = ‖P‖ * ‖A‖ * ‖B‖ * ‖h‖ := by ring

/-- **A-priori size bound for the third-derivative forcing term.**  The magnitude datum for the
third (third-derivative) forcing term `F_C`, the curryLeft/`Fin 1`-represented analogue of
`norm_bilinearCompForcing_le`: for a third derivative `T : E [×3]→L[ℝ] E`, directions `a`, `b`, and a
resolvent `W : E →L[ℝ] E`, the once-and-twice contracted map `e ↦ T[a, b, W e]` — realised as
`(continuousMultilinearCurryFin1 ℝ E E ((T.curryLeft a).curryLeft b)).comp W` (avoiding the
instance-less curried triple) — has operator norm `≤ ‖T‖ · ‖a‖ · ‖b‖ · ‖W‖`.

Proof: `opNorm_comp_le` for the outer `.comp W`, the isometry `continuousMultilinearCurryFin1`
(`LinearIsometryEquiv.norm_map`) turning it into `‖(T.curryLeft a).curryLeft b‖`, then two evaluation
bounds `le_opNorm` each folded through the `curryLeft` isometry
`ContinuousMultilinearMap.curryLeft_norm` (`‖T.curryLeft‖ = ‖T‖`).  Fed the flow bounds
(`‖D³v‖ ≤ C''`, `‖W‖ ≤ exp (K(T−t₀))`, `a = W k`, `b = W h`) this is the size datum `N` of the
third-derivative term that `norm_inhomogVariation_le` turns into an a-priori bound on the third
variation — completing, alongside `norm_bilinearCompForcing_le`, the forcing-size toolkit for all three
`D₃`-forcing terms. -/
theorem norm_thirdDerivForcing_le
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E) (a b : E) (W : E →L[ℝ] E) :
    ‖(continuousMultilinearCurryFin1 ℝ E E ((T.curryLeft a).curryLeft b)).comp W‖
      ≤ ‖T‖ * ‖a‖ * ‖b‖ * ‖W‖ := by
  calc ‖(continuousMultilinearCurryFin1 ℝ E E ((T.curryLeft a).curryLeft b)).comp W‖
      ≤ ‖continuousMultilinearCurryFin1 ℝ E E ((T.curryLeft a).curryLeft b)‖ * ‖W‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖(T.curryLeft a).curryLeft b‖ * ‖W‖ := by rw [LinearIsometryEquiv.norm_map]
    _ ≤ ‖(T.curryLeft a).curryLeft‖ * ‖b‖ * ‖W‖ := by
        gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖T.curryLeft a‖ * ‖b‖ * ‖W‖ := by rw [ContinuousMultilinearMap.curryLeft_norm]
    _ ≤ ‖T.curryLeft‖ * ‖a‖ * ‖b‖ * ‖W‖ := by
        gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖T‖ * ‖a‖ * ‖b‖ * ‖W‖ := by rw [ContinuousMultilinearMap.curryLeft_norm]

/-- **Bilinear-evaluation gap for a bounded operator field.**  The telescoping estimate underlying
every base-point gap computation: for two bounded linear maps `T₁, T₂ : E →L[ℝ] F` (any seminormed
target `F`) evaluated at two points `u₁, u₂`,
`‖T₁ u₁ − T₂ u₂‖ ≤ ‖T₁‖ · ‖u₁ − u₂‖ + ‖T₁ − T₂‖ · ‖u₂‖`.
Proof: `T₁ u₁ − T₂ u₂ = T₁ (u₁ − u₂) + (T₁ − T₂) u₂`, then the triangle inequality and the evaluation
bound `le_opNorm`.  Used to split a product gap into an "operand gap" part and an "operator gap" part;
in the third-variation forcing it turns the once-contracted third derivative
`z ↦ (D³v(Φ z s)).curryLeft (u z)` into `norm_thirdDerivCurryLeft_apply_flow_sub_le`. -/
theorem norm_clm_apply_sub_le {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (T₁ T₂ : E →L[ℝ] F) (u₁ u₂ : E) :
    ‖T₁ u₁ - T₂ u₂‖ ≤ ‖T₁‖ * ‖u₁ - u₂‖ + ‖T₁ - T₂‖ * ‖u₂‖ := by
  have hsplit : T₁ u₁ - T₂ u₂ = T₁ (u₁ - u₂) + (T₁ - T₂) u₂ := by
    rw [map_sub, ContinuousLinearMap.sub_apply]; abel
  calc ‖T₁ u₁ - T₂ u₂‖ = ‖T₁ (u₁ - u₂) + (T₁ - T₂) u₂‖ := by rw [hsplit]
    _ ≤ ‖T₁ (u₁ - u₂)‖ + ‖(T₁ - T₂) u₂‖ := norm_add_le _ _
    _ ≤ ‖T₁‖ * ‖u₁ - u₂‖ + ‖T₁ - T₂‖ * ‖u₂‖ :=
        add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)

/-- **Gap of the once-contracted third derivative field along the flow.**  The size datum for the
`D³v`-term (term 1) of the third-variation forcing.  Differentiating the second-variation forcing in
the base point contracts one slot of the third spatial derivative `D³v(Φ z s)` with a resolvent-type
direction `u`; the resulting field `z ↦ (D³v(Φ z s)).curryLeft u ∈ (E [×2]→L[ℝ] E)` moves, between
base points `z`, `w` and directions `u₁`, `u₂`, by at most
`‖D³v(Φ z s)‖ · ‖u₁ − u₂‖ + N · exp (K T) · ‖z − w‖ · ‖u₂‖`.  Proof: the bilinear-evaluation gap
`norm_clm_apply_sub_le` applied to `T = (D³v(Φ · s)).curryLeft`, with the `curryLeft` isometry
`ContinuousMultilinearMap.curryLeft_norm` turning `‖T‖` into `‖D³v(Φ z s)‖` and `‖T₁ − T₂‖` into
`‖D³v(Φ z s) − D³v(Φ w s)‖`, the latter bounded by `norm_thirdDerivField_apply_flow_sub_le`.  Fed to
the composition-forcing perturbation `norm_bilinearCompForcing_sub_le` (as the operator gap `dp`) this
completes the third-variation forcing gap that `norm_inhomogVariation_sub_le_of_gap` turns into the
continuity of the third fundamental solution. -/
theorem norm_thirdDerivCurryLeft_apply_flow_sub_le
    {Φ : E → ℝ → E} {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E}
    {N : ℝ≥0} {s T : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (hD3v : LipschitzWith N (D3v s)) (hsT : |s - t₀| ≤ T)
    (z w u₁ u₂ : E) :
    ‖(D3v s (Φ z s)).curryLeft u₁ - (D3v s (Φ w s)).curryLeft u₂‖
      ≤ ‖D3v s (Φ z s)‖ * ‖u₁ - u₂‖
        + (N : ℝ) * Real.exp ((K : ℝ) * T) * ‖z - w‖ * ‖u₂‖ := by
  have hbase := norm_clm_apply_sub_le
    (D3v s (Φ z s)).curryLeft (D3v s (Φ w s)).curryLeft u₁ u₂
  have h1 : ‖(D3v s (Φ z s)).curryLeft‖ = ‖D3v s (Φ z s)‖ :=
    ContinuousMultilinearMap.curryLeft_norm _
  have hcs : (D3v s (Φ z s) - D3v s (Φ w s)).curryLeft
      = (D3v s (Φ z s)).curryLeft - (D3v s (Φ w s)).curryLeft :=
    ContinuousLinearMap.ext (congrFun rfl)
  have h2 : ‖(D3v s (Φ z s)).curryLeft - (D3v s (Φ w s)).curryLeft‖
      = ‖D3v s (Φ z s) - D3v s (Φ w s)‖ := by
    rw [← hcs, ContinuousMultilinearMap.curryLeft_norm]
  have h3 : ‖D3v s (Φ z s) - D3v s (Φ w s)‖ ≤ (N : ℝ) * Real.exp ((K : ℝ) * T) * ‖z - w‖ :=
    norm_thirdDerivField_apply_flow_sub_le hv hΦ h0 hD3v hsT z w
  calc ‖(D3v s (Φ z s)).curryLeft u₁ - (D3v s (Φ w s)).curryLeft u₂‖
      ≤ ‖(D3v s (Φ z s)).curryLeft‖ * ‖u₁ - u₂‖
          + ‖(D3v s (Φ z s)).curryLeft - (D3v s (Φ w s)).curryLeft‖ * ‖u₂‖ := hbase
    _ = ‖D3v s (Φ z s)‖ * ‖u₁ - u₂‖
          + ‖D3v s (Φ z s) - D3v s (Φ w s)‖ * ‖u₂‖ := by rw [h1, h2]
    _ ≤ ‖D3v s (Φ z s)‖ * ‖u₁ - u₂‖
          + (N : ℝ) * Real.exp ((K : ℝ) * T) * ‖z - w‖ * ‖u₂‖ := by gcongr

/-- **Existence of the second-order (third) variation** — the `D₃`-analogue of
`exists_hasDerivAt_firstVariation_linearised_dir`, packaging the *existence half* of the base-point
`C³` bootstrap.

Differentiating the linearised first-variation ODE (whose forcing is the chain-rule term
`((D²v(Φ x₀ s) ∘ W) h) ∘ W`, `W = fundamentalSolution`) once more in the base point `x₀` produces a new
inhomogeneous linear variational ODE `V' = A₀ ∘ V + F`, `V t₀ = 0`, with `A₀ s = Dv s (Φ x₀ s)` and a
*three-term* forcing:

* the two **asymmetric composition** terms `((D²v(Φ x₀ s) ∘ W₂) h) ∘ W` and `((D²v(Φ x₀ s) ∘ W) h) ∘ W₂`
  — the outer/inner resolvent `W` differentiated into the *second fundamental solution* curve
  `W₂ s = ∂/∂x₀ (fundamentalSolution) s` in the base direction (supplied here as any continuous curve;
  its concrete construction as a second fundamental solution is a separate piece); and
* an abstract **third-derivative** forcing `F₃` (built from `D³v(Φ x₀ s)` contracted once with a
  resolvent direction — supplied here as any continuous curve, e.g.
  `s ↦ continuousMultilinearCurryFin1 ℝ E E (((D³v(Φ x₀ s)).curryLeft (W s k)).curryLeft (W s h))`).

Existence follows exactly as in the first-variation case: the two asymmetric terms are continuous by
`Continuous.clm_comp`/`Continuous.clm_apply` (from `hD2cont`, the resolvent continuity
`continuous_fundamentalSolution_time`, and `hW2`), so their sum with the continuous `F₃` is a
continuous forcing, and the merely-continuous global existence
`exists_hasDerivAt_inhomogVariation_of_continuous` (the forcing need not be globally bounded) supplies
the solution `V` through `(t₀, 0)`.  This is the `D₃`-solution existence datum that the packaged `D₃`
operator and the second-order Taylor remainder will consume, in the same way
`exists_hasDerivAt_firstVariation_linearised_dir` fed `exists_continuousLinearMap_linearisedVariation`
and `norm_fundamentalSolution_sub_sub_linearVariation_le_sq`. -/
theorem exists_hasDerivAt_secondVariation_linearised_dir [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))} {K : ℝ≥0}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hAcont : Continuous (fun s => Dv s (Φ x₀ s)))
    (hD2cont : Continuous (fun s => D2v s (Φ x₀ s)))
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    {W2 : ℝ → (E →L[ℝ] E)} (hW2 : Continuous W2)
    {F3 : ℝ → (E →L[ℝ] E)} (hF3 : Continuous F3)
    (h : E) :
    ∃ V : ℝ → (E →L[ℝ] E), V t₀ = 0 ∧
      ∀ s, HasDerivAt V
        ((Dv s (Φ x₀ s)).comp (V s)
          + (((D2v s (Φ x₀ s)).comp (W2 s) h).comp (fundamentalSolution hA hΦ' h0' s)
             + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 s)
             + F3 s)) s := by
  have hW : Continuous (fun s => fundamentalSolution hA hΦ' h0' s) :=
    continuous_fundamentalSolution_time hA hΦ' h0'
  have hFa : Continuous fun s =>
      ((D2v s (Φ x₀ s)).comp (W2 s) h).comp (fundamentalSolution hA hΦ' h0' s) :=
    ((hD2cont.clm_comp hW2).clm_apply continuous_const).clm_comp hW
  have hFb : Continuous fun s =>
      ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 s) :=
    ((hD2cont.clm_comp hW).clm_apply continuous_const).clm_comp hW2
  have hFc : Continuous fun s =>
      (((D2v s (Φ x₀ s)).comp (W2 s) h).comp (fundamentalSolution hA hΦ' h0' s)
        + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 s)
        + F3 s) :=
    (hFa.add hFb).add hF3
  exact exists_hasDerivAt_inhomogVariation_of_continuous hA hAcont hFc t₀

/-- **Continuity of the third-derivative forcing term.**  The concrete continuous realisation of the
abstract `F₃` slot in `exists_hasDerivAt_secondVariation_linearised_dir`.  For continuous curves
`D₃ : ℝ → (E [×3]→L[ℝ] E)` (the third spatial derivative along the reference trajectory, in the
canonical `iteratedFDeriv`-target `ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E`) and
`W : ℝ → (E →L[ℝ] E)` (the resolvent), and two directions `k`, `h`, the once-and-twice contracted map
`s ↦ (e ↦ D₃(s)[W s k, W s h, W s e])` — represented, avoiding the instance-less curried triple
`E →L E →L E →L E`, as
`(continuousMultilinearCurryFin1 ℝ E E ((D₃(s).curryLeft (W s k)).curryLeft (W s h))).comp (W s)` — is
continuous.

Proof: `curryLeft` is the underlying map of the isometric equivalence
`continuousMultilinearCurryLeftEquiv` (hence continuous), so each contraction `s ↦ (…).curryLeft (W s ·)`
is `Continuous.clm_apply` of the curried operator against the continuous direction `s ↦ W s ·`; the
final `Fin 1 → linear` isometry `continuousMultilinearCurryFin1` and the outer composition `.comp (W s)`
(`Continuous.clm_comp`) preserve continuity.  This is the `β`/size-carrying forcing term whose gap is
controlled by `norm_thirdDerivCurryLeft_apply_flow_sub_le`. -/
theorem continuous_thirdDerivForcing
    {D3 : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E}
    {W : ℝ → (E →L[ℝ] E)} (hD3 : Continuous D3) (hW : Continuous W) (k h : E) :
    Continuous fun s =>
      (continuousMultilinearCurryFin1 ℝ E E
        (((D3 s).curryLeft (W s k)).curryLeft (W s h))).comp (W s) := by
  have hcL1 : Continuous fun s => (D3 s).curryLeft :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => E) E).continuous.comp hD3
  have hWk : Continuous fun s => W s k := hW.clm_apply continuous_const
  have hWh : Continuous fun s => W s h := hW.clm_apply continuous_const
  have hc1 : Continuous fun s => (D3 s).curryLeft (W s k) := hcL1.clm_apply hWk
  have hcL2 : Continuous fun s => ((D3 s).curryLeft (W s k)).curryLeft :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) E).continuous.comp hc1
  have hc2 : Continuous fun s => ((D3 s).curryLeft (W s k)).curryLeft (W s h) := hcL2.clm_apply hWh
  have hc3 : Continuous fun s =>
      continuousMultilinearCurryFin1 ℝ E E (((D3 s).curryLeft (W s k)).curryLeft (W s h)) :=
    (continuousMultilinearCurryFin1 ℝ E E).continuous.comp hc2
  exact hc3.clm_comp hW

/-- **Existence of the second-order (third) variation with the concrete third-derivative forcing** —
the fully-instantiated `D₃`-analogue of `exists_hasDerivAt_firstVariation_linearised_dir`.  Specialises
`exists_hasDerivAt_secondVariation_linearised_dir` by supplying the abstract third term `F₃` as the
*concrete* once-and-twice contracted third derivative
`s ↦ (continuousMultilinearCurryFin1 ℝ E E ((D³v(Φ x₀ s).curryLeft (W s k)).curryLeft (W s h))).comp (W s)`
(`W = fundamentalSolution`, `e ↦ D³v(Φ x₀ s)[W k, W h, W e]`), whose continuity is
`continuous_thirdDerivForcing`.

Thus, for the reference base point `x₀` with `K`-bounded continuous coefficient `A₀ s = Dv s (Φ x₀ s)`,
continuous second/third derivatives along the trajectory (`hD2cont`, `hD3cont`), resolvent
`W = fundamentalSolution hA hΦ' h0'`, and any continuous second fundamental solution curve `W₂` in the
base direction `k`, the third-variation ODE `V' = A₀ ∘ V + (F_A + F_B + F_C)`, `V t₀ = 0` — with the two
asymmetric composition terms `F_A = ((D²v ∘ W₂) h) ∘ W`, `F_B = ((D²v ∘ W) h) ∘ W₂` and the
third-derivative term `F_C` above — has a global solution `V`.  This is the complete `D₃`-solution
existence datum that the packaged `D₃` operator and the second-order Taylor remainder
`‖(D₂(z) − D₂(x₀)) − D₃(z − x₀)‖ ≤ C‖z − x₀‖²` will consume toward `ContDiff ℝ 3`. -/
theorem exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E} {K : ℝ≥0}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hAcont : Continuous (fun s => Dv s (Φ x₀ s)))
    (hD2cont : Continuous (fun s => D2v s (Φ x₀ s)))
    (hD3cont : Continuous (fun s => D3v s (Φ x₀ s)))
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    {W2 : ℝ → (E →L[ℝ] E)} (hW2 : Continuous W2)
    (k h : E) :
    ∃ V : ℝ → (E →L[ℝ] E), V t₀ = 0 ∧
      ∀ s, HasDerivAt V
        ((Dv s (Φ x₀ s)).comp (V s)
          + (((D2v s (Φ x₀ s)).comp (W2 s) h).comp (fundamentalSolution hA hΦ' h0' s)
             + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 s)
             + (continuousMultilinearCurryFin1 ℝ E E
                 (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                   (fundamentalSolution hA hΦ' h0' s h))).comp
                 (fundamentalSolution hA hΦ' h0' s))) s := by
  have hW : Continuous (fun s => fundamentalSolution hA hΦ' h0' s) :=
    continuous_fundamentalSolution_time hA hΦ' h0'
  have hF3 : Continuous fun s =>
      (continuousMultilinearCurryFin1 ℝ E E
        (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
          (fundamentalSolution hA hΦ' h0' s h))).comp (fundamentalSolution hA hΦ' h0' s) :=
    continuous_thirdDerivForcing hD3cont hW k h
  exact exists_hasDerivAt_secondVariation_linearised_dir x₀ hA hAcont hD2cont hΦ' h0' hW2 hF3 h

/-- **A-priori size bound for the third variation** — the `D₃`-analogue of
`norm_linearisedFirstVariation_le`.  For a solution `V` of the third-variation ODE
`V' = A₀ ∘ V + (F_A + F_B + F_C)`, `V t₀ = 0` (`A₀ s = Dv s (Φ x₀ s)`, the exact forcing produced by
`exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv`), with the second/third derivatives
bounded along the reference trajectory (`‖D²v‖ ≤ C'`, `‖D³v‖ ≤ C''`) and the second fundamental
solution curve bounded on the time interval (`‖W₂ s‖ ≤ N₂`), the time-`t` value obeys
`‖V t‖ ≤ (2·C'·N₂·exp(K(T−t₀))·‖h‖ + C''·exp(3K(T−t₀))·‖k‖·‖h‖) · gronwallBound 0 K 1 (t − t₀)`.

Proof: bound the three forcing terms uniformly on `[t₀, T]` — `F_A`, `F_B` by
`norm_bilinearCompForcing_le` (fed `‖D²v‖ ≤ C'`, `‖W₂‖ ≤ N₂`, and the resolvent bound
`‖W‖ ≤ exp(K(T−t₀))` from `norm_fundamentalSolution_le`), and `F_C` by `norm_thirdDerivForcing_le`
(fed `‖D³v‖ ≤ C''`, `‖W k‖ ≤ exp·‖k‖`, `‖W h‖ ≤ exp·‖h‖`, `‖W‖ ≤ exp`) — sum them by the triangle
inequality (`exp·exp·exp = exp(3·)`), then feed the constant forcing bound to the generic Grönwall
estimate `norm_inhomogVariation_le`.  This is the `N`-datum that, together with the (future) linearity
of `V` in the directions, bounds the packaged `D₃` operator toward `ContDiff ℝ 3`. -/
theorem norm_thirdVariation_le
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E} {K : ℝ≥0}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    {C' C'' N₂ : ℝ} (hC'0 : 0 ≤ C') (hC''0 : 0 ≤ C'') (hN₂0 : 0 ≤ N₂)
    (hC' : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ C') (hC'' : ∀ s, ‖D3v s (Φ x₀ s)‖ ≤ C'')
    {W2 : ℝ → (E →L[ℝ] E)} {T : ℝ} (hW2 : ∀ s ∈ Set.Icc t₀ T, ‖W2 s‖ ≤ N₂)
    (k h : E) {V : ℝ → (E →L[ℝ] E)}
    (hV : ∀ s, HasDerivAt V
      ((Dv s (Φ x₀ s)).comp (V s)
        + (((D2v s (Φ x₀ s)).comp (W2 s) h).comp (fundamentalSolution hA hΦ' h0' s)
           + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 s)
           + (continuousMultilinearCurryFin1 ℝ E E
               (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                 (fundamentalSolution hA hΦ' h0' s h))).comp
               (fundamentalSolution hA hΦ' h0' s))) s)
    (hV0 : V t₀ = 0)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ‖V t‖
      ≤ (2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖
          + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)) * ‖k‖ * ‖h‖)
        * gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
  refine norm_inhomogVariation_le hA hV hV0 ?_ ht
  intro s hs
  have hsabs : |s - t₀| ≤ T - t₀ := by
    rw [abs_of_nonneg (by linarith [hs.1] : (0 : ℝ) ≤ s - t₀)]; linarith [hs.2]
  have hWle : ‖fundamentalSolution hA hΦ' h0' s‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) :=
    (norm_fundamentalSolution_le hA hΦ' h0' s).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsabs K.coe_nonneg))
  have hex0 : (0 : ℝ) ≤ Real.exp ((K : ℝ) * (T - t₀)) := (Real.exp_pos _).le
  have hPle : ‖D2v s (Φ x₀ s)‖ ≤ C' := hC' s
  have hDle : ‖D3v s (Φ x₀ s)‖ ≤ C'' := hC'' s
  have hW2le : ‖W2 s‖ ≤ N₂ := hW2 s hs
  have hWk : ‖fundamentalSolution hA hΦ' h0' s k‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) * ‖k‖ :=
    ((fundamentalSolution hA hΦ' h0' s).le_opNorm k).trans (by gcongr)
  have hWh : ‖fundamentalSolution hA hΦ' h0' s h‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖ :=
    ((fundamentalSolution hA hΦ' h0' s).le_opNorm h).trans (by gcongr)
  have hexp3 : Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
        * Real.exp ((K : ℝ) * (T - t₀)) = Real.exp (3 * (K : ℝ) * (T - t₀)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have htA : ‖((D2v s (Φ x₀ s)).comp (W2 s) h).comp (fundamentalSolution hA hΦ' h0' s)‖
      ≤ C' * N₂ * Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖ := by
    refine (norm_bilinearCompForcing_le (D2v s (Φ x₀ s)) (W2 s)
      (fundamentalSolution hA hΦ' h0' s) h).trans ?_
    gcongr
  have htB : ‖((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 s)‖
      ≤ C' * Real.exp ((K : ℝ) * (T - t₀)) * N₂ * ‖h‖ := by
    refine (norm_bilinearCompForcing_le (D2v s (Φ x₀ s))
      (fundamentalSolution hA hΦ' h0' s) (W2 s) h).trans ?_
    gcongr
  have htC : ‖(continuousMultilinearCurryFin1 ℝ E E
        (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
          (fundamentalSolution hA hΦ' h0' s h))).comp (fundamentalSolution hA hΦ' h0' s)‖
      ≤ C'' * (Real.exp ((K : ℝ) * (T - t₀)) * ‖k‖) * (Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖)
          * Real.exp ((K : ℝ) * (T - t₀)) := by
    refine (norm_thirdDerivForcing_le (D3v s (Φ x₀ s)) (fundamentalSolution hA hΦ' h0' s k)
      (fundamentalSolution hA hΦ' h0' s h) (fundamentalSolution hA hΦ' h0' s)).trans ?_
    gcongr
  calc ‖((D2v s (Φ x₀ s)).comp (W2 s) h).comp (fundamentalSolution hA hΦ' h0' s)
          + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 s)
          + (continuousMultilinearCurryFin1 ℝ E E
              (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                (fundamentalSolution hA hΦ' h0' s h))).comp (fundamentalSolution hA hΦ' h0' s)‖
      ≤ ‖((D2v s (Φ x₀ s)).comp (W2 s) h).comp (fundamentalSolution hA hΦ' h0' s)‖
          + ‖((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 s)‖
          + ‖(continuousMultilinearCurryFin1 ℝ E E
              (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                (fundamentalSolution hA hΦ' h0' s h))).comp (fundamentalSolution hA hΦ' h0' s)‖ :=
        norm_add₃_le
    _ ≤ C' * N₂ * Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖
          + C' * Real.exp ((K : ℝ) * (T - t₀)) * N₂ * ‖h‖
          + C'' * (Real.exp ((K : ℝ) * (T - t₀)) * ‖k‖) * (Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖)
              * Real.exp ((K : ℝ) * (T - t₀)) :=
        add_le_add (add_le_add htA htB) htC
    _ = 2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖
          + C'' * (Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
              * Real.exp ((K : ℝ) * (T - t₀))) * ‖k‖ * ‖h‖ := by ring
    _ = 2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖
          + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)) * ‖k‖ * ‖h‖ := by rw [hexp3]

/-- **Additivity of the third variation in the direction `h`.**  For a fixed base direction `k` and
fixed second fundamental solution curve `W₂`, the third variation `V^h` (the solution of the
three-term third-variation ODE for direction `h`) is *additive* in `h`: `V^{h₁+h₂} t = V^{h₁} t + V^{h₂} t`.

The whole three-term forcing `F(h) = ((D²v ∘ W₂) h) ∘ W + ((D²v ∘ W) h) ∘ W₂ +
(curryFin1 ((D³v.curryLeft (W k)).curryLeft (W h))) ∘ W` is *linear* in `h` (`h` enters each term
through a single bounded-linear application — `map_add` on the operator applications and on
`curryLeft`/`curryFin1`, then `add_comp`), so `F(h₁+h₂) = F(h₁) + F(h₂)`; the superposition
`hasDerivAt_inhomogVariation_add` and Grönwall uniqueness `inhomogVariation_unique` then identify
`V^{h₁+h₂}` with `V^{h₁} + V^{h₂}`.  The additive half of packaging `h ↦ D₃(k, h)` as a bounded linear
map (the `D₃`-analogue of `linearVariation_perturbation_add_eq`). -/
theorem thirdVariation_perturbation_add_eq
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E} {K : ℝ≥0}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    {W2 : ℝ → (E →L[ℝ] E)} (k h₁ h₂ : E) {V₁ V₂ V₁₂ : ℝ → (E →L[ℝ] E)}
    (hV₁ : ∀ s, HasDerivAt V₁
      ((Dv s (Φ x₀ s)).comp (V₁ s)
        + (((D2v s (Φ x₀ s)).comp (W2 s) h₁).comp (fundamentalSolution hA hΦ' h0' s)
           + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h₁).comp (W2 s)
           + (continuousMultilinearCurryFin1 ℝ E E
               (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                 (fundamentalSolution hA hΦ' h0' s h₁))).comp
               (fundamentalSolution hA hΦ' h0' s))) s)
    (hV₂ : ∀ s, HasDerivAt V₂
      ((Dv s (Φ x₀ s)).comp (V₂ s)
        + (((D2v s (Φ x₀ s)).comp (W2 s) h₂).comp (fundamentalSolution hA hΦ' h0' s)
           + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h₂).comp (W2 s)
           + (continuousMultilinearCurryFin1 ℝ E E
               (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                 (fundamentalSolution hA hΦ' h0' s h₂))).comp
               (fundamentalSolution hA hΦ' h0' s))) s)
    (hV₁₂ : ∀ s, HasDerivAt V₁₂
      ((Dv s (Φ x₀ s)).comp (V₁₂ s)
        + (((D2v s (Φ x₀ s)).comp (W2 s) (h₁ + h₂)).comp (fundamentalSolution hA hΦ' h0' s)
           + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) (h₁ + h₂)).comp (W2 s)
           + (continuousMultilinearCurryFin1 ℝ E E
               (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                 (fundamentalSolution hA hΦ' h0' s (h₁ + h₂)))).comp
               (fundamentalSolution hA hΦ' h0' s))) s)
    (hV₁0 : V₁ t₀ = 0) (hV₂0 : V₂ t₀ = 0) (hV₁₂0 : V₁₂ t₀ = 0)
    (t : ℝ) : V₁₂ t = V₁ t + V₂ t := by
  have hV₁₂' : ∀ s, HasDerivAt V₁₂
      ((Dv s (Φ x₀ s)).comp (V₁₂ s)
        + ((((D2v s (Φ x₀ s)).comp (W2 s) h₁).comp (fundamentalSolution hA hΦ' h0' s)
            + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h₁).comp (W2 s)
            + (continuousMultilinearCurryFin1 ℝ E E
                (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                  (fundamentalSolution hA hΦ' h0' s h₁))).comp
                (fundamentalSolution hA hΦ' h0' s))
          + (((D2v s (Φ x₀ s)).comp (W2 s) h₂).comp (fundamentalSolution hA hΦ' h0' s)
            + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h₂).comp (W2 s)
            + (continuousMultilinearCurryFin1 ℝ E E
                (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                  (fundamentalSolution hA hΦ' h0' s h₂))).comp
                (fundamentalSolution hA hΦ' h0' s)))) s := by
    intro s
    have hmap :
        (((D2v s (Φ x₀ s)).comp (W2 s) (h₁ + h₂)).comp (fundamentalSolution hA hΦ' h0' s)
          + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) (h₁ + h₂)).comp (W2 s)
          + (continuousMultilinearCurryFin1 ℝ E E
              (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                (fundamentalSolution hA hΦ' h0' s (h₁ + h₂)))).comp
              (fundamentalSolution hA hΦ' h0' s))
        = (((D2v s (Φ x₀ s)).comp (W2 s) h₁).comp (fundamentalSolution hA hΦ' h0' s)
            + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h₁).comp (W2 s)
            + (continuousMultilinearCurryFin1 ℝ E E
                (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                  (fundamentalSolution hA hΦ' h0' s h₁))).comp
                (fundamentalSolution hA hΦ' h0' s))
          + (((D2v s (Φ x₀ s)).comp (W2 s) h₂).comp (fundamentalSolution hA hΦ' h0' s)
            + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h₂).comp (W2 s)
            + (continuousMultilinearCurryFin1 ℝ E E
                (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                  (fundamentalSolution hA hΦ' h0' s h₂))).comp
                (fundamentalSolution hA hΦ' h0' s)) := by
      simp only [map_add, ContinuousLinearMap.add_comp]; abel
    have := hV₁₂ s
    rwa [hmap] at this
  have hsum := hasDerivAt_inhomogVariation_add hV₁ hV₂
  have h0 : V₁₂ t₀ = (fun r => V₁ r + V₂ r) t₀ := by simp [hV₁₂0, hV₁0, hV₂0]
  exact inhomogVariation_unique hA hV₁₂' hsum h0 t

/-- **Homogeneity of the third variation in the direction `h`.**  The scalar-homogeneous companion of
`thirdVariation_perturbation_add_eq`: `V^{c • h} t = c • V^h t`.  The three-term forcing is homogeneous
in `h` (`map_smul` on the operator applications and `curryLeft`/`curryFin1`, `smul_comp`, `smul_add`),
so `F(c • h) = c • F(h)`; homogeneity `hasDerivAt_inhomogVariation_smul` and uniqueness
`inhomogVariation_unique` finish.  The homogeneous half of packaging `h ↦ D₃(k, h)` as a bounded linear
map. -/
theorem thirdVariation_perturbation_smul_eq
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E} {K : ℝ≥0}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    {W2 : ℝ → (E →L[ℝ] E)} (k : E) (c : ℝ) (h : E) {V Vc : ℝ → (E →L[ℝ] E)}
    (hV : ∀ s, HasDerivAt V
      ((Dv s (Φ x₀ s)).comp (V s)
        + (((D2v s (Φ x₀ s)).comp (W2 s) h).comp (fundamentalSolution hA hΦ' h0' s)
           + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 s)
           + (continuousMultilinearCurryFin1 ℝ E E
               (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                 (fundamentalSolution hA hΦ' h0' s h))).comp
               (fundamentalSolution hA hΦ' h0' s))) s)
    (hVc : ∀ s, HasDerivAt Vc
      ((Dv s (Φ x₀ s)).comp (Vc s)
        + (((D2v s (Φ x₀ s)).comp (W2 s) (c • h)).comp (fundamentalSolution hA hΦ' h0' s)
           + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) (c • h)).comp (W2 s)
           + (continuousMultilinearCurryFin1 ℝ E E
               (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                 (fundamentalSolution hA hΦ' h0' s (c • h)))).comp
               (fundamentalSolution hA hΦ' h0' s))) s)
    (hV0 : V t₀ = 0) (hVc0 : Vc t₀ = 0)
    (t : ℝ) : Vc t = c • V t := by
  have hVc' : ∀ s, HasDerivAt Vc
      ((Dv s (Φ x₀ s)).comp (Vc s)
        + c • (((D2v s (Φ x₀ s)).comp (W2 s) h).comp (fundamentalSolution hA hΦ' h0' s)
            + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 s)
            + (continuousMultilinearCurryFin1 ℝ E E
                (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                  (fundamentalSolution hA hΦ' h0' s h))).comp
                (fundamentalSolution hA hΦ' h0' s))) s := by
    intro s
    have hmap :
        (((D2v s (Φ x₀ s)).comp (W2 s) (c • h)).comp (fundamentalSolution hA hΦ' h0' s)
          + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) (c • h)).comp (W2 s)
          + (continuousMultilinearCurryFin1 ℝ E E
              (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                (fundamentalSolution hA hΦ' h0' s (c • h)))).comp
              (fundamentalSolution hA hΦ' h0' s))
        = c • (((D2v s (Φ x₀ s)).comp (W2 s) h).comp (fundamentalSolution hA hΦ' h0' s)
            + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 s)
            + (continuousMultilinearCurryFin1 ℝ E E
                (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                  (fundamentalSolution hA hΦ' h0' s h))).comp
                (fundamentalSolution hA hΦ' h0' s)) := by
      simp only [map_smul, ContinuousLinearMap.smul_comp, smul_add]
    have := hVc s
    rwa [hmap] at this
  have hsmul := hasDerivAt_inhomogVariation_smul c hV
  have h0 : Vc t₀ = (fun r => c • V r) t₀ := by simp [hVc0, hV0]
  exact inhomogVariation_unique hA hVc' hsmul h0 t

/-- **The packaged third-variation operator `D₃(k)`** — the `D₃`-analogue of
`exists_continuousLinearMap_linearisedVariation`, packaging `h ↦ D₃(k, h)` as a *bounded linear map*
for a fixed base direction `k` and second fundamental solution curve `W₂`.

There is a bounded operator `D₃k : E →L[ℝ] (E →L[ℝ] E)` whose value on any direction `h` is the time-`t`
value of *any* solution `V` of the three-term third-variation ODE
`V' = A₀ ∘ V + (((D²v ∘ W₂) h) ∘ W + ((D²v ∘ W) h) ∘ W₂ +
(curryFin1 ((D³v.curryLeft (W k)).curryLeft (W h))) ∘ W)`, `V t₀ = 0`.

Assembly (as in the `C²` packaging): the direction-parameterised solution `h ↦ V^h`
(`exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv`) is additive and homogeneous in `h`
(`thirdVariation_perturbation_add_eq`/`_smul_eq`) and bounded with
`‖V^h t‖ ≤ ((2·C'·N₂·exp(K(T−t₀)) + C''·exp(3K(T−t₀))·‖k‖) · gronwallBound 0 K 1 (t−t₀)) · ‖h‖`
(`norm_thirdVariation_le`, factoring out `‖h‖`), so `LinearMap.mkContinuous` yields the bounded
operator; the value is independent of the chosen solution by the linear-ODE uniqueness
`inhomogVariation_unique`.  This is the operator `D₃(k)` that, fed with the (future) second-order Taylor
remainder `‖(D₂(z) − D₂(x₀)) − D₃(z − x₀)‖ ≤ C‖z − x₀‖²`, will give the spatial `C³` regularity of the
flow's resolvent (`ContDiff ℝ 3`). -/
theorem exists_continuousLinearMap_thirdVariation [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E} {K : ℝ≥0}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hAcont : Continuous (fun s => Dv s (Φ x₀ s)))
    (hD2cont : Continuous (fun s => D2v s (Φ x₀ s)))
    (hD3cont : Continuous (fun s => D3v s (Φ x₀ s)))
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    {C' C'' N₂ : ℝ} (hC'0 : 0 ≤ C') (hC''0 : 0 ≤ C'') (hN₂0 : 0 ≤ N₂)
    (hC' : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ C') (hC'' : ∀ s, ‖D3v s (Φ x₀ s)‖ ≤ C'')
    {W2 : ℝ → (E →L[ℝ] E)} (hW2cont : Continuous W2)
    {T : ℝ} (hW2 : ∀ s ∈ Set.Icc t₀ T, ‖W2 s‖ ≤ N₂)
    (k : E) {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ∃ D₃k : E →L[ℝ] (E →L[ℝ] E),
      ∀ (h : E) (V : ℝ → (E →L[ℝ] E)), V t₀ = 0 →
        (∀ s, HasDerivAt V
          ((Dv s (Φ x₀ s)).comp (V s)
            + (((D2v s (Φ x₀ s)).comp (W2 s) h).comp (fundamentalSolution hA hΦ' h0' s)
               + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 s)
               + (continuousMultilinearCurryFin1 ℝ E E
                   (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                     (fundamentalSolution hA hΦ' h0' s h))).comp
                   (fundamentalSolution hA hΦ' h0' s))) s) →
        D₃k h = V t := by
  choose Vsol hVsol0 hVsolderiv using fun h =>
    exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv x₀ hA hAcont hD2cont hD3cont
      hΦ' h0' hW2cont k h
  have hadd : ∀ h₁ h₂ : E, Vsol (h₁ + h₂) t = Vsol h₁ t + Vsol h₂ t := fun h₁ h₂ =>
    thirdVariation_perturbation_add_eq x₀ hA hΦ' h0' k h₁ h₂
      (hVsolderiv h₁) (hVsolderiv h₂) (hVsolderiv (h₁ + h₂))
      (hVsol0 h₁) (hVsol0 h₂) (hVsol0 (h₁ + h₂)) t
  have hsmul : ∀ (c : ℝ) (h : E), Vsol (c • h) t = c • Vsol h t := fun c h =>
    thirdVariation_perturbation_smul_eq x₀ hA hΦ' h0' k c h
      (hVsolderiv h) (hVsolderiv (c • h)) (hVsol0 h) (hVsol0 (c • h)) t
  have hbound : ∀ h : E,
      ‖Vsol h t‖
        ≤ (2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀))
              + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)) * ‖k‖)
            * gronwallBound 0 (K : ℝ) 1 (t - t₀) * ‖h‖ :=
    fun h => by
      have hle := norm_thirdVariation_le x₀ hA hΦ' h0' hC'0 hC''0 hN₂0 hC' hC'' hW2 k h
        (hVsolderiv h) (hVsol0 h) ht
      calc ‖Vsol h t‖
          ≤ (2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖
              + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)) * ‖k‖ * ‖h‖)
            * gronwallBound 0 (K : ℝ) 1 (t - t₀) := hle
        _ = (2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀))
              + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)) * ‖k‖)
            * gronwallBound 0 (K : ℝ) 1 (t - t₀) * ‖h‖ := by ring
  refine ⟨LinearMap.mkContinuous
    { toFun := fun h => Vsol h t
      map_add' := hadd
      map_smul' := fun c h => by simpa using hsmul c h }
    ((2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀))
        + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)) * ‖k‖)
      * gronwallBound 0 (K : ℝ) 1 (t - t₀)) hbound, ?_⟩
  intro h V hV0 hVderiv
  have huniq : Vsol h t = V t :=
    inhomogVariation_unique hA (hVsolderiv h) hVderiv (by rw [hVsol0 h, hV0]) t
  simpa using huniq

/-- **The packaged third-variation operator `D₃(k)` with its operator-norm bound.**  Strengthens
`exists_continuousLinearMap_thirdVariation` by exposing the a-priori bound
`‖D₃k‖ ≤ (2·C'·N₂·exp(K(T−t₀)) + C''·exp(3K(T−t₀))·‖k‖) · gronwallBound 0 K 1 (t−t₀)` alongside the value
characterisation.

The bound is `ContinuousLinearMap.opNorm_le_bound`: for each direction `h`, choosing the third-variation
solution `V^h` (`exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv`), the value
characterisation gives `D₃k h = V^h t`, and `norm_thirdVariation_le` bounds `‖V^h t‖ ≤ C · ‖h‖`
(factoring `‖h‖`).  Nonnegativity of the operator bound uses `0 ≤ gronwallBound 0 K 1 (t−t₀)` (from
`t₀ ≤ t`).  This is the size datum `‖D₃‖ ≤ …` that the second-order Taylor remainder for the resolvent's
second derivative will require. -/
theorem exists_continuousLinearMap_thirdVariation_norm_le [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E} {K : ℝ≥0}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hAcont : Continuous (fun s => Dv s (Φ x₀ s)))
    (hD2cont : Continuous (fun s => D2v s (Φ x₀ s)))
    (hD3cont : Continuous (fun s => D3v s (Φ x₀ s)))
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    {C' C'' N₂ : ℝ} (hC'0 : 0 ≤ C') (hC''0 : 0 ≤ C'') (hN₂0 : 0 ≤ N₂)
    (hC' : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ C') (hC'' : ∀ s, ‖D3v s (Φ x₀ s)‖ ≤ C'')
    {W2 : ℝ → (E →L[ℝ] E)} (hW2cont : Continuous W2)
    {T : ℝ} (hW2 : ∀ s ∈ Set.Icc t₀ T, ‖W2 s‖ ≤ N₂)
    (k : E) {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ∃ D₃k : E →L[ℝ] (E →L[ℝ] E),
      ‖D₃k‖ ≤ (2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀))
            + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)) * ‖k‖)
          * gronwallBound 0 (K : ℝ) 1 (t - t₀) ∧
      ∀ (h : E) (V : ℝ → (E →L[ℝ] E)), V t₀ = 0 →
        (∀ s, HasDerivAt V
          ((Dv s (Φ x₀ s)).comp (V s)
            + (((D2v s (Φ x₀ s)).comp (W2 s) h).comp (fundamentalSolution hA hΦ' h0' s)
               + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 s)
               + (continuousMultilinearCurryFin1 ℝ E E
                   (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                     (fundamentalSolution hA hΦ' h0' s h))).comp
                   (fundamentalSolution hA hΦ' h0' s))) s) →
        D₃k h = V t := by
  obtain ⟨D₃k, hD₃k⟩ := exists_continuousLinearMap_thirdVariation x₀ hA hAcont hD2cont hD3cont
    hΦ' h0' hC'0 hC''0 hN₂0 hC' hC'' hW2cont hW2 k ht
  have hgron : 0 ≤ gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
    have hx : 0 ≤ t - t₀ := sub_nonneg.mpr ht.1
    rcases eq_or_lt_of_le K.coe_nonneg with hK | hK
    · rw [← hK]; simp [gronwallBound_K0, hx]
    · rw [gronwallBound_of_K_ne_0 (ne_of_gt hK)]
      have h1 : 0 ≤ Real.exp ((K : ℝ) * (t - t₀)) - 1 :=
        by linarith [Real.one_le_exp (by positivity : (0 : ℝ) ≤ (K : ℝ) * (t - t₀))]
      positivity
  have hfac : (0 : ℝ) ≤ 2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀))
      + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)) * ‖k‖ := by
    have h1 : (0 : ℝ) ≤ 2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC'0) hN₂0) (Real.exp_pos _).le
    have h2 : (0 : ℝ) ≤ C'' * Real.exp (3 * (K : ℝ) * (T - t₀)) * ‖k‖ :=
      mul_nonneg (mul_nonneg hC''0 (Real.exp_pos _).le) (norm_nonneg _)
    linarith
  have hC0 : (0 : ℝ) ≤ (2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀))
      + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)) * ‖k‖)
      * gronwallBound 0 (K : ℝ) 1 (t - t₀) := mul_nonneg hfac hgron
  refine ⟨D₃k, ?_, hD₃k⟩
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 (fun h => ?_)
  obtain ⟨Vh, hVh0, hVhderiv⟩ :=
    exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv x₀ hA hAcont hD2cont hD3cont
      hΦ' h0' hW2cont k h
  rw [hD₃k h Vh hVh0 hVhderiv]
  have hle := norm_thirdVariation_le x₀ hA hΦ' h0' hC'0 hC''0 hN₂0 hC' hC'' hW2 k h
    hVhderiv hVh0 ht
  calc ‖Vh t‖
      ≤ (2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖
          + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)) * ‖k‖ * ‖h‖)
        * gronwallBound 0 (K : ℝ) 1 (t - t₀) := hle
    _ = (2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀))
          + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)) * ‖k‖)
        * gronwallBound 0 (K : ℝ) 1 (t - t₀) * ‖h‖ := by ring

/-- **Additivity of `curryLeft` in the multilinear map.**  `ContinuousMultilinearMap.curryLeft` is the
forward map of the continuous linear equivalence `continuousMultilinearCurryLeftEquiv`, hence linear;
this records the additive rewrite `(f + g).curryLeft = f.curryLeft + g.curryLeft` as a usable `simp`
lemma (the plain `def` form of `curryLeft` is not matched by `map_add` directly).  Used to push the
base-direction `k` through the *outer* `curryLeft` of the third-derivative forcing term `F_C` when
proving the `k`-linearity of the third variation. -/
theorem curryLeft_add {n : ℕ} {Ei : Fin (n + 1) → Type*}
    [∀ i, NormedAddCommGroup (Ei i)] [∀ i, NormedSpace ℝ (Ei i)]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f g : ContinuousMultilinearMap ℝ Ei G) :
    (f + g).curryLeft = f.curryLeft + g.curryLeft :=
  map_add (continuousMultilinearCurryLeftEquiv ℝ Ei G) f g

/-- **Homogeneity of `curryLeft` in the multilinear map.**  The scalar-homogeneous companion of
`curryLeft_add`: `(c • f).curryLeft = c • f.curryLeft`, again from the linearity of
`continuousMultilinearCurryLeftEquiv`.  Used to push the scalar factor through the outer `curryLeft` of
`F_C` when proving the `k`-homogeneity of the third variation. -/
theorem curryLeft_smul {n : ℕ} {Ei : Fin (n + 1) → Type*}
    [∀ i, NormedAddCommGroup (Ei i)] [∀ i, NormedSpace ℝ (Ei i)]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (c : ℝ) (f : ContinuousMultilinearMap ℝ Ei G) :
    (c • f).curryLeft = c • f.curryLeft :=
  map_smul (continuousMultilinearCurryLeftEquiv ℝ Ei G) c f

/-- **Additivity of the third variation in the base direction `k`.**  The `k`-analogue of
`thirdVariation_perturbation_add_eq` (which is additive in the inner direction `h`): if the second
fundamental solution curve `W₂` is *itself additive* in the base direction
(`W₂ (k₁ + k₂) s = W₂ k₁ s + W₂ k₂ s` — as it is when `W₂ k = ∂_{x₀} W · k`, linear in `k`), then the
whole three-term third-variation forcing
`F_A + F_B + F_C = ((D²v ∘ W₂ k) h) ∘ W + ((D²v ∘ W) h) ∘ (W₂ k) +
(curryFin1 ((D³v.curryLeft (W k)).curryLeft (W h))) ∘ W` is additive in `k`:
`F_A + F_B` split via the additivity of `W₂ k` (`comp_add`/`add_comp`/`add_apply`), and `F_C` via the
additivity of `W k` (`map_add`, `W` a bounded operator) pushed through the two `curryLeft` layers
(`map_add` on the inner `D³v.curryLeft`, `curryLeft_add` on the outer).  Uniqueness of the linear ODE
(`inhomogVariation_unique`, coefficient `A₀ s = Dv s (Φ x₀ s)`) then identifies
`V^{k₁+k₂} = V^{k₁} + V^{k₂}`.  The additive half of packaging the full bilinear operator
`(k, h) ↦ D₃(k, h)` toward the base-point `C³` Taylor remainder. -/
theorem thirdVariation_baseDir_add_eq
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E} {K : ℝ≥0}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    {W2 : E → ℝ → (E →L[ℝ] E)}
    (hW2add : ∀ k₁ k₂ s, W2 (k₁ + k₂) s = W2 k₁ s + W2 k₂ s)
    (k₁ k₂ h : E) {V₁ V₂ V₁₂ : ℝ → (E →L[ℝ] E)}
    (hV₁ : ∀ s, HasDerivAt V₁
      ((Dv s (Φ x₀ s)).comp (V₁ s)
        + (((D2v s (Φ x₀ s)).comp (W2 k₁ s) h).comp (fundamentalSolution hA hΦ' h0' s)
           + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 k₁ s)
           + (continuousMultilinearCurryFin1 ℝ E E
               (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k₁)).curryLeft
                 (fundamentalSolution hA hΦ' h0' s h))).comp
               (fundamentalSolution hA hΦ' h0' s))) s)
    (hV₂ : ∀ s, HasDerivAt V₂
      ((Dv s (Φ x₀ s)).comp (V₂ s)
        + (((D2v s (Φ x₀ s)).comp (W2 k₂ s) h).comp (fundamentalSolution hA hΦ' h0' s)
           + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 k₂ s)
           + (continuousMultilinearCurryFin1 ℝ E E
               (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k₂)).curryLeft
                 (fundamentalSolution hA hΦ' h0' s h))).comp
               (fundamentalSolution hA hΦ' h0' s))) s)
    (hV₁₂ : ∀ s, HasDerivAt V₁₂
      ((Dv s (Φ x₀ s)).comp (V₁₂ s)
        + (((D2v s (Φ x₀ s)).comp (W2 (k₁ + k₂) s) h).comp (fundamentalSolution hA hΦ' h0' s)
           + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 (k₁ + k₂) s)
           + (continuousMultilinearCurryFin1 ℝ E E
               (((D3v s (Φ x₀ s)).curryLeft
                     (fundamentalSolution hA hΦ' h0' s (k₁ + k₂))).curryLeft
                 (fundamentalSolution hA hΦ' h0' s h))).comp
               (fundamentalSolution hA hΦ' h0' s))) s)
    (hV₁0 : V₁ t₀ = 0) (hV₂0 : V₂ t₀ = 0) (hV₁₂0 : V₁₂ t₀ = 0)
    (t : ℝ) : V₁₂ t = V₁ t + V₂ t := by
  have hV₁₂' : ∀ s, HasDerivAt V₁₂
      ((Dv s (Φ x₀ s)).comp (V₁₂ s)
        + ((((D2v s (Φ x₀ s)).comp (W2 k₁ s) h).comp (fundamentalSolution hA hΦ' h0' s)
            + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 k₁ s)
            + (continuousMultilinearCurryFin1 ℝ E E
                (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k₁)).curryLeft
                  (fundamentalSolution hA hΦ' h0' s h))).comp
                (fundamentalSolution hA hΦ' h0' s))
          + (((D2v s (Φ x₀ s)).comp (W2 k₂ s) h).comp (fundamentalSolution hA hΦ' h0' s)
            + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 k₂ s)
            + (continuousMultilinearCurryFin1 ℝ E E
                (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k₂)).curryLeft
                  (fundamentalSolution hA hΦ' h0' s h))).comp
                (fundamentalSolution hA hΦ' h0' s)))) s := by
    intro s
    have hmap :
        (((D2v s (Φ x₀ s)).comp (W2 (k₁ + k₂) s) h).comp (fundamentalSolution hA hΦ' h0' s)
          + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 (k₁ + k₂) s)
          + (continuousMultilinearCurryFin1 ℝ E E
              (((D3v s (Φ x₀ s)).curryLeft
                    (fundamentalSolution hA hΦ' h0' s (k₁ + k₂))).curryLeft
                (fundamentalSolution hA hΦ' h0' s h))).comp
              (fundamentalSolution hA hΦ' h0' s))
        = (((D2v s (Φ x₀ s)).comp (W2 k₁ s) h).comp (fundamentalSolution hA hΦ' h0' s)
            + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 k₁ s)
            + (continuousMultilinearCurryFin1 ℝ E E
                (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k₁)).curryLeft
                  (fundamentalSolution hA hΦ' h0' s h))).comp
                (fundamentalSolution hA hΦ' h0' s))
          + (((D2v s (Φ x₀ s)).comp (W2 k₂ s) h).comp (fundamentalSolution hA hΦ' h0' s)
            + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 k₂ s)
            + (continuousMultilinearCurryFin1 ℝ E E
                (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k₂)).curryLeft
                  (fundamentalSolution hA hΦ' h0' s h))).comp
                (fundamentalSolution hA hΦ' h0' s)) := by
      rw [hW2add k₁ k₂ s]
      simp only [map_add, curryLeft_add, ContinuousLinearMap.comp_add,
        ContinuousLinearMap.add_comp, ContinuousLinearMap.add_apply]
      abel
    have := hV₁₂ s
    rwa [hmap] at this
  have hsum := hasDerivAt_inhomogVariation_add hV₁ hV₂
  have h0 : V₁₂ t₀ = (fun r => V₁ r + V₂ r) t₀ := by simp [hV₁₂0, hV₁0, hV₂0]
  exact inhomogVariation_unique hA hV₁₂' hsum h0 t

/-- **Homogeneity of the third variation in the base direction `k`.**  The scalar-homogeneous companion
of `thirdVariation_baseDir_add_eq`: if `W₂` is homogeneous in the base direction
(`W₂ (c • k) s = c • W₂ k s`), then `V^{c • k} t = c • V^k t`.  The three-term forcing is homogeneous in
`k` — `F_A`, `F_B` via `comp_smul`/`smul_comp`/`smul_apply` on the homogeneous `W₂ k`, and `F_C` via
`map_smul` on `W k` pushed through the two `curryLeft` layers (`map_smul` on the inner `D³v.curryLeft`,
`curryLeft_smul` on the outer) — so `hasDerivAt_inhomogVariation_smul` and `inhomogVariation_unique`
identify `V^{c • k}` with `c • V^k`.  The homogeneous half of packaging the full bilinear operator
`(k, h) ↦ D₃(k, h)`. -/
theorem thirdVariation_baseDir_smul_eq
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E} {K : ℝ≥0}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    {W2 : E → ℝ → (E →L[ℝ] E)}
    (hW2smul : ∀ (c : ℝ) (k : E) (s : ℝ), W2 (c • k) s = c • W2 k s)
    (k : E) (c : ℝ) (h : E) {V Vc : ℝ → (E →L[ℝ] E)}
    (hV : ∀ s, HasDerivAt V
      ((Dv s (Φ x₀ s)).comp (V s)
        + (((D2v s (Φ x₀ s)).comp (W2 k s) h).comp (fundamentalSolution hA hΦ' h0' s)
           + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 k s)
           + (continuousMultilinearCurryFin1 ℝ E E
               (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                 (fundamentalSolution hA hΦ' h0' s h))).comp
               (fundamentalSolution hA hΦ' h0' s))) s)
    (hVc : ∀ s, HasDerivAt Vc
      ((Dv s (Φ x₀ s)).comp (Vc s)
        + (((D2v s (Φ x₀ s)).comp (W2 (c • k) s) h).comp (fundamentalSolution hA hΦ' h0' s)
           + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 (c • k) s)
           + (continuousMultilinearCurryFin1 ℝ E E
               (((D3v s (Φ x₀ s)).curryLeft
                     (fundamentalSolution hA hΦ' h0' s (c • k))).curryLeft
                 (fundamentalSolution hA hΦ' h0' s h))).comp
               (fundamentalSolution hA hΦ' h0' s))) s)
    (hV0 : V t₀ = 0) (hVc0 : Vc t₀ = 0)
    (t : ℝ) : Vc t = c • V t := by
  have hVc' : ∀ s, HasDerivAt Vc
      ((Dv s (Φ x₀ s)).comp (Vc s)
        + c • (((D2v s (Φ x₀ s)).comp (W2 k s) h).comp (fundamentalSolution hA hΦ' h0' s)
            + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 k s)
            + (continuousMultilinearCurryFin1 ℝ E E
                (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                  (fundamentalSolution hA hΦ' h0' s h))).comp
                (fundamentalSolution hA hΦ' h0' s))) s := by
    intro s
    have hmap :
        (((D2v s (Φ x₀ s)).comp (W2 (c • k) s) h).comp (fundamentalSolution hA hΦ' h0' s)
          + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 (c • k) s)
          + (continuousMultilinearCurryFin1 ℝ E E
              (((D3v s (Φ x₀ s)).curryLeft
                    (fundamentalSolution hA hΦ' h0' s (c • k))).curryLeft
                (fundamentalSolution hA hΦ' h0' s h))).comp
              (fundamentalSolution hA hΦ' h0' s))
        = c • (((D2v s (Φ x₀ s)).comp (W2 k s) h).comp (fundamentalSolution hA hΦ' h0' s)
            + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 k s)
            + (continuousMultilinearCurryFin1 ℝ E E
                (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                  (fundamentalSolution hA hΦ' h0' s h))).comp
                (fundamentalSolution hA hΦ' h0' s)) := by
      rw [hW2smul c k s]
      simp only [map_smul, curryLeft_smul, ContinuousLinearMap.comp_smul,
        ContinuousLinearMap.smul_comp, ContinuousLinearMap.smul_apply, smul_add]
    have := hVc s
    rwa [hmap] at this
  have hsmul := hasDerivAt_inhomogVariation_smul c hV
  have h0 : Vc t₀ = (fun r => c • V r) t₀ := by simp [hVc0, hV0]
  exact inhomogVariation_unique hA hVc' hsmul h0 t

/-- **The packaged bilinear third-variation operator `D₃`** — the full `(k, h)`-bilinear operator
`D₃ : E →L[ℝ] (E →L[ℝ] (E →L[ℝ] E))`, whose value `D₃ k h` is the time-`t` third variation for base
direction `k` and inner direction `h`.

This upgrades `exists_continuousLinearMap_thirdVariation` (which packages only the inner
`h ↦ D₃(k, h)` for a *fixed* base direction `k`) to a bounded operator in *both* directions.  The inner
`h`-linearity gives, for each `k`, the operator `D₃(k) : E →L[ℝ] (E →L[ℝ] E)`
(`exists_continuousLinearMap_thirdVariation_norm_le`, fed the `‖k‖`-scaled curve bound `‖W₂ k s‖ ≤ N₂·‖k‖`
so its operator norm is `≤ (2·C'·N₂·exp(K(T−t₀)) + C''·exp(3K(T−t₀)))·gronwallBound 0 K 1 (t−t₀)·‖k‖`,
i.e. genuinely `O(‖k‖)`).  The outer `k`-linearity is the new content: `k ↦ D₃(k)` is additive and
homogeneous by `thirdVariation_baseDir_add_eq`/`_smul_eq` (through the value characterisation
`D₃(k) h = V^{k,h} t` and ODE uniqueness), and bounded by the `‖k‖`-scaled norm estimate, so
`LinearMap.mkContinuous` yields the bilinear operator.  The value is independent of the chosen solution
by `inhomogVariation_unique`.

This is the fully-packaged `D₃` — bilinear in `(k, h)` — that the base-point `C³` Taylor remainder
`‖(D₂(z) − D₂(x₀)) − D₃(z − x₀)‖ ≤ C‖z − x₀‖²` (with `k = z − x₀`) will compare against, en route to the
spatial `C³` regularity of the flow's resolvent (`ContDiff ℝ 3`). -/
theorem exists_continuousLinearMap_thirdVariation_bilinear [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E} {K : ℝ≥0}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hAcont : Continuous (fun s => Dv s (Φ x₀ s)))
    (hD2cont : Continuous (fun s => D2v s (Φ x₀ s)))
    (hD3cont : Continuous (fun s => D3v s (Φ x₀ s)))
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    {C' C'' N₂ : ℝ} (hC'0 : 0 ≤ C') (hC''0 : 0 ≤ C'') (hN₂0 : 0 ≤ N₂)
    (hC' : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ C') (hC'' : ∀ s, ‖D3v s (Φ x₀ s)‖ ≤ C'')
    {W2 : E → ℝ → (E →L[ℝ] E)} (hW2cont : ∀ k, Continuous (W2 k))
    (hW2add : ∀ k₁ k₂ s, W2 (k₁ + k₂) s = W2 k₁ s + W2 k₂ s)
    (hW2smul : ∀ (c : ℝ) (k : E) (s : ℝ), W2 (c • k) s = c • W2 k s)
    {T : ℝ} (hW2 : ∀ (k : E), ∀ s ∈ Set.Icc t₀ T, ‖W2 k s‖ ≤ N₂ * ‖k‖)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ∃ D₃ : E →L[ℝ] (E →L[ℝ] (E →L[ℝ] E)),
      ∀ (k h : E) (V : ℝ → (E →L[ℝ] E)), V t₀ = 0 →
        (∀ s, HasDerivAt V
          ((Dv s (Φ x₀ s)).comp (V s)
            + (((D2v s (Φ x₀ s)).comp (W2 k s) h).comp (fundamentalSolution hA hΦ' h0' s)
               + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 k s)
               + (continuousMultilinearCurryFin1 ℝ E E
                   (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                     (fundamentalSolution hA hΦ' h0' s h))).comp
                   (fundamentalSolution hA hΦ' h0' s))) s) →
        D₃ k h = V t := by
  -- per base direction `k`: the inner operator `D₃(k)` with its `‖k‖`-scaled operator-norm bound
  choose D₃ hD₃nb hD₃char using fun k =>
    exists_continuousLinearMap_thirdVariation_norm_le x₀ hA hAcont hD2cont hD3cont hΦ' h0'
      hC'0 hC''0 (mul_nonneg hN₂0 (norm_nonneg k)) hC' hC'' (hW2cont k) (hW2 k) k ht
  -- outer additivity `D₃(k₁+k₂) = D₃ k₁ + D₃ k₂`
  have hadd : ∀ k₁ k₂ : E, D₃ (k₁ + k₂) = D₃ k₁ + D₃ k₂ := by
    intro k₁ k₂
    refine ContinuousLinearMap.ext (fun h => ?_)
    obtain ⟨V₁, hV₁0, hV₁d⟩ := exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv
      x₀ hA hAcont hD2cont hD3cont hΦ' h0' (hW2cont k₁) k₁ h
    obtain ⟨V₂, hV₂0, hV₂d⟩ := exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv
      x₀ hA hAcont hD2cont hD3cont hΦ' h0' (hW2cont k₂) k₂ h
    obtain ⟨V₁₂, hV₁₂0, hV₁₂d⟩ := exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv
      x₀ hA hAcont hD2cont hD3cont hΦ' h0' (hW2cont (k₁ + k₂)) (k₁ + k₂) h
    rw [ContinuousLinearMap.add_apply, hD₃char (k₁ + k₂) h V₁₂ hV₁₂0 hV₁₂d,
      hD₃char k₁ h V₁ hV₁0 hV₁d, hD₃char k₂ h V₂ hV₂0 hV₂d]
    exact thirdVariation_baseDir_add_eq x₀ hA hΦ' h0' hW2add k₁ k₂ h
      hV₁d hV₂d hV₁₂d hV₁0 hV₂0 hV₁₂0 t
  -- outer homogeneity `D₃(c • k) = c • D₃ k`
  have hsmul : ∀ (c : ℝ) (k : E), D₃ (c • k) = c • D₃ k := by
    intro c k
    refine ContinuousLinearMap.ext (fun h => ?_)
    obtain ⟨V, hV0, hVd⟩ := exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv
      x₀ hA hAcont hD2cont hD3cont hΦ' h0' (hW2cont k) k h
    obtain ⟨Vc, hVc0, hVcd⟩ := exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv
      x₀ hA hAcont hD2cont hD3cont hΦ' h0' (hW2cont (c • k)) (c • k) h
    rw [ContinuousLinearMap.smul_apply, hD₃char (c • k) h Vc hVc0 hVcd,
      hD₃char k h V hV0 hVd]
    exact thirdVariation_baseDir_smul_eq x₀ hA hΦ' h0' hW2smul k c h hVd hVcd hV0 hVc0 t
  -- outer operator-norm bound, linear in `‖k‖`
  have hbound : ∀ k : E, ‖D₃ k‖
      ≤ ((2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀))
            + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)))
          * gronwallBound 0 (K : ℝ) 1 (t - t₀)) * ‖k‖ := by
    intro k
    refine (hD₃nb k).trans_eq ?_
    ring
  refine ⟨LinearMap.mkContinuous
    { toFun := D₃
      map_add' := hadd
      map_smul' := fun c k => by simpa using hsmul c k }
    ((2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀))
        + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)))
      * gronwallBound 0 (K : ℝ) 1 (t - t₀)) hbound, ?_⟩
  intro k h V hV0 hVderiv
  simpa using hD₃char k h V hV0 hVderiv

/-- **Second-order (Taylor) remainder scaffold: reduction to a forcing gap.**  The generic Grönwall
scaffold for the base-point `C³` Taylor remainder — the `D₃`-analogue of the shape of
`norm_fundamentalSolution_sub_sub_linearVariation_le_sq`, phrased at the level of *inhomogeneous
variations* so that the concrete `D₂`/`D₃` instantiation is deferred.

Given three anchored inhomogeneous variations sharing the reference coefficient `A₀` for the *second*
and *third*, and a possibly-different coefficient `A₁` for the *first*:
* `V₁` solves `V' = A₁ ∘ V + F₁`, `V t₀ = 0` (the linearised first variation at the *perturbed* base
  point — coefficient `A₁ = Dv(Φ z)`, forcing `F₁`);
* `V₀` solves `V' = A₀ ∘ V + F₀`, `V t₀ = 0` (the linearised first variation at the *reference* base
  point — coefficient `A₀ = Dv(Φ x₀)`, forcing `F₀`);
* `V₃` solves `V' = A₀ ∘ V + F₃`, `V t₀ = 0` (the *third* variation — same reference coefficient `A₀`,
  the packaged `D₃` forcing `F₃`),

the difference `(V₁ − V₀) − V₃` obeys `‖(V₁ t − V₀ t) − V₃ t‖ ≤ β · gronwallBound 0 K 1 (t − t₀)`, where
`β` bounds the **forcing gap** `((A₁ − A₀) ∘ V₁ + (F₁ − F₀)) − F₃` on the tube `[t₀, T]`.

Proof: the exact difference `W = (V₁ − V₀) − V₃` solves the `A₀`-coefficient inhomogeneous ODE
`W' = A₀ ∘ W + (((A₁ − A₀) ∘ V₁ + (F₁ − F₀)) − F₃)`, `W t₀ = 0` — obtained from `(hV₁.sub hV₀).sub hV₃`
by the algebraic rearrangement `A₁ ∘ V₁ = A₀ ∘ V₁ + (A₁ − A₀) ∘ V₁` (`comp_sub`/`sub_comp`, `abel`) — so
the a-priori bound `norm_inhomogVariation_le` (coefficient `A₀` is `K`-bounded) fed the forcing gap `β`
gives the estimate.  The remaining second-order content — that the forcing gap is genuinely
`O(‖z − x₀‖² · ‖h‖)`, i.e. that the packaged `D₃` forcing `F₃` is the correct linearisation of
`(A₁ − A₀) ∘ V₁ + (F₁ − F₀)` in `z − x₀` — is isolated into the single hypothesis `hβ`, exactly the
`β`-gap that the built forcing-gap toolkit (`norm_bilinearCompForcing_sub_le`,
`norm_thirdDerivCurryLeft_apply_flow_sub_le`, …) is designed to supply. -/
theorem norm_inhomogVariation_sub_sub_le_of_forcingGap
    {A₁ A₀ F₁ F₀ F₃ V₁ V₀ V₃ : ℝ → (E →L[ℝ] E)}
    (hA₀ : ∀ s, ‖A₀ s‖₊ ≤ K)
    (hV₁ : ∀ s, HasDerivAt V₁ ((A₁ s).comp (V₁ s) + F₁ s) s) (hV₁0 : V₁ t₀ = 0)
    (hV₀ : ∀ s, HasDerivAt V₀ ((A₀ s).comp (V₀ s) + F₀ s) s) (hV₀0 : V₀ t₀ = 0)
    (hV₃ : ∀ s, HasDerivAt V₃ ((A₀ s).comp (V₃ s) + F₃ s) s) (hV₃0 : V₃ t₀ = 0)
    {β T : ℝ}
    (hβ : ∀ s ∈ Set.Icc t₀ T,
      ‖((A₁ s - A₀ s).comp (V₁ s) + (F₁ s - F₀ s)) - F₃ s‖ ≤ β)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ‖(V₁ t - V₀ t) - V₃ t‖ ≤ β * gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
  have hWderiv : ∀ s, HasDerivAt (fun r => (V₁ r - V₀ r) - V₃ r)
      ((A₀ s).comp ((V₁ s - V₀ s) - V₃ s)
        + (((A₁ s - A₀ s).comp (V₁ s) + (F₁ s - F₀ s)) - F₃ s)) s := by
    intro s
    have h := ((hV₁ s).sub (hV₀ s)).sub (hV₃ s)
    have heq :
        (A₁ s).comp (V₁ s) + F₁ s - ((A₀ s).comp (V₀ s) + F₀ s)
            - ((A₀ s).comp (V₃ s) + F₃ s)
        = (A₀ s).comp ((V₁ s - V₀ s) - V₃ s)
          + (((A₁ s - A₀ s).comp (V₁ s) + (F₁ s - F₀ s)) - F₃ s) := by
      simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
      abel
    rwa [heq] at h
  have hW0 : (fun r => (V₁ r - V₀ r) - V₃ r) t₀ = 0 := by simp [hV₁0, hV₀0, hV₃0]
  exact norm_inhomogVariation_le hA₀ hWderiv hW0 hβ ht

/-- **Base-point Lipschitz continuity of the linearised first-variation curve (the second fundamental
solution as a curve).**  The `C³`-layer curve-level analogue of the `C²` time-`t`-value continuity of
the second fundamental solution: for the two linearised first-variation curves in a common direction
`h`, one at base point `z` (`Vz`: coefficient `A(z) s = Dv s (Φ z s)`, chain-rule forcing
`((D²v(Φ z s) ∘ W_z) h) ∘ W_z`, resolvent `W_z = D_x Φ_s^{A(z)} = fundamentalSolution hAz hΦ₁ h1`) and
one at base point `x₀` (`Vx`, the analogue at `x₀`), the whole curve difference is `O(‖z − x₀‖ · ‖h‖)`
uniformly on the forward tube `[t₀, T]`:
`‖Vz t − Vx t‖ ≤ exp(K(T−t₀))³ · (M + 3·L·C'·gronwallBound 0 K 1 (T−t₀)) · ‖z − x₀‖ · ‖h‖ ·
gronwallBound 0 K 1 (t − t₀)`.

Unlike the inline continuity buried in `exists_flow_contDiff_two_of_lipschitz_secondDeriv` (which only
extracts the time-`t` value `‖D₂ z h − D₂ x₀ h‖`), this exposes the full curve estimate as a standalone
reusable lemma — the `‖V₁ − V₀‖` size datum that the base-point second-order Taylor analysis of the
`C³` layer (the `hβ` forcing gap of `norm_inhomogVariation_sub_sub_le_of_forcingGap`) consumes for the
cross term `(A₁ − A₀) ∘ (V₁ − V₀)`.

Proof: `norm_inhomogVariation_sub_le_of_gap` (the coefficient-and-forcing-gap Grönwall estimate) fed
the coefficient gap `α = L·exp(K(T−t₀))·‖z−x₀‖` (`norm_derivField_apply_flow_sub_le`), the second-
solution size `N = C'·exp(2K(T−t₀))·‖h‖·gronwallBound 0 K 1 (T−t₀)` on `Vx`
(`norm_linearisedFirstVariation_le` + `gronwallBound_mono`), and the forcing gap `β`
(`norm_chainRuleForcing_sub_le` fed `‖D²v‖ ≤ C'`, the resolvent bound `‖W‖ ≤ exp` from
`norm_fundamentalSolution_le`, the `D²v`-gap `norm_secondDerivField_apply_flow_sub_le`, and the
resolvent base-gap `norm_fundamentalSolution_baseCurve_sub_le`); the messy `(α·N + β)·gronwall`
constant collapses to the clean `exp³·(M + 3LC'g)` form by `Real.exp_add` (`exp(2·) = exp(·)²`) and
`ring`. -/
theorem norm_linearisedFirstVariation_baseCurve_sub_le
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {L M : ℝ≥0} {C' : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hDvlip : ∀ s, LipschitzWith L (Dv s)) (hD2vlip : ∀ s, LipschitzWith M (D2v s))
    (z x₀ : E)
    (hAz : ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K) (hAx : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hC'0 : 0 ≤ C') (hC'z : ∀ s, ‖D2v s (Φ z s)‖ ≤ C') (hC'x : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ C')
    {Φ₁ Φ₂ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h1 : ∀ x, Φ₁ x t₀ = x)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h2 : ∀ x, Φ₂ x t₀ = x)
    (h : E) {T : ℝ}
    {Vz Vx : ℝ → (E →L[ℝ] E)}
    (hVz : ∀ s, HasDerivAt Vz
      ((Dv s (Φ z s)).comp (Vz s)
        + ((D2v s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h1 s) h).comp
            (fundamentalSolution hAz hΦ₁ h1 s)) s)
    (hVz0 : Vz t₀ = 0)
    (hVx : ∀ s, HasDerivAt Vx
      ((Dv s (Φ x₀ s)).comp (Vx s)
        + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) h).comp
            (fundamentalSolution hAx hΦ₂ h2 s)) s)
    (hVx0 : Vx t₀ = 0)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ‖Vz t - Vx t‖
      ≤ Real.exp ((K : ℝ) * (T - t₀)) ^ 3
          * ((M : ℝ) + 3 * (L : ℝ) * C' * gronwallBound 0 (K : ℝ) 1 (T - t₀))
          * ‖z - x₀‖ * ‖h‖ * gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
  -- Coefficient gap `α = L · exp(K(T−t₀)) · ‖z − x₀‖`.
  have hAgap : ∀ s ∈ Set.Icc t₀ T,
      ‖Dv s (Φ z s) - Dv s (Φ x₀ s)‖
        ≤ (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖ := by
    intro s hs
    have hsT : |s - t₀| ≤ T - t₀ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
    exact norm_derivField_apply_flow_sub_le hv hΦ h0 (hDvlip s) hsT z x₀
  -- Second-solution size `N = C' · exp(2K(T−t₀)) · ‖h‖ · gronwallBound 0 K 1 (T−t₀)`.
  have hVxbound : ∀ s ∈ Set.Icc t₀ T,
      ‖Vx s‖
        ≤ C' * Real.exp (2 * (K : ℝ) * (T - t₀)) * ‖h‖ * gronwallBound 0 (K : ℝ) 1 (T - t₀) := by
    intro s hs
    refine (norm_linearisedFirstVariation_le x₀ hAx hΦ₂ h2 hC'0 hC'x h hVx hVx0 hs).trans ?_
    have hmono : gronwallBound 0 (K : ℝ) 1 (s - t₀) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
      gronwallBound_mono (le_refl (0 : ℝ)) zero_le_one K.coe_nonneg (by linarith [hs.2])
    have hpre : (0 : ℝ) ≤ C' * Real.exp (2 * (K : ℝ) * (T - t₀)) * ‖h‖ :=
      mul_nonneg (mul_nonneg hC'0 (Real.exp_pos _).le) (norm_nonneg _)
    exact mul_le_mul_of_nonneg_left hmono hpre
  -- Forcing gap `β = (dp·w² + 2·C'·w·dw) · ‖h‖`.
  have hFgap : ∀ s ∈ Set.Icc t₀ T,
      ‖((D2v s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h1 s) h).comp
              (fundamentalSolution hAz hΦ₁ h1 s)
            - ((D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) h).comp
                (fundamentalSolution hAx hΦ₂ h2 s)‖
        ≤ ((M : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖
              * Real.exp ((K : ℝ) * (T - t₀)) ^ 2
            + 2 * C' * Real.exp ((K : ℝ) * (T - t₀))
                * ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖
                    * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
          * ‖h‖ := by
    intro s hs
    have hsT : |s - t₀| ≤ T - t₀ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
    have hexpmono : Real.exp ((K : ℝ) * |s - t₀|) ≤ Real.exp ((K : ℝ) * (T - t₀)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsT K.coe_nonneg)
    have hwz : ‖fundamentalSolution hAz hΦ₁ h1 s‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) :=
      (norm_fundamentalSolution_le hAz hΦ₁ h1 s).trans hexpmono
    have hwx : ‖fundamentalSolution hAx hΦ₂ h2 s‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) :=
      (norm_fundamentalSolution_le hAx hΦ₂ h2 s).trans hexpmono
    have hdp : ‖D2v s (Φ z s) - D2v s (Φ x₀ s)‖
        ≤ (M : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖ :=
      norm_secondDerivField_apply_flow_sub_le hv hΦ h0 (hD2vlip s) hsT z x₀
    have hgnn : (0 : ℝ) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
      gronwallBound_zero_one_nonneg K.coe_nonneg (sub_nonneg.mpr (le_trans hs.1 hs.2))
    have hdw : ‖fundamentalSolution hAz hΦ₁ h1 s - fundamentalSolution hAx hΦ₂ h2 s‖
        ≤ (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖
            * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀) := by
      refine (norm_fundamentalSolution_baseCurve_sub_le hv hΦ h0 hDvlip z x₀ hAz hAx
        hΦ₁ h1 hΦ₂ h2 hs).trans ?_
      have hmono : gronwallBound 0 (K : ℝ) 1 (s - t₀) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
        gronwallBound_mono (le_refl (0 : ℝ)) zero_le_one K.coe_nonneg (by linarith [hs.2])
      exact mul_le_mul_of_nonneg_left hmono (by positivity)
    exact norm_chainRuleForcing_sub_le h (hC'z s) hwz hwx hdp hdw hC'0 (Real.exp_pos _).le
      (by positivity) (mul_nonneg (by positivity) hgnn)
  -- Assemble via the coefficient-and-forcing-gap Grönwall estimate, then collapse the constant.
  have hα : (0 : ℝ) ≤ (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖ := by positivity
  refine (norm_inhomogVariation_sub_le_of_gap hAz hVz hVz0 hVx hVx0 hAgap hVxbound hFgap hα ht).trans
    (le_of_eq ?_)
  have he2 : Real.exp (2 * (K : ℝ) * (T - t₀)) = Real.exp ((K : ℝ) * (T - t₀)) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [he2]; ring

/-- **Second-order remainder of the coefficient-times-variation forcing term
`(A₁ − A₀) ∘ V₁`.**  In the base-point second-order Taylor analysis of the `C³` layer, the difference
curve `V₁ − V₀` of the two linearised first variations picks up the extra forcing
`Ψ = (A₁ − A₀) ∘ V₁ + (F₁ − F₀)` (relative to the reference `A₀`-coefficient ODE), and the leading
(linear-in-`z − x₀`) part of the first summand is `(D²v(Φ x₀ s)[W_x (z − x₀)]) ∘ V₀`
(`W_x = D_x Φ_s^{A(x₀)}` the resolvent, `V₀ = Vx` the second fundamental solution curve in direction
`h`).  This lemma is the design-independent quadratic Taylor bound isolating that linear part: for
`s ∈ [t₀, T]`,
`‖(Dv(Φ z s) − Dv(Φ x₀ s)) ∘ Vz s − ((D²v(Φ x₀ s) ∘ W_x s)(z − x₀)) ∘ Vx s‖ ≤ C · ‖z − x₀‖² · ‖h‖`.

Proof: telescope `P ∘ Vz − Q ∘ Vx = P ∘ (Vz − Vx) + (P − Q) ∘ Vx` (`comp_sub`/`sub_comp`) with
`P = Dv(Φ z) − Dv(Φ x₀)`, `Q = (D²v(Φ x₀) ∘ W_x)(z − x₀)`, so `P − Q` is exactly the field-Taylor
defect of `norm_derivField_sub_sub_comp_fundamentalSolution_le_sq` (`‖P − Q‖ = O(‖z − x₀‖²)`); bound
the cross term by the coefficient gap `‖P‖ ≤ L·exp·‖z − x₀‖` (`norm_derivField_apply_flow_sub_le`) times
the curve gap `‖Vz − Vx‖ = O(‖z − x₀‖·‖h‖)` (`norm_linearisedFirstVariation_baseCurve_sub_le`), and the
defect term by `‖P − Q‖·‖Vx‖` with `‖Vx‖ = O(‖h‖)` (`norm_linearisedFirstVariation_le`), both `t`-window
factors pushed to the endpoint by `gronwallBound_mono`.  This is one of the design-independent `O(‖z −
x₀‖²·‖h‖)` remainder pieces of the `hβ` forcing gap of `norm_inhomogVariation_sub_sub_le_of_forcingGap`
(it does not depend on how the packaged `D₃` forcing `F₃` distributes the leading term). -/
theorem norm_coeffVariation_sub_secondDerivComp_le_sq
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {L M : ℝ≥0} {C' : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ) (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2v : ∀ s ξ, HasFDerivAt (Dv s) (D2v s ξ) ξ) (hD2vlip : ∀ s, LipschitzWith M (D2v s))
    (z x₀ : E)
    (hAz : ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K) (hAx : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hC'0 : 0 ≤ C') (hC'z : ∀ s, ‖D2v s (Φ z s)‖ ≤ C') (hC'x : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ C')
    {Φ₁ Φ₂ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h1 : ∀ x, Φ₁ x t₀ = x)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h2 : ∀ x, Φ₂ x t₀ = x)
    (h : E) {T : ℝ}
    {Vz Vx : ℝ → (E →L[ℝ] E)}
    (hVz : ∀ s, HasDerivAt Vz
      ((Dv s (Φ z s)).comp (Vz s)
        + ((D2v s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h1 s) h).comp
            (fundamentalSolution hAz hΦ₁ h1 s)) s)
    (hVz0 : Vz t₀ = 0)
    (hVx : ∀ s, HasDerivAt Vx
      ((Dv s (Φ x₀ s)).comp (Vx s)
        + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) h).comp
            (fundamentalSolution hAx hΦ₂ h2 s)) s)
    (hVx0 : Vx t₀ = 0)
    {s : ℝ} (hs : s ∈ Set.Icc t₀ T) :
    ‖(Dv s (Φ z s) - Dv s (Φ x₀ s)).comp (Vz s)
        - ((D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) (z - x₀)).comp (Vx s)‖
      ≤ (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖
          * (Real.exp ((K : ℝ) * (T - t₀)) ^ 3
              * ((M : ℝ) + 3 * (L : ℝ) * C' * gronwallBound 0 (K : ℝ) 1 (T - t₀))
              * ‖z - x₀‖ * ‖h‖ * gronwallBound 0 (K : ℝ) 1 (T - t₀))
        + ((M : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
              + C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                  * gronwallBound 0 (K : ℝ) 1 (T - t₀))) * ‖z - x₀‖ ^ 2
          * (C' * Real.exp (2 * (K : ℝ) * (T - t₀)) * ‖h‖ * gronwallBound 0 (K : ℝ) 1 (T - t₀)) := by
  have hg : (0 : ℝ) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
    gronwallBound_zero_one_nonneg K.coe_nonneg (sub_nonneg.mpr (le_trans hs.1 hs.2))
  have hgmono : gronwallBound 0 (K : ℝ) 1 (s - t₀) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
    gronwallBound_mono (le_refl (0 : ℝ)) zero_le_one K.coe_nonneg (by linarith [hs.2])
  have hsT : |s - t₀| ≤ T - t₀ := by
    rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
  -- Coefficient gap `‖P‖ = ‖Dv(Φ z) − Dv(Φ x₀)‖ ≤ L·exp·‖z − x₀‖`.
  have hAg : ‖Dv s (Φ z s) - Dv s (Φ x₀ s)‖
      ≤ (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖ :=
    norm_derivField_apply_flow_sub_le hv hΦ h0 (hDvlip s) hsT z x₀
  -- Curve gap `‖Vz − Vx‖ ≤ exp³·(M + 3LC'g)·‖z − x₀‖·‖h‖·g` (uniform on the tube).
  have hVg : ‖Vz s - Vx s‖
      ≤ Real.exp ((K : ℝ) * (T - t₀)) ^ 3
          * ((M : ℝ) + 3 * (L : ℝ) * C' * gronwallBound 0 (K : ℝ) 1 (T - t₀))
          * ‖z - x₀‖ * ‖h‖ * gronwallBound 0 (K : ℝ) 1 (T - t₀) := by
    refine (norm_linearisedFirstVariation_baseCurve_sub_le hv hΦ h0 hDvlip hD2vlip z x₀ hAz hAx
      hC'0 hC'z hC'x hΦ₁ h1 hΦ₂ h2 h hVz hVz0 hVx hVx0 hs).trans ?_
    have hMLC : (0 : ℝ) ≤ (M : ℝ) + 3 * (L : ℝ) * C' * gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
      add_nonneg (by positivity) (mul_nonneg (mul_nonneg (by positivity) hC'0) hg)
    have hpre : (0 : ℝ) ≤ Real.exp ((K : ℝ) * (T - t₀)) ^ 3
        * ((M : ℝ) + 3 * (L : ℝ) * C' * gronwallBound 0 (K : ℝ) 1 (T - t₀))
        * ‖z - x₀‖ * ‖h‖ :=
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hMLC) (norm_nonneg _)) (norm_nonneg _)
    exact mul_le_mul_of_nonneg_left hgmono hpre
  -- Field-Taylor defect `‖P − Q‖ ≤ C_RA·‖z − x₀‖²`.
  have hRA : ‖Dv s (Φ z s) - Dv s (Φ x₀ s)
        - (D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) (z - x₀)‖
      ≤ ((M : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
          + C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
              * gronwallBound 0 (K : ℝ) 1 (T - t₀))) * ‖z - x₀‖ ^ 2 :=
    norm_derivField_sub_sub_comp_fundamentalSolution_le_sq hv hΦ h0 hDv hDvlip hD2v hD2vlip
      x₀ hAx hC'0 hC'x hΦ₂ h2 z hs
  -- Reference curve size `‖Vx‖ ≤ C'·exp2·‖h‖·g` (uniform on the tube).
  have hV0 : ‖Vx s‖
      ≤ C' * Real.exp (2 * (K : ℝ) * (T - t₀)) * ‖h‖ * gronwallBound 0 (K : ℝ) 1 (T - t₀) := by
    refine (norm_linearisedFirstVariation_le x₀ hAx hΦ₂ h2 hC'0 hC'x h hVx hVx0 hs).trans ?_
    have hpre : (0 : ℝ) ≤ C' * Real.exp (2 * (K : ℝ) * (T - t₀)) * ‖h‖ :=
      mul_nonneg (mul_nonneg hC'0 (Real.exp_pos _).le) (norm_nonneg _)
    exact mul_le_mul_of_nonneg_left hgmono hpre
  -- Telescope and combine.
  have hsplit : (Dv s (Φ z s) - Dv s (Φ x₀ s)).comp (Vz s)
        - ((D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) (z - x₀)).comp (Vx s)
      = (Dv s (Φ z s) - Dv s (Φ x₀ s)).comp (Vz s - Vx s)
        + (Dv s (Φ z s) - Dv s (Φ x₀ s)
            - (D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) (z - x₀)).comp (Vx s) := by
    simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]; abel
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · calc ‖(Dv s (Φ z s) - Dv s (Φ x₀ s)).comp (Vz s - Vx s)‖
        ≤ ‖Dv s (Φ z s) - Dv s (Φ x₀ s)‖ * ‖Vz s - Vx s‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖
            * (Real.exp ((K : ℝ) * (T - t₀)) ^ 3
                * ((M : ℝ) + 3 * (L : ℝ) * C' * gronwallBound 0 (K : ℝ) 1 (T - t₀))
                * ‖z - x₀‖ * ‖h‖ * gronwallBound 0 (K : ℝ) 1 (T - t₀)) :=
          mul_le_mul hAg hVg (norm_nonneg _) (by positivity)
  · calc ‖(Dv s (Φ z s) - Dv s (Φ x₀ s)
              - (D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) (z - x₀)).comp (Vx s)‖
        ≤ ‖Dv s (Φ z s) - Dv s (Φ x₀ s)
              - (D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) (z - x₀)‖ * ‖Vx s‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ((M : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
              + C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                  * gronwallBound 0 (K : ℝ) 1 (T - t₀))) * ‖z - x₀‖ ^ 2
            * (C' * Real.exp (2 * (K : ℝ) * (T - t₀)) * ‖h‖
                * gronwallBound 0 (K : ℝ) 1 (T - t₀)) :=
          mul_le_mul hRA hV0 (norm_nonneg _)
            (mul_nonneg (add_nonneg (by positivity)
              (mul_nonneg hC'0 (mul_nonneg (by positivity) hg))) (sq_nonneg _))

/-- **Base-point Lipschitz continuity of the chain-rule (second-variation) forcing along the flow.**
The linearised first-variation ODE at base point `z` carries the chain-rule forcing
`F(z) s = ((D²v(Φ z s) ∘ W_z) h) ∘ W_z` (`W_z = D_x Φ_s^{A(z)} = fundamentalSolution hAz hΦ₁ h1`).
This lemma is the standalone, clean-constant form of the forcing-gap datum computed inline inside
`norm_linearisedFirstVariation_baseCurve_sub_le`: the whole forcing moves by `O(‖z − x₀‖ · ‖h‖)` when
the base point moves from `x₀` to `z`, uniformly on `[t₀, T]`,
`‖F(z) s − F(x₀) s‖ ≤ exp(K(T−t₀))³ · (M + 2·L·C'·gronwallBound 0 K 1 (T−t₀)) · ‖z − x₀‖ · ‖h‖`.

Proof: `norm_chainRuleForcing_sub_le` (the joint `P, W` perturbation of `((P ∘ W) h) ∘ W`) fed the flow
bounds `‖D²v(Φ z s)‖ ≤ C'`, the resolvent bound `‖W‖ ≤ exp(K(T−t₀))` (`norm_fundamentalSolution_le`),
the `D²v`-gap `dp` (`norm_secondDerivField_apply_flow_sub_le`) and resolvent base-gap `dw`
(`norm_fundamentalSolution_baseCurve_sub_le`), whose raw output `(dp·w² + 2·C'·w·dw)·‖h‖` collapses to
the stated `exp³·(M + 2LC'g)` constant by `ring` (all factors are `exp(K(T−t₀))`).  This is the `β`
forcing-gap size datum of the base-point `C²` continuity / `C³` Taylor analysis, exposed for reuse. -/
theorem norm_chainRuleForcing_flow_sub_le
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {L M : ℝ≥0} {C' : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hDvlip : ∀ s, LipschitzWith L (Dv s)) (hD2vlip : ∀ s, LipschitzWith M (D2v s))
    (z x₀ : E)
    (hAz : ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K) (hAx : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hC'0 : 0 ≤ C') (hC'z : ∀ s, ‖D2v s (Φ z s)‖ ≤ C')
    {Φ₁ Φ₂ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h1 : ∀ x, Φ₁ x t₀ = x)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h2 : ∀ x, Φ₂ x t₀ = x)
    (h : E) {T s : ℝ} (hs : s ∈ Set.Icc t₀ T) :
    ‖((D2v s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h1 s) h).comp
          (fundamentalSolution hAz hΦ₁ h1 s)
        - ((D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) h).comp
            (fundamentalSolution hAx hΦ₂ h2 s)‖
      ≤ Real.exp ((K : ℝ) * (T - t₀)) ^ 3
          * ((M : ℝ) + 2 * (L : ℝ) * C' * gronwallBound 0 (K : ℝ) 1 (T - t₀))
          * ‖z - x₀‖ * ‖h‖ := by
  have hsT : |s - t₀| ≤ T - t₀ := by
    rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
  have hexpmono : Real.exp ((K : ℝ) * |s - t₀|) ≤ Real.exp ((K : ℝ) * (T - t₀)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsT K.coe_nonneg)
  have hwz : ‖fundamentalSolution hAz hΦ₁ h1 s‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) :=
    (norm_fundamentalSolution_le hAz hΦ₁ h1 s).trans hexpmono
  have hwx : ‖fundamentalSolution hAx hΦ₂ h2 s‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) :=
    (norm_fundamentalSolution_le hAx hΦ₂ h2 s).trans hexpmono
  have hdp : ‖D2v s (Φ z s) - D2v s (Φ x₀ s)‖
      ≤ (M : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖ :=
    norm_secondDerivField_apply_flow_sub_le hv hΦ h0 (hD2vlip s) hsT z x₀
  have hgnn : (0 : ℝ) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
    gronwallBound_zero_one_nonneg K.coe_nonneg (sub_nonneg.mpr (le_trans hs.1 hs.2))
  have hdw : ‖fundamentalSolution hAz hΦ₁ h1 s - fundamentalSolution hAx hΦ₂ h2 s‖
      ≤ (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖
          * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀) := by
    refine (norm_fundamentalSolution_baseCurve_sub_le hv hΦ h0 hDvlip z x₀ hAz hAx
      hΦ₁ h1 hΦ₂ h2 hs).trans ?_
    have hmono : gronwallBound 0 (K : ℝ) 1 (s - t₀) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
      gronwallBound_mono (le_refl (0 : ℝ)) zero_le_one K.coe_nonneg (by linarith [hs.2])
    exact mul_le_mul_of_nonneg_left hmono (by positivity)
  refine (norm_chainRuleForcing_sub_le h (hC'z s) hwz hwx hdp hdw hC'0 (Real.exp_pos _).le
    (by positivity) (mul_nonneg (by positivity) hgnn)).trans (le_of_eq ?_)
  ring

/-- **Operator-norm Lipschitz continuity of the packaged second fundamental solution in the base
point.**  The genuine `C^{0,1}` (operator-norm-continuous dependence) statement for the base-point
second derivative `D₂ = ∂/∂x₀ (D_x Φ_t)`: given the two packaged operators
`D₂z, D₂x : E →L[ℝ] (E →L[ℝ] E)` (each characterised, as produced by
`exists_continuousLinearMap_linearisedVariation`, by `D₂· h = Vlin t` for any solution `Vlin` of the
linearised first-variation ODE at the respective base point, direction `h`), their operator-norm
difference is linear in the base-point increment:
`‖D₂z − D₂x‖ ≤ exp(K(T−t₀))³ · (M + 3·L·C'·gronwallBound 0 K 1 (T−t₀)) · gronwallBound 0 K 1 (t−t₀) ·
‖z − x₀‖`.

Unlike the *pointwise-in-`h`* curve estimate `norm_linearisedFirstVariation_baseCurve_sub_le`, this is
the uniform operator bound, obtained via `ContinuousLinearMap.opNorm_le_bound`: for each direction `h`,
build the canonical linearised first variations `Vz`, `Vx`
(`exists_hasDerivAt_firstVariation_linearised_dir` at `z`, `x₀`), identify `D₂z h = Vz t`,
`D₂x h = Vx t` (the value characterisations `hD₂z`, `hD₂x`), and bound `‖Vz t − Vx t‖ ≤ … · ‖h‖` by
`norm_linearisedFirstVariation_baseCurve_sub_le` (constant rearranged by `ring`).  This packages the
`C²` continuity of the second fundamental solution as an honest operator-norm Lipschitz bound — the
`z ↦ D₂(z)` regularity datum that the `C³` layer differentiates. -/
theorem norm_secondFundamentalSolution_op_sub_le [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {L M : ℝ≥0} {C' : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hDvlip : ∀ s, LipschitzWith L (Dv s)) (hD2vlip : ∀ s, LipschitzWith M (D2v s))
    (z x₀ : E)
    (hAz : ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K) (hAx : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hAzcont : Continuous (fun s => Dv s (Φ z s))) (hAxcont : Continuous (fun s => Dv s (Φ x₀ s)))
    (hD2zcont : Continuous (fun s => D2v s (Φ z s)))
    (hD2xcont : Continuous (fun s => D2v s (Φ x₀ s)))
    (hC'0 : 0 ≤ C') (hC'z : ∀ s, ‖D2v s (Φ z s)‖ ≤ C') (hC'x : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ C')
    {Φ₁ Φ₂ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h1 : ∀ x, Φ₁ x t₀ = x)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h2 : ∀ x, Φ₂ x t₀ = x)
    {D₂z D₂x : E →L[ℝ] (E →L[ℝ] E)}
    (hD₂z : ∀ (h : E) (Vlin : ℝ → (E →L[ℝ] E)), Vlin t₀ = 0 →
      (∀ s, HasDerivAt Vlin
        ((Dv s (Φ z s)).comp (Vlin s)
          + ((D2v s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h1 s) h).comp
              (fundamentalSolution hAz hΦ₁ h1 s)) s) →
      D₂z h = Vlin t)
    (hD₂x : ∀ (h : E) (Vlin : ℝ → (E →L[ℝ] E)), Vlin t₀ = 0 →
      (∀ s, HasDerivAt Vlin
        ((Dv s (Φ x₀ s)).comp (Vlin s)
          + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) h).comp
              (fundamentalSolution hAx hΦ₂ h2 s)) s) →
      D₂x h = Vlin t)
    {T : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ‖D₂z - D₂x‖
      ≤ Real.exp ((K : ℝ) * (T - t₀)) ^ 3
          * ((M : ℝ) + 3 * (L : ℝ) * C' * gronwallBound 0 (K : ℝ) 1 (T - t₀))
          * gronwallBound 0 (K : ℝ) 1 (t - t₀) * ‖z - x₀‖ := by
  have hg : (0 : ℝ) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
    gronwallBound_zero_one_nonneg K.coe_nonneg (sub_nonneg.mpr (le_trans ht.1 ht.2))
  have hgt : (0 : ℝ) ≤ gronwallBound 0 (K : ℝ) 1 (t - t₀) :=
    gronwallBound_zero_one_nonneg K.coe_nonneg (sub_nonneg.mpr ht.1)
  have hMLC : (0 : ℝ) ≤ (M : ℝ) + 3 * (L : ℝ) * C' * gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
    add_nonneg (by positivity) (mul_nonneg (mul_nonneg (by positivity) hC'0) hg)
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hMLC) hgt) (norm_nonneg _)) (fun h => ?_)
  rw [ContinuousLinearMap.sub_apply]
  obtain ⟨Vz, hVz0, hVzd⟩ :=
    exists_hasDerivAt_firstVariation_linearised_dir z hAz hAzcont hD2zcont hΦ₁ h1 h
  obtain ⟨Vx, hVx0, hVxd⟩ :=
    exists_hasDerivAt_firstVariation_linearised_dir x₀ hAx hAxcont hD2xcont hΦ₂ h2 h
  rw [hD₂z h Vz hVz0 hVzd, hD₂x h Vx hVx0 hVxd]
  refine (norm_linearisedFirstVariation_baseCurve_sub_le hv hΦ h0 hDvlip hD2vlip z x₀ hAz hAx
    hC'0 hC'z hC'x hΦ₁ h1 hΦ₂ h2 h hVzd hVz0 hVxd hVx0 ht).trans (le_of_eq ?_)
  ring

/-- **Existence of the second-order (third) variation with the coefficient-variation leading term** —
the *design-corrected* `D₃`-solution existence, resolving the plan's open forcing-gap design question.

The packaged forcing of `exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv` is
`F_A + F_B + F_C`.  Differentiating the second-variation ODE `V' = A₀ ∘ V + ((D²v ∘ W) h) ∘ W` in the
base point (direction `k`) produces, *in addition*, the **coefficient-variation leading term**
`(D²v[W k]) ∘ V₀`.  Indeed `∂_k(A₀ ∘ V₀) = (∂_k A₀) ∘ V₀ + A₀ ∘ (∂_k V₀)`: the second summand is the
homogeneous `A₀ ∘ V` of the new unknown, while the first is `∂_k A₀ = D²v[W k]` (the chain rule
`∂_k[Dv(·, Φ(x₀, ·))] = D²v[∂_k Φ] = D²v[W k]`) composed with the reference `h`-direction second
fundamental solution curve `V₀`.  This term is *not* among `F_A`, `F_B`, `F_C` (which arise only from
differentiating the *forcing* `((D²v ∘ W) h) ∘ W`), and it is exactly the operator isolated by
`norm_coeffVariation_sub_secondDerivComp_le_sq` as the first-order-in-`k` part of `(A₁ − A₀) ∘ V₁`
(with `k = z − x₀`, `V₀ = Vx`).  Including it in `F₃` is precisely what makes the second-order Taylor
remainder `‖(D₂(z) − D₂(x₀)) − D₃(z − x₀)‖` genuinely `O(‖z − x₀‖²)`; no `D²v`-symmetry hypothesis is
required — the plan's open forcing-gap design question resolves in favour of the extra summand.

Given the reference base point `x₀`, resolvent `W = fundamentalSolution hA hΦ' h0'`, continuous second
fundamental solution curve `W₂` in direction `k`, and continuous `h`-direction second fundamental
solution curve `V₀`, the corrected third-variation ODE
`V' = A₀ ∘ V + (F_A + F_B + ((D²v[W k]) ∘ V₀ + F_C))`, `V t₀ = 0` has a global solution `V`.  Proof:
specialise `exists_hasDerivAt_secondVariation_linearised_dir` with the abstract `F₃` slot instantiated
to the sum of the coefficient-variation term (continuity by `clm_comp`/`clm_apply`, mirroring the `F_B`
continuity) and the third-derivative term `F_C` (`continuous_thirdDerivForcing`). -/
theorem exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv_coeff [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E} {K : ℝ≥0}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hAcont : Continuous (fun s => Dv s (Φ x₀ s)))
    (hD2cont : Continuous (fun s => D2v s (Φ x₀ s)))
    (hD3cont : Continuous (fun s => D3v s (Φ x₀ s)))
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    {W2 : ℝ → (E →L[ℝ] E)} (hW2 : Continuous W2)
    {V0 : ℝ → (E →L[ℝ] E)} (hV0 : Continuous V0)
    (k h : E) :
    ∃ V : ℝ → (E →L[ℝ] E), V t₀ = 0 ∧
      ∀ s, HasDerivAt V
        ((Dv s (Φ x₀ s)).comp (V s)
          + (((D2v s (Φ x₀ s)).comp (W2 s) h).comp (fundamentalSolution hA hΦ' h0' s)
             + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 s)
             + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (V0 s)
                + (continuousMultilinearCurryFin1 ℝ E E
                    (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                      (fundamentalSolution hA hΦ' h0' s h))).comp
                    (fundamentalSolution hA hΦ' h0' s)))) s := by
  have hW : Continuous (fun s => fundamentalSolution hA hΦ' h0' s) :=
    continuous_fundamentalSolution_time hA hΦ' h0'
  have hLead : Continuous fun s =>
      ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (V0 s) :=
    ((hD2cont.clm_comp hW).clm_apply continuous_const).clm_comp hV0
  have hF3 : Continuous fun s =>
      ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (V0 s)
      + (continuousMultilinearCurryFin1 ℝ E E
          (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
            (fundamentalSolution hA hΦ' h0' s h))).comp (fundamentalSolution hA hΦ' h0' s) :=
    hLead.add (continuous_thirdDerivForcing hD3cont hW k h)
  exact exists_hasDerivAt_secondVariation_linearised_dir x₀ hA hAcont hD2cont hΦ' h0' hW2 hF3 h

/-- **A-priori size bound for the design-corrected third variation** — the corrected analogue of
`norm_thirdVariation_le`, additionally accounting for the coefficient-variation leading term
`(D²v[W k]) ∘ V₀` supplied by `exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv_coeff`.

For a solution `V` of the corrected third-variation ODE
`V' = A₀ ∘ V + (F_A + F_B + ((D²v[W k]) ∘ V₀ + F_C))`, `V t₀ = 0`, with `‖D²v‖ ≤ C'`, `‖D³v‖ ≤ C''`
along the reference trajectory, the second fundamental solution curve bounded `‖W₂ s‖ ≤ N₂` and the
`h`-direction second fundamental solution curve bounded `‖V₀ s‖ ≤ N₀` on `[t₀, T]`, the time-`t` value
obeys `‖V t‖ ≤ (2·C'·N₂·exp(K(T−t₀))·‖h‖ + C'·N₀·exp(K(T−t₀))·‖k‖ + C''·exp(3K(T−t₀))·‖k‖·‖h‖) ·
gronwallBound 0 K 1 (t − t₀)`.

Proof: bound the four forcing terms uniformly on `[t₀, T]` — `F_A`, `F_B`, and the new leading term by
`norm_bilinearCompForcing_le` (the leading term fed `‖D²v‖ ≤ C'`, `‖W‖ ≤ exp`, `‖V₀‖ ≤ N₀`), and `F_C`
by `norm_thirdDerivForcing_le` — sum them by the triangle inequality (`norm_add₃_le` + `norm_add_le`,
`exp·exp·exp = exp(3·)`), then feed the constant forcing bound to `norm_inhomogVariation_le`.  This is
the corrected `N`-datum feeding the packaged (design-corrected) `D₃` operator toward `ContDiff ℝ 3`. -/
theorem norm_thirdVariation_coeff_le
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E} {K : ℝ≥0}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    {C' C'' N₂ N₀ : ℝ} (hC'0 : 0 ≤ C') (hC''0 : 0 ≤ C'') (hN₂0 : 0 ≤ N₂)
    (hC' : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ C') (hC'' : ∀ s, ‖D3v s (Φ x₀ s)‖ ≤ C'')
    {W2 V0 : ℝ → (E →L[ℝ] E)} {T : ℝ}
    (hW2 : ∀ s ∈ Set.Icc t₀ T, ‖W2 s‖ ≤ N₂) (hV0b : ∀ s ∈ Set.Icc t₀ T, ‖V0 s‖ ≤ N₀)
    (k h : E) {V : ℝ → (E →L[ℝ] E)}
    (hV : ∀ s, HasDerivAt V
      ((Dv s (Φ x₀ s)).comp (V s)
        + (((D2v s (Φ x₀ s)).comp (W2 s) h).comp (fundamentalSolution hA hΦ' h0' s)
           + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 s)
           + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (V0 s)
              + (continuousMultilinearCurryFin1 ℝ E E
                  (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                    (fundamentalSolution hA hΦ' h0' s h))).comp
                  (fundamentalSolution hA hΦ' h0' s)))) s)
    (hV0 : V t₀ = 0)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ‖V t‖
      ≤ (2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖
          + C' * N₀ * Real.exp ((K : ℝ) * (T - t₀)) * ‖k‖
          + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)) * ‖k‖ * ‖h‖)
        * gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
  refine norm_inhomogVariation_le hA hV hV0 ?_ ht
  intro s hs
  have hsabs : |s - t₀| ≤ T - t₀ := by
    rw [abs_of_nonneg (by linarith [hs.1] : (0 : ℝ) ≤ s - t₀)]; linarith [hs.2]
  have hWle : ‖fundamentalSolution hA hΦ' h0' s‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) :=
    (norm_fundamentalSolution_le hA hΦ' h0' s).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsabs K.coe_nonneg))
  have hex0 : (0 : ℝ) ≤ Real.exp ((K : ℝ) * (T - t₀)) := (Real.exp_pos _).le
  have hPle : ‖D2v s (Φ x₀ s)‖ ≤ C' := hC' s
  have hDle : ‖D3v s (Φ x₀ s)‖ ≤ C'' := hC'' s
  have hW2le : ‖W2 s‖ ≤ N₂ := hW2 s hs
  have hV0le : ‖V0 s‖ ≤ N₀ := hV0b s hs
  have hWk : ‖fundamentalSolution hA hΦ' h0' s k‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) * ‖k‖ :=
    ((fundamentalSolution hA hΦ' h0' s).le_opNorm k).trans (by gcongr)
  have hWh : ‖fundamentalSolution hA hΦ' h0' s h‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖ :=
    ((fundamentalSolution hA hΦ' h0' s).le_opNorm h).trans (by gcongr)
  have hexp3 : Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
        * Real.exp ((K : ℝ) * (T - t₀)) = Real.exp (3 * (K : ℝ) * (T - t₀)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have htA : ‖((D2v s (Φ x₀ s)).comp (W2 s) h).comp (fundamentalSolution hA hΦ' h0' s)‖
      ≤ C' * N₂ * Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖ := by
    refine (norm_bilinearCompForcing_le (D2v s (Φ x₀ s)) (W2 s)
      (fundamentalSolution hA hΦ' h0' s) h).trans ?_
    gcongr
  have htB : ‖((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 s)‖
      ≤ C' * Real.exp ((K : ℝ) * (T - t₀)) * N₂ * ‖h‖ := by
    refine (norm_bilinearCompForcing_le (D2v s (Φ x₀ s))
      (fundamentalSolution hA hΦ' h0' s) (W2 s) h).trans ?_
    gcongr
  have htLead : ‖((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (V0 s)‖
      ≤ C' * Real.exp ((K : ℝ) * (T - t₀)) * N₀ * ‖k‖ := by
    refine (norm_bilinearCompForcing_le (D2v s (Φ x₀ s))
      (fundamentalSolution hA hΦ' h0' s) (V0 s) k).trans ?_
    gcongr
  have htC : ‖(continuousMultilinearCurryFin1 ℝ E E
        (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
          (fundamentalSolution hA hΦ' h0' s h))).comp (fundamentalSolution hA hΦ' h0' s)‖
      ≤ C'' * (Real.exp ((K : ℝ) * (T - t₀)) * ‖k‖) * (Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖)
          * Real.exp ((K : ℝ) * (T - t₀)) := by
    refine (norm_thirdDerivForcing_le (D3v s (Φ x₀ s)) (fundamentalSolution hA hΦ' h0' s k)
      (fundamentalSolution hA hΦ' h0' s h) (fundamentalSolution hA hΦ' h0' s)).trans ?_
    gcongr
  calc ‖((D2v s (Φ x₀ s)).comp (W2 s) h).comp (fundamentalSolution hA hΦ' h0' s)
          + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 s)
          + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (V0 s)
              + (continuousMultilinearCurryFin1 ℝ E E
                  (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                    (fundamentalSolution hA hΦ' h0' s h))).comp (fundamentalSolution hA hΦ' h0' s))‖
      ≤ ‖((D2v s (Φ x₀ s)).comp (W2 s) h).comp (fundamentalSolution hA hΦ' h0' s)‖
          + ‖((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 s)‖
          + ‖((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (V0 s)
              + (continuousMultilinearCurryFin1 ℝ E E
                  (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                    (fundamentalSolution hA hΦ' h0' s h))).comp (fundamentalSolution hA hΦ' h0' s)‖ :=
        norm_add₃_le
    _ ≤ ‖((D2v s (Φ x₀ s)).comp (W2 s) h).comp (fundamentalSolution hA hΦ' h0' s)‖
          + ‖((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 s)‖
          + (‖((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (V0 s)‖
              + ‖(continuousMultilinearCurryFin1 ℝ E E
                  (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                    (fundamentalSolution hA hΦ' h0' s h))).comp (fundamentalSolution hA hΦ' h0' s)‖) :=
        add_le_add (le_refl _) (norm_add_le _ _)
    _ ≤ C' * N₂ * Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖
          + C' * Real.exp ((K : ℝ) * (T - t₀)) * N₂ * ‖h‖
          + (C' * Real.exp ((K : ℝ) * (T - t₀)) * N₀ * ‖k‖
              + C'' * (Real.exp ((K : ℝ) * (T - t₀)) * ‖k‖) * (Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖)
                  * Real.exp ((K : ℝ) * (T - t₀))) :=
        add_le_add (add_le_add htA htB) (add_le_add htLead htC)
    _ = 2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖
          + C' * N₀ * Real.exp ((K : ℝ) * (T - t₀)) * ‖k‖
          + C'' * (Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
              * Real.exp ((K : ℝ) * (T - t₀))) * ‖k‖ * ‖h‖ := by ring
    _ = 2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖
          + C' * N₀ * Real.exp ((K : ℝ) * (T - t₀)) * ‖k‖
          + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)) * ‖k‖ * ‖h‖ := by rw [hexp3]

/-- **Additivity of the design-corrected third variation in the direction `h`.**  The corrected
analogue of `thirdVariation_perturbation_add_eq`, accounting for the coefficient-variation leading term
`(D²v[W k]) ∘ V₀` of `exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv_coeff`.

Because that leading term carries the reference `h`-direction second fundamental solution curve `V₀`,
additivity in `h` requires `V₀` to be additive as well: for the two directions `h₁`, `h₂` with second
fundamental solution curves `V0₁`, `V0₂` (and the *same* base-direction curve `W₂` in `k`, which is
independent of `h`), the corrected third variation `V₁₂` for the pair `(h₁ + h₂, V0₁ + V0₂)` equals
`V₁ + V₂`.  The whole four-term forcing is additive in the `(h, V₀)` pair: `map_add` on the operator
applications and `curryLeft`/`curryFin1`, `ContinuousLinearMap.add_comp` on the `F_A`/`F_B`/`F_C` slots,
and `ContinuousLinearMap.comp_add` on the leading term `(D²v[W k]) ∘ (V0₁ + V0₂)`; superposition
`hasDerivAt_inhomogVariation_add` and Grönwall uniqueness `inhomogVariation_unique` then identify
`V₁₂` with `V₁ + V₂`.  The additive half of packaging the corrected `h ↦ D₃(k, h)` as a bounded linear
map (with `V₀ = Vlin^{x₀, ·}(h)` linear in `h`). -/
theorem thirdVariation_coeff_perturbation_add_eq
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E} {K : ℝ≥0}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    {W2 V0₁ V0₂ : ℝ → (E →L[ℝ] E)} (k h₁ h₂ : E) {V₁ V₂ V₁₂ : ℝ → (E →L[ℝ] E)}
    (hV₁ : ∀ s, HasDerivAt V₁
      ((Dv s (Φ x₀ s)).comp (V₁ s)
        + (((D2v s (Φ x₀ s)).comp (W2 s) h₁).comp (fundamentalSolution hA hΦ' h0' s)
           + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h₁).comp (W2 s)
           + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (V0₁ s)
              + (continuousMultilinearCurryFin1 ℝ E E
                  (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                    (fundamentalSolution hA hΦ' h0' s h₁))).comp
                  (fundamentalSolution hA hΦ' h0' s)))) s)
    (hV₂ : ∀ s, HasDerivAt V₂
      ((Dv s (Φ x₀ s)).comp (V₂ s)
        + (((D2v s (Φ x₀ s)).comp (W2 s) h₂).comp (fundamentalSolution hA hΦ' h0' s)
           + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h₂).comp (W2 s)
           + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (V0₂ s)
              + (continuousMultilinearCurryFin1 ℝ E E
                  (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                    (fundamentalSolution hA hΦ' h0' s h₂))).comp
                  (fundamentalSolution hA hΦ' h0' s)))) s)
    (hV₁₂ : ∀ s, HasDerivAt V₁₂
      ((Dv s (Φ x₀ s)).comp (V₁₂ s)
        + (((D2v s (Φ x₀ s)).comp (W2 s) (h₁ + h₂)).comp (fundamentalSolution hA hΦ' h0' s)
           + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) (h₁ + h₂)).comp (W2 s)
           + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (V0₁ s + V0₂ s)
              + (continuousMultilinearCurryFin1 ℝ E E
                  (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                    (fundamentalSolution hA hΦ' h0' s (h₁ + h₂)))).comp
                  (fundamentalSolution hA hΦ' h0' s)))) s)
    (hV₁0 : V₁ t₀ = 0) (hV₂0 : V₂ t₀ = 0) (hV₁₂0 : V₁₂ t₀ = 0)
    (t : ℝ) : V₁₂ t = V₁ t + V₂ t := by
  have hV₁₂' : ∀ s, HasDerivAt V₁₂
      ((Dv s (Φ x₀ s)).comp (V₁₂ s)
        + ((((D2v s (Φ x₀ s)).comp (W2 s) h₁).comp (fundamentalSolution hA hΦ' h0' s)
            + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h₁).comp (W2 s)
            + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (V0₁ s)
               + (continuousMultilinearCurryFin1 ℝ E E
                   (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                     (fundamentalSolution hA hΦ' h0' s h₁))).comp
                   (fundamentalSolution hA hΦ' h0' s)))
          + (((D2v s (Φ x₀ s)).comp (W2 s) h₂).comp (fundamentalSolution hA hΦ' h0' s)
            + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h₂).comp (W2 s)
            + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (V0₂ s)
               + (continuousMultilinearCurryFin1 ℝ E E
                   (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                     (fundamentalSolution hA hΦ' h0' s h₂))).comp
                   (fundamentalSolution hA hΦ' h0' s))))) s := by
    intro s
    have hmap :
        (((D2v s (Φ x₀ s)).comp (W2 s) (h₁ + h₂)).comp (fundamentalSolution hA hΦ' h0' s)
          + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) (h₁ + h₂)).comp (W2 s)
          + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (V0₁ s + V0₂ s)
             + (continuousMultilinearCurryFin1 ℝ E E
                 (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                   (fundamentalSolution hA hΦ' h0' s (h₁ + h₂)))).comp
                 (fundamentalSolution hA hΦ' h0' s)))
        = (((D2v s (Φ x₀ s)).comp (W2 s) h₁).comp (fundamentalSolution hA hΦ' h0' s)
            + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h₁).comp (W2 s)
            + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (V0₁ s)
               + (continuousMultilinearCurryFin1 ℝ E E
                   (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                     (fundamentalSolution hA hΦ' h0' s h₁))).comp
                   (fundamentalSolution hA hΦ' h0' s)))
          + (((D2v s (Φ x₀ s)).comp (W2 s) h₂).comp (fundamentalSolution hA hΦ' h0' s)
            + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h₂).comp (W2 s)
            + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (V0₂ s)
               + (continuousMultilinearCurryFin1 ℝ E E
                   (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                     (fundamentalSolution hA hΦ' h0' s h₂))).comp
                   (fundamentalSolution hA hΦ' h0' s))) := by
      simp only [map_add, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]; abel
    have := hV₁₂ s
    rwa [hmap] at this
  have hsum := hasDerivAt_inhomogVariation_add hV₁ hV₂
  have h0 : V₁₂ t₀ = (fun r => V₁ r + V₂ r) t₀ := by simp [hV₁₂0, hV₁0, hV₂0]
  exact inhomogVariation_unique hA hV₁₂' hsum h0 t

/-- **Homogeneity in `h` of the design-corrected third variation.**  The scalar-homogeneous companion
of `thirdVariation_coeff_perturbation_add_eq`: for the corrected four-term forcing (with the
coefficient-variation leading term `(D²v[W k]) ∘ V₀`), scaling the direction `h` *and* its second
fundamental solution curve `V₀` by `c` scales the third variation by `c`: `V^{c • h, c • V₀} t =
c • V^{h, V₀} t`.  The corrected forcing is homogeneous in the `(h, V₀)` pair: `map_smul` on the operator
applications and `curryLeft`/`curryFin1`, `ContinuousLinearMap.smul_comp` on the `F_A`/`F_B`/`F_C` slots,
and `ContinuousLinearMap.comp_smul` on the leading term `(D²v[W k]) ∘ (c • V₀)`; homogeneity
`hasDerivAt_inhomogVariation_smul` and uniqueness `inhomogVariation_unique` finish.  The homogeneous half
of packaging the corrected `h ↦ D₃(k, h)` as a bounded linear map. -/
theorem thirdVariation_coeff_perturbation_smul_eq
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E} {K : ℝ≥0}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    {W2 V0 : ℝ → (E →L[ℝ] E)} (k : E) (c : ℝ) (h : E) {V Vc : ℝ → (E →L[ℝ] E)}
    (hV : ∀ s, HasDerivAt V
      ((Dv s (Φ x₀ s)).comp (V s)
        + (((D2v s (Φ x₀ s)).comp (W2 s) h).comp (fundamentalSolution hA hΦ' h0' s)
           + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 s)
           + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (V0 s)
              + (continuousMultilinearCurryFin1 ℝ E E
                  (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                    (fundamentalSolution hA hΦ' h0' s h))).comp
                  (fundamentalSolution hA hΦ' h0' s)))) s)
    (hVc : ∀ s, HasDerivAt Vc
      ((Dv s (Φ x₀ s)).comp (Vc s)
        + (((D2v s (Φ x₀ s)).comp (W2 s) (c • h)).comp (fundamentalSolution hA hΦ' h0' s)
           + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) (c • h)).comp (W2 s)
           + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (c • V0 s)
              + (continuousMultilinearCurryFin1 ℝ E E
                  (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                    (fundamentalSolution hA hΦ' h0' s (c • h)))).comp
                  (fundamentalSolution hA hΦ' h0' s)))) s)
    (hV0 : V t₀ = 0) (hVc0 : Vc t₀ = 0)
    (t : ℝ) : Vc t = c • V t := by
  have hVc' : ∀ s, HasDerivAt Vc
      ((Dv s (Φ x₀ s)).comp (Vc s)
        + c • (((D2v s (Φ x₀ s)).comp (W2 s) h).comp (fundamentalSolution hA hΦ' h0' s)
            + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 s)
            + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (V0 s)
               + (continuousMultilinearCurryFin1 ℝ E E
                   (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                     (fundamentalSolution hA hΦ' h0' s h))).comp
                   (fundamentalSolution hA hΦ' h0' s)))) s := by
    intro s
    have hmap :
        (((D2v s (Φ x₀ s)).comp (W2 s) (c • h)).comp (fundamentalSolution hA hΦ' h0' s)
          + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) (c • h)).comp (W2 s)
          + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (c • V0 s)
             + (continuousMultilinearCurryFin1 ℝ E E
                 (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                   (fundamentalSolution hA hΦ' h0' s (c • h)))).comp
                 (fundamentalSolution hA hΦ' h0' s)))
        = c • (((D2v s (Φ x₀ s)).comp (W2 s) h).comp (fundamentalSolution hA hΦ' h0' s)
            + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 s)
            + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (V0 s)
               + (continuousMultilinearCurryFin1 ℝ E E
                   (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                     (fundamentalSolution hA hΦ' h0' s h))).comp
                   (fundamentalSolution hA hΦ' h0' s))) := by
      simp only [map_smul, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_add]
    have := hVc s
    rwa [hmap] at this
  have hsmul := hasDerivAt_inhomogVariation_smul c hV
  have h0 : Vc t₀ = (fun r => c • V r) t₀ := by simp [hVc0, hV0]
  exact inhomogVariation_unique hA hVc' hsmul h0 t

/-- **The packaged design-corrected third-variation operator `D₃(k)`** — the corrected analogue of
`exists_continuousLinearMap_thirdVariation`, packaging `h ↦ D₃(k, h)` as a *bounded linear map* for the
*corrected* four-term forcing (including the coefficient-variation leading term `(D²v[W k]) ∘ V₀`).

Since that leading term carries the reference `h`-direction second fundamental solution curve, the caller
supplies `V₀` as a *linear* function `V0fun : E → (ℝ → (E →L[ℝ] E))` of the direction `h` — additive
(`hV0add`), homogeneous (`hV0smul`), continuous (`hV0cont`), and bounded `‖V0fun h s‖ ≤ N₀ · ‖h‖`
(`hV0bound`, so the bound factors `‖h‖`).  There is then a bounded operator
`D₃k : E →L[ℝ] (E →L[ℝ] E)` whose value on any direction `h` is the time-`t` value of *any* solution `V`
of the corrected third-variation ODE
`V' = A₀ ∘ V + (((D²v ∘ W₂) h) ∘ W + ((D²v ∘ W) h) ∘ W₂ + ((D²v[W k]) ∘ (V0fun h) +
(curryFin1 ((D³v.curryLeft (W k)).curryLeft (W h))) ∘ W))`, `V t₀ = 0`.

Assembly: the direction-parameterised solution `h ↦ V^h`
(`exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv_coeff`) is additive and homogeneous in
`h` (`thirdVariation_coeff_perturbation_add_eq`/`_smul_eq`, feeding the rewritten
`V0fun (h₁+h₂) = V0fun h₁ + V0fun h₂` / `V0fun (c•h) = c • V0fun h`) and bounded with
`‖V^h t‖ ≤ ((2·C'·N₂·exp(K(T−t₀)) + C'·N₀·exp(K(T−t₀))·‖k‖ + C''·exp(3K(T−t₀))·‖k‖) ·
gronwallBound 0 K 1 (t−t₀)) · ‖h‖` (`norm_thirdVariation_coeff_le` with `N₀ ↦ N₀·‖h‖`, factoring `‖h‖`),
so `LinearMap.mkContinuous` yields the operator; the value is solution-independent by
`inhomogVariation_unique`.  This is the design-corrected operator `D₃(k)` whose second-order Taylor
remainder `‖(D₂(z) − D₂(x₀)) − D₃(z − x₀)‖ ≤ C‖z − x₀‖²` (now closable, since the corrected `F₃` cancels
the coefficient-variation leading term) gives the spatial `C³` regularity of the flow's resolvent. -/
theorem exists_continuousLinearMap_thirdVariation_coeff [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E} {K : ℝ≥0}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hAcont : Continuous (fun s => Dv s (Φ x₀ s)))
    (hD2cont : Continuous (fun s => D2v s (Φ x₀ s)))
    (hD3cont : Continuous (fun s => D3v s (Φ x₀ s)))
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    {C' C'' N₂ N₀ : ℝ} (hC'0 : 0 ≤ C') (hC''0 : 0 ≤ C'') (hN₂0 : 0 ≤ N₂)
    (hC' : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ C') (hC'' : ∀ s, ‖D3v s (Φ x₀ s)‖ ≤ C'')
    {W2 : ℝ → (E →L[ℝ] E)} (hW2cont : Continuous W2)
    {T : ℝ} (hW2 : ∀ s ∈ Set.Icc t₀ T, ‖W2 s‖ ≤ N₂)
    {V0fun : E → (ℝ → (E →L[ℝ] E))} (hV0cont : ∀ h, Continuous (V0fun h))
    (hV0add : ∀ (h₁ h₂ : E) (s : ℝ), V0fun (h₁ + h₂) s = V0fun h₁ s + V0fun h₂ s)
    (hV0smul : ∀ (c : ℝ) (h : E) (s : ℝ), V0fun (c • h) s = c • V0fun h s)
    (hV0bound : ∀ (h : E), ∀ s ∈ Set.Icc t₀ T, ‖V0fun h s‖ ≤ N₀ * ‖h‖)
    (k : E) {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ∃ D₃k : E →L[ℝ] (E →L[ℝ] E),
      ∀ (h : E) (V : ℝ → (E →L[ℝ] E)), V t₀ = 0 →
        (∀ s, HasDerivAt V
          ((Dv s (Φ x₀ s)).comp (V s)
            + (((D2v s (Φ x₀ s)).comp (W2 s) h).comp (fundamentalSolution hA hΦ' h0' s)
               + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 s)
               + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (V0fun h s)
                  + (continuousMultilinearCurryFin1 ℝ E E
                      (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                        (fundamentalSolution hA hΦ' h0' s h))).comp
                      (fundamentalSolution hA hΦ' h0' s)))) s) →
        D₃k h = V t := by
  choose Vsol hVsol0 hVsolderiv using fun h =>
    exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv_coeff x₀ hA hAcont hD2cont hD3cont
      hΦ' h0' hW2cont (hV0cont h) k h
  have hadd : ∀ h₁ h₂ : E, Vsol (h₁ + h₂) t = Vsol h₁ t + Vsol h₂ t := fun h₁ h₂ =>
    thirdVariation_coeff_perturbation_add_eq x₀ hA hΦ' h0' k h₁ h₂
      (hVsolderiv h₁) (hVsolderiv h₂)
      (fun s => by have hh := hVsolderiv (h₁ + h₂) s; rwa [hV0add h₁ h₂ s] at hh)
      (hVsol0 h₁) (hVsol0 h₂) (hVsol0 (h₁ + h₂)) t
  have hsmul : ∀ (c : ℝ) (h : E), Vsol (c • h) t = c • Vsol h t := fun c h =>
    thirdVariation_coeff_perturbation_smul_eq x₀ hA hΦ' h0' k c h
      (hVsolderiv h)
      (fun s => by have hh := hVsolderiv (c • h) s; rwa [hV0smul c h s] at hh)
      (hVsol0 h) (hVsol0 (c • h)) t
  have hbound : ∀ h : E,
      ‖Vsol h t‖
        ≤ ((2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀))
              + C' * N₀ * Real.exp ((K : ℝ) * (T - t₀)) * ‖k‖
              + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)) * ‖k‖)
            * gronwallBound 0 (K : ℝ) 1 (t - t₀)) * ‖h‖ :=
    fun h => by
      have hle := norm_thirdVariation_coeff_le x₀ hA hΦ' h0' hC'0 hC''0 hN₂0 hC' hC''
        hW2 (hV0bound h) k h (hVsolderiv h) (hVsol0 h) ht
      calc ‖Vsol h t‖
          ≤ (2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖
              + C' * (N₀ * ‖h‖) * Real.exp ((K : ℝ) * (T - t₀)) * ‖k‖
              + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)) * ‖k‖ * ‖h‖)
            * gronwallBound 0 (K : ℝ) 1 (t - t₀) := hle
        _ = ((2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀))
              + C' * N₀ * Real.exp ((K : ℝ) * (T - t₀)) * ‖k‖
              + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)) * ‖k‖)
            * gronwallBound 0 (K : ℝ) 1 (t - t₀)) * ‖h‖ := by ring
  refine ⟨LinearMap.mkContinuous
    { toFun := fun h => Vsol h t
      map_add' := hadd
      map_smul' := fun c h => by simpa using hsmul c h }
    ((2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀))
        + C' * N₀ * Real.exp ((K : ℝ) * (T - t₀)) * ‖k‖
        + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)) * ‖k‖)
      * gronwallBound 0 (K : ℝ) 1 (t - t₀)) hbound, ?_⟩
  intro h V hV0 hVderiv
  have huniq : Vsol h t = V t :=
    inhomogVariation_unique hA (hVsolderiv h) hVderiv (by rw [hVsol0 h, hV0]) t
  simpa using huniq

/-- **The packaged design-corrected `D₃(k)` with its operator-norm bound.**  Strengthens
`exists_continuousLinearMap_thirdVariation_coeff` by exposing the a-priori bound
`‖D₃k‖ ≤ (2·C'·N₂·exp(K(T−t₀)) + C'·N₀·exp(K(T−t₀))·‖k‖ + C''·exp(3K(T−t₀))·‖k‖) ·
gronwallBound 0 K 1 (t−t₀)` alongside the value characterisation, for the *corrected* four-term forcing
(with the coefficient-variation leading term `(D²v[W k]) ∘ (V0fun h)`, `V0fun` linear in `h`).

The bound is `ContinuousLinearMap.opNorm_le_bound`: for each `h`, choosing the corrected solution `V^h`
(`exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv_coeff` with `V₀ = V0fun h`), the value
characterisation gives `D₃k h = V^h t`, and `norm_thirdVariation_coeff_le` (with `N₀ ↦ N₀·‖h‖`) bounds
`‖V^h t‖ ≤ C · ‖h‖`.  Nonnegativity of the operator constant uses `0 ≤ N₀` (the new middle summand
`C'·N₀·exp·‖k‖`) and `0 ≤ gronwallBound 0 K 1 (t−t₀)` (from `t₀ ≤ t`).  This is the corrected size datum
`‖D₃‖ ≤ …` that the second-order Taylor remainder for the resolvent's second derivative requires. -/
theorem exists_continuousLinearMap_thirdVariation_coeff_norm_le [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E} {K : ℝ≥0}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hAcont : Continuous (fun s => Dv s (Φ x₀ s)))
    (hD2cont : Continuous (fun s => D2v s (Φ x₀ s)))
    (hD3cont : Continuous (fun s => D3v s (Φ x₀ s)))
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    {C' C'' N₂ N₀ : ℝ} (hC'0 : 0 ≤ C') (hC''0 : 0 ≤ C'') (hN₂0 : 0 ≤ N₂) (hN₀0 : 0 ≤ N₀)
    (hC' : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ C') (hC'' : ∀ s, ‖D3v s (Φ x₀ s)‖ ≤ C'')
    {W2 : ℝ → (E →L[ℝ] E)} (hW2cont : Continuous W2)
    {T : ℝ} (hW2 : ∀ s ∈ Set.Icc t₀ T, ‖W2 s‖ ≤ N₂)
    {V0fun : E → (ℝ → (E →L[ℝ] E))} (hV0cont : ∀ h, Continuous (V0fun h))
    (hV0add : ∀ (h₁ h₂ : E) (s : ℝ), V0fun (h₁ + h₂) s = V0fun h₁ s + V0fun h₂ s)
    (hV0smul : ∀ (c : ℝ) (h : E) (s : ℝ), V0fun (c • h) s = c • V0fun h s)
    (hV0bound : ∀ (h : E), ∀ s ∈ Set.Icc t₀ T, ‖V0fun h s‖ ≤ N₀ * ‖h‖)
    (k : E) {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ∃ D₃k : E →L[ℝ] (E →L[ℝ] E),
      ‖D₃k‖ ≤ (2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀))
            + C' * N₀ * Real.exp ((K : ℝ) * (T - t₀)) * ‖k‖
            + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)) * ‖k‖)
          * gronwallBound 0 (K : ℝ) 1 (t - t₀) ∧
      ∀ (h : E) (V : ℝ → (E →L[ℝ] E)), V t₀ = 0 →
        (∀ s, HasDerivAt V
          ((Dv s (Φ x₀ s)).comp (V s)
            + (((D2v s (Φ x₀ s)).comp (W2 s) h).comp (fundamentalSolution hA hΦ' h0' s)
               + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 s)
               + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (V0fun h s)
                  + (continuousMultilinearCurryFin1 ℝ E E
                      (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                        (fundamentalSolution hA hΦ' h0' s h))).comp
                      (fundamentalSolution hA hΦ' h0' s)))) s) →
        D₃k h = V t := by
  obtain ⟨D₃k, hD₃k⟩ := exists_continuousLinearMap_thirdVariation_coeff x₀ hA hAcont hD2cont hD3cont
    hΦ' h0' hC'0 hC''0 hN₂0 hC' hC'' hW2cont hW2 hV0cont hV0add hV0smul hV0bound k ht
  have hgron : 0 ≤ gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
    have hx : 0 ≤ t - t₀ := sub_nonneg.mpr ht.1
    rcases eq_or_lt_of_le K.coe_nonneg with hK | hK
    · rw [← hK]; simp [gronwallBound_K0, hx]
    · rw [gronwallBound_of_K_ne_0 (ne_of_gt hK)]
      have h1 : 0 ≤ Real.exp ((K : ℝ) * (t - t₀)) - 1 :=
        by linarith [Real.one_le_exp (by positivity : (0 : ℝ) ≤ (K : ℝ) * (t - t₀))]
      positivity
  have hfac : (0 : ℝ) ≤ 2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀))
      + C' * N₀ * Real.exp ((K : ℝ) * (T - t₀)) * ‖k‖
      + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)) * ‖k‖ := by
    have h1 : (0 : ℝ) ≤ 2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC'0) hN₂0) (Real.exp_pos _).le
    have h2 : (0 : ℝ) ≤ C' * N₀ * Real.exp ((K : ℝ) * (T - t₀)) * ‖k‖ :=
      mul_nonneg (mul_nonneg (mul_nonneg hC'0 hN₀0) (Real.exp_pos _).le) (norm_nonneg _)
    have h3 : (0 : ℝ) ≤ C'' * Real.exp (3 * (K : ℝ) * (T - t₀)) * ‖k‖ :=
      mul_nonneg (mul_nonneg hC''0 (Real.exp_pos _).le) (norm_nonneg _)
    linarith
  have hC0 : (0 : ℝ) ≤ (2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀))
      + C' * N₀ * Real.exp ((K : ℝ) * (T - t₀)) * ‖k‖
      + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)) * ‖k‖)
      * gronwallBound 0 (K : ℝ) 1 (t - t₀) := mul_nonneg hfac hgron
  refine ⟨D₃k, ?_, hD₃k⟩
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 (fun h => ?_)
  obtain ⟨Vh, hVh0, hVhderiv⟩ :=
    exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv_coeff x₀ hA hAcont hD2cont hD3cont
      hΦ' h0' hW2cont (hV0cont h) k h
  rw [hD₃k h Vh hVh0 hVhderiv]
  have hle := norm_thirdVariation_coeff_le x₀ hA hΦ' h0' hC'0 hC''0 hN₂0 hC' hC'' hW2
    (hV0bound h) k h hVhderiv hVh0 ht
  calc ‖Vh t‖
      ≤ (2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖
          + C' * (N₀ * ‖h‖) * Real.exp ((K : ℝ) * (T - t₀)) * ‖k‖
          + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)) * ‖k‖ * ‖h‖)
        * gronwallBound 0 (K : ℝ) 1 (t - t₀) := hle
    _ = (2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀))
          + C' * N₀ * Real.exp ((K : ℝ) * (T - t₀)) * ‖k‖
          + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)) * ‖k‖)
        * gronwallBound 0 (K : ℝ) 1 (t - t₀) * ‖h‖ := by ring

/-- **Additivity in the base direction `k` of the design-corrected third variation.**  The `k`-analogue
of `thirdVariation_coeff_perturbation_add_eq` and the corrected analogue of
`thirdVariation_baseDir_add_eq`.  The coefficient-variation leading term `(D²v[W k]) ∘ V₀` carries the
base direction `k` *explicitly* (through `W k`), while its `h`-direction curve `V₀` is fixed (independent
of `k`); the base-direction curve `W₂` is additive (`hW2add`, as for `W₂ k = ∂_{x₀} W · k`).  So for
`k₁ + k₂` with `W₂ (k₁ + k₂) = W₂ k₁ + W₂ k₂` (and the same fixed `V₀`), the corrected four-term forcing
is additive: `F_A`, `F_B` via the additivity of `W₂ k`, the leading term via `map_add` on `W (k₁+k₂)`
then `add_comp` (with `V₀` fixed), and `F_C` via `map_add`/`curryLeft_add`; `hasDerivAt_inhomogVariation_add`
and `inhomogVariation_unique` give `V^{k₁+k₂} = V^{k₁} + V^{k₂}`.  The additive-in-`k` half of packaging
the full bilinear corrected operator `(k, h) ↦ D₃(k, h)`. -/
theorem thirdVariation_coeff_baseDir_add_eq
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E} {K : ℝ≥0}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    {W2 : E → ℝ → (E →L[ℝ] E)} {V0 : ℝ → (E →L[ℝ] E)}
    (hW2add : ∀ k₁ k₂ s, W2 (k₁ + k₂) s = W2 k₁ s + W2 k₂ s)
    (k₁ k₂ h : E) {V₁ V₂ V₁₂ : ℝ → (E →L[ℝ] E)}
    (hV₁ : ∀ s, HasDerivAt V₁
      ((Dv s (Φ x₀ s)).comp (V₁ s)
        + (((D2v s (Φ x₀ s)).comp (W2 k₁ s) h).comp (fundamentalSolution hA hΦ' h0' s)
           + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 k₁ s)
           + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k₁).comp (V0 s)
              + (continuousMultilinearCurryFin1 ℝ E E
                  (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k₁)).curryLeft
                    (fundamentalSolution hA hΦ' h0' s h))).comp
                  (fundamentalSolution hA hΦ' h0' s)))) s)
    (hV₂ : ∀ s, HasDerivAt V₂
      ((Dv s (Φ x₀ s)).comp (V₂ s)
        + (((D2v s (Φ x₀ s)).comp (W2 k₂ s) h).comp (fundamentalSolution hA hΦ' h0' s)
           + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 k₂ s)
           + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k₂).comp (V0 s)
              + (continuousMultilinearCurryFin1 ℝ E E
                  (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k₂)).curryLeft
                    (fundamentalSolution hA hΦ' h0' s h))).comp
                  (fundamentalSolution hA hΦ' h0' s)))) s)
    (hV₁₂ : ∀ s, HasDerivAt V₁₂
      ((Dv s (Φ x₀ s)).comp (V₁₂ s)
        + (((D2v s (Φ x₀ s)).comp (W2 (k₁ + k₂) s) h).comp (fundamentalSolution hA hΦ' h0' s)
           + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 (k₁ + k₂) s)
           + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) (k₁ + k₂)).comp (V0 s)
              + (continuousMultilinearCurryFin1 ℝ E E
                  (((D3v s (Φ x₀ s)).curryLeft
                        (fundamentalSolution hA hΦ' h0' s (k₁ + k₂))).curryLeft
                    (fundamentalSolution hA hΦ' h0' s h))).comp
                  (fundamentalSolution hA hΦ' h0' s)))) s)
    (hV₁0 : V₁ t₀ = 0) (hV₂0 : V₂ t₀ = 0) (hV₁₂0 : V₁₂ t₀ = 0)
    (t : ℝ) : V₁₂ t = V₁ t + V₂ t := by
  have hV₁₂' : ∀ s, HasDerivAt V₁₂
      ((Dv s (Φ x₀ s)).comp (V₁₂ s)
        + ((((D2v s (Φ x₀ s)).comp (W2 k₁ s) h).comp (fundamentalSolution hA hΦ' h0' s)
            + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 k₁ s)
            + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k₁).comp (V0 s)
               + (continuousMultilinearCurryFin1 ℝ E E
                   (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k₁)).curryLeft
                     (fundamentalSolution hA hΦ' h0' s h))).comp
                   (fundamentalSolution hA hΦ' h0' s)))
          + (((D2v s (Φ x₀ s)).comp (W2 k₂ s) h).comp (fundamentalSolution hA hΦ' h0' s)
            + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 k₂ s)
            + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k₂).comp (V0 s)
               + (continuousMultilinearCurryFin1 ℝ E E
                   (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k₂)).curryLeft
                     (fundamentalSolution hA hΦ' h0' s h))).comp
                   (fundamentalSolution hA hΦ' h0' s))))) s := by
    intro s
    have hmap :
        (((D2v s (Φ x₀ s)).comp (W2 (k₁ + k₂) s) h).comp (fundamentalSolution hA hΦ' h0' s)
          + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 (k₁ + k₂) s)
          + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) (k₁ + k₂)).comp (V0 s)
             + (continuousMultilinearCurryFin1 ℝ E E
                 (((D3v s (Φ x₀ s)).curryLeft
                       (fundamentalSolution hA hΦ' h0' s (k₁ + k₂))).curryLeft
                   (fundamentalSolution hA hΦ' h0' s h))).comp
                 (fundamentalSolution hA hΦ' h0' s)))
        = (((D2v s (Φ x₀ s)).comp (W2 k₁ s) h).comp (fundamentalSolution hA hΦ' h0' s)
            + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 k₁ s)
            + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k₁).comp (V0 s)
               + (continuousMultilinearCurryFin1 ℝ E E
                   (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k₁)).curryLeft
                     (fundamentalSolution hA hΦ' h0' s h))).comp
                   (fundamentalSolution hA hΦ' h0' s)))
          + (((D2v s (Φ x₀ s)).comp (W2 k₂ s) h).comp (fundamentalSolution hA hΦ' h0' s)
            + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 k₂ s)
            + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k₂).comp (V0 s)
               + (continuousMultilinearCurryFin1 ℝ E E
                   (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k₂)).curryLeft
                     (fundamentalSolution hA hΦ' h0' s h))).comp
                   (fundamentalSolution hA hΦ' h0' s))) := by
      rw [hW2add k₁ k₂ s]
      simp only [map_add, curryLeft_add, ContinuousLinearMap.comp_add,
        ContinuousLinearMap.add_comp, ContinuousLinearMap.add_apply]
      abel
    have := hV₁₂ s
    rwa [hmap] at this
  have hsum := hasDerivAt_inhomogVariation_add hV₁ hV₂
  have h0 : V₁₂ t₀ = (fun r => V₁ r + V₂ r) t₀ := by simp [hV₁₂0, hV₁0, hV₂0]
  exact inhomogVariation_unique hA hV₁₂' hsum h0 t

/-- **Homogeneity in the base direction `k` of the design-corrected third variation.**  The
scalar-homogeneous companion of `thirdVariation_coeff_baseDir_add_eq` and the corrected analogue of
`thirdVariation_baseDir_smul_eq`.  With `W₂` homogeneous in the base direction (`hW2smul`) and the fixed
`h`-direction curve `V₀`, scaling `k` by `c` scales the corrected third variation by `c`:
`V^{c • k} t = c • V^k t`.  The corrected four-term forcing is homogeneous in `k`: `F_A`, `F_B` via
`comp_smul`/`smul_comp`/`smul_apply` on `W₂ k`, the leading term `(D²v[W (c•k)]) ∘ V₀` via `map_smul` on
`W (c•k)` then `smul_comp` (with `V₀` fixed), and `F_C` via `map_smul`/`curryLeft_smul` on `W k`; then
`hasDerivAt_inhomogVariation_smul` and `inhomogVariation_unique` finish.  The homogeneous-in-`k` half of
packaging the full bilinear corrected operator `(k, h) ↦ D₃(k, h)`. -/
theorem thirdVariation_coeff_baseDir_smul_eq
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E} {K : ℝ≥0}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    {W2 : E → ℝ → (E →L[ℝ] E)} {V0 : ℝ → (E →L[ℝ] E)}
    (hW2smul : ∀ (c : ℝ) (k : E) (s : ℝ), W2 (c • k) s = c • W2 k s)
    (c : ℝ) (k h : E) {V Vc : ℝ → (E →L[ℝ] E)}
    (hV : ∀ s, HasDerivAt V
      ((Dv s (Φ x₀ s)).comp (V s)
        + (((D2v s (Φ x₀ s)).comp (W2 k s) h).comp (fundamentalSolution hA hΦ' h0' s)
           + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 k s)
           + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (V0 s)
              + (continuousMultilinearCurryFin1 ℝ E E
                  (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                    (fundamentalSolution hA hΦ' h0' s h))).comp
                  (fundamentalSolution hA hΦ' h0' s)))) s)
    (hVc : ∀ s, HasDerivAt Vc
      ((Dv s (Φ x₀ s)).comp (Vc s)
        + (((D2v s (Φ x₀ s)).comp (W2 (c • k) s) h).comp (fundamentalSolution hA hΦ' h0' s)
           + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 (c • k) s)
           + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) (c • k)).comp (V0 s)
              + (continuousMultilinearCurryFin1 ℝ E E
                  (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s (c • k))).curryLeft
                    (fundamentalSolution hA hΦ' h0' s h))).comp
                  (fundamentalSolution hA hΦ' h0' s)))) s)
    (hV0 : V t₀ = 0) (hVc0 : Vc t₀ = 0)
    (t : ℝ) : Vc t = c • V t := by
  have hVc' : ∀ s, HasDerivAt Vc
      ((Dv s (Φ x₀ s)).comp (Vc s)
        + c • (((D2v s (Φ x₀ s)).comp (W2 k s) h).comp (fundamentalSolution hA hΦ' h0' s)
            + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 k s)
            + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (V0 s)
               + (continuousMultilinearCurryFin1 ℝ E E
                   (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                     (fundamentalSolution hA hΦ' h0' s h))).comp
                   (fundamentalSolution hA hΦ' h0' s)))) s := by
    intro s
    have hmap :
        (((D2v s (Φ x₀ s)).comp (W2 (c • k) s) h).comp (fundamentalSolution hA hΦ' h0' s)
          + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 (c • k) s)
          + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) (c • k)).comp (V0 s)
             + (continuousMultilinearCurryFin1 ℝ E E
                 (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s (c • k))).curryLeft
                   (fundamentalSolution hA hΦ' h0' s h))).comp
                 (fundamentalSolution hA hΦ' h0' s)))
        = c • (((D2v s (Φ x₀ s)).comp (W2 k s) h).comp (fundamentalSolution hA hΦ' h0' s)
            + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 k s)
            + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (V0 s)
               + (continuousMultilinearCurryFin1 ℝ E E
                   (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                     (fundamentalSolution hA hΦ' h0' s h))).comp
                   (fundamentalSolution hA hΦ' h0' s))) := by
      rw [hW2smul c k s]
      simp only [map_smul, curryLeft_smul, ContinuousLinearMap.comp_smul,
        ContinuousLinearMap.smul_comp, ContinuousLinearMap.smul_apply, smul_add]
    have := hVc s
    rwa [hmap] at this
  have hsmul := hasDerivAt_inhomogVariation_smul c hV
  have h0 : Vc t₀ = (fun r => c • V r) t₀ := by simp [hVc0, hV0]
  exact inhomogVariation_unique hA hVc' hsmul h0 t

/-- **The full bilinear design-corrected third-variation operator `D₃`.**  The corrected analogue of
`exists_continuousLinearMap_thirdVariation_bilinear`: packages `(k, h) ↦ D₃(k, h)` for the *corrected*
four-term forcing as a bounded linear map `D₃ : E →L[ℝ] (E →L[ℝ] (E →L[ℝ] E))`.

Both auxiliary curves are supplied linearly: the base-direction curve `W₂ : E → (ℝ → (E →L E))` linear in
`k` (`hW2add`/`hW2smul`, continuous `hW2cont`, bounded `‖W₂ k s‖ ≤ N₂·‖k‖`), and the inner-direction
curve `V0fun : E → (ℝ → (E →L E))` linear in `h` (`hV0add`/`hV0smul`, continuous `hV0cont`, bounded
`‖V0fun h s‖ ≤ N₀·‖h‖`).  For each base direction `k` the inner operator `D₃(k)`
(`exists_continuousLinearMap_thirdVariation_coeff_norm_le`, with `N₂ ↦ N₂·‖k‖`) has `‖k‖`-scaled
operator norm; the outer additivity/homogeneity `D₃(k₁+k₂) = D₃ k₁ + D₃ k₂`, `D₃(c•k) = c • D₃ k` come
from `thirdVariation_coeff_baseDir_add_eq`/`_smul_eq` (via the value characterisation and
`ContinuousLinearMap.ext`), and the `‖k‖`-linear bound collapses by `ring`, so `LinearMap.mkContinuous`
yields `D₃`.  This is the design-corrected `D₃ : E →L (E →L (E →L E))` — the object the base-point
second-order Taylor remainder `‖(D₂(z) − D₂(x₀)) − D₃(z − x₀)‖ ≤ C‖z − x₀‖²` (now closable, `F₃` being the
correct linearisation) consumes toward the flow-resolvent's spatial `ContDiff ℝ 3`. -/
theorem exists_continuousLinearMap_thirdVariation_coeff_bilinear [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E} {K : ℝ≥0}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hAcont : Continuous (fun s => Dv s (Φ x₀ s)))
    (hD2cont : Continuous (fun s => D2v s (Φ x₀ s)))
    (hD3cont : Continuous (fun s => D3v s (Φ x₀ s)))
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    {C' C'' N₂ N₀ : ℝ} (hC'0 : 0 ≤ C') (hC''0 : 0 ≤ C'') (hN₂0 : 0 ≤ N₂) (hN₀0 : 0 ≤ N₀)
    (hC' : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ C') (hC'' : ∀ s, ‖D3v s (Φ x₀ s)‖ ≤ C'')
    {W2 : E → ℝ → (E →L[ℝ] E)} (hW2cont : ∀ k, Continuous (W2 k))
    (hW2add : ∀ k₁ k₂ s, W2 (k₁ + k₂) s = W2 k₁ s + W2 k₂ s)
    (hW2smul : ∀ (c : ℝ) (k : E) (s : ℝ), W2 (c • k) s = c • W2 k s)
    {T : ℝ} (hW2 : ∀ (k : E), ∀ s ∈ Set.Icc t₀ T, ‖W2 k s‖ ≤ N₂ * ‖k‖)
    {V0fun : E → (ℝ → (E →L[ℝ] E))} (hV0cont : ∀ h, Continuous (V0fun h))
    (hV0add : ∀ (h₁ h₂ : E) (s : ℝ), V0fun (h₁ + h₂) s = V0fun h₁ s + V0fun h₂ s)
    (hV0smul : ∀ (c : ℝ) (h : E) (s : ℝ), V0fun (c • h) s = c • V0fun h s)
    (hV0bound : ∀ (h : E), ∀ s ∈ Set.Icc t₀ T, ‖V0fun h s‖ ≤ N₀ * ‖h‖)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ∃ D₃ : E →L[ℝ] (E →L[ℝ] (E →L[ℝ] E)),
      ∀ (k h : E) (V : ℝ → (E →L[ℝ] E)), V t₀ = 0 →
        (∀ s, HasDerivAt V
          ((Dv s (Φ x₀ s)).comp (V s)
            + (((D2v s (Φ x₀ s)).comp (W2 k s) h).comp (fundamentalSolution hA hΦ' h0' s)
               + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (W2 k s)
               + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (V0fun h s)
                  + (continuousMultilinearCurryFin1 ℝ E E
                      (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                        (fundamentalSolution hA hΦ' h0' s h))).comp
                      (fundamentalSolution hA hΦ' h0' s)))) s) →
        D₃ k h = V t := by
  choose D₃ hD₃nb hD₃char using fun k =>
    exists_continuousLinearMap_thirdVariation_coeff_norm_le x₀ hA hAcont hD2cont hD3cont hΦ' h0'
      hC'0 hC''0 (mul_nonneg hN₂0 (norm_nonneg k)) hN₀0 hC' hC'' (hW2cont k) (hW2 k)
      hV0cont hV0add hV0smul hV0bound k ht
  have hadd : ∀ k₁ k₂ : E, D₃ (k₁ + k₂) = D₃ k₁ + D₃ k₂ := by
    intro k₁ k₂
    refine ContinuousLinearMap.ext (fun h => ?_)
    obtain ⟨V₁, hV₁0, hV₁d⟩ := exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv_coeff
      x₀ hA hAcont hD2cont hD3cont hΦ' h0' (hW2cont k₁) (hV0cont h) k₁ h
    obtain ⟨V₂, hV₂0, hV₂d⟩ := exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv_coeff
      x₀ hA hAcont hD2cont hD3cont hΦ' h0' (hW2cont k₂) (hV0cont h) k₂ h
    obtain ⟨V₁₂, hV₁₂0, hV₁₂d⟩ := exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv_coeff
      x₀ hA hAcont hD2cont hD3cont hΦ' h0' (hW2cont (k₁ + k₂)) (hV0cont h) (k₁ + k₂) h
    rw [ContinuousLinearMap.add_apply, hD₃char (k₁ + k₂) h V₁₂ hV₁₂0 hV₁₂d,
      hD₃char k₁ h V₁ hV₁0 hV₁d, hD₃char k₂ h V₂ hV₂0 hV₂d]
    exact thirdVariation_coeff_baseDir_add_eq x₀ hA hΦ' h0' hW2add k₁ k₂ h
      hV₁d hV₂d hV₁₂d hV₁0 hV₂0 hV₁₂0 t
  have hsmul : ∀ (c : ℝ) (k : E), D₃ (c • k) = c • D₃ k := by
    intro c k
    refine ContinuousLinearMap.ext (fun h => ?_)
    obtain ⟨V, hV0, hVd⟩ := exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv_coeff
      x₀ hA hAcont hD2cont hD3cont hΦ' h0' (hW2cont k) (hV0cont h) k h
    obtain ⟨Vc, hVc0, hVcd⟩ := exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv_coeff
      x₀ hA hAcont hD2cont hD3cont hΦ' h0' (hW2cont (c • k)) (hV0cont h) (c • k) h
    rw [ContinuousLinearMap.smul_apply, hD₃char (c • k) h Vc hVc0 hVcd,
      hD₃char k h V hV0 hVd]
    exact thirdVariation_coeff_baseDir_smul_eq x₀ hA hΦ' h0' hW2smul c k h hVd hVcd hV0 hVc0 t
  have hbound : ∀ k : E, ‖D₃ k‖
      ≤ ((2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀))
            + C' * N₀ * Real.exp ((K : ℝ) * (T - t₀))
            + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)))
          * gronwallBound 0 (K : ℝ) 1 (t - t₀)) * ‖k‖ := by
    intro k
    refine (hD₃nb k).trans_eq ?_
    ring
  refine ⟨LinearMap.mkContinuous
    { toFun := D₃
      map_add' := hadd
      map_smul' := fun c k => by simpa using hsmul c k }
    ((2 * C' * N₂ * Real.exp ((K : ℝ) * (T - t₀))
        + C' * N₀ * Real.exp ((K : ℝ) * (T - t₀))
        + C'' * Real.exp (3 * (K : ℝ) * (T - t₀)))
      * gronwallBound 0 (K : ℝ) 1 (t - t₀)) hbound, ?_⟩
  intro k h V hV0 hVderiv
  simpa using hD₃char k h V hV0 hVderiv

/-- **Second-order (quadratic-remainder) Taylor engine for the bilinear composition forcing.**
The `C³`-layer analogue of the first-order (Lipschitz) perturbation bound
`norm_bilinearCompForcing_sub_le`: it identifies the **three linear-variation terms** of the
composition forcing `G(P, A, B) := ((P ∘ A) h) ∘ B` (trilinear in `(P, A, B)`) with a remainder
controlled *quadratically* by the factor Taylor remainders and first-order gaps.

For base operands `P₀ : E →L (E →L E)`, `A₀, B₀ : E →L E` (sizes `p, a, b`), perturbed operands
`P₁, A₁, B₁` (first-order gaps `‖P₁ − P₀‖ ≤ δp`, `‖A₁ − A₀‖ ≤ δa`, `‖B₁ − B₀‖ ≤ δb`) and *candidate
linearisations* `dP, dA, dB` with factor Taylor remainders `‖P₁ − P₀ − dP‖ ≤ εp`,
`‖A₁ − A₀ − dA‖ ≤ εa`, `‖B₁ − B₀ − dB‖ ≤ εb`,
`‖(G(P₁,A₁,B₁) − G(P₀,A₀,B₀)) − (G(dP,A₀,B₀) + G(P₀,dA,B₀) + G(P₀,A₀,dB))‖`
`  ≤ (εp·a·b + p·εa·b + p·a·εb + δp·δa·b + δp·a·δb + p·δa·δb + δp·δa·δb) · ‖h‖`.

Proof: the exact trilinear (multilinear) expansion identity
`(G(P₁,A₁,B₁) − G(P₀,A₀,B₀)) − (G(dP,A₀,B₀)+G(P₀,dA,B₀)+G(P₀,A₀,dB))`
`= G(P₁−P₀−dP, A₀, B₀) + G(P₀, A₁−A₀−dA, B₀) + G(P₀, A₀, B₁−B₀−dB)`
`  + G(P₁−P₀, A₁−A₀, B₀) + G(P₁−P₀, A₀, B₁−B₀) + G(P₀, A₁−A₀, B₁−B₀) + G(P₁−P₀, A₁−A₀, B₁−B₀)`
(pure `comp`/apply bilinearity, closed by `simp only [comp_sub, sub_comp, sub_apply]; abel`), followed
by the triangle inequality and the a-priori size bound `norm_bilinearCompForcing_le`
(`‖G(P,A,B)‖ ≤ ‖P‖·‖A‖·‖B‖·‖h‖`) on each of the seven summands: the three "linear-remainder" terms are
`O(ε)` and the four cross terms are quadratic/cubic in the first-order gaps `δ`.

In the `C³` bootstrap this is the engine that identifies the two asymmetric composition forcing terms
`F_A = ((D²v ∘ W₂) h) ∘ W`, `F_B = ((D²v ∘ W) h) ∘ W₂` (with `P₀ = D²v(Φ x₀)`, `A₀ = B₀ = W = D_x Φ`,
`dA = dB = W₂` the second fundamental solution curve) as the linear-in-`(z − x₀)` part of the
second-variation forcing gap `F(z) − F(x₀)` (`F(z) = ((D²v(Φ z) ∘ W_z) h) ∘ W_z`), with the required
`O(‖z − x₀‖²·‖h‖)` remainder — the analytic content of the plan's remaining `(F₁ − F₀)` second-order
forcing remainder toward `ContDiff ℝ 3`. -/
theorem norm_bilinearCompForcing_sub_sub_le
    {P₀ P₁ dP : E →L[ℝ] (E →L[ℝ] E)} {A₀ A₁ dA B₀ B₁ dB : E →L[ℝ] E} (h : E)
    {p a b δp δa δb εp εa εb : ℝ}
    (hP₀ : ‖P₀‖ ≤ p) (hA₀ : ‖A₀‖ ≤ a) (hB₀ : ‖B₀‖ ≤ b)
    (hrP : ‖P₁ - P₀‖ ≤ δp) (hrA : ‖A₁ - A₀‖ ≤ δa) (hrB : ‖B₁ - B₀‖ ≤ δb)
    (hεP : ‖P₁ - P₀ - dP‖ ≤ εp) (hεA : ‖A₁ - A₀ - dA‖ ≤ εa) (hεB : ‖B₁ - B₀ - dB‖ ≤ εb)
    (hp : 0 ≤ p) (ha : 0 ≤ a) (hδp : 0 ≤ δp) (hδa : 0 ≤ δa) :
    ‖(((P₁.comp A₁) h).comp B₁ - ((P₀.comp A₀) h).comp B₀)
        - ((((dP.comp A₀) h).comp B₀) + (((P₀.comp dA) h).comp B₀)
            + (((P₀.comp A₀) h).comp dB))‖
      ≤ (εp * a * b + p * εa * b + p * a * εb
          + δp * δa * b + δp * a * δb + p * δa * δb + δp * δa * δb) * ‖h‖ := by
  have hid :
      (((P₁.comp A₁) h).comp B₁ - ((P₀.comp A₀) h).comp B₀)
        - ((((dP.comp A₀) h).comp B₀) + (((P₀.comp dA) h).comp B₀)
            + (((P₀.comp A₀) h).comp dB))
      = ((((P₁ - P₀ - dP).comp A₀) h).comp B₀)
        + (((P₀.comp (A₁ - A₀ - dA)) h).comp B₀)
        + (((P₀.comp A₀) h).comp (B₁ - B₀ - dB))
        + ((((P₁ - P₀).comp (A₁ - A₀)) h).comp B₀)
        + ((((P₁ - P₀).comp A₀) h).comp (B₁ - B₀))
        + (((P₀.comp (A₁ - A₀)) h).comp (B₁ - B₀))
        + ((((P₁ - P₀).comp (A₁ - A₀)) h).comp (B₁ - B₀)) := by
    simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.sub_apply]
    abel
  rw [hid]
  have hεp0 : 0 ≤ εp := (norm_nonneg (P₁ - P₀ - dP)).trans hεP
  have hεa0 : 0 ≤ εa := (norm_nonneg (A₁ - A₀ - dA)).trans hεA
  have hεb0 : 0 ≤ εb := (norm_nonneg (B₁ - B₀ - dB)).trans hεB
  have hδb0 : 0 ≤ δb := (norm_nonneg (B₁ - B₀)).trans hrB
  have h1 : ‖(((P₁ - P₀ - dP).comp A₀) h).comp B₀‖ ≤ εp * a * b * ‖h‖ :=
    (norm_bilinearCompForcing_le (P₁ - P₀ - dP) A₀ B₀ h).trans (by gcongr)
  have h2 : ‖((P₀.comp (A₁ - A₀ - dA)) h).comp B₀‖ ≤ p * εa * b * ‖h‖ :=
    (norm_bilinearCompForcing_le P₀ (A₁ - A₀ - dA) B₀ h).trans (by gcongr)
  have h3 : ‖((P₀.comp A₀) h).comp (B₁ - B₀ - dB)‖ ≤ p * a * εb * ‖h‖ :=
    (norm_bilinearCompForcing_le P₀ A₀ (B₁ - B₀ - dB) h).trans (by gcongr)
  have h4 : ‖(((P₁ - P₀).comp (A₁ - A₀)) h).comp B₀‖ ≤ δp * δa * b * ‖h‖ :=
    (norm_bilinearCompForcing_le (P₁ - P₀) (A₁ - A₀) B₀ h).trans (by gcongr)
  have h5 : ‖(((P₁ - P₀).comp A₀) h).comp (B₁ - B₀)‖ ≤ δp * a * δb * ‖h‖ :=
    (norm_bilinearCompForcing_le (P₁ - P₀) A₀ (B₁ - B₀) h).trans (by gcongr)
  have h6 : ‖((P₀.comp (A₁ - A₀)) h).comp (B₁ - B₀)‖ ≤ p * δa * δb * ‖h‖ :=
    (norm_bilinearCompForcing_le P₀ (A₁ - A₀) (B₁ - B₀) h).trans (by gcongr)
  have h7 : ‖(((P₁ - P₀).comp (A₁ - A₀)) h).comp (B₁ - B₀)‖ ≤ δp * δa * δb * ‖h‖ :=
    (norm_bilinearCompForcing_le (P₁ - P₀) (A₁ - A₀) (B₁ - B₀) h).trans (by gcongr)
  calc ‖((((P₁ - P₀ - dP).comp A₀) h).comp B₀)
          + (((P₀.comp (A₁ - A₀ - dA)) h).comp B₀)
          + (((P₀.comp A₀) h).comp (B₁ - B₀ - dB))
          + ((((P₁ - P₀).comp (A₁ - A₀)) h).comp B₀)
          + ((((P₁ - P₀).comp A₀) h).comp (B₁ - B₀))
          + (((P₀.comp (A₁ - A₀)) h).comp (B₁ - B₀))
          + ((((P₁ - P₀).comp (A₁ - A₀)) h).comp (B₁ - B₀))‖
      ≤ ‖(((P₁ - P₀ - dP).comp A₀) h).comp B₀‖
          + ‖((P₀.comp (A₁ - A₀ - dA)) h).comp B₀‖
          + ‖((P₀.comp A₀) h).comp (B₁ - B₀ - dB)‖
          + ‖(((P₁ - P₀).comp (A₁ - A₀)) h).comp B₀‖
          + ‖(((P₁ - P₀).comp A₀) h).comp (B₁ - B₀)‖
          + ‖((P₀.comp (A₁ - A₀)) h).comp (B₁ - B₀)‖
          + ‖(((P₁ - P₀).comp (A₁ - A₀)) h).comp (B₁ - B₀)‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact norm_add_le _ _
    _ ≤ εp * a * b * ‖h‖ + p * εa * b * ‖h‖ + p * a * εb * ‖h‖
          + δp * δa * b * ‖h‖ + δp * a * δb * ‖h‖ + p * δa * δb * ‖h‖ + δp * δa * δb * ‖h‖ :=
        add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5)
          h6) h7
    _ = (εp * a * b + p * εa * b + p * a * εb
          + δp * δa * b + δp * a * δb + p * δa * δb + δp * δa * δb) * ‖h‖ := by ring

/-- **`O(‖k‖²)` collapse of the second-order composition-forcing Taylor engine (diagonal case).**
Specialises `norm_bilinearCompForcing_sub_sub_le` to the **diagonal** operand shape
`F(·) = ((P ∘ W) h) ∘ W` (inner and outer factors equal — exactly the second-variation forcing
`((D²v ∘ W) h) ∘ W`) and collapses the seven-term bound into the single clean target rate
`Cquad · ‖k‖² · ‖h‖` that the `ContDiff ℝ 3` `HasFDerivAt`-bridge
`hasFDerivAt_of_eventually_norm_sub_sub_le_sq` consumes.

Given a base point's operator `P₀` (`‖P₀‖ ≤ p`) and resolvent `W₀` (`‖W₀‖ ≤ w`), a perturbed
`P₁, W₁` with **first-order gaps** linear in `k` (`‖P₁ − P₀‖ ≤ dp·‖k‖`, `‖W₁ − W₀‖ ≤ dw·‖k‖`) and
**candidate linearisations** `dP, dW` with **quadratic Taylor remainders** (`‖P₁ − P₀ − dP‖ ≤ cp·‖k‖²`,
`‖W₁ − W₀ − dW‖ ≤ cw·‖k‖²`), and `‖k‖ ≤ 1`,
`‖(((P₁ ∘ W₁) h) ∘ W₁ − ((P₀ ∘ W₀) h) ∘ W₀) − (((dP ∘ W₀) h) ∘ W₀ + ((P₀ ∘ dW) h) ∘ W₀ + ((P₀ ∘ W₀) h) ∘ dW)‖`
`  ≤ (cp·w² + 2·p·cw·w + 2·dp·dw·w + p·dw² + dp·dw²) · ‖k‖² · ‖h‖`.

Proof: `norm_bilinearCompForcing_sub_sub_le` (with `A₀ = B₀ = W₀`, `dA = dB = dW`) gives the seven-term
bound; each summand is `O(‖k‖²)` except the cubic cross term `dp·dw²·‖k‖³`, which the constraint
`‖k‖ ≤ 1` bounds by `dp·dw²·‖k‖²` (`‖k‖³ ≤ ‖k‖²`); `nlinarith` then absorbs everything into the single
`Cquad·‖k‖²` factor.  In the `C³` bootstrap `k = z − x₀`, `P₀ = D²v(Φ x₀)`, `P₁ = D²v(Φ z)`,
`W₀ = D_x Φ`, `W₁ = D_x Φ^{A(z)}`, `dW = W₂` (second fundamental solution curve); the two `dW`-linear
terms are `F_A`, `F_B` and the `dP`-linear term becomes `F_C` after the (remaining) `D³v`-contraction
identification.  So this is the `(F₁ − F₀)` second-order forcing remainder in the diagonal shape, its
final `O(‖z − x₀‖²·‖h‖)` rate exposed. -/
theorem norm_bilinearCompForcing_sub_sub_le_sq
    {P₀ P₁ dP : E →L[ℝ] (E →L[ℝ] E)} {W₀ W₁ dW : E →L[ℝ] E} (h k : E)
    {p w cp cw dp dw : ℝ}
    (hP₀ : ‖P₀‖ ≤ p) (hW₀ : ‖W₀‖ ≤ w)
    (hrP : ‖P₁ - P₀‖ ≤ dp * ‖k‖) (hrW : ‖W₁ - W₀‖ ≤ dw * ‖k‖)
    (hεP : ‖P₁ - P₀ - dP‖ ≤ cp * ‖k‖ ^ 2) (hεW : ‖W₁ - W₀ - dW‖ ≤ cw * ‖k‖ ^ 2)
    (hp : 0 ≤ p) (hw : 0 ≤ w) (hdp : 0 ≤ dp) (hdw : 0 ≤ dw) (hk : ‖k‖ ≤ 1) :
    ‖(((P₁.comp W₁) h).comp W₁ - ((P₀.comp W₀) h).comp W₀)
        - ((((dP.comp W₀) h).comp W₀) + (((P₀.comp dW) h).comp W₀)
            + (((P₀.comp W₀) h).comp dW))‖
      ≤ (cp * w * w + 2 * p * cw * w + 2 * dp * dw * w + p * dw * dw + dp * dw * dw)
          * ‖k‖ ^ 2 * ‖h‖ := by
  refine (norm_bilinearCompForcing_sub_sub_le h hP₀ hW₀ hW₀ hrP hrW hrW hεP hεW hεW hp hw
      (mul_nonneg hdp (norm_nonneg k)) (mul_nonneg hdw (norm_nonneg k))).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg h)
  have hknn : (0 : ℝ) ≤ ‖k‖ := norm_nonneg k
  have hextra : dp * dw * dw * ‖k‖ ^ 2 * (1 - ‖k‖) ≥ 0 :=
    mul_nonneg (by positivity) (by linarith)
  nlinarith [hextra, hknn, hk, sq_nonneg ‖k‖]

/-- **Pure quadratic (`C^{2,1}`) Taylor bound for the field's second spatial derivative** — the
`D²v`-analogue of `norm_derivField_sub_sub_secondDeriv_le`, one order up.  For the field's second
spatial derivative in the **multilinear representation** `D²v s : E → (E[×2]→L E)` — with third spatial
derivative `D³v s : E → (E →L (E[×2]→L E))`, `M`-Lipschitz — the Taylor remainder is quadratic:
`‖D²v s b − D²v s a − D³v s a (b − a)‖ ≤ M · ‖b − a‖²`.

Crucially the derivative's codomain `E[×2]→L E = ContinuousMultilinearMap ℝ (Fin 2) E` **does** carry
`NormedAddCommGroup`/`NormedSpace` instances (so `E →L (E[×2]→L E)` does too, and `LipschitzWith M`
type-checks), whereas the naive operator-curried triple `E →L (E →L (E →L E))` carries **no** norm
instance in Mathlib v4.29.1 (verified) — hence the second derivative must be Taylor-expanded in this
multilinear representation, and later bridged to the composition form of the second-variation forcing
via the `continuousMultilinearCurryFin1` isometries.  A one-line specialisation of the codomain-generic
`norm_sub_fderiv_le_mul_sq_of_lipschitz` (`g = D²v s`, `g' = D³v s`).  This is the `D³v`-Taylor
ingredient of the remaining `(F₁ − F₀)` second-order forcing remainder toward `ContDiff ℝ 3`. -/
theorem norm_secondDerivField_sub_sub_thirdDeriv_ml_le
    {D2v : ℝ → E → (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)}
    {D3v : ℝ → E → (E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E))}
    {M : ℝ≥0} {s : ℝ}
    (hD2v : ∀ ξ, HasFDerivAt (D2v s) (D3v s ξ) ξ) (hD3vlip : LipschitzWith M (D3v s)) (a b : E) :
    ‖D2v s b - D2v s a - D3v s a (b - a)‖ ≤ (M : ℝ) * ‖b - a‖ ^ 2 :=
  norm_sub_fderiv_le_mul_sq_of_lipschitz hD2v hD3vlip a b

/-- **Flow-tube quadratic bound for the field's second-derivative linearisation defect** — the
`D²v`-analogue of `norm_field_linearizationDefect_flow_le`.  For a uniformly `K`-Lipschitz field `v`
whose second spatial derivative `D²v s : E → (E[×2]→L E)` has an everywhere-defined, `M`-Lipschitz
Fréchet derivative `D³v s : E → (E →L (E[×2]→L E))`, the trajectory linearisation of `D²v` has a
quadratically small defect, uniformly on the compact time tube `|s − t₀| ≤ T`:
`‖D²v s (Φ z s) − D²v s (Φ x s) − D³v s (Φ x s) (Φ z s − Φ x s)‖ ≤ M · exp (2 K T) · ‖z − x‖²`.
Combines the pure multilinear Taylor bound `norm_secondDerivField_sub_sub_thirdDeriv_ml_le`
(`a = Φ x s`, `b = Φ z s`) with the flow-separation square bound `norm_flow_sub_sq_le`
(`‖Φ z s − Φ x s‖² ≤ exp (2 K T) ‖z − x‖²`).  With `Φ z s − Φ x s ≈ D_x Φ_s (z − x)` this is the
`O(‖z − x‖²)` residual isolating the leading `D³v(Φ x s)[D_x Φ_s (z − x)]` term of the base-point
second-derivative coefficient expansion — the flow-tube `D³v`-Taylor datum the `(F₁ − F₀)` forcing
remainder consumes for its `dP`-linear (`F_C`) term. -/
theorem norm_secondDerivField_sub_sub_thirdDeriv_ml_flow_le
    {Φ : E → ℝ → E}
    {D2v : ℝ → E → (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)}
    {D3v : ℝ → E → (E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E))}
    {M : ℝ≥0} {s T : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hD2v : ∀ ξ, HasFDerivAt (D2v s) (D3v s ξ) ξ) (hD3vlip : LipschitzWith M (D3v s))
    (hsT : |s - t₀| ≤ T) (x z : E) :
    ‖D2v s (Φ z s) - D2v s (Φ x s) - D3v s (Φ x s) (Φ z s - Φ x s)‖
      ≤ (M : ℝ) * Real.exp (2 * (K : ℝ) * T) * ‖z - x‖ ^ 2 := by
  refine (norm_secondDerivField_sub_sub_thirdDeriv_ml_le hD2v hD3vlip (Φ x s) (Φ z s)).trans ?_
  have hfs := norm_flow_sub_sq_le hv hΦ h0 hsT x z
  calc (M : ℝ) * ‖Φ z s - Φ x s‖ ^ 2
      ≤ (M : ℝ) * (Real.exp (2 * (K : ℝ) * T) * ‖z - x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hfs M.coe_nonneg
    _ = (M : ℝ) * Real.exp (2 * (K : ℝ) * T) * ‖z - x‖ ^ 2 := by ring

/-- **Central `C³` coefficient Taylor bound (multilinear representation)** — the `D²v`-analogue of
`norm_derivField_sub_sub_comp_fundamentalSolution_le_sq`, one order up.  This is the *single remaining
analytic ingredient* of the `(F₁ − F₀)` second-order forcing remainder toward `ContDiff ℝ 3`: it
identifies the base-point second-derivative gap `D²v(Φ z s) − D²v(Φ x₀ s)` with its **linearised**
form `D³v(Φ x₀ s)[D_x Φ_s (z − x₀)]` — the third derivative contracted with the resolvent-linearised
increment `W_x k = fundamentalSolution … s (z − x₀)` — up to a quadratic `O(‖z − x₀‖²)` remainder,
uniformly on the compact time tube `[t₀, T]`:
`‖(D²v(Φ z s) − D²v(Φ x₀ s)) − D³v(Φ x₀ s)(W_x (z − x₀))‖ ≤ (M · e + N · (L · e · g)) · ‖z − x₀‖²`,
with `e = exp (2 K (T − t₀))`, `g = gronwallBound 0 K 1 (T − t₀)`.

Everything is in the *multilinear* representation `D²v s : E → (E[×2]→L E)`,
`D³v s : E → (E →L (E[×2]→L E))` (both norm-carrying, unlike the instance-less operator-curried
triple `E →L (E →L (E →L E))`), so `LipschitzWith M (D³v s)` and the operator-evaluation bounds
type-check.  Proof mirrors the `C²` template: split the linearised gap as the flow-Taylor defect
`D²v(Φ z s) − D²v(Φ x₀ s) − D³v(Φ x₀ s)(Φ z s − Φ x₀ s)` (bounded `≤ M · e · ‖k‖²` by the flow-tube
multilinear Taylor `norm_secondDerivField_sub_sub_thirdDeriv_ml_flow_le`) plus the linearisation
residual `D³v(Φ x₀ s)((Φ z s − Φ x₀ s) − W_x k)` (bounded `≤ N · (L · e · g) · ‖k‖²` by the operator
bound `‖D³v(Φ x₀ s)‖ ≤ N` times the first-order flow remainder
`norm_flow_sub_fundamentalSolution_le_sq`).  With this the `dP`-linear term of
`norm_bilinearCompForcing_sub_sub_le` — after the `continuousMultilinearCurryFin1`/`curryLeft`
representation bridge — is identified with the module's `F_C` with an `O(‖z − x₀‖²)` residual,
completing (alongside `norm_coeffVariation_sub_secondDerivComp_le_sq`) the `(F₁ − F₀)` forcing gap. -/
theorem norm_secondDerivField_sub_sub_thirdDeriv_ml_fundamentalSolution_le_sq
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)}
    {D2v : ℝ → E → (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)}
    {D3v : ℝ → E → (E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E))}
    {L M : ℝ≥0} {N : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ) (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD3v : ∀ s ξ, HasFDerivAt (D2v s) (D3v s ξ) ξ) (hD3vlip : ∀ s, LipschitzWith M (D3v s))
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hN0 : 0 ≤ N) (hN : ∀ s, ‖D3v s (Φ x₀ s)‖ ≤ N)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    (z : E) {T s : ℝ} (hs : s ∈ Icc t₀ T) :
    ‖D2v s (Φ z s) - D2v s (Φ x₀ s)
        - D3v s (Φ x₀ s) (fundamentalSolution hA hΦ' h0' s (z - x₀))‖
      ≤ ((M : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
          + N * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
              * gronwallBound 0 (K : ℝ) 1 (T - t₀))) * ‖z - x₀‖ ^ 2 := by
  have hsT : |s - t₀| ≤ T - t₀ := by
    rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
  have hms : D3v s (Φ x₀ s) ((Φ z s - Φ x₀ s) - fundamentalSolution hA hΦ' h0' s (z - x₀))
      = D3v s (Φ x₀ s) (Φ z s - Φ x₀ s)
        - D3v s (Φ x₀ s) (fundamentalSolution hA hΦ' h0' s (z - x₀)) :=
    (D3v s (Φ x₀ s)).map_sub _ _
  have hsplit :
      D2v s (Φ z s) - D2v s (Φ x₀ s)
          - D3v s (Φ x₀ s) (fundamentalSolution hA hΦ' h0' s (z - x₀))
        = (D2v s (Φ z s) - D2v s (Φ x₀ s) - D3v s (Φ x₀ s) (Φ z s - Φ x₀ s))
          + D3v s (Φ x₀ s) ((Φ z s - Φ x₀ s) - fundamentalSolution hA hΦ' h0' s (z - x₀)) := by
    rw [hms]; abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hb1 : ‖D2v s (Φ z s) - D2v s (Φ x₀ s) - D3v s (Φ x₀ s) (Φ z s - Φ x₀ s)‖
      ≤ (M : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀)) * ‖z - x₀‖ ^ 2 :=
    norm_secondDerivField_sub_sub_thirdDeriv_ml_flow_le hv hΦ h0 (hD3v s) (hD3vlip s) hsT x₀ z
  have hb2 : ‖D3v s (Φ x₀ s) ((Φ z s - Φ x₀ s) - fundamentalSolution hA hΦ' h0' s (z - x₀))‖
      ≤ N * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
          * gronwallBound 0 (K : ℝ) 1 (T - t₀)) * ‖z - x₀‖ ^ 2 := by
    have hflow := norm_flow_sub_fundamentalSolution_le_sq hv hΦ h0 hDv hDvlip x₀ hA hΦ' h0' z hs
    calc ‖D3v s (Φ x₀ s) ((Φ z s - Φ x₀ s) - fundamentalSolution hA hΦ' h0' s (z - x₀))‖
        ≤ ‖D3v s (Φ x₀ s)‖
            * ‖(Φ z s - Φ x₀ s) - fundamentalSolution hA hΦ' h0' s (z - x₀)‖ :=
          (D3v s (Φ x₀ s)).le_opNorm _
      _ ≤ N * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
            * gronwallBound 0 (K : ℝ) 1 (T - t₀) * ‖z - x₀‖ ^ 2) :=
          mul_le_mul (hN s) hflow (norm_nonneg _) hN0
      _ = N * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
            * gronwallBound 0 (K : ℝ) 1 (T - t₀)) * ‖z - x₀‖ ^ 2 := by ring
  exact (add_le_add hb1 hb2).trans_eq (by ring)

/-- **Two-fold left-curry to composition form.**  The isometric realisation of a `Fin 2` multilinear
map `X : E[×2]→L E` as an honest iterated operator `E →L (E →L E)`, with `curry2 X a b = X ![a, b]`
(`curry2_apply`).  This is the representation bridge between the *multilinear* form — in which the
field's second derivative `D²v : E → (E[×2]→L E)` and its `C³` Taylor expansion live (the only form in
which the third derivative carries a norm, `E →L (E[×2]→L E)`) — and the *composition* form
`E →L (E →L E)` in which the second-variation forcing `((D²v ∘ W) h) ∘ W` and the trilinear engine
`norm_bilinearCompForcing_*` operate.  Built by post-composing the left-curry
`X.curryLeft : E →L (E[×1]→L E)` with the `Fin 1` evaluation isometry
`continuousMultilinearCurryFin1 ℝ E E : (E[×1]→L E) ≃ₗᵢ (E →L E)`. -/
noncomputable def curry2 (X : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E) :
    E →L[ℝ] (E →L[ℝ] E) :=
  (continuousMultilinearCurryFin1 ℝ E E).toContinuousLinearEquiv.toContinuousLinearMap.comp
    X.curryLeft

/-- **Pointwise evaluation of the two-fold curry**: `curry2 X a b = X ![a, b]`.  Gives the composition
form its meaning — the operator `a ↦ (b ↦ X[a, b])` — so that a composition-form forcing
`((curry2 X ∘ W) h) ∘ W` evaluated at `e` is `X[W h, W e]`, identifying it (with `X` a contracted third
derivative) as the module's third-derivative forcing term `F_C`. -/
theorem curry2_apply (X : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E) (a b : E) :
    curry2 X a b = X ![a, b] := by
  rw [curry2, ContinuousLinearMap.comp_apply]
  simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    continuousMultilinearCurryFin1_apply, ContinuousMultilinearMap.curryLeft_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- The two-fold curry distributes over subtraction (it is linear). -/
theorem curry2_sub (X Y : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E) :
    curry2 (X - Y) = curry2 X - curry2 Y := by
  rw [curry2, curry2, curry2,
    show (X - Y).curryLeft = X.curryLeft - Y.curryLeft from
      ContinuousLinearMap.ext (congrFun rfl),
    ContinuousLinearMap.comp_sub]

/-- The two-fold curry is norm-nonexpansive: `‖curry2 X‖ ≤ ‖X‖` (in fact an isometry, `curryLeft`
being one and `continuousMultilinearCurryFin1` a linear isometric equivalence).  This is what lets the
multilinear central `C³` Taylor bound transport verbatim to the composition form without constant
inflation. -/
theorem norm_curry2_le (X : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E) :
    ‖curry2 X‖ ≤ ‖X‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun a => ?_)
  rw [curry2, ContinuousLinearMap.comp_apply]
  have hC : ‖(continuousMultilinearCurryFin1 ℝ E E).toContinuousLinearEquiv.toContinuousLinearMap
      (X.curryLeft a)‖ = ‖X.curryLeft a‖ := by
    simp [LinearIsometryEquiv.norm_map]
  rw [hC]
  calc ‖X.curryLeft a‖ ≤ ‖X.curryLeft‖ * ‖a‖ := (X.curryLeft).le_opNorm a
    _ = ‖X‖ * ‖a‖ := by rw [ContinuousMultilinearMap.curryLeft_norm]

/-- **Composition-form central `C³` coefficient Taylor bound** — the `curry2`-bridged form of
`norm_secondDerivField_sub_sub_thirdDeriv_ml_fundamentalSolution_le_sq`.  Transported through the
representation isometry `curry2`, the multilinear central `C³` Taylor bound becomes a bound on the
*composition-form* second-derivative gap `curry2 (D²v(Φ z s)) − curry2 (D²v(Φ x₀ s))` and its
linearisation `curry2 (D³v(Φ x₀ s)(W_x (z − x₀)))` — exactly the shape the trilinear forcing engine
`norm_bilinearCompForcing_sub_sub_le_sq` consumes as its candidate operator `dP` and quadratic
remainder `εp = cp · ‖k‖²`:
`‖(curry2 (D²v(Φ z s)) − curry2 (D²v(Φ x₀ s))) − curry2 (D³v(Φ x₀ s)(W_x (z − x₀)))‖ ≤ Cquad · ‖z − x₀‖²`,
`Cquad = M · e + N · (L · e · g)`, `e = exp (2 K (T − t₀))`, `g = gronwallBound 0 K 1 (T − t₀)`.

By `curry2_apply`, `curry2 (D²v(·)) : E →L (E →L E)` is the composition form `a b ↦ D²v(·)[a, b]` of the
field's second derivative, and the candidate `dP = curry2 (D³v(Φ x₀ s)(W_x k))` evaluates to
`a b ↦ D³v(Φ x₀ s)[W_x k, a, b]` — so `((dP ∘ W) h) ∘ W` is the once-and-twice contracted third
derivative, i.e. the third-derivative forcing term `F_C`.  Proof: `curry2` is linear (`curry2_sub`), so
the three-term combination collapses to `curry2 (D²v(Φ z s) − D²v(Φ x₀ s) − D³v(Φ x₀ s)(W_x k))`, whose
norm is `≤` the multilinear residual norm (`norm_curry2_le`), bounded by the multilinear central `C³`
Taylor bound `norm_secondDerivField_sub_sub_thirdDeriv_ml_fundamentalSolution_le_sq`.  This is the
representation half of the remaining `(F₁ − F₀)` forcing-remainder step toward `ContDiff ℝ 3`. -/
theorem norm_secondDerivField_curry2_sub_sub_thirdDeriv_le_sq
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)}
    {D2v : ℝ → E → (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)}
    {D3v : ℝ → E → (E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E))}
    {L M : ℝ≥0} {N : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ z, IsIntegralCurve (Φ z) v) (h0 : ∀ z, Φ z t₀ = z)
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ) (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD3v : ∀ s ξ, HasFDerivAt (D2v s) (D3v s ξ) ξ) (hD3vlip : ∀ s, LipschitzWith M (D3v s))
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hN0 : 0 ≤ N) (hN : ∀ s, ‖D3v s (Φ x₀ s)‖ ≤ N)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    (z : E) {T s : ℝ} (hs : s ∈ Icc t₀ T) :
    ‖curry2 (D2v s (Φ z s)) - curry2 (D2v s (Φ x₀ s))
        - curry2 (D3v s (Φ x₀ s) (fundamentalSolution hA hΦ' h0' s (z - x₀)))‖
      ≤ ((M : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
          + N * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
              * gronwallBound 0 (K : ℝ) 1 (T - t₀))) * ‖z - x₀‖ ^ 2 := by
  have hcollapse : curry2 (D2v s (Φ z s)) - curry2 (D2v s (Φ x₀ s))
        - curry2 (D3v s (Φ x₀ s) (fundamentalSolution hA hΦ' h0' s (z - x₀)))
      = curry2 (D2v s (Φ z s) - D2v s (Φ x₀ s)
          - D3v s (Φ x₀ s) (fundamentalSolution hA hΦ' h0' s (z - x₀))) := by
    rw [curry2_sub, curry2_sub]
  rw [hcollapse]
  refine (norm_curry2_le _).trans ?_
  exact norm_secondDerivField_sub_sub_thirdDeriv_ml_fundamentalSolution_le_sq
    hv hΦ h0 hDv hDvlip hD3v hD3vlip x₀ hA hN0 hN hΦ' h0' z hs

/-- **Composition-form `dP`-term equals the third-derivative forcing `F_C`.**  The algebraic identity
completing the representation bridge: the trilinear forcing engine's `dP`-linear term
`((curry2 S ∘ W) h) ∘ W` — the composition-form once-and-twice contracted operator — coincides with
the module's `continuousMultilinearCurryFin1`/`curryLeft`-shaped forcing term
`(continuousMultilinearCurryFin1 ℝ E E (S.curryLeft (W h))).comp W`.  Both send `e ↦ S[W h, W e]`
(`curry2_apply` on the left, `continuousMultilinearCurryFin1_apply` + `curryLeft_apply` on the right).

Applied with `S = (D³v(Φ x₀ s)).curryLeft (W k)` (`W = fundamentalSolution`) the right-hand side is
exactly the third-derivative forcing term `F_C` of
`exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv`
(`(continuousMultilinearCurryFin1 ℝ E E (((D³v(Φ x₀ s)).curryLeft (W k)).curryLeft (W h))).comp W`),
so the composition-form candidate `dP = curry2 ((D³v(Φ x₀ s)).curryLeft (W k))` produced by the trilinear
engine `norm_bilinearCompForcing_sub_sub_le_sq` is identified with `F_C`.  Together with
`norm_secondDerivField_curry2_sub_sub_thirdDeriv_le_sq` (the quadratic remainder `εp = cp · ‖k‖²` for
this `dP`) this closes the representation half of the remaining `(F₁ − F₀)` forcing-remainder step
toward `ContDiff ℝ 3`. -/
theorem bilinearCompForcing_curry2_eq
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E) (W : E →L[ℝ] E) (h : E) :
    (((curry2 S).comp W) h).comp W
      = (continuousMultilinearCurryFin1 ℝ E E (S.curryLeft (W h))).comp W := by
  ext e
  simp only [ContinuousLinearMap.comp_apply, curry2_apply, continuousMultilinearCurryFin1_apply,
    ContinuousMultilinearMap.curryLeft_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- **Flow-Lipschitz first-order gap for the field's second derivative (multilinear representation)** —
the `D²v`-multilinear analogue of `norm_secondDerivField_apply_flow_sub_le`.  For the field's second
derivative in the multilinear representation `D²v s : E → (E[×2]→L E)`, `M`-Lipschitz, the values along
two trajectories differ by `‖D²v s (Φ z s) − D²v s (Φ w s)‖ ≤ M · exp (K T) · ‖z − w‖` on the tube
`|s − t₀| ≤ T` (`M`-Lipschitz composed with the exponential flow-Lipschitz bound
`lipschitzWith_flow_apply_of_abs_le`).  This is the first-order (`dp`) datum of the `(F₁ − F₀)` forcing
remainder in the multilinear representation. -/
theorem norm_secondDerivField_ml_apply_flow_sub_le
    {Φ : E → ℝ → E} {D2v : ℝ → E → (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)}
    {M : ℝ≥0} {s T : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (hD2v : LipschitzWith M (D2v s)) (hsT : |s - t₀| ≤ T) (z w : E) :
    ‖D2v s (Φ z s) - D2v s (Φ w s)‖ ≤ (M : ℝ) * Real.exp ((K : ℝ) * T) * ‖z - w‖ := by
  have hlip : LipschitzWith (M * (Real.exp ((K : ℝ) * T)).toNNReal) (fun z => D2v s (Φ z s)) :=
    hD2v.comp (lipschitzWith_flow_apply_of_abs_le hv hΦ h0 hsT)
  have hd := hlip.dist_le_mul z w
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mul, Real.coe_toNNReal _ (Real.exp_pos _).le] at hd
  exact hd

/-- **Flow-Lipschitz first-order gap for the composition-form second derivative `curry2 (D²v)`** — the
`dp` datum of the `(F₁ − F₀)` forcing remainder in the composition form the trilinear engine consumes:
`‖curry2 (D²v s (Φ z s)) − curry2 (D²v s (Φ w s))‖ ≤ M · exp (K T) · ‖z − w‖`.  The composition-form
operators `P₁ = curry2 (D²v(Φ z s))`, `P₀ = curry2 (D²v(Φ x₀ s))` are the `hrP`/`dp` inputs of
`norm_bilinearCompForcing_sub_sub_le_sq`; since `curry2` is linear (`curry2_sub`) and norm-nonexpansive
(`norm_curry2_le`), the composition-form gap is `≤` the multilinear gap
`norm_secondDerivField_ml_apply_flow_sub_le`. -/
theorem norm_secondDerivField_curry2_apply_flow_sub_le
    {Φ : E → ℝ → E} {D2v : ℝ → E → (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)}
    {M : ℝ≥0} {s T : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v)
    (h0 : ∀ x, Φ x t₀ = x) (hD2v : LipschitzWith M (D2v s)) (hsT : |s - t₀| ≤ T) (z w : E) :
    ‖curry2 (D2v s (Φ z s)) - curry2 (D2v s (Φ w s))‖
      ≤ (M : ℝ) * Real.exp ((K : ℝ) * T) * ‖z - w‖ := by
  rw [← curry2_sub]
  exact (norm_curry2_le _).trans
    (norm_secondDerivField_ml_apply_flow_sub_le hv hΦ h0 hD2v hsT z w)

/-- **`F_C`-form second-order composition-forcing Taylor engine.**  The trilinear quadratic-remainder
engine `norm_bilinearCompForcing_sub_sub_le_sq` fused with the representation bridge
`bilinearCompForcing_curry2_eq`, so its `dP`-linear output is delivered *directly* in the module's
third-derivative forcing shape `F_C = (continuousMultilinearCurryFin1 ℝ E E (S.curryLeft (W₀ h))).comp W₀`
instead of the raw composition-form `((curry2 S ∘ W₀) h) ∘ W₀`.

Choosing the candidate operator `dP := curry2 S` (`S : E[×2]→L E`, the contracted third derivative) and
supplying the six factor bounds (`p, w` sizes; `dp, dw` first-order gaps; `cp, cw` quadratic Taylor
remainders; `‖k‖ ≤ 1`),
`‖(((P₁ ∘ W₁) h) ∘ W₁ − ((P₀ ∘ W₀) h) ∘ W₀) − (F_C + ((P₀ ∘ dW) h) ∘ W₀ + ((P₀ ∘ W₀) h) ∘ dW)‖`
`  ≤ (cp·w² + 2·p·cw·w + 2·dp·dw·w + p·dw² + dp·dw²)·‖k‖²·‖h‖`.
Proof: apply `norm_bilinearCompForcing_sub_sub_le_sq` with `dP = curry2 S`, then rewrite its
`dP`-linear term `((curry2 S ∘ W₀) h) ∘ W₀` into `F_C` via `bilinearCompForcing_curry2_eq`.  This is the
assembled `(F₁ − F₀)` forcing-remainder engine: fed `P₀ = curry2 (D²v(Φ x₀ s))`,
`P₁ = curry2 (D²v(Φ z s))`, `S = D³v(Φ x₀ s)(W_x k)`, `W₀ = W_x`, `W₁ = W_z`, `dW = W₂`, with the six
bounds supplied by `norm_curry2_le`/`hC'` (`p`), `norm_fundamentalSolution_le` (`w`),
`norm_secondDerivField_curry2_apply_flow_sub_le` (`dp`), `norm_fundamentalSolution_baseCurve_sub_le`
(`dw`), `norm_secondDerivField_curry2_sub_sub_thirdDeriv_le_sq` (`cp`) and
`norm_fundamentalSolution_sub_sub_linearVariation_le_sq` (`cw`), it yields the `(F₁ − F₀)` forcing gap
`‖(F₁ − F₀) − (F_C + F_A + F_B)‖ ≤ Cquad·‖z − x₀‖²·‖h‖` toward `ContDiff ℝ 3`. -/
theorem norm_bilinearCompForcing_curry2_sub_sub_le_sq
    {P₀ P₁ : E →L[ℝ] (E →L[ℝ] E)} {W₀ W₁ dW : E →L[ℝ] E}
    (S : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E) (h k : E)
    {p w cp cw dp dw : ℝ}
    (hP₀ : ‖P₀‖ ≤ p) (hW₀ : ‖W₀‖ ≤ w)
    (hrP : ‖P₁ - P₀‖ ≤ dp * ‖k‖) (hrW : ‖W₁ - W₀‖ ≤ dw * ‖k‖)
    (hεP : ‖P₁ - P₀ - curry2 S‖ ≤ cp * ‖k‖ ^ 2) (hεW : ‖W₁ - W₀ - dW‖ ≤ cw * ‖k‖ ^ 2)
    (hp : 0 ≤ p) (hw : 0 ≤ w) (hdp : 0 ≤ dp) (hdw : 0 ≤ dw) (hk : ‖k‖ ≤ 1) :
    ‖(((P₁.comp W₁) h).comp W₁ - ((P₀.comp W₀) h).comp W₀)
        - (((continuousMultilinearCurryFin1 ℝ E E (S.curryLeft (W₀ h))).comp W₀)
            + (((P₀.comp dW) h).comp W₀) + (((P₀.comp W₀) h).comp dW))‖
      ≤ (cp * w * w + 2 * p * cw * w + 2 * dp * dw * w + p * dw * dw + dp * dw * dw)
          * ‖k‖ ^ 2 * ‖h‖ := by
  have hbase := norm_bilinearCompForcing_sub_sub_le_sq h k hP₀ hW₀ hrP hrW hεP hεW hp hw hdp hdw hk
  rwa [bilinearCompForcing_curry2_eq S W₀ h] at hbase

/-- **Representation compatibility of the two second-derivative forms.**  The two-fold curry
`curry2 (iteratedFDeriv ℝ 2 f z)` of the *multilinear* second derivative
`iteratedFDeriv ℝ 2 f z : E[×2]→L E` (the norm-carrying form in which the `C³` Taylor bounds live)
equals the *composition-form* second derivative `fderiv ℝ (fderiv ℝ f) z : E →L (E →L E)` (the form in
which the second-variation ODE forcing and the trilinear engine `norm_bilinearCompForcing_*` operate).

This is the pure `iteratedFDeriv`/`fderiv` representation bridge the `(F₁ − F₀)` assembly needs to
identify the module's composition-form forcing operators `P = curry2 (D²v_ml)` with the field's honest
composition second derivative.  Unconditional (`iteratedFDeriv`/`fderiv` are total): by `curry2_apply`
and Mathlib's `iteratedFDeriv_two_apply` (`iteratedFDeriv ℝ 2 f z m = fderiv (fderiv f) z (m 0) (m 1)`)
evaluated at `m = ![a, b]`. -/
theorem curry2_iteratedFDeriv_two (f : E → E) (z : E) :
    curry2 (iteratedFDeriv ℝ 2 f z) = fderiv ℝ (fderiv ℝ f) z := by
  ext a b
  rw [curry2_apply, iteratedFDeriv_two_apply]
  simp

/-- **Consumable form of the second-derivative representation compatibility.**  If `Df` is the
(composition-form) first derivative of `f` at every point and `D2comp` is the derivative of `Df` at
`x`, then the two-fold curry of the multilinear second derivative equals `D2comp`:
`curry2 (iteratedFDeriv ℝ 2 f x) = D2comp`.  This is the form the `(F₁ − F₀)` assembly threads: the
second-variation ODE forcing of `exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv` carries
its second derivative as an abstract composition-form operator `D2comp` satisfying
`HasFDerivAt Df D2comp x` (with `Df` the field's first derivative), and the `curry2` Taylor bounds carry
it as the multilinear `iteratedFDeriv ℝ 2 f`; this lemma identifies them.  Proof: rewrite by
`curry2_iteratedFDeriv_two`, replace `fderiv ℝ f = Df` (uniqueness of `HasFDerivAt` derivatives), then
`hD2.fderiv`. -/
theorem curry2_iteratedFDeriv_two_eq_of_hasFDerivAt
    {f : E → E} {Df : E → (E →L[ℝ] E)} {D2comp : E →L[ℝ] (E →L[ℝ] E)} {x : E}
    (hDf : ∀ y, HasFDerivAt f (Df y) y) (hD2 : HasFDerivAt Df D2comp x) :
    curry2 (iteratedFDeriv ℝ 2 f x) = D2comp := by
  rw [curry2_iteratedFDeriv_two]
  have hf' : fderiv ℝ f = Df := funext (fun y => (hDf y).fderiv)
  rw [hf']
  exact hD2.fderiv

/-- **Representation bridge for the third derivative.**  The left-curry of the Fin-3 multilinear third
derivative `iteratedFDeriv ℝ 3 f x : E[×3]→L E` equals the composition-form derivative of the Fin-2
multilinear second derivative, `fderiv ℝ (iteratedFDeriv ℝ 2 f) x : E →L (E[×2]→L E)`.  This is the
third-order companion of `curry2_iteratedFDeriv_two`: the module's `F_C` forcing contracts the third
derivative as `(iteratedFDeriv ℝ 3 f ξ).curryLeft (W k)`, whereas the `C³` Taylor bound
`norm_secondDerivField_curry2_sub_sub_thirdDeriv_le_sq` produces it as
`(fderiv ℝ (iteratedFDeriv ℝ 2 f) ξ) (W k)`; this lemma identifies the two.  Unconditional: by
`ContinuousMultilinearMap.curryLeft_apply` and Mathlib's `iteratedFDeriv_succ_apply_left`
(`iteratedFDeriv ℝ 3 f x m = fderiv (iteratedFDeriv ℝ 2 f) x (m 0) (tail m)`) at `m = Fin.cons a b`. -/
theorem curryLeft_iteratedFDeriv_three (f : E → E) (x : E) :
    (iteratedFDeriv ℝ 3 f x).curryLeft = fderiv ℝ (iteratedFDeriv ℝ 2 f) x := by
  ext a b
  rw [ContinuousMultilinearMap.curryLeft_apply, iteratedFDeriv_succ_apply_left]
  simp

/-- **Consumable form of the third-derivative bridge.**  If `D3ml` is the (composition-form) derivative
of the multilinear second derivative `iteratedFDeriv ℝ 2 f` at `x`, then
`D3ml = (iteratedFDeriv ℝ 3 f x).curryLeft`.  This is the form the `(F₁ − F₀)` assembly threads: the
`C³` Taylor bound carries the third derivative as an abstract `D3ml` satisfying
`HasFDerivAt (iteratedFDeriv ℝ 2 f) D3ml x`, and the module's `F_C` forcing carries it as
`(iteratedFDeriv ℝ 3 f x).curryLeft`; this lemma identifies them.  Proof: rewrite the right side by
`curryLeft_iteratedFDeriv_three`, then `hD3.fderiv` (uniqueness of `HasFDerivAt` derivatives). -/
theorem curryLeft_iteratedFDeriv_three_eq_of_hasFDerivAt
    {f : E → E} {D3ml : E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E} {x : E}
    (hD3 : HasFDerivAt (iteratedFDeriv ℝ 2 f) D3ml x) :
    D3ml = (iteratedFDeriv ℝ 3 f x).curryLeft := by
  rw [curryLeft_iteratedFDeriv_three]
  exact hD3.fderiv.symm


/-- **Concrete `(F₁ − F₀)` second-order forcing remainder along the flow.**  The `C³`-layer analogue of
`norm_chainRuleForcing_flow_sub_le`: the second-variation chain-rule forcing
`((D²v(Φ y) ∘ W_y) h) ∘ W_y` at base points `z` and `x₀`, minus its design-corrected first-order
variation `F_C + F_A + F_B`, is `O(‖z − x₀‖² · ‖h‖)` on the forward tube `[t₀, T]`. -/
theorem norm_chainRuleForcing_flow_sub_sub_le_sq [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)}
    {D2vc : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D2vm : ℝ → E → (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)}
    {D3vm : ℝ → E → (E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E))}
    {L M₂ M₃ : ℝ≥0} {C' N : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ) (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2vc : ∀ s ξ, HasFDerivAt (Dv s) (D2vc s ξ) ξ) (hD2vclip : ∀ s, LipschitzWith M₂ (D2vc s))
    (hD3vm : ∀ s ξ, HasFDerivAt (D2vm s) (D3vm s ξ) ξ) (hD3vmlip : ∀ s, LipschitzWith M₃ (D3vm s))
    (hcompat : ∀ s ξ, D2vc s ξ = curry2 (D2vm s ξ))
    (z x₀ : E)
    (hAx : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K) (hAz : ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K)
    (hAxcont : Continuous (fun s => Dv s (Φ x₀ s))) (hAzcont : Continuous (fun s => Dv s (Φ z s)))
    (hC'0 : 0 ≤ C') (hC' : ∀ s, ‖D2vc s (Φ x₀ s)‖ ≤ C')
    (hN0 : 0 ≤ N) (hN : ∀ s, ‖D3vm s (Φ x₀ s)‖ ≤ N)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ x, IsIntegralCurve (Φ' x) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ x, Φ' x t₀ = x)
    {Φ₁ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h0₁ : ∀ x, Φ₁ x t₀ = x)
    {Vz Vlin : ℝ → (E →L[ℝ] E)}
    (hVz : ∀ s, HasDerivAt Vz
      ((Dv s (Φ x₀ s)).comp (Vz s)
        + (Dv s (Φ z s) - Dv s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s)) s)
    (hVz0 : Vz t₀ = 0)
    (hVlin : ∀ s, HasDerivAt Vlin
      ((Dv s (Φ x₀ s)).comp (Vlin s)
        + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) (z - x₀)).comp
            (fundamentalSolution hAx hΦ' h0' s)) s)
    (hVlin0 : Vlin t₀ = 0)
    (h : E) {T : ℝ} (hk : ‖z - x₀‖ ≤ 1) :
    ∃ C : ℝ, ∀ s ∈ Set.Icc t₀ T,
      ‖(((D2vc s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h0₁ s) h).comp
              (fundamentalSolution hAz hΦ₁ h0₁ s)
            - ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp
                (fundamentalSolution hAx hΦ' h0' s))
          - ((continuousMultilinearCurryFin1 ℝ E E
                  ((D3vm s (Φ x₀ s)
                      (fundamentalSolution hAx hΦ' h0' s (z - x₀))).curryLeft
                    (fundamentalSolution hAx hΦ' h0' s h))).comp
                (fundamentalSolution hAx hΦ' h0' s)
              + ((D2vc s (Φ x₀ s)).comp (Vlin s) h).comp (fundamentalSolution hAx hΦ' h0' s)
              + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp (Vlin s))‖
        ≤ C * ‖z - x₀‖ ^ 2 * ‖h‖ := by
  refine ⟨?_, fun s hs => ?_⟩
  rotate_left
  have hsT : |s - t₀| ≤ T - t₀ := by
    rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
  have hexpmono : Real.exp ((K : ℝ) * |s - t₀|) ≤ Real.exp ((K : ℝ) * (T - t₀)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsT K.coe_nonneg)
  have hg : (0 : ℝ) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
    gronwallBound_zero_one_nonneg K.coe_nonneg (sub_nonneg.mpr (le_trans hs.1 hs.2))
  -- p : ‖P₀‖ ≤ C'
  have hP₀ : ‖D2vc s (Φ x₀ s)‖ ≤ C' := hC' s
  -- w : ‖W₀‖ ≤ exp
  have hW₀ : ‖fundamentalSolution hAx hΦ' h0' s‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) :=
    (norm_fundamentalSolution_le hAx hΦ' h0' s).trans hexpmono
  -- dp : first-order D²v gap
  have hrP : ‖D2vc s (Φ z s) - D2vc s (Φ x₀ s)‖
      ≤ (M₂ : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖ :=
    norm_secondDerivField_apply_flow_sub_le hv hΦ h0 (hD2vclip s) hsT z x₀
  -- dw : first-order resolvent gap
  have hrW : ‖fundamentalSolution hAz hΦ₁ h0₁ s - fundamentalSolution hAx hΦ' h0' s‖
      ≤ ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
          * gronwallBound 0 (K : ℝ) 1 (T - t₀)) * ‖z - x₀‖ := by
    have hbase := norm_fundamentalSolution_baseCurve_sub_le hv hΦ h0 hDvlip z x₀ hAz hAx
      hΦ₁ h0₁ hΦ' h0' hs
    have hmono : gronwallBound 0 (K : ℝ) 1 (s - t₀) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
      gronwallBound_mono le_rfl zero_le_one K.coe_nonneg (by linarith [hs.2])
    refine hbase.trans ?_
    calc (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖ * Real.exp ((K : ℝ) * (T - t₀))
            * gronwallBound 0 (K : ℝ) 1 (s - t₀)
        ≤ (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖ * Real.exp ((K : ℝ) * (T - t₀))
            * gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
              * gronwallBound 0 (K : ℝ) 1 (T - t₀)) * ‖z - x₀‖ := by ring
  -- cp : quadratic D²v Taylor remainder (in composition form via hcompat)
  have hεP : ‖D2vc s (Φ z s) - D2vc s (Φ x₀ s)
        - curry2 (D3vm s (Φ x₀ s) (fundamentalSolution hAx hΦ' h0' s (z - x₀)))‖
      ≤ ((M₃ : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
          + N * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
              * gronwallBound 0 (K : ℝ) 1 (T - t₀))) * ‖z - x₀‖ ^ 2 := by
    have hcp := norm_secondDerivField_curry2_sub_sub_thirdDeriv_le_sq
      hv hΦ h0 hDv hDvlip hD3vm hD3vmlip x₀ hAx hN0 hN hΦ' h0' z hs
    rw [← hcompat s (Φ z s), ← hcompat s (Φ x₀ s)] at hcp
    exact hcp
  -- cw : quadratic resolvent Taylor remainder
  have hεW : ‖(fundamentalSolution hAz hΦ₁ h0₁ s - fundamentalSolution hAx hΦ' h0' s) - Vlin s‖
      ≤ ((L : ℝ) ^ 2 * Real.exp ((K : ℝ) * (T - t₀)) ^ 3
            * gronwallBound 0 (K : ℝ) 1 (T - t₀) ^ 2
          + ((M₂ : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
              + C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                  * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
            * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀))
        * ‖z - x₀‖ ^ 2 :=
    norm_fundamentalSolution_sub_sub_linearVariation_le_sq hv hΦ h0 hDv hDvlip hD2vc hD2vclip
      x₀ hAx hAxcont hC'0 hC' hΦ' h0' z hAz hAzcont hΦ₁ h0₁ hVz hVz0 hVlin hVlin0 hs
  exact norm_bilinearCompForcing_curry2_sub_sub_le_sq
    (D3vm s (Φ x₀ s) (fundamentalSolution hAx hΦ' h0' s (z - x₀))) h (z - x₀)
    hP₀ hW₀ hrP hrW hεP hεW hC'0 (Real.exp_pos _).le
    (by positivity) (mul_nonneg (by positivity) hg) hk

/-- **Forcing-gap combinator for the design-corrected third variation.**  Assembles the two
independently-proved second-order remainders — the coefficient-variation remainder
`‖(A₁ − A₀) ∘ V₁ − newLeading‖ ≤ β₁` (`norm_coeffVariation_sub_secondDerivComp_le_sq`) and the
chain-rule forcing remainder `‖(F₁ − F₀) − (F_C + F_A + F_B)‖ ≤ β₂`
(`norm_chainRuleForcing_flow_sub_sub_le_sq`) — into the single forcing gap
`‖((A₁ − A₀) ∘ V₁ + (F₁ − F₀)) − F₃‖ ≤ β₁ + β₂` with `F₃ = F_A + F_B + (newLeading + F_C)`, exactly the
design-corrected third-variation forcing of
`exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv_coeff` and the `hβ` hypothesis of
`norm_inhomogVariation_sub_sub_le_of_forcingGap`.  Pure algebra: regroup by `abel` (the composition
`(A₁ − A₀) ∘ V₁` and the forcing operators are treated as additive atoms), then `norm_add_le` +
`add_le_add`. -/
theorem norm_forcingGap_le_of_remainders
    {A₁ A₀ V₁ Fone Fzero FA FB FC newLeading : E →L[ℝ] E} {β₁ β₂ : ℝ}
    (hcoeff : ‖(A₁ - A₀).comp V₁ - newLeading‖ ≤ β₁)
    (hforcing : ‖(Fone - Fzero) - (FC + FA + FB)‖ ≤ β₂) :
    ‖((A₁ - A₀).comp V₁ + (Fone - Fzero)) - (FA + FB + (newLeading + FC))‖ ≤ β₁ + β₂ := by
  have hre : ((A₁ - A₀).comp V₁ + (Fone - Fzero)) - (FA + FB + (newLeading + FC))
      = ((A₁ - A₀).comp V₁ - newLeading) + ((Fone - Fzero) - (FC + FA + FB)) := by abel
  rw [hre]
  exact (norm_add_le _ _).trans (add_le_add hcoeff hforcing)

/-- **The `C³` forcing-gap estimate `hβ`** (the design-corrected third-variation forcing gap, along the
flow).  Assembles the two independently-proved second-order remainders — the coefficient-variation
remainder (`norm_coeffVariation_sub_secondDerivComp_le_sq`, ring-reshaped to the clean
`C₁ · ‖z − x₀‖² · ‖h‖` rate) and the chain-rule forcing remainder
(`norm_chainRuleForcing_flow_sub_sub_le_sq`) — via `norm_forcingGap_le_of_remainders` into the single
forcing gap
`‖((Dv(Φz) − Dv(Φx₀)) ∘ Uz + (F₁ − F₀)) − (F_A + F_B + (newLeading + F_C))‖ ≤ C · ‖z − x₀‖² · ‖h‖`,
uniformly on the forward tube `[t₀, T]`.  Here `Uz`/`Ux` are the linearised first-variation (second
fundamental solution) curves at base points `z`/`x₀` in the common direction `h`, `W₂` is the second
fundamental solution curve at `x₀` in the base direction `z − x₀`, `Wdiff` the `C²`-numerator difference
curve, and `F_A + F_B + (newLeading + F_C)` is exactly the *design-corrected* third-variation forcing
`F₃` of `exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv_coeff`.  This is precisely the
`hβ` hypothesis of `norm_inhomogVariation_sub_sub_le_of_forcingGap`, closing the analytic core of the
base-point second-order Taylor remainder for the second fundamental solution toward `ContDiff ℝ 3`. -/
theorem norm_forcingGap_flow_le_sq [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)}
    {D2vc : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D2vm : ℝ → E → (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)}
    {D3vm : ℝ → E → (E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E))}
    {L M₂ M₃ : ℝ≥0} {C' N : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ) (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2vc : ∀ s ξ, HasFDerivAt (Dv s) (D2vc s ξ) ξ) (hD2vclip : ∀ s, LipschitzWith M₂ (D2vc s))
    (hD3vm : ∀ s ξ, HasFDerivAt (D2vm s) (D3vm s ξ) ξ) (hD3vmlip : ∀ s, LipschitzWith M₃ (D3vm s))
    (hcompat : ∀ s ξ, D2vc s ξ = curry2 (D2vm s ξ))
    (z x₀ : E)
    (hAz : ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K) (hAx : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hAxcont : Continuous (fun s => Dv s (Φ x₀ s))) (hAzcont : Continuous (fun s => Dv s (Φ z s)))
    (hC'0 : 0 ≤ C') (hC'z : ∀ s, ‖D2vc s (Φ z s)‖ ≤ C') (hC'x : ∀ s, ‖D2vc s (Φ x₀ s)‖ ≤ C')
    (hN0 : 0 ≤ N) (hN : ∀ s, ‖D3vm s (Φ x₀ s)‖ ≤ N)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ x, IsIntegralCurve (Φ' x) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ x, Φ' x t₀ = x)
    {Φ₁ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h0₁ : ∀ x, Φ₁ x t₀ = x)
    (h : E)
    {Uz Ux W₂ Wdiff : ℝ → (E →L[ℝ] E)}
    (hUz : ∀ s, HasDerivAt Uz
      ((Dv s (Φ z s)).comp (Uz s)
        + ((D2vc s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h0₁ s) h).comp
            (fundamentalSolution hAz hΦ₁ h0₁ s)) s)
    (hUz0 : Uz t₀ = 0)
    (hUx : ∀ s, HasDerivAt Ux
      ((Dv s (Φ x₀ s)).comp (Ux s)
        + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp
            (fundamentalSolution hAx hΦ' h0' s)) s)
    (hUx0 : Ux t₀ = 0)
    (hW₂ : ∀ s, HasDerivAt W₂
      ((Dv s (Φ x₀ s)).comp (W₂ s)
        + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) (z - x₀)).comp
            (fundamentalSolution hAx hΦ' h0' s)) s)
    (hW₂0 : W₂ t₀ = 0)
    (hWdiff : ∀ s, HasDerivAt Wdiff
      ((Dv s (Φ x₀ s)).comp (Wdiff s)
        + (Dv s (Φ z s) - Dv s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s)) s)
    (hWdiff0 : Wdiff t₀ = 0)
    {T : ℝ} (hk : ‖z - x₀‖ ≤ 1) :
    ∃ C : ℝ, ∀ s ∈ Set.Icc t₀ T,
      ‖((Dv s (Φ z s) - Dv s (Φ x₀ s)).comp (Uz s)
            + (((D2vc s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h0₁ s) h).comp
                  (fundamentalSolution hAz hΦ₁ h0₁ s)
                - ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp
                    (fundamentalSolution hAx hΦ' h0' s)))
          - (((D2vc s (Φ x₀ s)).comp (W₂ s) h).comp (fundamentalSolution hAx hΦ' h0' s)
              + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp (W₂ s)
              + (((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) (z - x₀)).comp (Ux s)
                  + (continuousMultilinearCurryFin1 ℝ E E
                        ((D3vm s (Φ x₀ s)
                            (fundamentalSolution hAx hΦ' h0' s (z - x₀))).curryLeft
                          (fundamentalSolution hAx hΦ' h0' s h))).comp
                      (fundamentalSolution hAx hΦ' h0' s)))‖
        ≤ C * ‖z - x₀‖ ^ 2 * ‖h‖ := by
  -- chain-rule forcing remainder `‖(F₁ − F₀) − (F_C + F_A + F_B)‖ ≤ C₂ · ‖z − x₀‖² · ‖h‖`
  obtain ⟨C₂, hC₂⟩ := norm_chainRuleForcing_flow_sub_sub_le_sq (T := T) hv hΦ h0 hDv hDvlip
    hD2vc hD2vclip hD3vm hD3vmlip hcompat z x₀ hAx hAz hAxcont hAzcont hC'0 hC'x hN0 hN
    hΦ' h0' hΦ₁ h0₁ hWdiff hWdiff0 hW₂ hW₂0 h hk
  -- explicit nonnegative coefficient-remainder constant `C₁` (ring-reshape of the messy bound)
  set C₁ : ℝ := (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀)) ^ 3
        * ((M₂ : ℝ) + 3 * (L : ℝ) * C' * gronwallBound 0 (K : ℝ) 1 (T - t₀))
        * gronwallBound 0 (K : ℝ) 1 (T - t₀)
      + ((M₂ : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
            + C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
          * (C' * Real.exp (2 * (K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀))
    with hC₁def
  refine ⟨C₁ + max C₂ 0, fun s hs => ?_⟩
  -- coefficient-variation remainder at `s`, reshaped to `C₁ · ‖z − x₀‖² · ‖h‖`
  have hc := norm_coeffVariation_sub_secondDerivComp_le_sq hv hΦ h0 hDv hDvlip hD2vc hD2vclip
    z x₀ hAz hAx hC'0 hC'z hC'x (hΦ₁ := hΦ₁) (h1 := h0₁) (hΦ₂ := hΦ') (h2 := h0') (h := h)
    (hVz := hUz) (hVz0 := hUz0) (hVx := hUx) (hVx0 := hUx0) (hs := hs)
  have hcoeff' : ‖(Dv s (Φ z s) - Dv s (Φ x₀ s)).comp (Uz s)
        - ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) (z - x₀)).comp (Ux s)‖
      ≤ C₁ * ‖z - x₀‖ ^ 2 * ‖h‖ := by
    refine hc.trans (le_of_eq ?_)
    rw [hC₁def]; ring
  -- chain-rule forcing remainder at `s`
  have hf := hC₂ s hs
  -- combine into the single forcing gap
  have hcomb := norm_forcingGap_le_of_remainders hcoeff' hf
  refine hcomb.trans ?_
  have hXnn : (0 : ℝ) ≤ ‖z - x₀‖ ^ 2 * ‖h‖ := by positivity
  have hmax : C₂ * ‖z - x₀‖ ^ 2 * ‖h‖ ≤ max C₂ 0 * ‖z - x₀‖ ^ 2 * ‖h‖ := by
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left C₂ 0) hXnn
  have hexp : (C₁ + max C₂ 0) * ‖z - x₀‖ ^ 2 * ‖h‖
      = C₁ * ‖z - x₀‖ ^ 2 * ‖h‖ + max C₂ 0 * ‖z - x₀‖ ^ 2 * ‖h‖ := by ring
  rw [hexp]
  linarith [hmax]

/-- **The curve-level `C³` second-order Taylor remainder for the second fundamental solution.**  The
`D₃`-analogue of the `C²` numerator `norm_fundamentalSolution_sub_sub_linearVariation_le_sq`, at the
level of the per-direction second fundamental solution curves: the base-point difference of the second
fundamental solution `Uz − Ux` (the linearised first-variation curves in the common direction `h` at
base points `z`, `x₀`) minus the third variation `V₃` (the design-corrected third-variation curve
solving `V₃' = Dv(Φx₀) ∘ V₃ + (F_A + F_B + (newLeading + F_C))`, `V₃ t₀ = 0`) is second order in the
base-point displacement:
`‖(Uz t − Ux t) − V₃ t‖ ≤ C · ‖z − x₀‖² · ‖h‖` on the forward tube `[t₀, T]`.  Proof: the forcing-gap
estimate `norm_forcingGap_flow_le_sq` supplies the `hβ` of `norm_inhomogVariation_sub_sub_le_of_forcingGap`
(with the three ODE solutions `Uz`, `Ux`, `V₃`), whose Grönwall bound is then reshaped by `ring`.  This
is exactly the numerator the packaged operators `D₂`, `D₃` feed to
`hasFDerivAt_of_eventually_norm_sub_sub_le_sq` (with `k = z − x₀`) to obtain
`HasFDerivAt (fun z => D₂ z) D₃ x₀`, i.e. the flow's second fundamental solution is Fréchet
differentiable in the initial data — the last analytic step before `ContDiff ℝ 3`. -/
theorem norm_secondFundamentalSolution_sub_sub_thirdVariation_le_sq [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)}
    {D2vc : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D2vm : ℝ → E → (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)}
    {D3vm : ℝ → E → (E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E))}
    {L M₂ M₃ : ℝ≥0} {C' N : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ) (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2vc : ∀ s ξ, HasFDerivAt (Dv s) (D2vc s ξ) ξ) (hD2vclip : ∀ s, LipschitzWith M₂ (D2vc s))
    (hD3vm : ∀ s ξ, HasFDerivAt (D2vm s) (D3vm s ξ) ξ) (hD3vmlip : ∀ s, LipschitzWith M₃ (D3vm s))
    (hcompat : ∀ s ξ, D2vc s ξ = curry2 (D2vm s ξ))
    (z x₀ : E)
    (hAz : ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K) (hAx : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hAxcont : Continuous (fun s => Dv s (Φ x₀ s))) (hAzcont : Continuous (fun s => Dv s (Φ z s)))
    (hC'0 : 0 ≤ C') (hC'z : ∀ s, ‖D2vc s (Φ z s)‖ ≤ C') (hC'x : ∀ s, ‖D2vc s (Φ x₀ s)‖ ≤ C')
    (hN0 : 0 ≤ N) (hN : ∀ s, ‖D3vm s (Φ x₀ s)‖ ≤ N)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ x, IsIntegralCurve (Φ' x) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ x, Φ' x t₀ = x)
    {Φ₁ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h0₁ : ∀ x, Φ₁ x t₀ = x)
    (h : E)
    {Uz Ux W₂ Wdiff V₃ : ℝ → (E →L[ℝ] E)}
    (hUz : ∀ s, HasDerivAt Uz
      ((Dv s (Φ z s)).comp (Uz s)
        + ((D2vc s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h0₁ s) h).comp
            (fundamentalSolution hAz hΦ₁ h0₁ s)) s)
    (hUz0 : Uz t₀ = 0)
    (hUx : ∀ s, HasDerivAt Ux
      ((Dv s (Φ x₀ s)).comp (Ux s)
        + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp
            (fundamentalSolution hAx hΦ' h0' s)) s)
    (hUx0 : Ux t₀ = 0)
    (hW₂ : ∀ s, HasDerivAt W₂
      ((Dv s (Φ x₀ s)).comp (W₂ s)
        + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) (z - x₀)).comp
            (fundamentalSolution hAx hΦ' h0' s)) s)
    (hW₂0 : W₂ t₀ = 0)
    (hWdiff : ∀ s, HasDerivAt Wdiff
      ((Dv s (Φ x₀ s)).comp (Wdiff s)
        + (Dv s (Φ z s) - Dv s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s)) s)
    (hWdiff0 : Wdiff t₀ = 0)
    (hV₃ : ∀ s, HasDerivAt V₃
      ((Dv s (Φ x₀ s)).comp (V₃ s)
        + (((D2vc s (Φ x₀ s)).comp (W₂ s) h).comp (fundamentalSolution hAx hΦ' h0' s)
            + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp (W₂ s)
            + (((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) (z - x₀)).comp (Ux s)
                + (continuousMultilinearCurryFin1 ℝ E E
                      ((D3vm s (Φ x₀ s)
                          (fundamentalSolution hAx hΦ' h0' s (z - x₀))).curryLeft
                        (fundamentalSolution hAx hΦ' h0' s h))).comp
                    (fundamentalSolution hAx hΦ' h0' s)))) s)
    (hV₃0 : V₃ t₀ = 0)
    {T : ℝ} (hk : ‖z - x₀‖ ≤ 1) {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ∃ C : ℝ, ‖(Uz t - Ux t) - V₃ t‖ ≤ C * ‖z - x₀‖ ^ 2 * ‖h‖ := by
  obtain ⟨C, hβ⟩ := norm_forcingGap_flow_le_sq (T := T) hv hΦ h0 hDv hDvlip hD2vc hD2vclip
    hD3vm hD3vmlip hcompat z x₀ hAz hAx hAxcont hAzcont hC'0 hC'z hC'x hN0 hN hΦ' h0' hΦ₁ h0₁
    h hUz hUz0 hUx hUx0 hW₂ hW₂0 hWdiff hWdiff0 hk
  refine ⟨C * gronwallBound 0 (K : ℝ) 1 (t - t₀), ?_⟩
  have hmain := norm_inhomogVariation_sub_sub_le_of_forcingGap
    (β := C * ‖z - x₀‖ ^ 2 * ‖h‖) hAx hUz hUz0 hUx hUx0 hV₃ hV₃0 hβ ht
  refine hmain.trans (le_of_eq ?_)
  ring

/-- **Continuity of the `D3vm`-representation third-derivative forcing term.**  The companion of
`continuous_thirdDerivForcing` for the *already-once-curried* representation of the third derivative
`DF : ℝ → (E →L[ℝ] (E[×2]→L E))` (i.e. `DF s = D³v(·)` in the `E →L ContinuousMultilinearMap (Fin 2)`
form carrying the norm/continuity instances that the curried triple `E →L E →L E →L E` lacks): the
once-and-twice contracted map
`s ↦ (continuousMultilinearCurryFin1 ℝ E E ((DF s (W s k)).curryLeft (W s h))).comp (W s)`
(`e ↦ DF s [W s k][W s h, W s e]`) is continuous.  Proof mirrors `continuous_thirdDerivForcing` from the
first inner application onward (`DF s (W s k)` via `Continuous.clm_apply`, the `curryLeft` isometry
`continuousMultilinearCurryLeftEquiv`, `continuousMultilinearCurryFin1`, and `Continuous.clm_comp`).
This is the continuity of the `F_C` forcing in the `D3vm` representation used by the flow-forcing chain
rule and the design-corrected third variation. -/
theorem continuous_thirdDerivCurryForcing
    {DF : ℝ → (E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E))}
    {W : ℝ → (E →L[ℝ] E)} (hDF : Continuous DF) (hW : Continuous W) (k h : E) :
    Continuous fun s =>
      (continuousMultilinearCurryFin1 ℝ E E ((DF s (W s k)).curryLeft (W s h))).comp (W s) := by
  have hWk : Continuous fun s => W s k := hW.clm_apply continuous_const
  have hWh : Continuous fun s => W s h := hW.clm_apply continuous_const
  have hc1 : Continuous fun s => DF s (W s k) := hDF.clm_apply hWk
  have hcL2 : Continuous fun s => (DF s (W s k)).curryLeft :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) E).continuous.comp hc1
  have hc2 : Continuous fun s => (DF s (W s k)).curryLeft (W s h) := hcL2.clm_apply hWh
  have hc3 : Continuous fun s =>
      continuousMultilinearCurryFin1 ℝ E E ((DF s (W s k)).curryLeft (W s h)) :=
    (continuousMultilinearCurryFin1 ℝ E E).continuous.comp hc2
  exact hc3.clm_comp hW

/-- **`h`-uniform (direction-independent constant) form of the chain-rule forcing remainder.**
Identical to `norm_chainRuleForcing_flow_sub_sub_le_sq` except the direction `h` is quantified *inside*
the conclusion with the constant `C` chosen **once, before** `h` — legitimate because the engine
constant of `norm_bilinearCompForcing_curry2_sub_sub_le_sq` (assembled from the six field bounds
`p,w,dp,dw,cp,cw`, all direction-independent) never mentions `h`; `h` enters only as the linear `‖h‖`
factor.  This uniform form is what the operator-norm packaging of the second fundamental solution's
base-point derivative needs (`ContinuousLinearMap.opNorm_le_bound` requires a single bound valid for
every direction `h`).  Proof: the verbatim proof of `norm_chainRuleForcing_flow_sub_sub_le_sq` with the
direction abstracted (`fun h s hs`); the metavariable constant is unified to the (direction-free) engine
constant on the single `exact`. -/
theorem norm_chainRuleForcing_flow_sub_sub_le_sq_uniform [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)}
    {D2vc : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D2vm : ℝ → E → (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)}
    {D3vm : ℝ → E → (E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E))}
    {L M₂ M₃ : ℝ≥0} {C' N : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ) (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2vc : ∀ s ξ, HasFDerivAt (Dv s) (D2vc s ξ) ξ) (hD2vclip : ∀ s, LipschitzWith M₂ (D2vc s))
    (hD3vm : ∀ s ξ, HasFDerivAt (D2vm s) (D3vm s ξ) ξ) (hD3vmlip : ∀ s, LipschitzWith M₃ (D3vm s))
    (hcompat : ∀ s ξ, D2vc s ξ = curry2 (D2vm s ξ))
    (z x₀ : E)
    (hAx : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K) (hAz : ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K)
    (hAxcont : Continuous (fun s => Dv s (Φ x₀ s))) (hAzcont : Continuous (fun s => Dv s (Φ z s)))
    (hC'0 : 0 ≤ C') (hC' : ∀ s, ‖D2vc s (Φ x₀ s)‖ ≤ C')
    (hN0 : 0 ≤ N) (hN : ∀ s, ‖D3vm s (Φ x₀ s)‖ ≤ N)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ x, IsIntegralCurve (Φ' x) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ x, Φ' x t₀ = x)
    {Φ₁ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h0₁ : ∀ x, Φ₁ x t₀ = x)
    {Vz Vlin : ℝ → (E →L[ℝ] E)}
    (hVz : ∀ s, HasDerivAt Vz
      ((Dv s (Φ x₀ s)).comp (Vz s)
        + (Dv s (Φ z s) - Dv s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s)) s)
    (hVz0 : Vz t₀ = 0)
    (hVlin : ∀ s, HasDerivAt Vlin
      ((Dv s (Φ x₀ s)).comp (Vlin s)
        + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) (z - x₀)).comp
            (fundamentalSolution hAx hΦ' h0' s)) s)
    (hVlin0 : Vlin t₀ = 0)
    {T : ℝ} (hk : ‖z - x₀‖ ≤ 1) :
    ∃ C : ℝ, ∀ (h : E), ∀ s ∈ Set.Icc t₀ T,
      ‖(((D2vc s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h0₁ s) h).comp
              (fundamentalSolution hAz hΦ₁ h0₁ s)
            - ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp
                (fundamentalSolution hAx hΦ' h0' s))
          - ((continuousMultilinearCurryFin1 ℝ E E
                  ((D3vm s (Φ x₀ s)
                      (fundamentalSolution hAx hΦ' h0' s (z - x₀))).curryLeft
                    (fundamentalSolution hAx hΦ' h0' s h))).comp
                (fundamentalSolution hAx hΦ' h0' s)
              + ((D2vc s (Φ x₀ s)).comp (Vlin s) h).comp (fundamentalSolution hAx hΦ' h0' s)
              + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp (Vlin s))‖
        ≤ C * ‖z - x₀‖ ^ 2 * ‖h‖ := by
  refine ⟨?_, fun h s hs => ?_⟩
  rotate_left
  have hsT : |s - t₀| ≤ T - t₀ := by
    rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
  have hexpmono : Real.exp ((K : ℝ) * |s - t₀|) ≤ Real.exp ((K : ℝ) * (T - t₀)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsT K.coe_nonneg)
  have hg : (0 : ℝ) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
    gronwallBound_zero_one_nonneg K.coe_nonneg (sub_nonneg.mpr (le_trans hs.1 hs.2))
  -- p : ‖P₀‖ ≤ C'
  have hP₀ : ‖D2vc s (Φ x₀ s)‖ ≤ C' := hC' s
  -- w : ‖W₀‖ ≤ exp
  have hW₀ : ‖fundamentalSolution hAx hΦ' h0' s‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) :=
    (norm_fundamentalSolution_le hAx hΦ' h0' s).trans hexpmono
  -- dp : first-order D²v gap
  have hrP : ‖D2vc s (Φ z s) - D2vc s (Φ x₀ s)‖
      ≤ (M₂ : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖ :=
    norm_secondDerivField_apply_flow_sub_le hv hΦ h0 (hD2vclip s) hsT z x₀
  -- dw : first-order resolvent gap
  have hrW : ‖fundamentalSolution hAz hΦ₁ h0₁ s - fundamentalSolution hAx hΦ' h0' s‖
      ≤ ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
          * gronwallBound 0 (K : ℝ) 1 (T - t₀)) * ‖z - x₀‖ := by
    have hbase := norm_fundamentalSolution_baseCurve_sub_le hv hΦ h0 hDvlip z x₀ hAz hAx
      hΦ₁ h0₁ hΦ' h0' hs
    have hmono : gronwallBound 0 (K : ℝ) 1 (s - t₀) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
      gronwallBound_mono le_rfl zero_le_one K.coe_nonneg (by linarith [hs.2])
    refine hbase.trans ?_
    calc (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖ * Real.exp ((K : ℝ) * (T - t₀))
            * gronwallBound 0 (K : ℝ) 1 (s - t₀)
        ≤ (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖ * Real.exp ((K : ℝ) * (T - t₀))
            * gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
              * gronwallBound 0 (K : ℝ) 1 (T - t₀)) * ‖z - x₀‖ := by ring
  -- cp : quadratic D²v Taylor remainder (in composition form via hcompat)
  have hεP : ‖D2vc s (Φ z s) - D2vc s (Φ x₀ s)
        - curry2 (D3vm s (Φ x₀ s) (fundamentalSolution hAx hΦ' h0' s (z - x₀)))‖
      ≤ ((M₃ : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
          + N * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
              * gronwallBound 0 (K : ℝ) 1 (T - t₀))) * ‖z - x₀‖ ^ 2 := by
    have hcp := norm_secondDerivField_curry2_sub_sub_thirdDeriv_le_sq
      hv hΦ h0 hDv hDvlip hD3vm hD3vmlip x₀ hAx hN0 hN hΦ' h0' z hs
    rw [← hcompat s (Φ z s), ← hcompat s (Φ x₀ s)] at hcp
    exact hcp
  -- cw : quadratic resolvent Taylor remainder
  have hεW : ‖(fundamentalSolution hAz hΦ₁ h0₁ s - fundamentalSolution hAx hΦ' h0' s) - Vlin s‖
      ≤ ((L : ℝ) ^ 2 * Real.exp ((K : ℝ) * (T - t₀)) ^ 3
            * gronwallBound 0 (K : ℝ) 1 (T - t₀) ^ 2
          + ((M₂ : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
              + C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                  * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
            * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀))
        * ‖z - x₀‖ ^ 2 :=
    norm_fundamentalSolution_sub_sub_linearVariation_le_sq hv hΦ h0 hDv hDvlip hD2vc hD2vclip
      x₀ hAx hAxcont hC'0 hC' hΦ' h0' z hAz hAzcont hΦ₁ h0₁ hVz hVz0 hVlin hVlin0 hs
  exact norm_bilinearCompForcing_curry2_sub_sub_le_sq
    (D3vm s (Φ x₀ s) (fundamentalSolution hAx hΦ' h0' s (z - x₀))) h (z - x₀)
    hP₀ hW₀ hrP hrW hεP hεW hC'0 (Real.exp_pos _).le
    (by positivity) (mul_nonneg (by positivity) hg) hk

/-- **Explicit-constant form of the `h`-uniform chain-rule forcing remainder.**  Identical to
`norm_chainRuleForcing_flow_sub_sub_le_sq_uniform` except the (direction- and base-point-independent)
engine constant of `norm_bilinearCompForcing_curry2_sub_sub_le_sq` is written out *explicitly* instead of
being existentially quantified.  Exposing the constant is what the *neighbourhood-uniform* `HasFDerivAt`
packaging of the second fundamental solution needs: `hasFDerivAt_of_eventually_norm_sub_sub_le_sq`
requires a **single** constant `C` valid for every base point `z` in a neighbourhood of `x₀`, whereas the
`∃ C` form binds a (morally identical) witness separately to each `z`.  The constant here depends only on
the field data `K, L, M₂, M₃, C', N, T, t₀` — never on `z` or `h`.  Proof: the verbatim proof of the
`∃`-form, closed by `.trans_eq (by ring)` against the engine's explicit output constant
`cp·w² + 2p·cw·w + 2dp·dw·w + p·dw² + dp·dw²`. -/
theorem norm_chainRuleForcing_flow_sub_sub_le_sq_uniformC [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)}
    {D2vc : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D2vm : ℝ → E → (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)}
    {D3vm : ℝ → E → (E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E))}
    {L M₂ M₃ : ℝ≥0} {C' N : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ) (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2vc : ∀ s ξ, HasFDerivAt (Dv s) (D2vc s ξ) ξ) (hD2vclip : ∀ s, LipschitzWith M₂ (D2vc s))
    (hD3vm : ∀ s ξ, HasFDerivAt (D2vm s) (D3vm s ξ) ξ) (hD3vmlip : ∀ s, LipschitzWith M₃ (D3vm s))
    (hcompat : ∀ s ξ, D2vc s ξ = curry2 (D2vm s ξ))
    (z x₀ : E)
    (hAx : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K) (hAz : ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K)
    (hAxcont : Continuous (fun s => Dv s (Φ x₀ s))) (hAzcont : Continuous (fun s => Dv s (Φ z s)))
    (hC'0 : 0 ≤ C') (hC' : ∀ s, ‖D2vc s (Φ x₀ s)‖ ≤ C')
    (hN0 : 0 ≤ N) (hN : ∀ s, ‖D3vm s (Φ x₀ s)‖ ≤ N)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ x, IsIntegralCurve (Φ' x) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ x, Φ' x t₀ = x)
    {Φ₁ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h0₁ : ∀ x, Φ₁ x t₀ = x)
    {Vz Vlin : ℝ → (E →L[ℝ] E)}
    (hVz : ∀ s, HasDerivAt Vz
      ((Dv s (Φ x₀ s)).comp (Vz s)
        + (Dv s (Φ z s) - Dv s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s)) s)
    (hVz0 : Vz t₀ = 0)
    (hVlin : ∀ s, HasDerivAt Vlin
      ((Dv s (Φ x₀ s)).comp (Vlin s)
        + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) (z - x₀)).comp
            (fundamentalSolution hAx hΦ' h0' s)) s)
    (hVlin0 : Vlin t₀ = 0)
    {T : ℝ} (hk : ‖z - x₀‖ ≤ 1) :
    ∀ (h : E), ∀ s ∈ Set.Icc t₀ T,
      ‖(((D2vc s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h0₁ s) h).comp
              (fundamentalSolution hAz hΦ₁ h0₁ s)
            - ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp
                (fundamentalSolution hAx hΦ' h0' s))
          - ((continuousMultilinearCurryFin1 ℝ E E
                  ((D3vm s (Φ x₀ s)
                      (fundamentalSolution hAx hΦ' h0' s (z - x₀))).curryLeft
                    (fundamentalSolution hAx hΦ' h0' s h))).comp
                (fundamentalSolution hAx hΦ' h0' s)
              + ((D2vc s (Φ x₀ s)).comp (Vlin s) h).comp (fundamentalSolution hAx hΦ' h0' s)
              + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp (Vlin s))‖
        ≤ (((M₃ : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                + N * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                    * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
              * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
            + 2 * C'
                * ((L : ℝ) ^ 2 * Real.exp ((K : ℝ) * (T - t₀)) ^ 3
                      * gronwallBound 0 (K : ℝ) 1 (T - t₀) ^ 2
                    + ((M₂ : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                        + C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                            * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
                      * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀))
                * Real.exp ((K : ℝ) * (T - t₀))
            + 2 * ((M₂ : ℝ) * Real.exp ((K : ℝ) * (T - t₀)))
                * ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
                    * gronwallBound 0 (K : ℝ) 1 (T - t₀))
                * Real.exp ((K : ℝ) * (T - t₀))
            + C'
                * ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
                    * gronwallBound 0 (K : ℝ) 1 (T - t₀))
                * ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
                    * gronwallBound 0 (K : ℝ) 1 (T - t₀))
            + (M₂ : ℝ) * Real.exp ((K : ℝ) * (T - t₀))
                * ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
                    * gronwallBound 0 (K : ℝ) 1 (T - t₀))
                * ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
                    * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
          * ‖z - x₀‖ ^ 2 * ‖h‖ := by
  intro h s hs
  have hsT : |s - t₀| ≤ T - t₀ := by
    rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
  have hexpmono : Real.exp ((K : ℝ) * |s - t₀|) ≤ Real.exp ((K : ℝ) * (T - t₀)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsT K.coe_nonneg)
  have hg : (0 : ℝ) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
    gronwallBound_zero_one_nonneg K.coe_nonneg (sub_nonneg.mpr (le_trans hs.1 hs.2))
  have hP₀ : ‖D2vc s (Φ x₀ s)‖ ≤ C' := hC' s
  have hW₀ : ‖fundamentalSolution hAx hΦ' h0' s‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) :=
    (norm_fundamentalSolution_le hAx hΦ' h0' s).trans hexpmono
  have hrP : ‖D2vc s (Φ z s) - D2vc s (Φ x₀ s)‖
      ≤ (M₂ : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖ :=
    norm_secondDerivField_apply_flow_sub_le hv hΦ h0 (hD2vclip s) hsT z x₀
  have hrW : ‖fundamentalSolution hAz hΦ₁ h0₁ s - fundamentalSolution hAx hΦ' h0' s‖
      ≤ ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
          * gronwallBound 0 (K : ℝ) 1 (T - t₀)) * ‖z - x₀‖ := by
    have hbase := norm_fundamentalSolution_baseCurve_sub_le hv hΦ h0 hDvlip z x₀ hAz hAx
      hΦ₁ h0₁ hΦ' h0' hs
    have hmono : gronwallBound 0 (K : ℝ) 1 (s - t₀) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
      gronwallBound_mono le_rfl zero_le_one K.coe_nonneg (by linarith [hs.2])
    refine hbase.trans ?_
    calc (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖ * Real.exp ((K : ℝ) * (T - t₀))
            * gronwallBound 0 (K : ℝ) 1 (s - t₀)
        ≤ (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖ * Real.exp ((K : ℝ) * (T - t₀))
            * gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
              * gronwallBound 0 (K : ℝ) 1 (T - t₀)) * ‖z - x₀‖ := by ring
  have hεP : ‖D2vc s (Φ z s) - D2vc s (Φ x₀ s)
        - curry2 (D3vm s (Φ x₀ s) (fundamentalSolution hAx hΦ' h0' s (z - x₀)))‖
      ≤ ((M₃ : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
          + N * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
              * gronwallBound 0 (K : ℝ) 1 (T - t₀))) * ‖z - x₀‖ ^ 2 := by
    have hcp := norm_secondDerivField_curry2_sub_sub_thirdDeriv_le_sq
      hv hΦ h0 hDv hDvlip hD3vm hD3vmlip x₀ hAx hN0 hN hΦ' h0' z hs
    rw [← hcompat s (Φ z s), ← hcompat s (Φ x₀ s)] at hcp
    exact hcp
  have hεW : ‖(fundamentalSolution hAz hΦ₁ h0₁ s - fundamentalSolution hAx hΦ' h0' s) - Vlin s‖
      ≤ ((L : ℝ) ^ 2 * Real.exp ((K : ℝ) * (T - t₀)) ^ 3
            * gronwallBound 0 (K : ℝ) 1 (T - t₀) ^ 2
          + ((M₂ : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
              + C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                  * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
            * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀))
        * ‖z - x₀‖ ^ 2 :=
    norm_fundamentalSolution_sub_sub_linearVariation_le_sq hv hΦ h0 hDv hDvlip hD2vc hD2vclip
      x₀ hAx hAxcont hC'0 hC' hΦ' h0' z hAz hAzcont hΦ₁ h0₁ hVz hVz0 hVlin hVlin0 hs
  refine (norm_bilinearCompForcing_curry2_sub_sub_le_sq
    (D3vm s (Φ x₀ s) (fundamentalSolution hAx hΦ' h0' s (z - x₀))) h (z - x₀)
    hP₀ hW₀ hrP hrW hεP hεW hC'0 (Real.exp_pos _).le
    (by positivity) (mul_nonneg (by positivity) hg) hk).trans_eq ?_
  ring

/-- **`h`-uniform (direction-independent constant) curve-level `C³` Taylor remainder.**  The
direction-uniform strengthening of `norm_secondFundamentalSolution_sub_sub_thirdVariation_le_sq`: the
constant `C` is chosen **once, before** the direction `h` and the `h`-dependent curves `Uz`, `Ux`, `V₃`
(quantified inside).  This is exactly the form `ContinuousLinearMap.opNorm_le_bound` consumes when
packaging the base-point derivative of the second fundamental solution into an operator: one bound valid
for every direction.  The `h`-independence of `C` is genuine — the coefficient-variation constant `C₁`
is a field/flow constant (`norm_coeffVariation_sub_secondDerivComp_le_sq`, `‖h‖` factored out) and the
chain-rule forcing constant comes from the `h`-uniform `norm_chainRuleForcing_flow_sub_sub_le_sq_uniform`
(`C` before `h`); the two combine through `norm_forcingGap_le_of_remainders` and feed
`norm_inhomogVariation_sub_sub_le_of_forcingGap`, the Grönwall bound reshaped by `ring`. -/
theorem norm_secondFundamentalSolution_sub_sub_thirdVariation_le_sq_uniform [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)}
    {D2vc : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D2vm : ℝ → E → (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)}
    {D3vm : ℝ → E → (E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E))}
    {L M₂ M₃ : ℝ≥0} {C' N : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ) (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2vc : ∀ s ξ, HasFDerivAt (Dv s) (D2vc s ξ) ξ) (hD2vclip : ∀ s, LipschitzWith M₂ (D2vc s))
    (hD3vm : ∀ s ξ, HasFDerivAt (D2vm s) (D3vm s ξ) ξ) (hD3vmlip : ∀ s, LipschitzWith M₃ (D3vm s))
    (hcompat : ∀ s ξ, D2vc s ξ = curry2 (D2vm s ξ))
    (z x₀ : E)
    (hAz : ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K) (hAx : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hAxcont : Continuous (fun s => Dv s (Φ x₀ s))) (hAzcont : Continuous (fun s => Dv s (Φ z s)))
    (hC'0 : 0 ≤ C') (hC'z : ∀ s, ‖D2vc s (Φ z s)‖ ≤ C') (hC'x : ∀ s, ‖D2vc s (Φ x₀ s)‖ ≤ C')
    (hN0 : 0 ≤ N) (hN : ∀ s, ‖D3vm s (Φ x₀ s)‖ ≤ N)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ x, IsIntegralCurve (Φ' x) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ x, Φ' x t₀ = x)
    {Φ₁ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h0₁ : ∀ x, Φ₁ x t₀ = x)
    {W₂ Wdiff : ℝ → (E →L[ℝ] E)}
    (hW₂ : ∀ s, HasDerivAt W₂
      ((Dv s (Φ x₀ s)).comp (W₂ s)
        + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) (z - x₀)).comp
            (fundamentalSolution hAx hΦ' h0' s)) s)
    (hW₂0 : W₂ t₀ = 0)
    (hWdiff : ∀ s, HasDerivAt Wdiff
      ((Dv s (Φ x₀ s)).comp (Wdiff s)
        + (Dv s (Φ z s) - Dv s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s)) s)
    (hWdiff0 : Wdiff t₀ = 0)
    {T : ℝ} (hk : ‖z - x₀‖ ≤ 1) {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ∃ C : ℝ, ∀ (h : E) (Uz Ux V₃ : ℝ → (E →L[ℝ] E)),
      (∀ s, HasDerivAt Uz
        ((Dv s (Φ z s)).comp (Uz s)
          + ((D2vc s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h0₁ s) h).comp
              (fundamentalSolution hAz hΦ₁ h0₁ s)) s) → Uz t₀ = 0 →
      (∀ s, HasDerivAt Ux
        ((Dv s (Φ x₀ s)).comp (Ux s)
          + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp
              (fundamentalSolution hAx hΦ' h0' s)) s) → Ux t₀ = 0 →
      (∀ s, HasDerivAt V₃
        ((Dv s (Φ x₀ s)).comp (V₃ s)
          + (((D2vc s (Φ x₀ s)).comp (W₂ s) h).comp (fundamentalSolution hAx hΦ' h0' s)
              + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp (W₂ s)
              + (((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) (z - x₀)).comp (Ux s)
                  + (continuousMultilinearCurryFin1 ℝ E E
                        ((D3vm s (Φ x₀ s)
                            (fundamentalSolution hAx hΦ' h0' s (z - x₀))).curryLeft
                          (fundamentalSolution hAx hΦ' h0' s h))).comp
                      (fundamentalSolution hAx hΦ' h0' s)))) s) → V₃ t₀ = 0 →
      ‖(Uz t - Ux t) - V₃ t‖ ≤ C * ‖z - x₀‖ ^ 2 * ‖h‖ := by
  obtain ⟨C₂, hC₂⟩ := norm_chainRuleForcing_flow_sub_sub_le_sq_uniform (T := T) hv hΦ h0 hDv hDvlip
    hD2vc hD2vclip hD3vm hD3vmlip hcompat z x₀ hAx hAz hAxcont hAzcont hC'0 hC'x hN0 hN
    hΦ' h0' hΦ₁ h0₁ hWdiff hWdiff0 hW₂ hW₂0 hk
  set C₁ : ℝ := (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀)) ^ 3
        * ((M₂ : ℝ) + 3 * (L : ℝ) * C' * gronwallBound 0 (K : ℝ) 1 (T - t₀))
        * gronwallBound 0 (K : ℝ) 1 (T - t₀)
      + ((M₂ : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
            + C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
          * (C' * Real.exp (2 * (K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀))
    with hC₁def
  refine ⟨(C₁ + max C₂ 0) * gronwallBound 0 (K : ℝ) 1 (t - t₀),
    fun h Uz Ux V₃ hUz hUz0 hUx hUx0 hV₃ hV₃0 => ?_⟩
  have hβ : ∀ s ∈ Set.Icc t₀ T,
      ‖((Dv s (Φ z s) - Dv s (Φ x₀ s)).comp (Uz s)
            + (((D2vc s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h0₁ s) h).comp
                  (fundamentalSolution hAz hΦ₁ h0₁ s)
                - ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp
                    (fundamentalSolution hAx hΦ' h0' s)))
          - (((D2vc s (Φ x₀ s)).comp (W₂ s) h).comp (fundamentalSolution hAx hΦ' h0' s)
              + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp (W₂ s)
              + (((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) (z - x₀)).comp (Ux s)
                  + (continuousMultilinearCurryFin1 ℝ E E
                        ((D3vm s (Φ x₀ s)
                            (fundamentalSolution hAx hΦ' h0' s (z - x₀))).curryLeft
                          (fundamentalSolution hAx hΦ' h0' s h))).comp
                      (fundamentalSolution hAx hΦ' h0' s)))‖
        ≤ (C₁ + max C₂ 0) * ‖z - x₀‖ ^ 2 * ‖h‖ := by
    intro s hs
    have hc := norm_coeffVariation_sub_secondDerivComp_le_sq hv hΦ h0 hDv hDvlip hD2vc hD2vclip
      z x₀ hAz hAx hC'0 hC'z hC'x (hΦ₁ := hΦ₁) (h1 := h0₁) (hΦ₂ := hΦ') (h2 := h0') (h := h)
      (hVz := hUz) (hVz0 := hUz0) (hVx := hUx) (hVx0 := hUx0) (hs := hs)
    have hcoeff' : ‖(Dv s (Φ z s) - Dv s (Φ x₀ s)).comp (Uz s)
          - ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) (z - x₀)).comp (Ux s)‖
        ≤ C₁ * ‖z - x₀‖ ^ 2 * ‖h‖ := by
      refine hc.trans (le_of_eq ?_)
      rw [hC₁def]; ring
    have hf := hC₂ h s hs
    have hcomb := norm_forcingGap_le_of_remainders hcoeff' hf
    refine hcomb.trans ?_
    have hXnn : (0 : ℝ) ≤ ‖z - x₀‖ ^ 2 * ‖h‖ := by positivity
    have hmax : C₂ * ‖z - x₀‖ ^ 2 * ‖h‖ ≤ max C₂ 0 * ‖z - x₀‖ ^ 2 * ‖h‖ := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left C₂ 0) hXnn
    have hexp : (C₁ + max C₂ 0) * ‖z - x₀‖ ^ 2 * ‖h‖
        = C₁ * ‖z - x₀‖ ^ 2 * ‖h‖ + max C₂ 0 * ‖z - x₀‖ ^ 2 * ‖h‖ := by ring
    rw [hexp]
    linarith [hmax]
  have hmain := norm_inhomogVariation_sub_sub_le_of_forcingGap
    (β := (C₁ + max C₂ 0) * ‖z - x₀‖ ^ 2 * ‖h‖) hAx hUz hUz0 hUx hUx0 hV₃ hV₃0 hβ ht
  refine hmain.trans (le_of_eq ?_)
  ring

/-- **Explicit-constant form of the `h`-uniform curve-level `C³` Taylor remainder.**  Identical to
`norm_secondFundamentalSolution_sub_sub_thirdVariation_le_sq_uniform` except the constant is written out
*explicitly* — `(C₁ + C₂) · gronwallBound 0 K 1 (t − t₀)`, where `C₁` is the coefficient-variation
constant of `norm_coeffVariation_sub_secondDerivComp_le_sq` and `C₂` is the explicit engine constant of
`norm_chainRuleForcing_flow_sub_sub_le_sq_uniformC` — rather than existentially quantified.  The constant
depends only on the field data `K, L, M₂, M₃, C', N, T, t₀`, never on `z` or `h`, so a *single* `C` is
valid for every base point `z` in a neighbourhood of `x₀`: the neighbourhood-uniformity that the operator
packaging and `hasFDerivAt_of_eventually_norm_sub_sub_le_sq` require.  Proof: the `∃`-form's proof with
`norm_chainRuleForcing_flow_sub_sub_le_sq_uniformC` supplying the explicit forcing constant and the
Grönwall remainder `norm_inhomogVariation_sub_sub_le_of_forcingGap` reshaped by `ring`. -/
theorem norm_secondFundamentalSolution_sub_sub_thirdVariation_le_sq_uniformC [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)}
    {D2vc : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D2vm : ℝ → E → (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)}
    {D3vm : ℝ → E → (E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E))}
    {L M₂ M₃ : ℝ≥0} {C' N : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ) (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2vc : ∀ s ξ, HasFDerivAt (Dv s) (D2vc s ξ) ξ) (hD2vclip : ∀ s, LipschitzWith M₂ (D2vc s))
    (hD3vm : ∀ s ξ, HasFDerivAt (D2vm s) (D3vm s ξ) ξ) (hD3vmlip : ∀ s, LipschitzWith M₃ (D3vm s))
    (hcompat : ∀ s ξ, D2vc s ξ = curry2 (D2vm s ξ))
    (z x₀ : E)
    (hAz : ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K) (hAx : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hAxcont : Continuous (fun s => Dv s (Φ x₀ s))) (hAzcont : Continuous (fun s => Dv s (Φ z s)))
    (hC'0 : 0 ≤ C') (hC'z : ∀ s, ‖D2vc s (Φ z s)‖ ≤ C') (hC'x : ∀ s, ‖D2vc s (Φ x₀ s)‖ ≤ C')
    (hN0 : 0 ≤ N) (hN : ∀ s, ‖D3vm s (Φ x₀ s)‖ ≤ N)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ x, IsIntegralCurve (Φ' x) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ x, Φ' x t₀ = x)
    {Φ₁ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h0₁ : ∀ x, Φ₁ x t₀ = x)
    {W₂ Wdiff : ℝ → (E →L[ℝ] E)}
    (hW₂ : ∀ s, HasDerivAt W₂
      ((Dv s (Φ x₀ s)).comp (W₂ s)
        + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) (z - x₀)).comp
            (fundamentalSolution hAx hΦ' h0' s)) s)
    (hW₂0 : W₂ t₀ = 0)
    (hWdiff : ∀ s, HasDerivAt Wdiff
      ((Dv s (Φ x₀ s)).comp (Wdiff s)
        + (Dv s (Φ z s) - Dv s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s)) s)
    (hWdiff0 : Wdiff t₀ = 0)
    {T : ℝ} (hk : ‖z - x₀‖ ≤ 1) {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ∀ (h : E) (Uz Ux V₃ : ℝ → (E →L[ℝ] E)),
      (∀ s, HasDerivAt Uz
        ((Dv s (Φ z s)).comp (Uz s)
          + ((D2vc s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h0₁ s) h).comp
              (fundamentalSolution hAz hΦ₁ h0₁ s)) s) → Uz t₀ = 0 →
      (∀ s, HasDerivAt Ux
        ((Dv s (Φ x₀ s)).comp (Ux s)
          + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp
              (fundamentalSolution hAx hΦ' h0' s)) s) → Ux t₀ = 0 →
      (∀ s, HasDerivAt V₃
        ((Dv s (Φ x₀ s)).comp (V₃ s)
          + (((D2vc s (Φ x₀ s)).comp (W₂ s) h).comp (fundamentalSolution hAx hΦ' h0' s)
              + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp (W₂ s)
              + (((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) (z - x₀)).comp (Ux s)
                  + (continuousMultilinearCurryFin1 ℝ E E
                        ((D3vm s (Φ x₀ s)
                            (fundamentalSolution hAx hΦ' h0' s (z - x₀))).curryLeft
                          (fundamentalSolution hAx hΦ' h0' s h))).comp
                      (fundamentalSolution hAx hΦ' h0' s)))) s) → V₃ t₀ = 0 →
      ‖(Uz t - Ux t) - V₃ t‖
        ≤ (((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀)) ^ 3
                * ((M₂ : ℝ) + 3 * (L : ℝ) * C' * gronwallBound 0 (K : ℝ) 1 (T - t₀))
                * gronwallBound 0 (K : ℝ) 1 (T - t₀)
              + ((M₂ : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                    + C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                        * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
                  * (C' * Real.exp (2 * (K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
            + (((M₃ : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                    + N * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                        * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
                  * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
                + 2 * C'
                    * ((L : ℝ) ^ 2 * Real.exp ((K : ℝ) * (T - t₀)) ^ 3
                          * gronwallBound 0 (K : ℝ) 1 (T - t₀) ^ 2
                        + ((M₂ : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                            + C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                                * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
                          * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀))
                    * Real.exp ((K : ℝ) * (T - t₀))
                + 2 * ((M₂ : ℝ) * Real.exp ((K : ℝ) * (T - t₀)))
                    * ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
                        * gronwallBound 0 (K : ℝ) 1 (T - t₀))
                    * Real.exp ((K : ℝ) * (T - t₀))
                + C'
                    * ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
                        * gronwallBound 0 (K : ℝ) 1 (T - t₀))
                    * ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
                        * gronwallBound 0 (K : ℝ) 1 (T - t₀))
                + (M₂ : ℝ) * Real.exp ((K : ℝ) * (T - t₀))
                    * ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
                        * gronwallBound 0 (K : ℝ) 1 (T - t₀))
                    * ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
                        * gronwallBound 0 (K : ℝ) 1 (T - t₀))))
            * gronwallBound 0 (K : ℝ) 1 (t - t₀) * ‖z - x₀‖ ^ 2 * ‖h‖ := by
  intro h Uz Ux V₃ hUz hUz0 hUx hUx0 hV₃ hV₃0
  set C₁ : ℝ := (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀)) ^ 3
        * ((M₂ : ℝ) + 3 * (L : ℝ) * C' * gronwallBound 0 (K : ℝ) 1 (T - t₀))
        * gronwallBound 0 (K : ℝ) 1 (T - t₀)
      + ((M₂ : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
            + C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
          * (C' * Real.exp (2 * (K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀))
    with hC₁def
  have hf_all := norm_chainRuleForcing_flow_sub_sub_le_sq_uniformC (T := T) hv hΦ h0 hDv hDvlip
    hD2vc hD2vclip hD3vm hD3vmlip hcompat z x₀ hAx hAz hAxcont hAzcont hC'0 hC'x hN0 hN
    hΦ' h0' hΦ₁ h0₁ hWdiff hWdiff0 hW₂ hW₂0 hk
  refine (norm_inhomogVariation_sub_sub_le_of_forcingGap
    (β := (C₁
        + (((M₃ : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
              + N * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                  * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
            * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
          + 2 * C'
              * ((L : ℝ) ^ 2 * Real.exp ((K : ℝ) * (T - t₀)) ^ 3
                    * gronwallBound 0 (K : ℝ) 1 (T - t₀) ^ 2
                  + ((M₂ : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                      + C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                          * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
                    * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀))
              * Real.exp ((K : ℝ) * (T - t₀))
          + 2 * ((M₂ : ℝ) * Real.exp ((K : ℝ) * (T - t₀)))
              * ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
                  * gronwallBound 0 (K : ℝ) 1 (T - t₀))
              * Real.exp ((K : ℝ) * (T - t₀))
          + C'
              * ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
                  * gronwallBound 0 (K : ℝ) 1 (T - t₀))
              * ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
                  * gronwallBound 0 (K : ℝ) 1 (T - t₀))
          + (M₂ : ℝ) * Real.exp ((K : ℝ) * (T - t₀))
              * ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
                  * gronwallBound 0 (K : ℝ) 1 (T - t₀))
              * ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
                  * gronwallBound 0 (K : ℝ) 1 (T - t₀)))) * ‖z - x₀‖ ^ 2 * ‖h‖)
    hAx hUz hUz0 hUx hUx0 hV₃ hV₃0 ?_ ht).trans (le_of_eq (by ring))
  intro s hs
  have hc := norm_coeffVariation_sub_secondDerivComp_le_sq hv hΦ h0 hDv hDvlip hD2vc hD2vclip
    z x₀ hAz hAx hC'0 hC'z hC'x (hΦ₁ := hΦ₁) (h1 := h0₁) (hΦ₂ := hΦ') (h2 := h0') (h := h)
    (hVz := hUz) (hVz0 := hUz0) (hVx := hUx) (hVx0 := hUx0) (hs := hs)
  have hcoeff' : ‖(Dv s (Φ z s) - Dv s (Φ x₀ s)).comp (Uz s)
        - ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) (z - x₀)).comp (Ux s)‖
      ≤ C₁ * ‖z - x₀‖ ^ 2 * ‖h‖ := by
    refine hc.trans (le_of_eq ?_)
    rw [hC₁def]; ring
  have hf := hf_all h s hs
  exact (norm_forcingGap_le_of_remainders hcoeff' hf).trans_eq (by ring)

/-- **Operator-level `C³` second-order Taylor remainder for the second fundamental solution.**  The
`D₃`-analogue of the `C²` operator estimate `norm_secondFundamentalSolution_op_sub_le`, and the
operator-norm packaging of the curve-level Taylor remainder: for the packaged base-point second
derivatives `D₂z, D₂x : E →L (E →L E)` (each characterised, à la `exists_continuousLinearMap_linearisedVariation`,
by `D₂· h =` the time-`t` value of the linearised first variation in direction `h`) and the packaged
design-corrected third variation `D₃ : E →L (E →L (E →L E))` (`D₃ (z − x₀) h =` the time-`t` value of the
third variation with base direction `z − x₀`), the second-order Taylor remainder is genuinely quadratic:
`‖(D₂z − D₂x) − D₃ (z − x₀)‖ ≤ C · ‖z − x₀‖²`.

Proof: `ContinuousLinearMap.opNorm_le_bound` reduces to a per-direction bound; for each `h` the three
canonical curves are built (`exists_hasDerivAt_firstVariation_linearised_dir` for the two second
fundamental solutions, `exists_hasDerivAt_secondVariation_linearised_dir` with the concrete
`newLeading + F_C` forcing — `newLeading` continuous by `Continuous.clm_comp`/`clm_apply`, `F_C` by
`continuous_thirdDerivCurryForcing` — for the third variation), the operator values are rewritten to
the curve values via the characterisations, and the *direction-uniform* curve bound
`norm_secondFundamentalSolution_sub_sub_thirdVariation_le_sq_uniform` (whose constant is chosen before
`h`) closes it.  This is exactly the numerator `hasFDerivAt_of_eventually_norm_sub_sub_le_sq` consumes
(with `k = z − x₀`) to prove `HasFDerivAt (fun z => D₂ z) D₃ x₀` — the second fundamental solution's
Fréchet differentiability in the initial data, i.e. the flow's resolvent is spatially `ContDiff ℝ 3`. -/
theorem norm_secondFundamentalSolution_op_sub_thirdVariation_le_sq [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)}
    {D2vc : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D2vm : ℝ → E → (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)}
    {D3vm : ℝ → E → (E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E))}
    {L M₂ M₃ : ℝ≥0} {C' N : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ) (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2vc : ∀ s ξ, HasFDerivAt (Dv s) (D2vc s ξ) ξ) (hD2vclip : ∀ s, LipschitzWith M₂ (D2vc s))
    (hD3vm : ∀ s ξ, HasFDerivAt (D2vm s) (D3vm s ξ) ξ) (hD3vmlip : ∀ s, LipschitzWith M₃ (D3vm s))
    (hcompat : ∀ s ξ, D2vc s ξ = curry2 (D2vm s ξ))
    (z x₀ : E)
    (hAz : ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K) (hAx : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hAxcont : Continuous (fun s => Dv s (Φ x₀ s))) (hAzcont : Continuous (fun s => Dv s (Φ z s)))
    (hD2zcont : Continuous (fun s => D2vc s (Φ z s)))
    (hD2xcont : Continuous (fun s => D2vc s (Φ x₀ s)))
    (hD3xcont : Continuous (fun s => D3vm s (Φ x₀ s)))
    (hC'0 : 0 ≤ C') (hC'z : ∀ s, ‖D2vc s (Φ z s)‖ ≤ C') (hC'x : ∀ s, ‖D2vc s (Φ x₀ s)‖ ≤ C')
    (hN0 : 0 ≤ N) (hN : ∀ s, ‖D3vm s (Φ x₀ s)‖ ≤ N)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ x, IsIntegralCurve (Φ' x) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ x, Φ' x t₀ = x)
    {Φ₁ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h0₁ : ∀ x, Φ₁ x t₀ = x)
    {W₂ Wdiff : ℝ → (E →L[ℝ] E)}
    (hW₂ : ∀ s, HasDerivAt W₂
      ((Dv s (Φ x₀ s)).comp (W₂ s)
        + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) (z - x₀)).comp
            (fundamentalSolution hAx hΦ' h0' s)) s)
    (hW₂0 : W₂ t₀ = 0)
    (hWdiff : ∀ s, HasDerivAt Wdiff
      ((Dv s (Φ x₀ s)).comp (Wdiff s)
        + (Dv s (Φ z s) - Dv s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s)) s)
    (hWdiff0 : Wdiff t₀ = 0)
    {D₂z D₂x : E →L[ℝ] (E →L[ℝ] E)} {D₃ : E →L[ℝ] (E →L[ℝ] (E →L[ℝ] E))}
    (hD₂z : ∀ (h : E) (V : ℝ → (E →L[ℝ] E)), V t₀ = 0 →
      (∀ s, HasDerivAt V
        ((Dv s (Φ z s)).comp (V s)
          + ((D2vc s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h0₁ s) h).comp
              (fundamentalSolution hAz hΦ₁ h0₁ s)) s) →
      D₂z h = V t)
    (hD₂x : ∀ (h : E) (V : ℝ → (E →L[ℝ] E)), V t₀ = 0 →
      (∀ s, HasDerivAt V
        ((Dv s (Φ x₀ s)).comp (V s)
          + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp
              (fundamentalSolution hAx hΦ' h0' s)) s) →
      D₂x h = V t)
    (hD₃ : ∀ (h : E) (V₀ V : ℝ → (E →L[ℝ] E)),
      V₀ t₀ = 0 →
      (∀ s, HasDerivAt V₀
        ((Dv s (Φ x₀ s)).comp (V₀ s)
          + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp
              (fundamentalSolution hAx hΦ' h0' s)) s) →
      V t₀ = 0 →
      (∀ s, HasDerivAt V
        ((Dv s (Φ x₀ s)).comp (V s)
          + (((D2vc s (Φ x₀ s)).comp (W₂ s) h).comp (fundamentalSolution hAx hΦ' h0' s)
              + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp (W₂ s)
              + (((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) (z - x₀)).comp (V₀ s)
                  + (continuousMultilinearCurryFin1 ℝ E E
                        ((D3vm s (Φ x₀ s)
                            (fundamentalSolution hAx hΦ' h0' s (z - x₀))).curryLeft
                          (fundamentalSolution hAx hΦ' h0' s h))).comp
                      (fundamentalSolution hAx hΦ' h0' s)))) s) →
      D₃ (z - x₀) h = V t)
    {T : ℝ} (hk : ‖z - x₀‖ ≤ 1) (ht : t ∈ Set.Icc t₀ T) :
    ∃ C : ℝ, ‖(D₂z - D₂x) - D₃ (z - x₀)‖ ≤ C * ‖z - x₀‖ ^ 2 := by
  obtain ⟨C, hC⟩ := norm_secondFundamentalSolution_sub_sub_thirdVariation_le_sq_uniform (T := T)
    hv hΦ h0 hDv hDvlip hD2vc hD2vclip hD3vm hD3vmlip hcompat z x₀ hAz hAx hAxcont hAzcont
    hC'0 hC'z hC'x hN0 hN hΦ' h0' hΦ₁ h0₁ hW₂ hW₂0 hWdiff hWdiff0 hk ht
  refine ⟨max C 0, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (le_max_right C 0) (sq_nonneg _)) (fun h => ?_)
  obtain ⟨Uz, hUz0, hUzd⟩ :=
    exists_hasDerivAt_firstVariation_linearised_dir z hAz hAzcont hD2zcont hΦ₁ h0₁ h
  obtain ⟨Ux, hUx0, hUxd⟩ :=
    exists_hasDerivAt_firstVariation_linearised_dir x₀ hAx hAxcont hD2xcont hΦ' h0' h
  have hW : Continuous (fun s => fundamentalSolution hAx hΦ' h0' s) :=
    continuous_fundamentalSolution_time hAx hΦ' h0'
  have hUxc : Continuous Ux := Differentiable.continuous (fun s => (hUxd s).differentiableAt)
  have hW₂c : Continuous W₂ := Differentiable.continuous (fun s => (hW₂ s).differentiableAt)
  have hLead : Continuous fun s =>
      ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) (z - x₀)).comp (Ux s) :=
    ((hD2xcont.clm_comp hW).clm_apply continuous_const).clm_comp hUxc
  have hFC := continuous_thirdDerivCurryForcing hD3xcont hW (z - x₀) h
  obtain ⟨V₃, hV₃0, hV₃d⟩ :=
    exists_hasDerivAt_secondVariation_linearised_dir x₀ hAx hAxcont hD2xcont hΦ' h0' hW₂c
      (hLead.add hFC) h
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
      hD₂z h Uz hUz0 hUzd, hD₂x h Ux hUx0 hUxd, hD₃ h Ux V₃ hUx0 hUxd hV₃0 hV₃d]
  refine (hC h Uz Ux V₃ hUzd hUz0 hUxd hUx0 hV₃d hV₃0).trans ?_
  gcongr
  exact le_max_left C 0

/-- **Explicit-constant (neighbourhood-uniform) operator-level `C³` Taylor remainder for the second
fundamental solution.**  Identical to `norm_secondFundamentalSolution_op_sub_thirdVariation_le_sq` except
the constant is written out *explicitly* — `max ((C₁ + C₂) · gronwallBound 0 K 1 (t − t₀)) 0`, the
constant of `norm_secondFundamentalSolution_sub_sub_thirdVariation_le_sq_uniformC` clamped nonnegative —
rather than existentially quantified.  This is the operator numerator in the exact form
`hasFDerivAt_of_eventually_norm_sub_sub_le_sq` consumes: a **single** constant `C`, depending only on the
field data `K, L, M₂, M₃, C', N, T, t₀` (never on `z`), valid for every base point `z` in a neighbourhood
of `x₀`.  Feeding this (with `k = z − x₀`, `D₂z = D₂ z`, `D₂x = D₂ x₀`, `D₃` the bilinear third variation)
gives `HasFDerivAt (fun z => D₂ z) D₃ x₀` — the second fundamental solution's Fréchet differentiability in
the initial data, hence the flow resolvent's spatial `ContDiff ℝ 3`.  Proof: the `∃`-form's proof with the
explicit-constant curve bound `norm_secondFundamentalSolution_sub_sub_thirdVariation_le_sq_uniformC`
closing each per-direction estimate after `ContinuousLinearMap.opNorm_le_bound`. -/
theorem norm_secondFundamentalSolution_op_sub_thirdVariation_le_sq_uniformC [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)}
    {D2vc : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D2vm : ℝ → E → (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)}
    {D3vm : ℝ → E → (E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E))}
    {L M₂ M₃ : ℝ≥0} {C' N : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ) (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2vc : ∀ s ξ, HasFDerivAt (Dv s) (D2vc s ξ) ξ) (hD2vclip : ∀ s, LipschitzWith M₂ (D2vc s))
    (hD3vm : ∀ s ξ, HasFDerivAt (D2vm s) (D3vm s ξ) ξ) (hD3vmlip : ∀ s, LipschitzWith M₃ (D3vm s))
    (hcompat : ∀ s ξ, D2vc s ξ = curry2 (D2vm s ξ))
    (z x₀ : E)
    (hAz : ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K) (hAx : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hAxcont : Continuous (fun s => Dv s (Φ x₀ s))) (hAzcont : Continuous (fun s => Dv s (Φ z s)))
    (hD2zcont : Continuous (fun s => D2vc s (Φ z s)))
    (hD2xcont : Continuous (fun s => D2vc s (Φ x₀ s)))
    (hD3xcont : Continuous (fun s => D3vm s (Φ x₀ s)))
    (hC'0 : 0 ≤ C') (hC'z : ∀ s, ‖D2vc s (Φ z s)‖ ≤ C') (hC'x : ∀ s, ‖D2vc s (Φ x₀ s)‖ ≤ C')
    (hN0 : 0 ≤ N) (hN : ∀ s, ‖D3vm s (Φ x₀ s)‖ ≤ N)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ x, IsIntegralCurve (Φ' x) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ x, Φ' x t₀ = x)
    {Φ₁ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h0₁ : ∀ x, Φ₁ x t₀ = x)
    {W₂ Wdiff : ℝ → (E →L[ℝ] E)}
    (hW₂ : ∀ s, HasDerivAt W₂
      ((Dv s (Φ x₀ s)).comp (W₂ s)
        + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) (z - x₀)).comp
            (fundamentalSolution hAx hΦ' h0' s)) s)
    (hW₂0 : W₂ t₀ = 0)
    (hWdiff : ∀ s, HasDerivAt Wdiff
      ((Dv s (Φ x₀ s)).comp (Wdiff s)
        + (Dv s (Φ z s) - Dv s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s)) s)
    (hWdiff0 : Wdiff t₀ = 0)
    {D₂z D₂x : E →L[ℝ] (E →L[ℝ] E)} {D₃ : E →L[ℝ] (E →L[ℝ] (E →L[ℝ] E))}
    (hD₂z : ∀ (h : E) (V : ℝ → (E →L[ℝ] E)), V t₀ = 0 →
      (∀ s, HasDerivAt V
        ((Dv s (Φ z s)).comp (V s)
          + ((D2vc s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h0₁ s) h).comp
              (fundamentalSolution hAz hΦ₁ h0₁ s)) s) →
      D₂z h = V t)
    (hD₂x : ∀ (h : E) (V : ℝ → (E →L[ℝ] E)), V t₀ = 0 →
      (∀ s, HasDerivAt V
        ((Dv s (Φ x₀ s)).comp (V s)
          + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp
              (fundamentalSolution hAx hΦ' h0' s)) s) →
      D₂x h = V t)
    (hD₃ : ∀ (h : E) (V₀ V : ℝ → (E →L[ℝ] E)),
      V₀ t₀ = 0 →
      (∀ s, HasDerivAt V₀
        ((Dv s (Φ x₀ s)).comp (V₀ s)
          + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp
              (fundamentalSolution hAx hΦ' h0' s)) s) →
      V t₀ = 0 →
      (∀ s, HasDerivAt V
        ((Dv s (Φ x₀ s)).comp (V s)
          + (((D2vc s (Φ x₀ s)).comp (W₂ s) h).comp (fundamentalSolution hAx hΦ' h0' s)
              + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp (W₂ s)
              + (((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) (z - x₀)).comp (V₀ s)
                  + (continuousMultilinearCurryFin1 ℝ E E
                        ((D3vm s (Φ x₀ s)
                            (fundamentalSolution hAx hΦ' h0' s (z - x₀))).curryLeft
                          (fundamentalSolution hAx hΦ' h0' s h))).comp
                      (fundamentalSolution hAx hΦ' h0' s)))) s) →
      D₃ (z - x₀) h = V t)
    {T : ℝ} (hk : ‖z - x₀‖ ≤ 1) (ht : t ∈ Set.Icc t₀ T) :
    ‖(D₂z - D₂x) - D₃ (z - x₀)‖
      ≤ max ((((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀)) ^ 3
                * ((M₂ : ℝ) + 3 * (L : ℝ) * C' * gronwallBound 0 (K : ℝ) 1 (T - t₀))
                * gronwallBound 0 (K : ℝ) 1 (T - t₀)
              + ((M₂ : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                    + C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                        * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
                  * (C' * Real.exp (2 * (K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
            + (((M₃ : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                    + N * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                        * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
                  * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
                + 2 * C'
                    * ((L : ℝ) ^ 2 * Real.exp ((K : ℝ) * (T - t₀)) ^ 3
                          * gronwallBound 0 (K : ℝ) 1 (T - t₀) ^ 2
                        + ((M₂ : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                            + C' * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (T - t₀))
                                * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
                          * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀))
                    * Real.exp ((K : ℝ) * (T - t₀))
                + 2 * ((M₂ : ℝ) * Real.exp ((K : ℝ) * (T - t₀)))
                    * ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
                        * gronwallBound 0 (K : ℝ) 1 (T - t₀))
                    * Real.exp ((K : ℝ) * (T - t₀))
                + C'
                    * ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
                        * gronwallBound 0 (K : ℝ) 1 (T - t₀))
                    * ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
                        * gronwallBound 0 (K : ℝ) 1 (T - t₀))
                + (M₂ : ℝ) * Real.exp ((K : ℝ) * (T - t₀))
                    * ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
                        * gronwallBound 0 (K : ℝ) 1 (T - t₀))
                    * ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))
                        * gronwallBound 0 (K : ℝ) 1 (T - t₀))))
            * gronwallBound 0 (K : ℝ) 1 (t - t₀)) 0 * ‖z - x₀‖ ^ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (le_max_right _ 0) (sq_nonneg _)) (fun h => ?_)
  have hC := norm_secondFundamentalSolution_sub_sub_thirdVariation_le_sq_uniformC (T := T)
    hv hΦ h0 hDv hDvlip hD2vc hD2vclip hD3vm hD3vmlip hcompat z x₀ hAz hAx hAxcont hAzcont
    hC'0 hC'z hC'x hN0 hN hΦ' h0' hΦ₁ h0₁ hW₂ hW₂0 hWdiff hWdiff0 hk ht
  obtain ⟨Uz, hUz0, hUzd⟩ :=
    exists_hasDerivAt_firstVariation_linearised_dir z hAz hAzcont hD2zcont hΦ₁ h0₁ h
  obtain ⟨Ux, hUx0, hUxd⟩ :=
    exists_hasDerivAt_firstVariation_linearised_dir x₀ hAx hAxcont hD2xcont hΦ' h0' h
  have hW : Continuous (fun s => fundamentalSolution hAx hΦ' h0' s) :=
    continuous_fundamentalSolution_time hAx hΦ' h0'
  have hUxc : Continuous Ux := Differentiable.continuous (fun s => (hUxd s).differentiableAt)
  have hW₂c : Continuous W₂ := Differentiable.continuous (fun s => (hW₂ s).differentiableAt)
  have hLead : Continuous fun s =>
      ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) (z - x₀)).comp (Ux s) :=
    ((hD2xcont.clm_comp hW).clm_apply continuous_const).clm_comp hUxc
  have hFC := continuous_thirdDerivCurryForcing hD3xcont hW (z - x₀) h
  obtain ⟨V₃, hV₃0, hV₃d⟩ :=
    exists_hasDerivAt_secondVariation_linearised_dir x₀ hAx hAxcont hD2xcont hΦ' h0' hW₂c
      (hLead.add hFC) h
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
      hD₂z h Uz hUz0 hUzd, hD₂x h Ux hUx0 hUxd, hD₃ h Ux V₃ hUx0 hUxd hV₃0 hV₃d]
  refine (hC h Uz Ux V₃ hUzd hUz0 hUxd hUx0 hV₃d hV₃0).trans ?_
  gcongr
  exact le_max_left _ _

/-- **The canonical linearised-first-variation family, linear in the direction.**  Packages the
per-direction linearised first variation at `x₀` (`exists_hasDerivAt_firstVariation_linearised_dir`,
chosen over all directions `h`) into a single family `Vfam : E → (ℝ → (E →L[ℝ] E))` that is *linear* in
`h` — pointwise additive `Vfam (h₁ + h₂) s = Vfam h₁ s + Vfam h₂ s` (`linearVariation_perturbation_add_eq`)
and homogeneous `Vfam (c • h) s = c • Vfam h s` (`linearVariation_perturbation_smul_eq`) — continuous in
time (`Differentiable.continuous` of the ODE), solving the linearised first-variation ODE
`(Vfam h)' = A₀ ∘ Vfam h + (D²v(Φ x₀ s) ∘ W₀ · h) ∘ W₀` with `Vfam h t₀ = 0`, and bounded
`‖Vfam h s‖ ≤ C' · exp(2K(T − t₀)) · gronwallBound 0 K 1 (T − t₀) · ‖h‖` uniformly on `[t₀, T]`
(`norm_linearisedFirstVariation_le`, the `s`-dependent Grönwall factor pushed to the endpoint by
`gronwallBound_mono`).

This single family supplies **both** the base-direction curve `W2` (evaluated at `k`) and the
inner-direction curve `V0fun` (at `h`) required by the design-corrected bilinear third-variation packaging
`exists_continuousLinearMap_thirdVariation_coeff_bilinear` (linearity/continuity/bound are exactly its
`hW2*`/`hV0*` hypotheses), and — through its exposed ODE — matches the per-`z` base-direction curve
`W₂ = Vfam (z − x₀)` and inner curve `V₀ = Vfam h` of the operator numerator
`norm_secondFundamentalSolution_op_sub_thirdVariation_le_sq_uniformC`.  A constructive input for the
`HasFDerivAt (fun z => D₂ z) D₃ x₀` everywhere assembly toward the flow resolvent's spatial
`ContDiff ℝ 3`. -/
theorem exists_linearisedFirstVariationFamily [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hAcont : Continuous (fun s => Dv s (Φ x₀ s)))
    (hD2cont : Continuous (fun s => D2v s (Φ x₀ s)))
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    {C' : ℝ} (hC'0 : 0 ≤ C') (hC' : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ C') (T : ℝ) :
    ∃ Vfam : E → (ℝ → (E →L[ℝ] E)),
      (∀ h, Vfam h t₀ = 0) ∧
      (∀ (h : E) (s : ℝ), HasDerivAt (Vfam h)
        ((Dv s (Φ x₀ s)).comp (Vfam h s)
          + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp
              (fundamentalSolution hA hΦ' h0' s)) s) ∧
      (∀ h, Continuous (Vfam h)) ∧
      (∀ (h₁ h₂ : E) (s : ℝ), Vfam (h₁ + h₂) s = Vfam h₁ s + Vfam h₂ s) ∧
      (∀ (c : ℝ) (h : E) (s : ℝ), Vfam (c • h) s = c • Vfam h s) ∧
      (∀ (h : E), ∀ s ∈ Set.Icc t₀ T,
        ‖Vfam h s‖ ≤ C' * Real.exp (2 * (K : ℝ) * (T - t₀))
          * gronwallBound 0 (K : ℝ) 1 (T - t₀) * ‖h‖) := by
  choose Vfam hVfam0 hVfamd using fun h =>
    exists_hasDerivAt_firstVariation_linearised_dir x₀ hA hAcont hD2cont hΦ' h0' h
  refine ⟨Vfam, hVfam0, hVfamd, ?_, ?_, ?_, ?_⟩
  · intro h
    exact Differentiable.continuous (fun s => (hVfamd h s).differentiableAt)
  · intro h₁ h₂ s
    exact linearVariation_perturbation_add_eq x₀ hA hΦ' h0' h₁ h₂
      (hVfamd h₁) (hVfamd h₂) (hVfamd (h₁ + h₂)) (hVfam0 h₁) (hVfam0 h₂) (hVfam0 (h₁ + h₂)) s
  · intro c h s
    exact linearVariation_perturbation_smul_eq x₀ hA hΦ' h0' c h
      (hVfamd h) (hVfamd (c • h)) (hVfam0 h) (hVfam0 (c • h)) s
  · intro h s hs
    refine (norm_linearisedFirstVariation_le x₀ hA hΦ' h0' hC'0 hC' h
      (hVfamd h) (hVfam0 h) hs).trans ?_
    have hmono : gronwallBound 0 (K : ℝ) 1 (s - t₀) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
      gronwallBound_mono (le_refl (0 : ℝ)) zero_le_one K.coe_nonneg (by linarith [hs.2])
    have hnn : (0 : ℝ) ≤ C' * Real.exp (2 * (K : ℝ) * (T - t₀)) * ‖h‖ :=
      mul_nonneg (mul_nonneg hC'0 (Real.exp_pos _).le) (norm_nonneg _)
    calc C' * Real.exp (2 * (K : ℝ) * (T - t₀)) * ‖h‖ * gronwallBound 0 (K : ℝ) 1 (s - t₀)
        ≤ C' * Real.exp (2 * (K : ℝ) * (T - t₀)) * ‖h‖ * gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
          mul_le_mul_of_nonneg_left hmono hnn
      _ = C' * Real.exp (2 * (K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀) * ‖h‖ := by
          ring

/-- **The design-corrected third-variation operator, constructed from field data.**  Self-contained
existence of the packaged bilinear third variation `D₃ : E →L[ℝ] (E →L[ℝ] (E →L[ℝ] E))` directly from a
`C^{3}`-regular field: rather than assuming the linear auxiliary families `W2`, `V0fun`, this feeds the
*canonical* linearised-first-variation family `Vfam` (`exists_linearisedFirstVariationFamily`) as **both**
the base-direction curve and the inner-direction curve into
`exists_continuousLinearMap_thirdVariation_coeff_bilinear`, so `W2 = V0fun = Vfam` and the shared
`‖Vfam · s‖ ≤ C' · exp(2K(T − t₀)) · gronwallBound 0 K 1 (T − t₀) · ‖·‖` bound supplies both `N₂` and `N₀`.

Returns the family `Vfam` alongside `D₃`, exposing `Vfam`'s initial value, its linearised first-variation
ODE, continuity, additivity, homogeneity, and uniform bound, together with the characterisation
`D₃ k h = V t` for any `V` solving the design-corrected third-variation ODE (with `W2 = V0fun = Vfam` and
the `Fin 3` multilinear third derivative `D3v`).  This is the packaged `D₃` (with the constructive family)
the `HasFDerivAt (fun z => D₂ z) D₃ x₀` everywhere assembly consumes: `W₂ = Vfam (z − x₀)` and `V₀ = Vfam h`
match its per-`z` curves, bridging to the `hD₃` slot of
`norm_secondFundamentalSolution_op_sub_thirdVariation_le_sq_uniformC` (up to the representation identity
`D3vm s ξ = (D3v s ξ).curryLeft` and first-variation uniqueness). -/
theorem exists_thirdVariationOperator_of_field [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E}
    (x₀ : E) (hA : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hAcont : Continuous (fun s => Dv s (Φ x₀ s)))
    (hD2cont : Continuous (fun s => D2v s (Φ x₀ s)))
    (hD3cont : Continuous (fun s => D3v s (Φ x₀ s)))
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ z, IsIntegralCurve (Φ' z) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ z, Φ' z t₀ = z)
    {C' C'' : ℝ} (hC'0 : 0 ≤ C') (hC''0 : 0 ≤ C'')
    (hC' : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ C') (hC'' : ∀ s, ‖D3v s (Φ x₀ s)‖ ≤ C'')
    {T : ℝ} {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ∃ (Vfam : E → (ℝ → (E →L[ℝ] E))) (D₃ : E →L[ℝ] (E →L[ℝ] (E →L[ℝ] E))),
      (∀ h, Vfam h t₀ = 0) ∧
      (∀ (h : E) (s : ℝ), HasDerivAt (Vfam h)
        ((Dv s (Φ x₀ s)).comp (Vfam h s)
          + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp
              (fundamentalSolution hA hΦ' h0' s)) s) ∧
      (∀ h, Continuous (Vfam h)) ∧
      (∀ (h₁ h₂ : E) (s : ℝ), Vfam (h₁ + h₂) s = Vfam h₁ s + Vfam h₂ s) ∧
      (∀ (c : ℝ) (h : E) (s : ℝ), Vfam (c • h) s = c • Vfam h s) ∧
      (∀ (h : E), ∀ s ∈ Set.Icc t₀ T,
        ‖Vfam h s‖ ≤ C' * Real.exp (2 * (K : ℝ) * (T - t₀))
          * gronwallBound 0 (K : ℝ) 1 (T - t₀) * ‖h‖) ∧
      (∀ (k h : E) (V : ℝ → (E →L[ℝ] E)), V t₀ = 0 →
        (∀ s, HasDerivAt V
          ((Dv s (Φ x₀ s)).comp (V s)
            + (((D2v s (Φ x₀ s)).comp (Vfam k s) h).comp (fundamentalSolution hA hΦ' h0' s)
               + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) h).comp (Vfam k s)
               + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hA hΦ' h0' s) k).comp (Vfam h s)
                  + (continuousMultilinearCurryFin1 ℝ E E
                      (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hA hΦ' h0' s k)).curryLeft
                        (fundamentalSolution hA hΦ' h0' s h))).comp
                      (fundamentalSolution hA hΦ' h0' s)))) s) →
        D₃ k h = V t) := by
  obtain ⟨Vfam, hVfam0, hVfamd, hVfamcont, hVfamadd, hVfamsmul, hVfambound⟩ :=
    exists_linearisedFirstVariationFamily x₀ hA hAcont hD2cont hΦ' h0' hC'0 hC' T
  have hNnn : (0 : ℝ) ≤ C' * Real.exp (2 * (K : ℝ) * (T - t₀))
      * gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
    mul_nonneg (mul_nonneg hC'0 (Real.exp_pos _).le)
      (gronwallBound_zero_one_nonneg K.coe_nonneg (sub_nonneg.mpr (le_trans ht.1 ht.2)))
  obtain ⟨D₃, hD₃⟩ := exists_continuousLinearMap_thirdVariation_coeff_bilinear
    x₀ hA hAcont hD2cont hD3cont hΦ' h0' hC'0 hC''0 hNnn hNnn hC' hC''
    hVfamcont hVfamadd hVfamsmul hVfambound hVfamcont hVfamadd hVfamsmul hVfambound ht
  exact ⟨Vfam, D₃, hVfam0, hVfamd, hVfamcont, hVfamadd, hVfamsmul, hVfambound, hD₃⟩

/-- **The characterisation bridge: the packaged third-variation operator discharges the `hD₃` slot of
the operator numerator.**  Given the canonical linearised-first-variation family `Vfam` and the packaged
bilinear third-variation operator `D₃` produced by `exists_thirdVariationOperator_of_field` (its
`Fin 3`-multilinear characterisation `hD₃bilinear`), together with the curry-left compatibility
`D3vm s (Φ x₀ s) = (D3v s (Φ x₀ s)).curryLeft` between the field's third derivative in its
`E →L (E[×2] →L E)` (`D3vm`) and `E[×3] →L E` (`D3v`) representations, the operator `D₃` satisfies the
`hD₃` hypothesis slot required by `norm_secondFundamentalSolution_op_sub_thirdVariation_le_sq_uniformC`
for the increment direction `z − x₀`.

Proof.  The numerator's slot fixes an inner direction `h`, a base curve `V₀` (an arbitrary linearised
first variation of direction `h`) and a curve `V` solving the design-corrected third-variation ODE with
the numerator's base curve `W₂` (a linearised first variation of direction `z − x₀`).  Grönwall
uniqueness (`inhomogVariation_unique`, coefficient `Dv (Φ x₀ ·)`, same anchor `0` at `t₀`) pins the
two auxiliary curves to the canonical family: `W₂ = Vfam (z − x₀)` and `V₀ = Vfam h` pointwise.
Rewriting the third-variation forcing by these two identities and the curry-left compatibility turns it
term-for-term into the `Fin 3`-multilinear bilinear forcing of `hD₃bilinear` (base direction `k = z − x₀`,
inner `h`), whose four summands are exactly `((D²v ∘ Vfam k) h) ∘ W₀`, `((D²v ∘ W₀) h) ∘ Vfam k`,
`((D²v ∘ W₀) k) ∘ Vfam h` and `(curryFin1 (D³v.curryLeft (W₀ k)).curryLeft (W₀ h)) ∘ W₀`.  Then
`hD₃bilinear (z − x₀) h V` closes the slot with `D₃ (z − x₀) h = V t`.

This is the missing link between the constructive packaged operator and the neighbourhood-uniform
operator-level `C³` Taylor remainder — the last purely-algebraic step before the everywhere
`HasFDerivAt (fun z => D₂ z) D₃ x₀` assembly of the resolvent's spatial `ContDiff ℝ 3`. -/
theorem thirdVariationOperator_hD₃_slot_of_bilinear [CompleteSpace E]
    {Dv : ℝ → E → (E →L[ℝ] E)}
    {D2vc : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3vm : ℝ → E → (E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E}
    (x₀ z : E) (hAx : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    {Φ' : E → ℝ → E}
    (hΦ' : ∀ x, IsIntegralCurve (Φ' x) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h0' : ∀ x, Φ' x t₀ = x)
    {Vfam : E → (ℝ → (E →L[ℝ] E))}
    (hVfam0 : ∀ h, Vfam h t₀ = 0)
    (hVfamd : ∀ (h : E) (s : ℝ), HasDerivAt (Vfam h)
      ((Dv s (Φ x₀ s)).comp (Vfam h s)
        + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp
            (fundamentalSolution hAx hΦ' h0' s)) s)
    (hcurry : ∀ s, D3vm s (Φ x₀ s) = (D3v s (Φ x₀ s)).curryLeft)
    {D₃ : E →L[ℝ] (E →L[ℝ] (E →L[ℝ] E))}
    (hD₃bilinear : ∀ (k h : E) (V : ℝ → (E →L[ℝ] E)), V t₀ = 0 →
      (∀ s, HasDerivAt V
        ((Dv s (Φ x₀ s)).comp (V s)
          + (((D2vc s (Φ x₀ s)).comp (Vfam k s) h).comp (fundamentalSolution hAx hΦ' h0' s)
             + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp (Vfam k s)
             + (((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) k).comp (Vfam h s)
                + (continuousMultilinearCurryFin1 ℝ E E
                    (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hAx hΦ' h0' s k)).curryLeft
                      (fundamentalSolution hAx hΦ' h0' s h))).comp
                    (fundamentalSolution hAx hΦ' h0' s)))) s) →
      D₃ k h = V t)
    {W₂ : ℝ → (E →L[ℝ] E)}
    (hW₂ : ∀ s, HasDerivAt W₂
      ((Dv s (Φ x₀ s)).comp (W₂ s)
        + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) (z - x₀)).comp
            (fundamentalSolution hAx hΦ' h0' s)) s)
    (hW₂0 : W₂ t₀ = 0) :
    ∀ (h : E) (V₀ V : ℝ → (E →L[ℝ] E)),
      V₀ t₀ = 0 →
      (∀ s, HasDerivAt V₀
        ((Dv s (Φ x₀ s)).comp (V₀ s)
          + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp
              (fundamentalSolution hAx hΦ' h0' s)) s) →
      V t₀ = 0 →
      (∀ s, HasDerivAt V
        ((Dv s (Φ x₀ s)).comp (V s)
          + (((D2vc s (Φ x₀ s)).comp (W₂ s) h).comp (fundamentalSolution hAx hΦ' h0' s)
              + ((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) h).comp (W₂ s)
              + (((D2vc s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ' h0' s) (z - x₀)).comp (V₀ s)
                  + (continuousMultilinearCurryFin1 ℝ E E
                        ((D3vm s (Φ x₀ s)
                            (fundamentalSolution hAx hΦ' h0' s (z - x₀))).curryLeft
                          (fundamentalSolution hAx hΦ' h0' s h))).comp
                      (fundamentalSolution hAx hΦ' h0' s)))) s) →
      D₃ (z - x₀) h = V t := by
  intro h V₀ V hV₀0 hV₀d hV0 hVd
  have hW₂eq : ∀ s, W₂ s = Vfam (z - x₀) s := fun s =>
    inhomogVariation_unique hAx hW₂ (hVfamd (z - x₀)) (by rw [hW₂0, hVfam0]) s
  have hV₀eq : ∀ s, V₀ s = Vfam h s := fun s =>
    inhomogVariation_unique hAx hV₀d (hVfamd h) (by rw [hV₀0, hVfam0]) s
  refine hD₃bilinear (z - x₀) h V hV0 (fun s => ?_)
  have hh := hVd s
  rw [hW₂eq s, hV₀eq s, hcurry s] at hh
  exact hh

/-- **Base-point `C³` bootstrap of the flow resolvent (assembly).**  For a `C^{3,1}` field `v`
(uniformly `K`-Lipschitz, everywhere Fréchet differentiable with `L`-Lipschitz spatial derivative
`Dv`, `M₂`-Lipschitz second derivative `D2vc`, and third derivative `D3vm`/`D3v` in both its
`E →L (E[×2] →L E)` and `E[×3] →L E` representations — `M₃`-Lipschitz, with the two-fold curry
`hcompat` and the curry-left compatibility `hcurry`) and a variational flow family `Ψ`, the packaged
**second** fundamental solution `z ↦ D₂ z` (the spatial derivative of the resolvent
`z ↦ D_x Φ_t^{A(z)}`, characterised by `D₂ z h = Vlin^{z,h} t`) is itself Fréchet differentiable at
the reference base point `x₀`, with derivative the packaged design-corrected **third**-variation
operator `D₃` of `exists_thirdVariationOperator_of_field`.

Assembly.  `exists_continuousLinearMap_linearisedVariation` (chosen over all `z`) packages the family
`D₂` of second fundamental solutions with its linearised-first-variation characterisation.
`exists_thirdVariationOperator_of_field` supplies the candidate derivative `D₃` (with the canonical
linearised-first-variation family `Vfam` and the `Fin 3`-multilinear bilinear characterisation
`hD₃bilinear`).  For each `z` near `x₀` (`‖z − x₀‖ ≤ 1`): the base curve `W₂`
(`exists_hasDerivAt_firstVariation_linearised`) and difference curve `Wdiff`
(`exists_hasDerivAt_inhomogVariation_of_continuous`) are built;
`thirdVariationOperator_hD₃_slot_of_bilinear` discharges the `hD₃` slot from `hD₃bilinear`; and
`norm_secondFundamentalSolution_op_sub_thirdVariation_le_sq_uniformC` gives the neighbourhood-uniform
operator-level `C³` Taylor remainder `‖(D₂ z − D₂ x₀) − D₃ (z − x₀)‖ ≤ C · ‖z − x₀‖²` with `C`
independent of `z`.  `hasFDerivAt_of_eventually_norm_sub_sub_le_sq` upgrades the `O(‖z − x₀‖²)` error
to `HasFDerivAt D₂ D₃ x₀`.  The spatial `C³` layer of the smooth-dependence tower unblocking Items 1
& 2; everything is proved from field-level data, no PDE or manifold content.  The remaining step to
the resolvent's spatial `ContDiff ℝ 3` is the continuity of `z ↦ D₃` and the
`contDiff_succ_iff_fderiv` chain. -/
theorem exists_hasFDerivAt_secondFundamentalSolution_baseCurve [CompleteSpace E]
    {Dv : ℝ → E → (E →L[ℝ] E)}
    {D2vc : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D2vm : ℝ → E → (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)}
    {D3vm : ℝ → E → (E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E}
    {L M₂ M₃ : ℝ≥0} {C' C'' N : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ) (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2vc : ∀ s ξ, HasFDerivAt (Dv s) (D2vc s ξ) ξ) (hD2vclip : ∀ s, LipschitzWith M₂ (D2vc s))
    (hD3vm : ∀ s ξ, HasFDerivAt (D2vm s) (D3vm s ξ) ξ) (hD3vmlip : ∀ s, LipschitzWith M₃ (D3vm s))
    (hcompat : ∀ s ξ, D2vc s ξ = curry2 (D2vm s ξ))
    (x₀ : E)
    (hAfun : ∀ z, ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K)
    (hAcontfun : ∀ z, Continuous (fun s => Dv s (Φ z s)))
    (hD2contfun : ∀ z, Continuous (fun s => D2vc s (Φ z s)))
    (hD3mcont : Continuous (fun s => D3vm s (Φ x₀ s)))
    (hD3vcont : Continuous (fun s => D3v s (Φ x₀ s)))
    (hC'0 : 0 ≤ C') (hC'fun : ∀ z, ∀ s, ‖D2vc s (Φ z s)‖ ≤ C')
    (hN0 : 0 ≤ N) (hN : ∀ s, ‖D3vm s (Φ x₀ s)‖ ≤ N)
    (hC''0 : 0 ≤ C'') (hC'' : ∀ s, ‖D3v s (Φ x₀ s)‖ ≤ C'')
    (hcurry : ∀ s, D3vm s (Φ x₀ s) = (D3v s (Φ x₀ s)).curryLeft)
    {Ψ : E → E → ℝ → E}
    (hΨ : ∀ z, ∀ x, IsIntegralCurve (Ψ z x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h0Ψ : ∀ z, ∀ x, Ψ z x t₀ = x)
    {T : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ∃ (D₂ : E → (E →L[ℝ] (E →L[ℝ] E))) (D₃ : E →L[ℝ] (E →L[ℝ] (E →L[ℝ] E))),
      (∀ (z h : E) (Vlin : ℝ → (E →L[ℝ] E)), Vlin t₀ = 0 →
        (∀ s, HasDerivAt Vlin
          ((Dv s (Φ z s)).comp (Vlin s)
            + ((D2vc s (Φ z s)).comp (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s) h).comp
                (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s)) s) →
        D₂ z h = Vlin t) ∧
      HasFDerivAt D₂ D₃ x₀ := by
  choose D₂ hD₂char using fun z => exists_continuousLinearMap_linearisedVariation
    z (hAfun z) (hAcontfun z) (hD2contfun z) (hΨ z) (h0Ψ z) hC'0 (hC'fun z) ht
  obtain ⟨Vfam, D₃, hVfam0, hVfamd, _, _, _, _, hD₃bilinear⟩ :=
    exists_thirdVariationOperator_of_field x₀ (hAfun x₀) (hAcontfun x₀) (hD2contfun x₀)
      hD3vcont (hΨ x₀) (h0Ψ x₀) hC'0 hC''0 (hC'fun x₀) hC'' ht
  refine ⟨D₂, D₃, hD₂char, ?_⟩
  apply hasFDerivAt_of_eventually_norm_sub_sub_le_sq (f := D₂) (f' := D₃) (x₀ := x₀)
  filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with z hz
  have hk : ‖z - x₀‖ ≤ 1 := by
    have hmem := Metric.mem_ball.mp hz
    rw [dist_eq_norm] at hmem
    exact hmem.le
  have hW : Continuous (fun s => fundamentalSolution (hAfun x₀) (hΨ x₀) (h0Ψ x₀) s) :=
    continuous_fundamentalSolution_time (hAfun x₀) (hΨ x₀) (h0Ψ x₀)
  obtain ⟨W₂, hW₂0, hW₂⟩ := exists_hasDerivAt_firstVariation_linearised
    x₀ (hAfun x₀) (hAcontfun x₀) (hD2contfun x₀) (hΨ x₀) (h0Ψ x₀) z
  obtain ⟨Wdiff, hWdiff0, hWdiff⟩ := exists_hasDerivAt_inhomogVariation_of_continuous
    (hAfun x₀) (hAcontfun x₀) (((hAcontfun z).sub (hAcontfun x₀)).clm_comp hW) t₀
  have hslot := thirdVariationOperator_hD₃_slot_of_bilinear x₀ z (hAfun x₀) (hΨ x₀) (h0Ψ x₀)
    hVfam0 hVfamd hcurry hD₃bilinear hW₂ hW₂0
  exact norm_secondFundamentalSolution_op_sub_thirdVariation_le_sq_uniformC
    hv hΦ h0 hDv hDvlip hD2vc hD2vclip hD3vm hD3vmlip hcompat z x₀
    (hAfun z) (hAfun x₀) (hAcontfun x₀) (hAcontfun z) (hD2contfun z) (hD2contfun x₀) hD3mcont
    hC'0 (hC'fun z) (hC'fun x₀) hN0 hN (hΨ x₀) (h0Ψ x₀) (hΨ z) (h0Ψ z)
    hW₂ hW₂0 hWdiff hWdiff0 (hD₂char z) (hD₂char x₀) hslot hk ht

/-- **Everywhere base-point `C³` bootstrap (family form).**  The uniform-in-base-point version of
`exists_hasFDerivAt_secondFundamentalSolution_baseCurve`: for a `C^{3,1}` field `v` whose third
derivative data (`D3vm`/`D3v` continuity and bounds, the curry-left compatibility `hcurry`) is
uniform over all base points, there is a **single** packaged second-fundamental-solution family
`D₂ : E → (E →L (E →L E))` (with its linearised-first-variation characterisation) and a **third**
fundamental solution family `D₃fam : E → (E →L (E →L (E →L E)))` such that `D₂` is Fréchet
differentiable at *every* base point `y` with derivative `D₃fam y`.

Assembly.  `D₂` is chosen once (`exists_continuousLinearMap_linearisedVariation`, base-point
independent); `D₃fam` (and its canonical family `Vfamfam`) is chosen over all base points
(`exists_thirdVariationOperator_of_field`).  At each base point `y` the single-base-point argument of
`exists_hasFDerivAt_secondFundamentalSolution_baseCurve` runs verbatim — per `z` near `y` build the
base curve `W₂` and difference curve `Wdiff`, discharge the `hD₃` slot with
`thirdVariationOperator_hD₃_slot_of_bilinear`, apply the neighbourhood-uniform operator-level `C³`
Taylor remainder and `hasFDerivAt_of_eventually_norm_sub_sub_le_sq`.

This is the everywhere `fderiv D₂ = D₃fam` half of the resolvent's spatial `ContDiff ℝ 3`; the sole
remaining ingredient is the continuity of the third fundamental solution `y ↦ D₃fam y`, after which
the `contDiff_succ_iff_fderiv` chain closes `exists_flow_contDiff_three_of_lipschitz_thirdDeriv`. -/
theorem exists_hasFDerivAt_secondFundamentalSolution [CompleteSpace E]
    {Dv : ℝ → E → (E →L[ℝ] E)}
    {D2vc : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D2vm : ℝ → E → (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)}
    {D3vm : ℝ → E → (E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E}
    {L M₂ M₃ : ℝ≥0} {C' C'' N : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ) (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2vc : ∀ s ξ, HasFDerivAt (Dv s) (D2vc s ξ) ξ) (hD2vclip : ∀ s, LipschitzWith M₂ (D2vc s))
    (hD3vm : ∀ s ξ, HasFDerivAt (D2vm s) (D3vm s ξ) ξ) (hD3vmlip : ∀ s, LipschitzWith M₃ (D3vm s))
    (hcompat : ∀ s ξ, D2vc s ξ = curry2 (D2vm s ξ))
    (hAfun : ∀ z, ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K)
    (hAcontfun : ∀ z, Continuous (fun s => Dv s (Φ z s)))
    (hD2contfun : ∀ z, Continuous (fun s => D2vc s (Φ z s)))
    (hD3mcont : ∀ z, Continuous (fun s => D3vm s (Φ z s)))
    (hD3vcont : ∀ z, Continuous (fun s => D3v s (Φ z s)))
    (hC'0 : 0 ≤ C') (hC'fun : ∀ z, ∀ s, ‖D2vc s (Φ z s)‖ ≤ C')
    (hN0 : 0 ≤ N) (hN : ∀ z, ∀ s, ‖D3vm s (Φ z s)‖ ≤ N)
    (hC''0 : 0 ≤ C'') (hC'' : ∀ z, ∀ s, ‖D3v s (Φ z s)‖ ≤ C'')
    (hcurry : ∀ z, ∀ s, D3vm s (Φ z s) = (D3v s (Φ z s)).curryLeft)
    {Ψ : E → E → ℝ → E}
    (hΨ : ∀ z, ∀ x, IsIntegralCurve (Ψ z x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h0Ψ : ∀ z, ∀ x, Ψ z x t₀ = x)
    {T : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ∃ (D₂ : E → (E →L[ℝ] (E →L[ℝ] E)))
        (D₃fam : E → (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] E)))),
      (∀ (z h : E) (Vlin : ℝ → (E →L[ℝ] E)), Vlin t₀ = 0 →
        (∀ s, HasDerivAt Vlin
          ((Dv s (Φ z s)).comp (Vlin s)
            + ((D2vc s (Φ z s)).comp (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s) h).comp
                (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s)) s) →
        D₂ z h = Vlin t) ∧
      (∀ y, HasFDerivAt D₂ (D₃fam y) y) := by
  choose D₂ hD₂char using fun z => exists_continuousLinearMap_linearisedVariation
    z (hAfun z) (hAcontfun z) (hD2contfun z) (hΨ z) (h0Ψ z) hC'0 (hC'fun z) ht
  choose Vfamfam D₃fam hprops using fun z => exists_thirdVariationOperator_of_field
    z (hAfun z) (hAcontfun z) (hD2contfun z) (hD3vcont z) (hΨ z) (h0Ψ z) hC'0 hC''0
      (hC'fun z) (hC'' z) ht
  refine ⟨D₂, D₃fam, hD₂char, fun y => ?_⟩
  obtain ⟨hVfam0, hVfamd, _, _, _, _, hD₃bilinear⟩ := hprops y
  apply hasFDerivAt_of_eventually_norm_sub_sub_le_sq (f := D₂) (f' := D₃fam y) (x₀ := y)
  filter_upwards [Metric.ball_mem_nhds y one_pos] with z hz
  have hk : ‖z - y‖ ≤ 1 := by
    have hmem := Metric.mem_ball.mp hz
    rw [dist_eq_norm] at hmem
    exact hmem.le
  have hW : Continuous (fun s => fundamentalSolution (hAfun y) (hΨ y) (h0Ψ y) s) :=
    continuous_fundamentalSolution_time (hAfun y) (hΨ y) (h0Ψ y)
  obtain ⟨W₂, hW₂0, hW₂⟩ := exists_hasDerivAt_firstVariation_linearised
    y (hAfun y) (hAcontfun y) (hD2contfun y) (hΨ y) (h0Ψ y) z
  obtain ⟨Wdiff, hWdiff0, hWdiff⟩ := exists_hasDerivAt_inhomogVariation_of_continuous
    (hAfun y) (hAcontfun y) (((hAcontfun z).sub (hAcontfun y)).clm_comp hW) t₀
  have hslot := thirdVariationOperator_hD₃_slot_of_bilinear y z (hAfun y) (hΨ y) (h0Ψ y)
    hVfam0 hVfamd (hcurry y) hD₃bilinear hW₂ hW₂0
  exact norm_secondFundamentalSolution_op_sub_thirdVariation_le_sq_uniformC
    hv hΦ h0 hDv hDvlip hD2vc hD2vclip hD3vm hD3vmlip hcompat z y
    (hAfun z) (hAfun y) (hAcontfun y) (hAcontfun z) (hD2contfun z) (hD2contfun y) (hD3mcont y)
    hC'0 (hC'fun z) (hC'fun y) hN0 (hN y) (hΨ y) (h0Ψ y) (hΨ z) (h0Ψ z)
    hW₂ hW₂0 hWdiff hWdiff0 (hD₂char z) (hD₂char y) hslot hk ht

/-- **Abstract base-point telescoping gap for the fully-contracted third-derivative forcing term.**
The pure operator-norm skeleton of the base-point Lipschitz gap of the fourth (third-derivative)
forcing term of the third-variation ODE.  For two third derivatives `T₁, T₂ : E [×3]→L[ℝ] E`, two
pairs of contraction directions `a₁, a₂` and `b₁, b₂`, and two outer resolvents `C₁, C₂ : E →L[ℝ] E`,
the fully-contracted forcing operators
`(continuousMultilinearCurryFin1 ((Tᵢ.curryLeft aᵢ).curryLeft bᵢ)).comp Cᵢ` differ by at most
`(p·na·nb)·dc + (p·na·db + (p·da + dp·na)·nb)·nc`, given the size bounds `‖T₁‖ ≤ p`, `‖aᵢ‖ ≤ na`,
`‖bᵢ‖ ≤ nb`, `‖C₂‖ ≤ nc` and the gaps `‖T₁ − T₂‖ ≤ dp`, `‖a₁ − a₂‖ ≤ da`, `‖b₁ − b₂‖ ≤ db`,
`‖C₁ − C₂‖ ≤ dc`.

Proof: telescope the outer composition
`(CF Mz).comp C₁ − (CF Mx).comp C₂ = (CF Mz).comp (C₁ − C₂) + (CF Mz − CF Mx).comp C₂`
(`comp_sub`/`sub_comp`), bound each summand by `opNorm_comp_le`, and fold the
`continuousMultilinearCurryFin1` isometry (`norm_map`, `map_sub`) to replace `‖CF Mz‖` by `‖Mz‖` and
`‖CF Mz − CF Mx‖` by `‖Mz − Mx‖`.  The size `‖Mz‖ ≤ p·na·nb` and the double-contraction gap
`‖Mz − Mx‖ ≤ (p·na)·db + (p·da + dp·na)·nb` both come from the bilinear evaluation gap
`norm_clm_apply_sub_le` and the `curryLeft` isometry `ContinuousMultilinearMap.curryLeft_norm`.  This
is the `curryFin1`-composed analogue of `norm_bilinearCompForcing_sub_le` — the perturbation primitive
for the one third-variation forcing term not of the `((P ∘ A) h) ∘ B` shape. -/
theorem norm_curryFin1_biContract_comp_sub_le
    {T₁ T₂ : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E}
    {a₁ a₂ b₁ b₂ : E} {C₁ C₂ : E →L[ℝ] E}
    {p na nb nc dp da db dc : ℝ}
    (hT₁ : ‖T₁‖ ≤ p)
    (ha₁ : ‖a₁‖ ≤ na) (ha₂ : ‖a₂‖ ≤ na)
    (hb₁ : ‖b₁‖ ≤ nb) (hb₂ : ‖b₂‖ ≤ nb)
    (hC₂ : ‖C₂‖ ≤ nc)
    (hTd : ‖T₁ - T₂‖ ≤ dp) (had : ‖a₁ - a₂‖ ≤ da)
    (hbd : ‖b₁ - b₂‖ ≤ db) (hCd : ‖C₁ - C₂‖ ≤ dc) :
    ‖(continuousMultilinearCurryFin1 ℝ E E ((T₁.curryLeft a₁).curryLeft b₁)).comp C₁
        - (continuousMultilinearCurryFin1 ℝ E E ((T₂.curryLeft a₂).curryLeft b₂)).comp C₂‖
      ≤ (p * na * nb) * dc + (p * na * db + (p * da + dp * na) * nb) * nc := by
  have hp0 : 0 ≤ p := le_trans (norm_nonneg _) hT₁
  have hna0 : 0 ≤ na := le_trans (norm_nonneg _) ha₁
  have hnb0 : 0 ≤ nb := le_trans (norm_nonneg _) hb₁
  have hdp0 : 0 ≤ dp := le_trans (norm_nonneg _) hTd
  have hda0 : 0 ≤ da := le_trans (norm_nonneg _) had
  have hdb0 : 0 ≤ db := le_trans (norm_nonneg _) hbd
  -- `‖T₁.curryLeft a₁‖ ≤ p · na`
  have hPz : ‖T₁.curryLeft a₁‖ ≤ p * na := by
    calc ‖T₁.curryLeft a₁‖ ≤ ‖T₁.curryLeft‖ * ‖a₁‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖T₁‖ * ‖a₁‖ := by rw [ContinuousMultilinearMap.curryLeft_norm]
      _ ≤ p * na := mul_le_mul hT₁ ha₁ (norm_nonneg _) hp0
  -- `‖Mz‖ ≤ p · na · nb`
  have hMz : ‖(T₁.curryLeft a₁).curryLeft b₁‖ ≤ p * na * nb := by
    calc ‖(T₁.curryLeft a₁).curryLeft b₁‖
        ≤ ‖(T₁.curryLeft a₁).curryLeft‖ * ‖b₁‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖T₁.curryLeft a₁‖ * ‖b₁‖ := by rw [ContinuousMultilinearMap.curryLeft_norm]
      _ ≤ (p * na) * nb := mul_le_mul hPz hb₁ (norm_nonneg _) (mul_nonneg hp0 hna0)
  -- first-contraction gap `‖T₁.curryLeft a₁ − T₂.curryLeft a₂‖ ≤ p · da + dp · na`
  have hPgap : ‖T₁.curryLeft a₁ - T₂.curryLeft a₂‖ ≤ p * da + dp * na := by
    have hbb := norm_clm_apply_sub_le T₁.curryLeft T₂.curryLeft a₁ a₂
    have e1 : ‖T₁.curryLeft‖ = ‖T₁‖ := ContinuousMultilinearMap.curryLeft_norm _
    have e2 : ‖T₁.curryLeft - T₂.curryLeft‖ = ‖T₁ - T₂‖ := by
      rw [show T₁.curryLeft - T₂.curryLeft = (T₁ - T₂).curryLeft from
            (ContinuousLinearMap.ext (congrFun rfl)).symm,
          ContinuousMultilinearMap.curryLeft_norm]
    rw [e1, e2] at hbb
    refine hbb.trans (add_le_add ?_ ?_)
    · exact mul_le_mul hT₁ had (norm_nonneg _) hp0
    · exact mul_le_mul hTd ha₂ (norm_nonneg _) hdp0
  -- double-contraction gap `‖Mz − Mx‖ ≤ (p·na)·db + (p·da + dp·na)·nb`
  have hMgap : ‖(T₁.curryLeft a₁).curryLeft b₁ - (T₂.curryLeft a₂).curryLeft b₂‖
      ≤ p * na * db + (p * da + dp * na) * nb := by
    have hbb := norm_clm_apply_sub_le (T₁.curryLeft a₁).curryLeft (T₂.curryLeft a₂).curryLeft b₁ b₂
    have e1 : ‖(T₁.curryLeft a₁).curryLeft‖ = ‖T₁.curryLeft a₁‖ :=
      ContinuousMultilinearMap.curryLeft_norm _
    have e2 : ‖(T₁.curryLeft a₁).curryLeft - (T₂.curryLeft a₂).curryLeft‖
        = ‖T₁.curryLeft a₁ - T₂.curryLeft a₂‖ := by
      rw [show (T₁.curryLeft a₁).curryLeft - (T₂.curryLeft a₂).curryLeft
            = ((T₁.curryLeft a₁) - (T₂.curryLeft a₂)).curryLeft from
            (ContinuousLinearMap.ext (congrFun rfl)).symm,
          ContinuousMultilinearMap.curryLeft_norm]
    rw [e1, e2] at hbb
    refine hbb.trans (add_le_add ?_ ?_)
    · exact mul_le_mul hPz hbd (norm_nonneg _) (mul_nonneg hp0 hna0)
    · exact mul_le_mul hPgap hb₂ (norm_nonneg _)
        (add_nonneg (mul_nonneg hp0 hda0) (mul_nonneg hdp0 hna0))
  -- fold the outer isometry
  have hcf1 : ‖continuousMultilinearCurryFin1 ℝ E E ((T₁.curryLeft a₁).curryLeft b₁)‖
      = ‖(T₁.curryLeft a₁).curryLeft b₁‖ :=
    (continuousMultilinearCurryFin1 ℝ E E).norm_map _
  have hcf2 : ‖continuousMultilinearCurryFin1 ℝ E E ((T₁.curryLeft a₁).curryLeft b₁)
        - continuousMultilinearCurryFin1 ℝ E E ((T₂.curryLeft a₂).curryLeft b₂)‖
      = ‖(T₁.curryLeft a₁).curryLeft b₁ - (T₂.curryLeft a₂).curryLeft b₂‖ := by
    rw [← map_sub (continuousMultilinearCurryFin1 ℝ E E)]
    exact (continuousMultilinearCurryFin1 ℝ E E).norm_map _
  have hsplit :
      (continuousMultilinearCurryFin1 ℝ E E ((T₁.curryLeft a₁).curryLeft b₁)).comp C₁
        - (continuousMultilinearCurryFin1 ℝ E E ((T₂.curryLeft a₂).curryLeft b₂)).comp C₂
      = (continuousMultilinearCurryFin1 ℝ E E ((T₁.curryLeft a₁).curryLeft b₁)).comp (C₁ - C₂)
        + (continuousMultilinearCurryFin1 ℝ E E ((T₁.curryLeft a₁).curryLeft b₁)
            - continuousMultilinearCurryFin1 ℝ E E ((T₂.curryLeft a₂).curryLeft b₂)).comp C₂ := by
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]; abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
    (ContinuousLinearMap.opNorm_comp_le _ _)).trans ?_
  rw [hcf1, hcf2]
  refine add_le_add
    (mul_le_mul hMz hCd (norm_nonneg _) (mul_nonneg (mul_nonneg hp0 hna0) hnb0)) ?_
  refine mul_le_mul hMgap hC₂ (norm_nonneg _) ?_
  exact add_nonneg (mul_nonneg (mul_nonneg hp0 hna0) hdb0)
    (mul_nonneg (add_nonneg (mul_nonneg hp0 hda0) (mul_nonneg hdp0 hna0)) hnb0)

/-- **Base-point Lipschitz gap of the fully-contracted third-derivative forcing term.**  The linear
(continuity-grade) base-point gap of the fourth forcing term of the third-variation ODE, and the
`C³`-layer analogue one order up of the chain-rule forcing gap inside
`norm_linearisedFirstVariation_baseCurve_sub_le`.  For two base points `z`, `x₀` with their variational
resolvents `W_z = fundamentalSolution hAz hΦ₁ h1`, `W_x = fundamentalSolution hAx hΦ₂ h2`, the
fully-contracted third-derivative forcing operator
`s ↦ (continuousMultilinearCurryFin1 ((D³v(Φ · s)).curryLeft (W k)).curryLeft (W h)).comp W`
moves, for `s ∈ [t₀, T]`, by at most
`exp(K(T−t₀))⁴ · (M₃ + 3·C''·L·gronwallBound 0 K 1 (T−t₀)) · ‖z − x₀‖ · ‖k‖ · ‖h‖`.

Proof: instantiate the abstract telescoping gap `norm_curryFin1_biContract_comp_sub_le` with
`T₁ = D³v(Φ z s)`, `a₁ = W_z k`, `b₁ = W_z h`, `C₁ = W_z` (and the `x₀`-versions), feeding the flow
size data `‖D³v(Φ z s)‖ ≤ C''`, `‖W_· u‖ ≤ exp(K(T−t₀))·‖u‖` (`norm_fundamentalSolution_le`), the
resolvent base-gap `‖W_z − W_x‖ ≤ L·exp(K(T−t₀))²·gronwallBound 0 K 1 (T−t₀)·‖z − x₀‖`
(`norm_fundamentalSolution_baseCurve_sub_le` + `gronwallBound_mono`), and the third-derivative field
base-gap `‖D³v(Φ z s) − D³v(Φ x₀ s)‖ ≤ M₃·exp(K(T−t₀))·‖z − x₀‖`
(`norm_thirdDerivField_apply_flow_sub_le`); the abstract polynomial constant collapses to the clean
`exp⁴·(M₃ + 3C''Lg)` form by `ring`.  This is the last of the four forcing-term base-gaps needed for
the third-variation curve continuity — the `D₃`-analogue of the `chainRuleForcing` gap. -/
theorem norm_thirdDerivForcing_baseCurve_sub_le
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E}
    {L M₃ : ℝ≥0} {C'' : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hDvlip : ∀ s, LipschitzWith L (Dv s)) (hD3vlip : ∀ s, LipschitzWith M₃ (D3v s))
    (z x₀ : E)
    (hAz : ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K) (hAx : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hC''z : ∀ s, ‖D3v s (Φ z s)‖ ≤ C'')
    {Φ₁ Φ₂ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h1 : ∀ x, Φ₁ x t₀ = x)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h2 : ∀ x, Φ₂ x t₀ = x)
    (k h : E) {T s : ℝ} (hs : s ∈ Set.Icc t₀ T) :
    ‖(continuousMultilinearCurryFin1 ℝ E E
          (((D3v s (Φ z s)).curryLeft (fundamentalSolution hAz hΦ₁ h1 s k)).curryLeft
            (fundamentalSolution hAz hΦ₁ h1 s h))).comp (fundamentalSolution hAz hΦ₁ h1 s)
        - (continuousMultilinearCurryFin1 ℝ E E
          (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hAx hΦ₂ h2 s k)).curryLeft
            (fundamentalSolution hAx hΦ₂ h2 s h))).comp (fundamentalSolution hAx hΦ₂ h2 s)‖
      ≤ Real.exp ((K : ℝ) * (T - t₀)) ^ 4
          * (3 * C'' * (L : ℝ) * gronwallBound 0 (K : ℝ) 1 (T - t₀) + (M₃ : ℝ))
          * ‖z - x₀‖ * ‖k‖ * ‖h‖ := by
  have hsT : |s - t₀| ≤ T - t₀ := by
    rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
  have hexpmono : Real.exp ((K : ℝ) * |s - t₀|) ≤ Real.exp ((K : ℝ) * (T - t₀)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsT K.coe_nonneg)
  have hWzn : ‖fundamentalSolution hAz hΦ₁ h1 s‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) :=
    (norm_fundamentalSolution_le hAz hΦ₁ h1 s).trans hexpmono
  have hWxn : ‖fundamentalSolution hAx hΦ₂ h2 s‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) :=
    (norm_fundamentalSolution_le hAx hΦ₂ h2 s).trans hexpmono
  have hdw : ‖fundamentalSolution hAz hΦ₁ h1 s - fundamentalSolution hAx hΦ₂ h2 s‖
      ≤ (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖
          * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀) := by
    refine (norm_fundamentalSolution_baseCurve_sub_le hv hΦ h0 hDvlip z x₀ hAz hAx
      hΦ₁ h1 hΦ₂ h2 hs).trans ?_
    have hmono : gronwallBound 0 (K : ℝ) 1 (s - t₀) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
      gronwallBound_mono (le_refl (0:ℝ)) zero_le_one K.coe_nonneg (by linarith [hs.2])
    exact mul_le_mul_of_nonneg_left hmono (by positivity)
  -- contracted resolvent-direction sizes
  have haz : ‖fundamentalSolution hAz hΦ₁ h1 s k‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) * ‖k‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hWzn (norm_nonneg _))
  have hax : ‖fundamentalSolution hAx hΦ₂ h2 s k‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) * ‖k‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hWxn (norm_nonneg _))
  have hbz : ‖fundamentalSolution hAz hΦ₁ h1 s h‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hWzn (norm_nonneg _))
  have hbx : ‖fundamentalSolution hAx hΦ₂ h2 s h‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hWxn (norm_nonneg _))
  -- third-derivative field base-gap
  have hTd : ‖D3v s (Φ z s) - D3v s (Φ x₀ s)‖
      ≤ (M₃ : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖ :=
    norm_thirdDerivField_apply_flow_sub_le hv hΦ h0 (hD3vlip s) hsT z x₀
  -- contracted resolvent-direction gaps
  have had : ‖fundamentalSolution hAz hΦ₁ h1 s k - fundamentalSolution hAx hΦ₂ h2 s k‖
      ≤ ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖
          * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀)) * ‖k‖ := by
    rw [← ContinuousLinearMap.sub_apply]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hdw (norm_nonneg _))
  have hbd : ‖fundamentalSolution hAz hΦ₁ h1 s h - fundamentalSolution hAx hΦ₂ h2 s h‖
      ≤ ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖
          * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀)) * ‖h‖ := by
    rw [← ContinuousLinearMap.sub_apply]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hdw (norm_nonneg _))
  refine (norm_curryFin1_biContract_comp_sub_le (hC''z s) haz hax hbz hbx hWxn hTd had hbd
    hdw).trans_eq ?_
  ring

/-- **Base-point Lipschitz gap of the `Vfam`-inner bilinear composition forcing term
`((D²v ∘ Vfam_k) h) ∘ W`.**  The first of the three `((P ∘ A) d) ∘ B`-shaped forcing terms of the
third-variation ODE, in which the *inner* operand `A` is a linearised first-variation curve `Vfam_k`
(direction `k`) and the *outer* operand `B` is the resolvent `W`.  For two base points `z`, `x₀` with
resolvents `W_z`, `W_x` and linearised first-variation curves `U_z`, `U_x` in direction `k` (solving the
linearised ODE at `z`, `x₀` respectively), the forcing operator
`s ↦ ((D²v(Φ · s) ∘ U_·) h) ∘ W_·` moves, for `s ∈ [t₀, T]`, by at most
`exp(K(T−t₀))⁴ · g · (2·M₂·C' + 4·L·C'²·g) · ‖z − x₀‖ · ‖k‖ · ‖h‖` with `g = gronwallBound 0 K 1 (T−t₀)`.

Proof: instantiate the abstract composition-forcing perturbation `norm_bilinearCompForcing_sub_le` with
`P = D²v(Φ · s)`, `A = U_·` (the `Vfam_k` curve), `B = W_·`, feeding the sizes `‖D²v‖ ≤ C'`,
`‖U_·‖ ≤ C'·exp(K(T−t₀))²·‖k‖·g` (`norm_linearisedFirstVariation_le`), `‖W_x‖ ≤ exp(K(T−t₀))`, and the
base-gaps `‖D²v(Φ z) − D²v(Φ x₀)‖ ≤ M₂·exp·‖z−x₀‖` (`norm_secondDerivField_apply_flow_sub_le`),
`‖U_z − U_x‖ ≤ exp³·(M₂ + 3LC'g)·‖z−x₀‖·‖k‖·g` (`norm_linearisedFirstVariation_baseCurve_sub_le`),
`‖W_z − W_x‖ ≤ L·exp²·g·‖z−x₀‖` (`norm_fundamentalSolution_baseCurve_sub_le`); the abstract
`(dp·a·b + p·da·b + p·a·db)·‖h‖` bound collapses to the clean `exp⁴·g·(2M₂C' + 4LC'²g)` form by
`ring`. -/
theorem norm_bilinearComp_VfamInner_baseCurve_sub_le
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {L M₂ : ℝ≥0} {C' : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hDvlip : ∀ s, LipschitzWith L (Dv s)) (hD2vlip : ∀ s, LipschitzWith M₂ (D2v s))
    (z x₀ : E)
    (hAz : ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K) (hAx : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hC'0 : 0 ≤ C') (hC'z : ∀ s, ‖D2v s (Φ z s)‖ ≤ C') (hC'x : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ C')
    {Φ₁ Φ₂ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h1 : ∀ x, Φ₁ x t₀ = x)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h2 : ∀ x, Φ₂ x t₀ = x)
    (k h : E) {T : ℝ}
    {Uz Ux : ℝ → (E →L[ℝ] E)}
    (hUz : ∀ s, HasDerivAt Uz
      ((Dv s (Φ z s)).comp (Uz s)
        + ((D2v s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h1 s) k).comp
            (fundamentalSolution hAz hΦ₁ h1 s)) s)
    (hUz0 : Uz t₀ = 0)
    (hUx : ∀ s, HasDerivAt Ux
      ((Dv s (Φ x₀ s)).comp (Ux s)
        + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) k).comp
            (fundamentalSolution hAx hΦ₂ h2 s)) s)
    (hUx0 : Ux t₀ = 0)
    {s : ℝ} (hs : s ∈ Set.Icc t₀ T) :
    ‖((D2v s (Φ z s)).comp (Uz s) h).comp (fundamentalSolution hAz hΦ₁ h1 s)
        - ((D2v s (Φ x₀ s)).comp (Ux s) h).comp (fundamentalSolution hAx hΦ₂ h2 s)‖
      ≤ Real.exp ((K : ℝ) * (T - t₀)) ^ 4 * gronwallBound 0 (K : ℝ) 1 (T - t₀)
          * (2 * (M₂ : ℝ) * C' + 4 * (L : ℝ) * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀))
          * ‖z - x₀‖ * ‖k‖ * ‖h‖ := by
  have hsabs : |s - t₀| ≤ T - t₀ := by
    rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
  have he0 : (0 : ℝ) ≤ Real.exp ((K : ℝ) * (T - t₀)) := (Real.exp_pos _).le
  have hg0 : (0 : ℝ) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
    gronwallBound_zero_one_nonneg K.coe_nonneg (sub_nonneg.mpr (le_trans hs.1 hs.2))
  have hgmono : gronwallBound 0 (K : ℝ) 1 (s - t₀) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
    gronwallBound_mono (le_refl (0 : ℝ)) zero_le_one K.coe_nonneg (by linarith [hs.2])
  have he2 : Real.exp (2 * (K : ℝ) * (T - t₀)) = Real.exp ((K : ℝ) * (T - t₀)) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  -- resolvent sizes and base-gap
  have hWxn : ‖fundamentalSolution hAx hΦ₂ h2 s‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) :=
    (norm_fundamentalSolution_le hAx hΦ₂ h2 s).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsabs K.coe_nonneg))
  have hBd : ‖fundamentalSolution hAz hΦ₁ h1 s - fundamentalSolution hAx hΦ₂ h2 s‖
      ≤ (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖
          * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀) := by
    refine (norm_fundamentalSolution_baseCurve_sub_le hv hΦ h0 hDvlip z x₀ hAz hAx
      hΦ₁ h1 hΦ₂ h2 hs).trans ?_
    exact mul_le_mul_of_nonneg_left hgmono (by positivity)
  -- `Vfam_k`-curve sizes
  have hA₁ : ‖Uz s‖ ≤ C' * Real.exp ((K : ℝ) * (T - t₀)) ^ 2 * ‖k‖
      * gronwallBound 0 (K : ℝ) 1 (T - t₀) := by
    have hle := norm_linearisedFirstVariation_le z hAz hΦ₁ h1 hC'0 hC'z k hUz hUz0 hs
    rw [he2] at hle
    refine hle.trans ?_
    exact mul_le_mul_of_nonneg_left hgmono
      (mul_nonneg (mul_nonneg hC'0 (by positivity)) (norm_nonneg _))
  have hA₂ : ‖Ux s‖ ≤ C' * Real.exp ((K : ℝ) * (T - t₀)) ^ 2 * ‖k‖
      * gronwallBound 0 (K : ℝ) 1 (T - t₀) := by
    have hle := norm_linearisedFirstVariation_le x₀ hAx hΦ₂ h2 hC'0 hC'x k hUx hUx0 hs
    rw [he2] at hle
    refine hle.trans ?_
    exact mul_le_mul_of_nonneg_left hgmono
      (mul_nonneg (mul_nonneg hC'0 (by positivity)) (norm_nonneg _))
  -- `Vfam_k`-curve base-gap
  have hMco : (0 : ℝ) ≤ (M₂ : ℝ) + 3 * (L : ℝ) * C' * gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
    add_nonneg M₂.coe_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) L.coe_nonneg) hC'0) hg0)
  have hAd : ‖Uz s - Ux s‖
      ≤ Real.exp ((K : ℝ) * (T - t₀)) ^ 3
          * ((M₂ : ℝ) + 3 * (L : ℝ) * C' * gronwallBound 0 (K : ℝ) 1 (T - t₀))
          * ‖z - x₀‖ * ‖k‖ * gronwallBound 0 (K : ℝ) 1 (T - t₀) := by
    refine (norm_linearisedFirstVariation_baseCurve_sub_le hv hΦ h0 hDvlip hD2vlip z x₀ hAz hAx
      hC'0 hC'z hC'x hΦ₁ h1 hΦ₂ h2 k hUz hUz0 hUx hUx0 hs).trans ?_
    exact mul_le_mul_of_nonneg_left hgmono
      (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hMco) (norm_nonneg _)) (norm_nonneg _))
  -- second-derivative field base-gap
  have hPd : ‖D2v s (Φ z s) - D2v s (Φ x₀ s)‖
      ≤ (M₂ : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖ :=
    norm_secondDerivField_apply_flow_sub_le hv hΦ h0 (hD2vlip s) hsabs z x₀
  refine (norm_bilinearCompForcing_sub_le h (hC'z s) hA₁ hA₂ hWxn hPd hAd hBd hC'0
    (mul_nonneg (mul_nonneg (mul_nonneg hC'0 (by positivity)) (norm_nonneg _)) hg0)
    (mul_nonneg (mul_nonneg M₂.coe_nonneg he0) (norm_nonneg _))
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hMco) (norm_nonneg _))
      (norm_nonneg _)) hg0)).trans_eq ?_
  ring

/-- **Base-point Lipschitz gap of the `Vfam`-outer bilinear composition forcing term
`((D²v ∘ W) d) ∘ Vfam_e`.**  The second and third `((P ∘ A) d) ∘ B`-shaped forcing terms of the
third-variation ODE, in which the *inner* operand `A` is the resolvent `W` and the *outer* operand `B`
is a linearised first-variation curve `Vfam_e` (direction `e`); the two forcing terms `2` and `3`
differ only by the choice of the fixed direction `d` and the family direction `e` (`d = h, e = k` for
term 2; `d = k, e = h` for term 3).  For two base points `z`, `x₀` with resolvents `W_z`, `W_x` and
linearised first-variation curves `U_z`, `U_x` in direction `e`, the forcing operator
`s ↦ ((D²v(Φ · s) ∘ W_·) d) ∘ U_·` moves, for `s ∈ [t₀, T]`, by at most
`exp(K(T−t₀))⁴ · g · (2·M₂·C' + 4·L·C'²·g) · ‖z − x₀‖ · ‖e‖ · ‖d‖` with `g = gronwallBound 0 K 1 (T−t₀)`
— the same clean constant as the `Vfam`-inner term, with `‖k‖·‖h‖` replaced by `‖e‖·‖d‖`.

Proof: instantiate `norm_bilinearCompForcing_sub_le` with `P = D²v(Φ · s)`, inner `A = W_·`, outer
`B = U_·`, feeding `‖D²v‖ ≤ C'`, `‖W_·‖ ≤ exp(K(T−t₀))`, `‖U_x‖ ≤ C'·exp²·‖e‖·g`
(`norm_linearisedFirstVariation_le`), the `D²v`-gap `M₂·exp·‖z−x₀‖`, the resolvent base-gap
`L·exp²·g·‖z−x₀‖`, and the `Vfam_e` base-gap `exp³·(M₂ + 3LC'g)·‖z−x₀‖·‖e‖·g`; the abstract bound
collapses by `ring`. -/
theorem norm_bilinearComp_VfamOuter_baseCurve_sub_le
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {L M₂ : ℝ≥0} {C' : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hDvlip : ∀ s, LipschitzWith L (Dv s)) (hD2vlip : ∀ s, LipschitzWith M₂ (D2v s))
    (z x₀ : E)
    (hAz : ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K) (hAx : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hC'0 : 0 ≤ C') (hC'z : ∀ s, ‖D2v s (Φ z s)‖ ≤ C') (hC'x : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ C')
    {Φ₁ Φ₂ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h1 : ∀ x, Φ₁ x t₀ = x)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h2 : ∀ x, Φ₂ x t₀ = x)
    (d e : E) {T : ℝ}
    {Uz Ux : ℝ → (E →L[ℝ] E)}
    (hUz : ∀ s, HasDerivAt Uz
      ((Dv s (Φ z s)).comp (Uz s)
        + ((D2v s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h1 s) e).comp
            (fundamentalSolution hAz hΦ₁ h1 s)) s)
    (hUz0 : Uz t₀ = 0)
    (hUx : ∀ s, HasDerivAt Ux
      ((Dv s (Φ x₀ s)).comp (Ux s)
        + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) e).comp
            (fundamentalSolution hAx hΦ₂ h2 s)) s)
    (hUx0 : Ux t₀ = 0)
    {s : ℝ} (hs : s ∈ Set.Icc t₀ T) :
    ‖((D2v s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h1 s) d).comp (Uz s)
        - ((D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) d).comp (Ux s)‖
      ≤ Real.exp ((K : ℝ) * (T - t₀)) ^ 4 * gronwallBound 0 (K : ℝ) 1 (T - t₀)
          * (2 * (M₂ : ℝ) * C' + 4 * (L : ℝ) * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀))
          * ‖z - x₀‖ * ‖e‖ * ‖d‖ := by
  have hsabs : |s - t₀| ≤ T - t₀ := by
    rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
  have he0 : (0 : ℝ) ≤ Real.exp ((K : ℝ) * (T - t₀)) := (Real.exp_pos _).le
  have hg0 : (0 : ℝ) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
    gronwallBound_zero_one_nonneg K.coe_nonneg (sub_nonneg.mpr (le_trans hs.1 hs.2))
  have hgmono : gronwallBound 0 (K : ℝ) 1 (s - t₀) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
    gronwallBound_mono (le_refl (0 : ℝ)) zero_le_one K.coe_nonneg (by linarith [hs.2])
  have he2 : Real.exp (2 * (K : ℝ) * (T - t₀)) = Real.exp ((K : ℝ) * (T - t₀)) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  -- resolvent sizes and base-gap (inner operand)
  have hWzn : ‖fundamentalSolution hAz hΦ₁ h1 s‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) :=
    (norm_fundamentalSolution_le hAz hΦ₁ h1 s).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsabs K.coe_nonneg))
  have hWxn : ‖fundamentalSolution hAx hΦ₂ h2 s‖ ≤ Real.exp ((K : ℝ) * (T - t₀)) :=
    (norm_fundamentalSolution_le hAx hΦ₂ h2 s).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsabs K.coe_nonneg))
  have hAd : ‖fundamentalSolution hAz hΦ₁ h1 s - fundamentalSolution hAx hΦ₂ h2 s‖
      ≤ (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖
          * Real.exp ((K : ℝ) * (T - t₀)) * gronwallBound 0 (K : ℝ) 1 (T - t₀) := by
    refine (norm_fundamentalSolution_baseCurve_sub_le hv hΦ h0 hDvlip z x₀ hAz hAx
      hΦ₁ h1 hΦ₂ h2 hs).trans ?_
    exact mul_le_mul_of_nonneg_left hgmono (by positivity)
  -- `Vfam_e`-curve size (outer operand)
  have hB₂ : ‖Ux s‖ ≤ C' * Real.exp ((K : ℝ) * (T - t₀)) ^ 2 * ‖e‖
      * gronwallBound 0 (K : ℝ) 1 (T - t₀) := by
    have hle := norm_linearisedFirstVariation_le x₀ hAx hΦ₂ h2 hC'0 hC'x e hUx hUx0 hs
    rw [he2] at hle
    refine hle.trans ?_
    exact mul_le_mul_of_nonneg_left hgmono
      (mul_nonneg (mul_nonneg hC'0 (by positivity)) (norm_nonneg _))
  -- `Vfam_e`-curve base-gap (outer operand)
  have hMco : (0 : ℝ) ≤ (M₂ : ℝ) + 3 * (L : ℝ) * C' * gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
    add_nonneg M₂.coe_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) L.coe_nonneg) hC'0) hg0)
  have hBd : ‖Uz s - Ux s‖
      ≤ Real.exp ((K : ℝ) * (T - t₀)) ^ 3
          * ((M₂ : ℝ) + 3 * (L : ℝ) * C' * gronwallBound 0 (K : ℝ) 1 (T - t₀))
          * ‖z - x₀‖ * ‖e‖ * gronwallBound 0 (K : ℝ) 1 (T - t₀) := by
    refine (norm_linearisedFirstVariation_baseCurve_sub_le hv hΦ h0 hDvlip hD2vlip z x₀ hAz hAx
      hC'0 hC'z hC'x hΦ₁ h1 hΦ₂ h2 e hUz hUz0 hUx hUx0 hs).trans ?_
    exact mul_le_mul_of_nonneg_left hgmono
      (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hMco) (norm_nonneg _)) (norm_nonneg _))
  -- second-derivative field base-gap
  have hPd : ‖D2v s (Φ z s) - D2v s (Φ x₀ s)‖
      ≤ (M₂ : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖ :=
    norm_secondDerivField_apply_flow_sub_le hv hΦ h0 (hD2vlip s) hsabs z x₀
  refine (norm_bilinearCompForcing_sub_le d (hC'z s) hWzn hWxn hB₂ hPd hAd hBd hC'0 he0
    (mul_nonneg (mul_nonneg M₂.coe_nonneg he0) (norm_nonneg _))
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg L.coe_nonneg he0) (norm_nonneg _)) he0)
      hg0)).trans_eq ?_
  ring

/-- **Four-fold triangle inequality for a difference of right-nested sums.**  For `a, b, c, d` and
`a', b', c', d'` in any seminormed additive group,
`‖(a + (b + (c + d))) − (a' + (b' + (c' + d')))‖ ≤ ‖a − a'‖ + ‖b − b'‖ + ‖c − c'‖ + ‖d − d'‖`.  The
grouping `a + (b + (c + d))` matches the right-nested shape of the four-term third-variation forcing, so
this reduces the base-point gap of the whole forcing to the four individual term gaps in one step. -/
theorem norm_add4_sub_add4_le {F : Type*} [SeminormedAddCommGroup F]
    (a b c d a' b' c' d' : F) :
    ‖a + (b + (c + d)) - (a' + (b' + (c' + d')))‖
      ≤ ‖a - a'‖ + ‖b - b'‖ + ‖c - c'‖ + ‖d - d'‖ := by
  have heq : a + (b + (c + d)) - (a' + (b' + (c' + d')))
      = (a - a') + ((b - b') + ((c - c') + (d - d'))) := by abel
  rw [heq]
  calc ‖(a - a') + ((b - b') + ((c - c') + (d - d')))‖
      ≤ ‖a - a'‖ + ‖(b - b') + ((c - c') + (d - d'))‖ := norm_add_le _ _
    _ ≤ ‖a - a'‖ + (‖b - b'‖ + ‖(c - c') + (d - d')‖) := add_le_add le_rfl (norm_add_le _ _)
    _ ≤ ‖a - a'‖ + (‖b - b'‖ + (‖c - c'‖ + ‖d - d'‖)) :=
        add_le_add le_rfl (add_le_add le_rfl (norm_add_le _ _))
    _ = ‖a - a'‖ + ‖b - b'‖ + ‖c - c'‖ + ‖d - d'‖ := by ring

/-- **Base-point Lipschitz gap of the full four-term third-variation forcing (`β`).**  The
`C³`-continuity forcing gap: for a `C^{3,1}` field and two base points `z`, `x₀` with resolvents
`W_z`, `W_x` and linearised first-variation curves `Uzk = Vfam^z k`, `Uxk = Vfam^x k` (direction `k`)
and `Uzh = Vfam^z h`, `Uxh = Vfam^x h` (direction `h`), the whole design-corrected third-variation
forcing
`F = ((D²v ∘ Vfam_k) h) ∘ W + (((D²v ∘ W) h) ∘ Vfam_k + (((D²v ∘ W) k) ∘ Vfam_h + curryFin1(D³v[Wk,Wh,W·])))`
moves, for `s ∈ [t₀, T]`, by at most
`(3·exp⁴·g·(2M₂C' + 4LC'²g) + exp⁴·(3C''Lg + M₃)) · ‖z − x₀‖ · ‖k‖ · ‖h‖`
with `exp = exp(K(T−t₀))`, `g = gronwallBound 0 K 1 (T−t₀)`.

Proof: the four-fold triangle inequality `norm_add4_sub_add4_le` reduces the forcing gap to the four
individual term gaps `norm_bilinearComp_VfamInner_baseCurve_sub_le` (term 1),
`norm_bilinearComp_VfamOuter_baseCurve_sub_le` (terms 2, 3) and `norm_thirdDerivForcing_baseCurve_sub_le`
(term 4); the sum of the four explicit constants collapses by `ring`.  This is the `β` ingredient of the
third-variation curve base gap, exactly analogous to the single chain-rule forcing gap `β` of
`norm_linearisedFirstVariation_baseCurve_sub_le` one order up. -/
theorem norm_thirdVariationForcing_baseCurve_sub_le
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E}
    {L M₂ M₃ : ℝ≥0} {C' C'' : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hDvlip : ∀ s, LipschitzWith L (Dv s)) (hD2vlip : ∀ s, LipschitzWith M₂ (D2v s))
    (hD3vlip : ∀ s, LipschitzWith M₃ (D3v s))
    (z x₀ : E)
    (hAz : ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K) (hAx : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hC'0 : 0 ≤ C') (hC'z : ∀ s, ‖D2v s (Φ z s)‖ ≤ C') (hC'x : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ C')
    (hC''z : ∀ s, ‖D3v s (Φ z s)‖ ≤ C'')
    {Φ₁ Φ₂ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h1 : ∀ x, Φ₁ x t₀ = x)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h2 : ∀ x, Φ₂ x t₀ = x)
    (k h : E) {T : ℝ}
    {Uzk Uxk Uzh Uxh : ℝ → (E →L[ℝ] E)}
    (hUzk : ∀ s, HasDerivAt Uzk
      ((Dv s (Φ z s)).comp (Uzk s)
        + ((D2v s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h1 s) k).comp
            (fundamentalSolution hAz hΦ₁ h1 s)) s)
    (hUzk0 : Uzk t₀ = 0)
    (hUxk : ∀ s, HasDerivAt Uxk
      ((Dv s (Φ x₀ s)).comp (Uxk s)
        + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) k).comp
            (fundamentalSolution hAx hΦ₂ h2 s)) s)
    (hUxk0 : Uxk t₀ = 0)
    (hUzh : ∀ s, HasDerivAt Uzh
      ((Dv s (Φ z s)).comp (Uzh s)
        + ((D2v s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h1 s) h).comp
            (fundamentalSolution hAz hΦ₁ h1 s)) s)
    (hUzh0 : Uzh t₀ = 0)
    (hUxh : ∀ s, HasDerivAt Uxh
      ((Dv s (Φ x₀ s)).comp (Uxh s)
        + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) h).comp
            (fundamentalSolution hAx hΦ₂ h2 s)) s)
    (hUxh0 : Uxh t₀ = 0)
    {s : ℝ} (hs : s ∈ Set.Icc t₀ T) :
    ‖(((D2v s (Φ z s)).comp (Uzk s) h).comp (fundamentalSolution hAz hΦ₁ h1 s)
        + (((D2v s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h1 s) h).comp (Uzk s)
           + (((D2v s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h1 s) k).comp (Uzh s)
              + (continuousMultilinearCurryFin1 ℝ E E
                  (((D3v s (Φ z s)).curryLeft (fundamentalSolution hAz hΦ₁ h1 s k)).curryLeft
                    (fundamentalSolution hAz hΦ₁ h1 s h))).comp
                  (fundamentalSolution hAz hΦ₁ h1 s))))
      - (((D2v s (Φ x₀ s)).comp (Uxk s) h).comp (fundamentalSolution hAx hΦ₂ h2 s)
        + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) h).comp (Uxk s)
           + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) k).comp (Uxh s)
              + (continuousMultilinearCurryFin1 ℝ E E
                  (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hAx hΦ₂ h2 s k)).curryLeft
                    (fundamentalSolution hAx hΦ₂ h2 s h))).comp
                  (fundamentalSolution hAx hΦ₂ h2 s))))‖
      ≤ (3 * (Real.exp ((K : ℝ) * (T - t₀)) ^ 4 * gronwallBound 0 (K : ℝ) 1 (T - t₀)
                * (2 * (M₂ : ℝ) * C' + 4 * (L : ℝ) * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
            + Real.exp ((K : ℝ) * (T - t₀)) ^ 4
                * (3 * C'' * (L : ℝ) * gronwallBound 0 (K : ℝ) 1 (T - t₀) + (M₃ : ℝ)))
          * ‖z - x₀‖ * ‖k‖ * ‖h‖ := by
  refine (norm_add4_sub_add4_le _ _ _ _ _ _ _ _).trans ?_
  have hT1 := norm_bilinearComp_VfamInner_baseCurve_sub_le hv hΦ h0 hDvlip hD2vlip z x₀ hAz hAx
    hC'0 hC'z hC'x hΦ₁ h1 hΦ₂ h2 k h hUzk hUzk0 hUxk hUxk0 hs
  have hT2 := norm_bilinearComp_VfamOuter_baseCurve_sub_le hv hΦ h0 hDvlip hD2vlip z x₀ hAz hAx
    hC'0 hC'z hC'x hΦ₁ h1 hΦ₂ h2 h k hUzk hUzk0 hUxk hUxk0 hs
  have hT3 := norm_bilinearComp_VfamOuter_baseCurve_sub_le hv hΦ h0 hDvlip hD2vlip z x₀ hAz hAx
    hC'0 hC'z hC'x hΦ₁ h1 hΦ₂ h2 k h hUzh hUzh0 hUxh hUxh0 hs
  have hT4 := norm_thirdDerivForcing_baseCurve_sub_le hv hΦ h0 hDvlip hD3vlip z x₀ hAz hAx
    hC''z hΦ₁ h1 hΦ₂ h2 k h hs
  refine (add_le_add (add_le_add (add_le_add hT1 hT2) hT3) hT4).trans_eq ?_
  ring

/-- **Base-point Lipschitz gap of the third-variation curve.**  The `C³`-continuity curve gap and the
direct one-order-up analogue of `norm_linearisedFirstVariation_baseCurve_sub_le`: for two base points
`z`, `x₀` with resolvents `W_z`, `W_x`, linearised first-variation curves `Uzk = Vfam^z k`,
`Uxk = Vfam^x k` (direction `k`) and `Uzh = Vfam^z h`, `Uxh = Vfam^x h` (direction `h`), and the
third-variation curves `Vz`, `Vx` solving the design-corrected third-variation ODE (coefficient
`Dv(Φ · s)`, four-term forcing) at `z`, `x₀`, the whole curve difference is `O(‖z − x₀‖·‖k‖·‖h‖)`
uniformly on `[t₀, T]`:
`‖Vz t − Vx t‖ ≤ Cλ · ‖z − x₀‖ · ‖k‖ · ‖h‖ · gronwallBound 0 K 1 (t − t₀)`
with `Cλ = L·exp⁴·g·(3C'²g + C'') + 3·exp⁴·g·(2M₂C' + 4LC'²g) + exp⁴·(3C''Lg + M₃)`,
`exp = exp(K(T−t₀))`, `g = gronwallBound 0 K 1 (T−t₀)`.

Proof: `norm_inhomogVariation_sub_le_of_gap` fed the coefficient gap `α = L·exp·‖z − x₀‖`
(`norm_derivField_apply_flow_sub_le`), the second-curve size `N = ‖Vx s‖`-bound
(`norm_thirdVariation_coeff_le` with the `Vfam^x` sizes `‖Uxk‖ ≤ C'exp²‖k‖g`, `‖Uxh‖ ≤ C'exp²‖h‖g` from
`norm_linearisedFirstVariation_le`), and the four-term forcing gap `β`
(`norm_thirdVariationForcing_baseCurve_sub_le`); the `(α·N + β)·gronwall` constant collapses to `Cλ` by
`ring`.  This is the size datum that `ContinuousLinearMap.opNorm_le_bound` (twice, over `k` then `h`)
turns into the Lipschitz continuity `‖D₃fam z − D₃fam x₀‖ ≤ Cλ·gronwall·‖z − x₀‖` of the third
fundamental solution — the sole remaining ingredient of the resolvent's spatial `ContDiff ℝ 3`. -/
theorem norm_thirdVariation_baseCurve_sub_le
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E}
    {L M₂ M₃ : ℝ≥0} {C' C'' : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hDvlip : ∀ s, LipschitzWith L (Dv s)) (hD2vlip : ∀ s, LipschitzWith M₂ (D2v s))
    (hD3vlip : ∀ s, LipschitzWith M₃ (D3v s))
    (z x₀ : E)
    (hAz : ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K) (hAx : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hC'0 : 0 ≤ C') (hC'z : ∀ s, ‖D2v s (Φ z s)‖ ≤ C') (hC'x : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ C')
    (hC''0 : 0 ≤ C'') (hC''z : ∀ s, ‖D3v s (Φ z s)‖ ≤ C'') (hC''x : ∀ s, ‖D3v s (Φ x₀ s)‖ ≤ C'')
    {Φ₁ Φ₂ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h1 : ∀ x, Φ₁ x t₀ = x)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h2 : ∀ x, Φ₂ x t₀ = x)
    (k h : E) {T : ℝ}
    {Uzk Uxk Uzh Uxh : ℝ → (E →L[ℝ] E)}
    (hUzk : ∀ s, HasDerivAt Uzk
      ((Dv s (Φ z s)).comp (Uzk s)
        + ((D2v s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h1 s) k).comp
            (fundamentalSolution hAz hΦ₁ h1 s)) s)
    (hUzk0 : Uzk t₀ = 0)
    (hUxk : ∀ s, HasDerivAt Uxk
      ((Dv s (Φ x₀ s)).comp (Uxk s)
        + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) k).comp
            (fundamentalSolution hAx hΦ₂ h2 s)) s)
    (hUxk0 : Uxk t₀ = 0)
    (hUzh : ∀ s, HasDerivAt Uzh
      ((Dv s (Φ z s)).comp (Uzh s)
        + ((D2v s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h1 s) h).comp
            (fundamentalSolution hAz hΦ₁ h1 s)) s)
    (hUzh0 : Uzh t₀ = 0)
    (hUxh : ∀ s, HasDerivAt Uxh
      ((Dv s (Φ x₀ s)).comp (Uxh s)
        + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) h).comp
            (fundamentalSolution hAx hΦ₂ h2 s)) s)
    (hUxh0 : Uxh t₀ = 0)
    {Vz Vx : ℝ → (E →L[ℝ] E)}
    (hVz : ∀ s, HasDerivAt Vz
      ((Dv s (Φ z s)).comp (Vz s)
        + (((D2v s (Φ z s)).comp (Uzk s) h).comp (fundamentalSolution hAz hΦ₁ h1 s)
           + (((D2v s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h1 s) h).comp (Uzk s)
              + (((D2v s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h1 s) k).comp (Uzh s)
                 + (continuousMultilinearCurryFin1 ℝ E E
                     (((D3v s (Φ z s)).curryLeft (fundamentalSolution hAz hΦ₁ h1 s k)).curryLeft
                       (fundamentalSolution hAz hΦ₁ h1 s h))).comp
                     (fundamentalSolution hAz hΦ₁ h1 s))))) s)
    (hVz0 : Vz t₀ = 0)
    (hVx : ∀ s, HasDerivAt Vx
      ((Dv s (Φ x₀ s)).comp (Vx s)
        + (((D2v s (Φ x₀ s)).comp (Uxk s) h).comp (fundamentalSolution hAx hΦ₂ h2 s)
           + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) h).comp (Uxk s)
              + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) k).comp (Uxh s)
                 + (continuousMultilinearCurryFin1 ℝ E E
                     (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hAx hΦ₂ h2 s k)).curryLeft
                       (fundamentalSolution hAx hΦ₂ h2 s h))).comp
                     (fundamentalSolution hAx hΦ₂ h2 s))))) s)
    (hVx0 : Vx t₀ = 0)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ‖Vz t - Vx t‖
      ≤ ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) ^ 4 * gronwallBound 0 (K : ℝ) 1 (T - t₀)
            * (3 * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀) + C'')
          + 3 * (Real.exp ((K : ℝ) * (T - t₀)) ^ 4 * gronwallBound 0 (K : ℝ) 1 (T - t₀)
              * (2 * (M₂ : ℝ) * C' + 4 * (L : ℝ) * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
          + Real.exp ((K : ℝ) * (T - t₀)) ^ 4
              * (3 * C'' * (L : ℝ) * gronwallBound 0 (K : ℝ) 1 (T - t₀) + (M₃ : ℝ)))
        * ‖z - x₀‖ * ‖k‖ * ‖h‖ * gronwallBound 0 (K : ℝ) 1 (t - t₀) := by
  have he0 : (0 : ℝ) ≤ Real.exp ((K : ℝ) * (T - t₀)) := (Real.exp_pos _).le
  have hg0 : (0 : ℝ) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
    gronwallBound_zero_one_nonneg K.coe_nonneg (sub_nonneg.mpr (le_trans ht.1 ht.2))
  have he2 : Real.exp (2 * (K : ℝ) * (T - t₀)) = Real.exp ((K : ℝ) * (T - t₀)) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have he3 : Real.exp (3 * (K : ℝ) * (T - t₀)) = Real.exp ((K : ℝ) * (T - t₀)) ^ 3 := by
    have hpow : Real.exp ((K : ℝ) * (T - t₀)) ^ 3
        = Real.exp ((K : ℝ) * (T - t₀))
          * (Real.exp ((K : ℝ) * (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀))) := by ring
    rw [hpow, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  -- coefficient gap `α`
  have hAgap : ∀ s ∈ Set.Icc t₀ T, ‖Dv s (Φ z s) - Dv s (Φ x₀ s)‖
      ≤ (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖ := by
    intro s hs
    have hsabs : |s - t₀| ≤ T - t₀ := by
      rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
    exact norm_derivField_apply_flow_sub_le hv hΦ h0 (hDvlip s) hsabs z x₀
  have hα : (0 : ℝ) ≤ (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) * ‖z - x₀‖ := by positivity
  -- `Vfam^x` sizes
  have hN₂ : ∀ s ∈ Set.Icc t₀ T, ‖Uxk s‖
      ≤ C' * Real.exp ((K : ℝ) * (T - t₀)) ^ 2 * ‖k‖ * gronwallBound 0 (K : ℝ) 1 (T - t₀) := by
    intro s hs
    have hle := norm_linearisedFirstVariation_le x₀ hAx hΦ₂ h2 hC'0 hC'x k hUxk hUxk0 hs
    rw [he2] at hle
    refine hle.trans ?_
    have hmono : gronwallBound 0 (K : ℝ) 1 (s - t₀) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
      gronwallBound_mono (le_refl (0 : ℝ)) zero_le_one K.coe_nonneg (by linarith [hs.2])
    exact mul_le_mul_of_nonneg_left hmono
      (mul_nonneg (mul_nonneg hC'0 (by positivity)) (norm_nonneg _))
  have hN₀ : ∀ s ∈ Set.Icc t₀ T, ‖Uxh s‖
      ≤ C' * Real.exp ((K : ℝ) * (T - t₀)) ^ 2 * ‖h‖ * gronwallBound 0 (K : ℝ) 1 (T - t₀) := by
    intro s hs
    have hle := norm_linearisedFirstVariation_le x₀ hAx hΦ₂ h2 hC'0 hC'x h hUxh hUxh0 hs
    rw [he2] at hle
    refine hle.trans ?_
    have hmono : gronwallBound 0 (K : ℝ) 1 (s - t₀) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
      gronwallBound_mono (le_refl (0 : ℝ)) zero_le_one K.coe_nonneg (by linarith [hs.2])
    exact mul_le_mul_of_nonneg_left hmono
      (mul_nonneg (mul_nonneg hC'0 (by positivity)) (norm_nonneg _))
  -- second-curve size `N`
  have hN₂0 : (0 : ℝ) ≤ C' * Real.exp ((K : ℝ) * (T - t₀)) ^ 2 * ‖k‖
      * gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC'0 (by positivity)) (norm_nonneg _)) hg0
  have hBIG0 : (0 : ℝ) ≤ 2 * C' * (C' * Real.exp ((K : ℝ) * (T - t₀)) ^ 2 * ‖k‖
          * gronwallBound 0 (K : ℝ) 1 (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖
        + C' * (C' * Real.exp ((K : ℝ) * (T - t₀)) ^ 2 * ‖h‖
            * gronwallBound 0 (K : ℝ) 1 (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀)) * ‖k‖
        + C'' * Real.exp ((K : ℝ) * (T - t₀)) ^ 3 * ‖k‖ * ‖h‖ := by
    have h1' : (0 : ℝ) ≤ 2 * C' * (C' * Real.exp ((K : ℝ) * (T - t₀)) ^ 2 * ‖k‖
          * gronwallBound 0 (K : ℝ) 1 (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖ :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hC'0) hN₂0) he0) (norm_nonneg _)
    have h2' : (0 : ℝ) ≤ C' * (C' * Real.exp ((K : ℝ) * (T - t₀)) ^ 2 * ‖h‖
            * gronwallBound 0 (K : ℝ) 1 (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀)) * ‖k‖ :=
      mul_nonneg (mul_nonneg (mul_nonneg hC'0
        (mul_nonneg (mul_nonneg (mul_nonneg hC'0 (by positivity)) (norm_nonneg _)) hg0)) he0)
        (norm_nonneg _)
    have h3' : (0 : ℝ) ≤ C'' * Real.exp ((K : ℝ) * (T - t₀)) ^ 3 * ‖k‖ * ‖h‖ :=
      mul_nonneg (mul_nonneg (mul_nonneg hC''0 (by positivity)) (norm_nonneg _)) (norm_nonneg _)
    exact add_nonneg (add_nonneg h1' h2') h3'
  have hV₂bound : ∀ s ∈ Set.Icc t₀ T, ‖Vx s‖
      ≤ (2 * C' * (C' * Real.exp ((K : ℝ) * (T - t₀)) ^ 2 * ‖k‖
              * gronwallBound 0 (K : ℝ) 1 (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀)) * ‖h‖
            + C' * (C' * Real.exp ((K : ℝ) * (T - t₀)) ^ 2 * ‖h‖
                * gronwallBound 0 (K : ℝ) 1 (T - t₀)) * Real.exp ((K : ℝ) * (T - t₀)) * ‖k‖
            + C'' * Real.exp ((K : ℝ) * (T - t₀)) ^ 3 * ‖k‖ * ‖h‖)
          * gronwallBound 0 (K : ℝ) 1 (T - t₀) := by
    intro s hs
    have hVx_C : ∀ s', HasDerivAt Vx
        ((Dv s' (Φ x₀ s')).comp (Vx s')
          + (((D2v s' (Φ x₀ s')).comp (Uxk s') h).comp (fundamentalSolution hAx hΦ₂ h2 s')
             + ((D2v s' (Φ x₀ s')).comp (fundamentalSolution hAx hΦ₂ h2 s') h).comp (Uxk s')
             + (((D2v s' (Φ x₀ s')).comp (fundamentalSolution hAx hΦ₂ h2 s') k).comp (Uxh s')
                + (continuousMultilinearCurryFin1 ℝ E E
                    (((D3v s' (Φ x₀ s')).curryLeft (fundamentalSolution hAx hΦ₂ h2 s' k)).curryLeft
                      (fundamentalSolution hAx hΦ₂ h2 s' h))).comp
                    (fundamentalSolution hAx hΦ₂ h2 s')))) s' := by
      intro s'
      convert hVx s' using 2
      abel
    have hb := norm_thirdVariation_coeff_le x₀ hAx hΦ₂ h2 hC'0 hC''0 hN₂0 hC'x hC''x hN₂ hN₀
      k h hVx_C hVx0 hs
    rw [he3] at hb
    refine hb.trans ?_
    have hmono : gronwallBound 0 (K : ℝ) 1 (s - t₀) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
      gronwallBound_mono (le_refl (0 : ℝ)) zero_le_one K.coe_nonneg (by linarith [hs.2])
    exact mul_le_mul_of_nonneg_left hmono hBIG0
  -- forcing gap `β`
  have hFgap : ∀ s ∈ Set.Icc t₀ T,
      ‖(((D2v s (Φ z s)).comp (Uzk s) h).comp (fundamentalSolution hAz hΦ₁ h1 s)
          + (((D2v s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h1 s) h).comp (Uzk s)
             + (((D2v s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h1 s) k).comp (Uzh s)
                + (continuousMultilinearCurryFin1 ℝ E E
                    (((D3v s (Φ z s)).curryLeft (fundamentalSolution hAz hΦ₁ h1 s k)).curryLeft
                      (fundamentalSolution hAz hΦ₁ h1 s h))).comp
                    (fundamentalSolution hAz hΦ₁ h1 s))))
        - (((D2v s (Φ x₀ s)).comp (Uxk s) h).comp (fundamentalSolution hAx hΦ₂ h2 s)
          + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) h).comp (Uxk s)
             + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) k).comp (Uxh s)
                + (continuousMultilinearCurryFin1 ℝ E E
                    (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hAx hΦ₂ h2 s k)).curryLeft
                      (fundamentalSolution hAx hΦ₂ h2 s h))).comp
                    (fundamentalSolution hAx hΦ₂ h2 s))))‖
      ≤ (3 * (Real.exp ((K : ℝ) * (T - t₀)) ^ 4 * gronwallBound 0 (K : ℝ) 1 (T - t₀)
                * (2 * (M₂ : ℝ) * C' + 4 * (L : ℝ) * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
            + Real.exp ((K : ℝ) * (T - t₀)) ^ 4
                * (3 * C'' * (L : ℝ) * gronwallBound 0 (K : ℝ) 1 (T - t₀) + (M₃ : ℝ)))
          * ‖z - x₀‖ * ‖k‖ * ‖h‖ := by
    intro s hs
    exact norm_thirdVariationForcing_baseCurve_sub_le hv hΦ h0 hDvlip hD2vlip hD3vlip z x₀
      hAz hAx hC'0 hC'z hC'x hC''z hΦ₁ h1 hΦ₂ h2 k h hUzk hUzk0 hUxk hUxk0 hUzh hUzh0 hUxh hUxh0 hs
  refine (norm_inhomogVariation_sub_le_of_gap hAz hVz hVz0 hVx hVx0 hAgap hV₂bound hFgap hα
    ht).trans_eq ?_
  ring

/-- **Per-direction operator-norm base-point gap of the packaged third fundamental solution `D₃`.**
The `C³` analogue of the `hkey` operator-difference bound buried in
`exists_flow_contDiff_two_of_lipschitz_secondDeriv` (there for the *second* fundamental solution
`D₂`), extracted as a standalone reusable lemma — the operator-level companion of the third-variation
curve base gap `norm_thirdVariation_baseCurve_sub_le`.

For two base points `z, x₀`, the packaged design-corrected third-variation operators `D₃z, D₃x`
(each characterised bilinearly through its canonical linearised-first-variation family `Vfamz`,
`Vfamx` by `hD₃z`, `hD₃x`, i.e. the `hD₃bilinear` slot of `exists_thirdVariationOperator_of_field`)
obey the per-direction (in the outer base direction `k`) base-point Lipschitz bound

`‖D₃z k − D₃x k‖ ≤ Cλ · gronwallBound 0 K 1 (t − t₀) · ‖z − x₀‖ · ‖k‖`,

with the *same* neighbourhood-uniform constant `Cλ` as `norm_thirdVariation_baseCurve_sub_le`
(the `L·exp⁴·g·(3C'²g + C'') + 3·exp⁴·g·(2M₂C' + 4LC'²g) + exp⁴·(3C''Lg + M₃)` tower).

The bound is stated per outer direction `k` (with the *double* continuous-linear-map norm
`‖D₃z k − D₃x k‖`, `D₃z k : E →L (E →L E)`) rather than on the full triple operator `‖D₃z − D₃x‖`
because the `Norm`/`NormedSpace` instance on `E →L E →L E →L E` does not synthesize in Mathlib
v4.29.1 (the endomorphism-ring/module diamond blocks `NormedSpace ℝ (E →L E →L E)`); the
per-`k` form carries exactly the same continuity content one norm level below.

Proof: `ContinuousLinearMap.opNorm_le_bound` (over the inner direction `h`) reduces the double-operator
gap to the scalar time-`t` value gap `‖D₃z k h − D₃x k h‖`.  For each `h`,
`exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv_coeff` (fed the two canonical family
curves `Vfamz k`, `Vfamz h` / `Vfamx k`, `Vfamx h`) builds the two third-variation curves `Vz`, `Vx`;
the bilinear characterisations `hD₃z`, `hD₃x` identify `D₃z k h = Vz t`, `D₃x k h = Vx t`; and
`norm_thirdVariation_baseCurve_sub_le` bounds `‖Vz t − Vx t‖`.  This is the operator-continuity datum
feeding `Continuous D₃fam` toward the resolvent's spatial `ContDiff ℝ 3`. -/
theorem norm_thirdFundamentalSolution_apply_baseCurve_sub_le [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E}
    {L M₂ M₃ : ℝ≥0} {C' C'' : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hDvlip : ∀ s, LipschitzWith L (Dv s)) (hD2vlip : ∀ s, LipschitzWith M₂ (D2v s))
    (hD3vlip : ∀ s, LipschitzWith M₃ (D3v s))
    (z x₀ : E)
    (hAz : ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K) (hAx : ∀ s, ‖Dv s (Φ x₀ s)‖₊ ≤ K)
    (hAcontz : Continuous (fun s => Dv s (Φ z s)))
    (hAcontx : Continuous (fun s => Dv s (Φ x₀ s)))
    (hD2contz : Continuous (fun s => D2v s (Φ z s)))
    (hD2contx : Continuous (fun s => D2v s (Φ x₀ s)))
    (hD3contz : Continuous (fun s => D3v s (Φ z s)))
    (hD3contx : Continuous (fun s => D3v s (Φ x₀ s)))
    (hC'0 : 0 ≤ C') (hC'z : ∀ s, ‖D2v s (Φ z s)‖ ≤ C') (hC'x : ∀ s, ‖D2v s (Φ x₀ s)‖ ≤ C')
    (hC''0 : 0 ≤ C'') (hC''z : ∀ s, ‖D3v s (Φ z s)‖ ≤ C'') (hC''x : ∀ s, ‖D3v s (Φ x₀ s)‖ ≤ C'')
    {Φ₁ Φ₂ : E → ℝ → E}
    (hΦ₁ : ∀ x, IsIntegralCurve (Φ₁ x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h1 : ∀ x, Φ₁ x t₀ = x)
    (hΦ₂ : ∀ x, IsIntegralCurve (Φ₂ x) (variationalFieldVec (fun s => Dv s (Φ x₀ s))))
    (h2 : ∀ x, Φ₂ x t₀ = x)
    {T : ℝ} {t : ℝ}
    {Vfamz Vfamx : E → (ℝ → (E →L[ℝ] E))}
    {D₃z D₃x : E →L[ℝ] (E →L[ℝ] (E →L[ℝ] E))}
    (hVfamz0 : ∀ h, Vfamz h t₀ = 0)
    (hVfamzd : ∀ (h : E) (s : ℝ), HasDerivAt (Vfamz h)
      ((Dv s (Φ z s)).comp (Vfamz h s)
        + ((D2v s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h1 s) h).comp
            (fundamentalSolution hAz hΦ₁ h1 s)) s)
    (hVfamzc : ∀ h, Continuous (Vfamz h))
    (hD₃z : ∀ (k h : E) (V : ℝ → (E →L[ℝ] E)), V t₀ = 0 →
      (∀ s, HasDerivAt V
        ((Dv s (Φ z s)).comp (V s)
          + (((D2v s (Φ z s)).comp (Vfamz k s) h).comp (fundamentalSolution hAz hΦ₁ h1 s)
             + ((D2v s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h1 s) h).comp (Vfamz k s)
             + (((D2v s (Φ z s)).comp (fundamentalSolution hAz hΦ₁ h1 s) k).comp (Vfamz h s)
                + (continuousMultilinearCurryFin1 ℝ E E
                    (((D3v s (Φ z s)).curryLeft (fundamentalSolution hAz hΦ₁ h1 s k)).curryLeft
                      (fundamentalSolution hAz hΦ₁ h1 s h))).comp
                    (fundamentalSolution hAz hΦ₁ h1 s)))) s) →
      D₃z k h = V t)
    (hVfamx0 : ∀ h, Vfamx h t₀ = 0)
    (hVfamxd : ∀ (h : E) (s : ℝ), HasDerivAt (Vfamx h)
      ((Dv s (Φ x₀ s)).comp (Vfamx h s)
        + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) h).comp
            (fundamentalSolution hAx hΦ₂ h2 s)) s)
    (hVfamxc : ∀ h, Continuous (Vfamx h))
    (hD₃x : ∀ (k h : E) (V : ℝ → (E →L[ℝ] E)), V t₀ = 0 →
      (∀ s, HasDerivAt V
        ((Dv s (Φ x₀ s)).comp (V s)
          + (((D2v s (Φ x₀ s)).comp (Vfamx k s) h).comp (fundamentalSolution hAx hΦ₂ h2 s)
             + ((D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) h).comp (Vfamx k s)
             + (((D2v s (Φ x₀ s)).comp (fundamentalSolution hAx hΦ₂ h2 s) k).comp (Vfamx h s)
                + (continuousMultilinearCurryFin1 ℝ E E
                    (((D3v s (Φ x₀ s)).curryLeft (fundamentalSolution hAx hΦ₂ h2 s k)).curryLeft
                      (fundamentalSolution hAx hΦ₂ h2 s h))).comp
                    (fundamentalSolution hAx hΦ₂ h2 s)))) s) →
      D₃x k h = V t)
    (ht : t ∈ Set.Icc t₀ T) (k : E) :
    ‖D₃z k - D₃x k‖
      ≤ ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) ^ 4 * gronwallBound 0 (K : ℝ) 1 (T - t₀)
            * (3 * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀) + C'')
          + 3 * (Real.exp ((K : ℝ) * (T - t₀)) ^ 4 * gronwallBound 0 (K : ℝ) 1 (T - t₀)
              * (2 * (M₂ : ℝ) * C' + 4 * (L : ℝ) * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
          + Real.exp ((K : ℝ) * (T - t₀)) ^ 4
              * (3 * C'' * (L : ℝ) * gronwallBound 0 (K : ℝ) 1 (T - t₀) + (M₃ : ℝ)))
        * gronwallBound 0 (K : ℝ) 1 (t - t₀) * ‖z - x₀‖ * ‖k‖ := by
  have he4 : (0 : ℝ) ≤ Real.exp ((K : ℝ) * (T - t₀)) ^ 4 := by positivity
  have hg0 : (0 : ℝ) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
    gronwallBound_zero_one_nonneg K.coe_nonneg (sub_nonneg.mpr (le_trans ht.1 ht.2))
  have hgt0 : (0 : ℝ) ≤ gronwallBound 0 (K : ℝ) 1 (t - t₀) :=
    gronwallBound_zero_one_nonneg K.coe_nonneg (sub_nonneg.mpr ht.1)
  have hL := L.coe_nonneg
  have hM₂ := M₂.coe_nonneg
  have hM₃ := M₃.coe_nonneg
  have hCbig0 : (0 : ℝ) ≤
      ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) ^ 4 * gronwallBound 0 (K : ℝ) 1 (T - t₀)
            * (3 * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀) + C'')
          + 3 * (Real.exp ((K : ℝ) * (T - t₀)) ^ 4 * gronwallBound 0 (K : ℝ) 1 (T - t₀)
              * (2 * (M₂ : ℝ) * C' + 4 * (L : ℝ) * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
          + Real.exp ((K : ℝ) * (T - t₀)) ^ 4
              * (3 * C'' * (L : ℝ) * gronwallBound 0 (K : ℝ) 1 (T - t₀) + (M₃ : ℝ))) := by
    have hA : (0 : ℝ) ≤ (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) ^ 4
        * gronwallBound 0 (K : ℝ) 1 (T - t₀)
        * (3 * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀) + C'') :=
      mul_nonneg (mul_nonneg (mul_nonneg hL he4) hg0)
        (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg C')) hg0) hC''0)
    have hB : (0 : ℝ) ≤ 3 * (Real.exp ((K : ℝ) * (T - t₀)) ^ 4
        * gronwallBound 0 (K : ℝ) 1 (T - t₀)
        * (2 * (M₂ : ℝ) * C' + 4 * (L : ℝ) * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀))) :=
      mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg he4 hg0)
        (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM₂) hC'0)
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) (sq_nonneg C')) hg0)))
    have hC : (0 : ℝ) ≤ Real.exp ((K : ℝ) * (T - t₀)) ^ 4
        * (3 * C'' * (L : ℝ) * gronwallBound 0 (K : ℝ) 1 (T - t₀) + (M₃ : ℝ)) :=
      mul_nonneg he4 (add_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC''0) hL) hg0) hM₃)
    linarith
  have hkbound : (0 : ℝ) ≤
      ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) ^ 4 * gronwallBound 0 (K : ℝ) 1 (T - t₀)
            * (3 * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀) + C'')
          + 3 * (Real.exp ((K : ℝ) * (T - t₀)) ^ 4 * gronwallBound 0 (K : ℝ) 1 (T - t₀)
              * (2 * (M₂ : ℝ) * C' + 4 * (L : ℝ) * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
          + Real.exp ((K : ℝ) * (T - t₀)) ^ 4
              * (3 * C'' * (L : ℝ) * gronwallBound 0 (K : ℝ) 1 (T - t₀) + (M₃ : ℝ)))
        * gronwallBound 0 (K : ℝ) 1 (t - t₀) * ‖z - x₀‖ * ‖k‖ :=
    mul_nonneg (mul_nonneg (mul_nonneg hCbig0 hgt0) (norm_nonneg _)) (norm_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _ hkbound (fun h => ?_)
  rw [ContinuousLinearMap.sub_apply]
  obtain ⟨Vz, hVz0, hVz⟩ := exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv_coeff
    z hAz hAcontz hD2contz hD3contz hΦ₁ h1 (hVfamzc k) (hVfamzc h) k h
  obtain ⟨Vx, hVx0, hVx⟩ := exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv_coeff
    x₀ hAx hAcontx hD2contx hD3contx hΦ₂ h2 (hVfamxc k) (hVfamxc h) k h
  rw [hD₃z k h Vz hVz0 hVz, hD₃x k h Vx hVx0 hVx]
  refine (norm_thirdVariation_baseCurve_sub_le hv hΦ h0 hDvlip hD2vlip hD3vlip z x₀
    hAz hAx hC'0 hC'z hC'x hC''0 hC''z hC''x hΦ₁ h1 hΦ₂ h2 k h
    (hVfamzd k) (hVfamz0 k) (hVfamxd k) (hVfamx0 k) (hVfamzd h) (hVfamz0 h) (hVfamxd h) (hVfamx0 h)
    ?hz hVz0 ?hx hVx0 ht).trans_eq ?heq
  case hz => intro s; convert hVz s using 2; abel
  case hx => intro s; convert hVx s using 2; abel
  case heq => ring

/-- **Per-direction Lipschitz continuity of the packaged third fundamental solution family.**  For
the packaged design-corrected third-variation operator family `D₃fam : E → (E →L E →L E →L E)` (with
its canonical linearised-first-variation family `Vfamfam` and bilinear characterisation `hD₃famchar`,
as produced base-point-by-base-point by `exists_thirdVariationOperator_of_field`), the map
`z ↦ D₃fam z k` — for each fixed outer direction `k`, valued in the *double* continuous-linear-map
space `E →L E →L E` — is Lipschitz with constant `Cλ · gronwallBound 0 K 1 (t − t₀) · ‖k‖`.

This is the genuine continuity content of the third fundamental solution that survives the Mathlib
v4.29.1 obstruction on the triple operator norm (`Norm`/`NormedSpace ℝ (E →L E →L E)` do not
synthesize — the endomorphism-ring/module diamond): although `Continuous D₃fam` cannot be phrased
through the triple operator norm, its per-direction slices `z ↦ D₃fam z k` land in the well-normed
double space and are honestly Lipschitz — i.e. `D₃fam` is continuous in the strong operator topology,
direction by direction.

Proof: `LipschitzWith.of_dist_le_mul`; the base-point gap
`norm_thirdFundamentalSolution_apply_baseCurve_sub_le` (fed `Vfamfam z`, `Vfamfam x₀` and the two
bilinear characterisations) supplies exactly `‖D₃fam z k − D₃fam x₀ k‖ ≤ Cλ·g·‖z − x₀‖·‖k‖`, and a
`ring` reassociation matches the Lipschitz constant `Cλ·g·‖k‖`. -/
theorem lipschitzWith_thirdFundamentalSolution_apply [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E}
    {L M₂ M₃ : ℝ≥0} {C' C'' : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hDvlip : ∀ s, LipschitzWith L (Dv s)) (hD2vlip : ∀ s, LipschitzWith M₂ (D2v s))
    (hD3vlip : ∀ s, LipschitzWith M₃ (D3v s))
    (hAfun : ∀ z, ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K)
    (hAcontfun : ∀ z, Continuous (fun s => Dv s (Φ z s)))
    (hD2contfun : ∀ z, Continuous (fun s => D2v s (Φ z s)))
    (hD3contfun : ∀ z, Continuous (fun s => D3v s (Φ z s)))
    (hC'0 : 0 ≤ C') (hC'fun : ∀ z, ∀ s, ‖D2v s (Φ z s)‖ ≤ C')
    (hC''0 : 0 ≤ C'') (hC''fun : ∀ z, ∀ s, ‖D3v s (Φ z s)‖ ≤ C'')
    {Ψ : E → E → ℝ → E}
    (hΨ : ∀ z, ∀ x, IsIntegralCurve (Ψ z x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h0Ψ : ∀ z, ∀ x, Ψ z x t₀ = x)
    {T : ℝ} {t : ℝ}
    {Vfamfam : E → E → (ℝ → (E →L[ℝ] E))}
    {D₃fam : E → (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] E)))}
    (hVfamfam0 : ∀ z, ∀ h, Vfamfam z h t₀ = 0)
    (hVfamfamd : ∀ z, ∀ (h : E) (s : ℝ), HasDerivAt (Vfamfam z h)
      ((Dv s (Φ z s)).comp (Vfamfam z h s)
        + ((D2v s (Φ z s)).comp (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s) h).comp
            (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s)) s)
    (hVfamfamc : ∀ z, ∀ h, Continuous (Vfamfam z h))
    (hD₃famchar : ∀ z, ∀ (k h : E) (V : ℝ → (E →L[ℝ] E)), V t₀ = 0 →
      (∀ s, HasDerivAt V
        ((Dv s (Φ z s)).comp (V s)
          + (((D2v s (Φ z s)).comp (Vfamfam z k s) h).comp
                (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s)
             + ((D2v s (Φ z s)).comp (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s) h).comp
                 (Vfamfam z k s)
             + (((D2v s (Φ z s)).comp (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s) k).comp
                   (Vfamfam z h s)
                + (continuousMultilinearCurryFin1 ℝ E E
                    (((D3v s (Φ z s)).curryLeft
                          (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s k)).curryLeft
                      (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s h))).comp
                    (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s)))) s) →
      D₃fam z k h = V t)
    (ht : t ∈ Set.Icc t₀ T) (k : E) :
    LipschitzWith
      (((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) ^ 4 * gronwallBound 0 (K : ℝ) 1 (T - t₀)
            * (3 * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀) + C'')
          + 3 * (Real.exp ((K : ℝ) * (T - t₀)) ^ 4 * gronwallBound 0 (K : ℝ) 1 (T - t₀)
              * (2 * (M₂ : ℝ) * C' + 4 * (L : ℝ) * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
          + Real.exp ((K : ℝ) * (T - t₀)) ^ 4
              * (3 * C'' * (L : ℝ) * gronwallBound 0 (K : ℝ) 1 (T - t₀) + (M₃ : ℝ)))
        * gronwallBound 0 (K : ℝ) 1 (t - t₀) * ‖k‖).toNNReal
      (fun z => D₃fam z k) := by
  have he4 : (0 : ℝ) ≤ Real.exp ((K : ℝ) * (T - t₀)) ^ 4 := by positivity
  have hg0 : (0 : ℝ) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
    gronwallBound_zero_one_nonneg K.coe_nonneg (sub_nonneg.mpr (le_trans ht.1 ht.2))
  have hgt0 : (0 : ℝ) ≤ gronwallBound 0 (K : ℝ) 1 (t - t₀) :=
    gronwallBound_zero_one_nonneg K.coe_nonneg (sub_nonneg.mpr ht.1)
  have hL := L.coe_nonneg
  have hM₂ := M₂.coe_nonneg
  have hM₃ := M₃.coe_nonneg
  have hCbig0 : (0 : ℝ) ≤
      ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) ^ 4 * gronwallBound 0 (K : ℝ) 1 (T - t₀)
            * (3 * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀) + C'')
          + 3 * (Real.exp ((K : ℝ) * (T - t₀)) ^ 4 * gronwallBound 0 (K : ℝ) 1 (T - t₀)
              * (2 * (M₂ : ℝ) * C' + 4 * (L : ℝ) * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
          + Real.exp ((K : ℝ) * (T - t₀)) ^ 4
              * (3 * C'' * (L : ℝ) * gronwallBound 0 (K : ℝ) 1 (T - t₀) + (M₃ : ℝ))) := by
    have hA : (0 : ℝ) ≤ (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) ^ 4
        * gronwallBound 0 (K : ℝ) 1 (T - t₀)
        * (3 * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀) + C'') :=
      mul_nonneg (mul_nonneg (mul_nonneg hL he4) hg0)
        (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg C')) hg0) hC''0)
    have hB : (0 : ℝ) ≤ 3 * (Real.exp ((K : ℝ) * (T - t₀)) ^ 4
        * gronwallBound 0 (K : ℝ) 1 (T - t₀)
        * (2 * (M₂ : ℝ) * C' + 4 * (L : ℝ) * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀))) :=
      mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg he4 hg0)
        (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM₂) hC'0)
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) (sq_nonneg C')) hg0)))
    have hC : (0 : ℝ) ≤ Real.exp ((K : ℝ) * (T - t₀)) ^ 4
        * (3 * C'' * (L : ℝ) * gronwallBound 0 (K : ℝ) 1 (T - t₀) + (M₃ : ℝ)) :=
      mul_nonneg he4 (add_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC''0) hL) hg0) hM₃)
    linarith
  have hCg0 : (0 : ℝ) ≤
      ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) ^ 4 * gronwallBound 0 (K : ℝ) 1 (T - t₀)
            * (3 * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀) + C'')
          + 3 * (Real.exp ((K : ℝ) * (T - t₀)) ^ 4 * gronwallBound 0 (K : ℝ) 1 (T - t₀)
              * (2 * (M₂ : ℝ) * C' + 4 * (L : ℝ) * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
          + Real.exp ((K : ℝ) * (T - t₀)) ^ 4
              * (3 * C'' * (L : ℝ) * gronwallBound 0 (K : ℝ) 1 (T - t₀) + (M₃ : ℝ)))
        * gronwallBound 0 (K : ℝ) 1 (t - t₀) * ‖k‖ :=
    mul_nonneg (mul_nonneg hCbig0 hgt0) (norm_nonneg _)
  refine LipschitzWith.of_dist_le_mul (fun z x₀ => ?_)
  rw [Real.coe_toNNReal _ hCg0, dist_eq_norm, dist_eq_norm]
  refine (norm_thirdFundamentalSolution_apply_baseCurve_sub_le hv hΦ h0 hDvlip hD2vlip hD3vlip
    z x₀ (hAfun z) (hAfun x₀) (hAcontfun z) (hAcontfun x₀) (hD2contfun z) (hD2contfun x₀)
    (hD3contfun z) (hD3contfun x₀) hC'0 (hC'fun z) (hC'fun x₀) hC''0 (hC''fun z) (hC''fun x₀)
    (hΨ z) (h0Ψ z) (hΨ x₀) (h0Ψ x₀)
    (hVfamfam0 z) (hVfamfamd z) (hVfamfamc z) (hD₃famchar z)
    (hVfamfam0 x₀) (hVfamfamd x₀) (hVfamfamc x₀) (hD₃famchar x₀) ht k).trans_eq ?_
  ring

/-- **Multilinear packaging of a double continuous-linear map.**  Sends `T : E →L (E →L E)` to the
`Fin 2` continuous multilinear map `w ↦ T (w 0) (w 1)`.  This is a genuine *bounded* operation
(a continuous linear map) because the inner space `E →L E` carries an operator norm; it is the
inverse of `curry2` at the operator level.  The point of routing through this map is that it lets us
climb one currying level without ever asking for a norm on a nested continuous-linear-map space that
Mathlib v4.29.1 cannot provide. -/
noncomputable def uncurry2CLM :
    (E →L[ℝ] E →L[ℝ] E) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E :=
  ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) E).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (ContinuousLinearMap.compL ℝ E (E →L[ℝ] E) (ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) E)
      (continuousMultilinearCurryFin1 ℝ E E).symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Pointwise evaluation of `uncurry2CLM`: `uncurry2CLM T w = T (w 0) (w 1)`. -/
theorem uncurry2CLM_apply (T : E →L[ℝ] E →L[ℝ] E) (w : Fin 2 → E) :
    uncurry2CLM T w = T (w 0) (w 1) := by
  simp only [uncurry2CLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    continuousMultilinearCurryLeftEquiv_symm_apply, continuousMultilinearCurryFin1_symm_apply]
  rfl

/-- **`uncurry2CLM` is a left inverse of `curry2`.**  `uncurry2CLM (curry2 M) = M`.  Together with
`curry2_uncurry2CLM` this exhibits the multilinear packaging `uncurry2CLM` and the composition-form
representation `curry2` as mutually inverse isometries between the `Fin 2` multilinear space and the
double continuous-linear-map space `E →L E →L E`.  This is what converts the existing
`curry2 (iteratedFDeriv ℝ 2 f) = D₂` identifications into the multilinear form
`iteratedFDeriv ℝ 2 f = uncurry2CLM (D₂)` needed to feed the `iteratedFDeriv ℝ 3` chain. -/
theorem uncurry2CLM_curry2 (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E) :
    uncurry2CLM (curry2 M) = M := by
  ext w
  rw [uncurry2CLM_apply, curry2_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- **`uncurry2CLM` is a right inverse of `curry2`.**  `curry2 (uncurry2CLM T) = T`. -/
theorem curry2_uncurry2CLM (T : E →L[ℝ] E →L[ℝ] E) :
    curry2 (uncurry2CLM T) = T := by
  ext a b
  rw [curry2_apply, uncurry2CLM_apply]
  simp

/-- **Second iterated derivative as a multilinear packaging.**  If `f` is everywhere differentiable
with derivative `Df`, and the first derivative `Df` is Fréchet differentiable at `x` with derivative
`D2 : E →L E →L E`, then the (multilinear) second iterated derivative equals the multilinear
packaging of `D2`: `iteratedFDeriv ℝ 2 f x = uncurry2CLM D2`.  The `C²`-side companion of
`iteratedFDeriv_three_eq_uncurry3_of_hasFDerivAt`, obtained from the composition-form identification
`curry2_iteratedFDeriv_two_eq_of_hasFDerivAt` by the inverse relation `uncurry2CLM_curry2`.  This is
the pointwise datum that (differentiated once more, through the continuous linear `uncurry2CLM`)
supplies the `HasFDerivAt (iteratedFDeriv ℝ 2 f) (uncurry2CLM.comp (D₃fam x)) x` hypothesis of
`iteratedFDeriv_three_eq_uncurry3_of_hasFDerivAt`. -/
theorem iteratedFDeriv_two_eq_uncurry2CLM_of_hasFDerivAt
    {f : E → E} {Df : E → (E →L[ℝ] E)} {D2 : E →L[ℝ] (E →L[ℝ] E)} {x : E}
    (hDf : ∀ y, HasFDerivAt f (Df y) y) (hD2 : HasFDerivAt Df D2 x) :
    iteratedFDeriv ℝ 2 f x = uncurry2CLM D2 := by
  rw [← uncurry2CLM_curry2 (iteratedFDeriv ℝ 2 f x),
    curry2_iteratedFDeriv_two_eq_of_hasFDerivAt hDf hD2]

/-- **Multilinear packaging of a triple continuous-linear map.**  Sends the nested triple operator
`T : E →L E →L E →L E` to the *properly normed* `Fin 3` continuous multilinear map
`v ↦ T (v 0) (v 1) (v 2)` in `ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E`.

This is the key object that sidesteps the Mathlib v4.29.1 obstruction on the third fundamental
solution.  The triple continuous-linear-map space `E →L E →L E →L E` carries **no** operator norm
(`Norm`/`SeminormedAddCommGroup (E →L E →L E →L E)` fail to synthesize — the endomorphism-ring/module
diamond), so a difference `‖D₃fam z − D₃fam x₀‖` cannot even be *stated* through the nested tower.
The multilinear target `ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E` **does** carry a genuine
operator norm at every order, and `uncurry3` is built entirely through normed intermediaries (the
inner double space `E →L E →L E` is normed, so `uncurry2CLM` is a bounded operation, and one further
left-uncurrying lands in the normed multilinear space) — never touching the un-normed triple space as
a normed space.  So `‖uncurry3 (D₃fam z) − uncurry3 (D₃fam x₀)‖` *is* well-formed, and continuity of
the third fundamental solution can be phrased and proved there. -/
noncomputable def uncurry3 (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => E) E).symm (uncurry2CLM.comp T)

/-- Pointwise evaluation of `uncurry3`: `uncurry3 T v = T (v 0) (v 1) (v 2)`.  This is the defining
property that lets the trilinear operator gaps of `D₃fam` be read off slot by slot. -/
theorem uncurry3_apply (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) (v : Fin 3 → E) :
    uncurry3 T v = T (v 0) (v 1) (v 2) := by
  rw [uncurry3, continuousMultilinearCurryLeftEquiv_symm_apply,
    ContinuousLinearMap.comp_apply, uncurry2CLM_apply]
  rfl

/-- **Left-curry of the multilinear packaging.**  `(uncurry3 T).curryLeft = uncurry2CLM.comp T`.  The
multilinear-side companion of `curryLeft_iteratedFDeriv_three`: it exhibits the composition-form
operator `uncurry2CLM ∘ T` as the left-curry of the multilinear packaging `uncurry3 T`, which is the
shape the `iteratedFDeriv ℝ 3` chain consumes.  Immediate from `uncurry3` being the equiv-inverse
image of `uncurry2CLM.comp T` under `continuousMultilinearCurryLeftEquiv`. -/
theorem uncurry3_curryLeft (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E) :
    (uncurry3 T).curryLeft = uncurry2CLM.comp T := by
  rw [uncurry3]
  exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => E) E).apply_symm_apply _

/-- **Third iterated derivative as a multilinear packaging.**  If the (multilinear) second iterated
derivative `iteratedFDeriv ℝ 2 f` is Fréchet differentiable at `x` with derivative the composition-form
operator `uncurry2CLM ∘ T` (for some triple operator `T : E →L E →L E →L E`), then the third iterated
derivative equals the multilinear packaging of `T`: `iteratedFDeriv ℝ 3 f x = uncurry3 T`.

This is the bridge that transports abstract third-fundamental-solution data `T` (e.g. `D₃fam x`) onto
the canonical `iteratedFDeriv ℝ 3` object *in the properly normed multilinear space*, where the
multilinear Lipschitz continuity `lipschitzWith_thirdFundamentalSolution_multilinear` lives.  Proof:
`curryLeft_iteratedFDeriv_three_eq_of_hasFDerivAt` identifies `uncurry2CLM ∘ T` with
`(iteratedFDeriv ℝ 3 f x).curryLeft`, `uncurry3_curryLeft` identifies it with `(uncurry3 T).curryLeft`,
and `curryLeft` (the coercion of `continuousMultilinearCurryLeftEquiv`) is injective. -/
theorem iteratedFDeriv_three_eq_uncurry3_of_hasFDerivAt
    {f : E → E} {T : E →L[ℝ] E →L[ℝ] E →L[ℝ] E} {x : E}
    (hD3 : HasFDerivAt (iteratedFDeriv ℝ 2 f) (uncurry2CLM.comp T) x) :
    iteratedFDeriv ℝ 3 f x = uncurry3 T := by
  have h1 : uncurry2CLM.comp T = (iteratedFDeriv ℝ 3 f x).curryLeft :=
    curryLeft_iteratedFDeriv_three_eq_of_hasFDerivAt hD3
  have h2 : (uncurry3 T).curryLeft = (iteratedFDeriv ℝ 3 f x).curryLeft := by
    rw [uncurry3_curryLeft, h1]
  exact ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => E) E).injective h2).symm

/-- **Abstract multilinear Lipschitz criterion.**  A per-outer-direction operator-gap bound
`‖F x k − F y k‖ ≤ C · dist x y · ‖k‖` (valued in the well-normed *double* space `E →L E →L E`)
promotes to genuine `LipschitzWith C.toNNReal` continuity of the `Fin 3` multilinear packaging
`x ↦ uncurry3 (F x)`, valued in the *properly normed* multilinear space.  Proof:
`ContinuousMultilinearMap.opNorm_le_bound` reduces the multilinear operator norm of the difference to
the per-slot bound, which follows by two `le_opNorm` steps (in the normed double space) and the
hypothesis at the outer slot.  This is the abstract engine that converts the per-direction third
fundamental solution gap into `Continuous`/`LipschitzWith` continuity of the third derivative, in a
space that the `contDiff_succ`/`iteratedFDeriv` chain can consume. -/
theorem lipschitzWith_uncurry3_of_apply_sub_le {X : Type*} [PseudoMetricSpace X]
    {F : X → (E →L[ℝ] E →L[ℝ] E →L[ℝ] E)} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x y : X, ∀ k : E, ‖F x k - F y k‖ ≤ C * dist x y * ‖k‖) :
    LipschitzWith C.toNNReal (fun x => uncurry3 (F x)) := by
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  rw [Real.coe_toNNReal C hC, dist_eq_norm]
  refine ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg hC dist_nonneg) (fun m => ?_)
  rw [ContinuousMultilinearMap.sub_apply, uncurry3_apply, uncurry3_apply,
    show F x (m 0) (m 1) (m 2) - F y (m 0) (m 1) (m 2)
        = (F x (m 0) - F y (m 0)) (m 1) (m 2) from by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]]
  calc ‖(F x (m 0) - F y (m 0)) (m 1) (m 2)‖
      ≤ ‖(F x (m 0) - F y (m 0)) (m 1)‖ * ‖m 2‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖F x (m 0) - F y (m 0)‖ * ‖m 1‖ * ‖m 2‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ C * dist x y * ‖m 0‖ * ‖m 1‖ * ‖m 2‖ := by
        gcongr; exact h x y (m 0)
    _ = C * dist x y * ∏ i, ‖m i‖ := by rw [Fin.prod_univ_three]; ring

/-- **Multilinear Lipschitz continuity of the packaged third fundamental solution.**  This is the
obstruction-free form of the continuity of `D₃fam` needed to feed the resolvent's spatial
`ContDiff ℝ 3`.  For the packaged design-corrected third-variation operator family
`D₃fam : E → (E →L E →L E →L E)` (with its canonical linearised-first-variation family `Vfamfam` and
bilinear characterisation `hD₃famchar`, as produced base-point-by-base-point by
`exists_thirdVariationOperator_of_field`), its `Fin 3` multilinear packaging
`z ↦ uncurry3 (D₃fam z)` — valued in the *properly normed* space
`ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E` — is genuinely `LipschitzWith`, with the same
constant `Cλ · gronwallBound 0 K 1 (t − t₀)` (now with **no** trailing `‖k‖`, absorbed into the
multilinear norm) as the per-direction slice bound.

Whereas `lipschitzWith_thirdFundamentalSolution_apply` established continuity of `D₃fam`
direction-by-direction in the strong operator topology (the best available through the un-normed
triple continuous-linear-map tower), this theorem upgrades it to `LipschitzWith`/`Continuous` in a
single honest operator norm, by transporting the family through `uncurry3` into the multilinear space
that carries a proper norm at every order.  Proof: `lipschitzWith_uncurry3_of_apply_sub_le` fed the
per-direction base-point gap `norm_thirdFundamentalSolution_apply_baseCurve_sub_le` (which supplies
`‖D₃fam z k − D₃fam x₀ k‖ ≤ Cλ·g·‖z − x₀‖·‖k‖`). -/
theorem lipschitzWith_thirdFundamentalSolution_multilinear [CompleteSpace E]
    {Φ : E → ℝ → E} {Dv : ℝ → E → (E →L[ℝ] E)} {D2v : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E}
    {L M₂ M₃ : ℝ≥0} {C' C'' : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hDvlip : ∀ s, LipschitzWith L (Dv s)) (hD2vlip : ∀ s, LipschitzWith M₂ (D2v s))
    (hD3vlip : ∀ s, LipschitzWith M₃ (D3v s))
    (hAfun : ∀ z, ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K)
    (hAcontfun : ∀ z, Continuous (fun s => Dv s (Φ z s)))
    (hD2contfun : ∀ z, Continuous (fun s => D2v s (Φ z s)))
    (hD3contfun : ∀ z, Continuous (fun s => D3v s (Φ z s)))
    (hC'0 : 0 ≤ C') (hC'fun : ∀ z, ∀ s, ‖D2v s (Φ z s)‖ ≤ C')
    (hC''0 : 0 ≤ C'') (hC''fun : ∀ z, ∀ s, ‖D3v s (Φ z s)‖ ≤ C'')
    {Ψ : E → E → ℝ → E}
    (hΨ : ∀ z, ∀ x, IsIntegralCurve (Ψ z x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h0Ψ : ∀ z, ∀ x, Ψ z x t₀ = x)
    {T : ℝ} {t : ℝ}
    {Vfamfam : E → E → (ℝ → (E →L[ℝ] E))}
    {D₃fam : E → (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] E)))}
    (hVfamfam0 : ∀ z, ∀ h, Vfamfam z h t₀ = 0)
    (hVfamfamd : ∀ z, ∀ (h : E) (s : ℝ), HasDerivAt (Vfamfam z h)
      ((Dv s (Φ z s)).comp (Vfamfam z h s)
        + ((D2v s (Φ z s)).comp (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s) h).comp
            (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s)) s)
    (hVfamfamc : ∀ z, ∀ h, Continuous (Vfamfam z h))
    (hD₃famchar : ∀ z, ∀ (k h : E) (V : ℝ → (E →L[ℝ] E)), V t₀ = 0 →
      (∀ s, HasDerivAt V
        ((Dv s (Φ z s)).comp (V s)
          + (((D2v s (Φ z s)).comp (Vfamfam z k s) h).comp
                (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s)
             + ((D2v s (Φ z s)).comp (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s) h).comp
                 (Vfamfam z k s)
             + (((D2v s (Φ z s)).comp (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s) k).comp
                   (Vfamfam z h s)
                + (continuousMultilinearCurryFin1 ℝ E E
                    (((D3v s (Φ z s)).curryLeft
                          (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s k)).curryLeft
                      (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s h))).comp
                    (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s)))) s) →
      D₃fam z k h = V t)
    (ht : t ∈ Set.Icc t₀ T) :
    LipschitzWith
      (((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) ^ 4 * gronwallBound 0 (K : ℝ) 1 (T - t₀)
            * (3 * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀) + C'')
          + 3 * (Real.exp ((K : ℝ) * (T - t₀)) ^ 4 * gronwallBound 0 (K : ℝ) 1 (T - t₀)
              * (2 * (M₂ : ℝ) * C' + 4 * (L : ℝ) * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
          + Real.exp ((K : ℝ) * (T - t₀)) ^ 4
              * (3 * C'' * (L : ℝ) * gronwallBound 0 (K : ℝ) 1 (T - t₀) + (M₃ : ℝ)))
        * gronwallBound 0 (K : ℝ) 1 (t - t₀)).toNNReal
      (fun z => uncurry3 (D₃fam z)) := by
  have he4 : (0 : ℝ) ≤ Real.exp ((K : ℝ) * (T - t₀)) ^ 4 := by positivity
  have hg0 : (0 : ℝ) ≤ gronwallBound 0 (K : ℝ) 1 (T - t₀) :=
    gronwallBound_zero_one_nonneg K.coe_nonneg (sub_nonneg.mpr (le_trans ht.1 ht.2))
  have hgt0 : (0 : ℝ) ≤ gronwallBound 0 (K : ℝ) 1 (t - t₀) :=
    gronwallBound_zero_one_nonneg K.coe_nonneg (sub_nonneg.mpr ht.1)
  have hL := L.coe_nonneg
  have hM₂ := M₂.coe_nonneg
  have hM₃ := M₃.coe_nonneg
  have hCbig0 : (0 : ℝ) ≤
      ((L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) ^ 4 * gronwallBound 0 (K : ℝ) 1 (T - t₀)
            * (3 * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀) + C'')
          + 3 * (Real.exp ((K : ℝ) * (T - t₀)) ^ 4 * gronwallBound 0 (K : ℝ) 1 (T - t₀)
              * (2 * (M₂ : ℝ) * C' + 4 * (L : ℝ) * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀)))
          + Real.exp ((K : ℝ) * (T - t₀)) ^ 4
              * (3 * C'' * (L : ℝ) * gronwallBound 0 (K : ℝ) 1 (T - t₀) + (M₃ : ℝ))) := by
    have hA : (0 : ℝ) ≤ (L : ℝ) * Real.exp ((K : ℝ) * (T - t₀)) ^ 4
        * gronwallBound 0 (K : ℝ) 1 (T - t₀)
        * (3 * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀) + C'') :=
      mul_nonneg (mul_nonneg (mul_nonneg hL he4) hg0)
        (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg C')) hg0) hC''0)
    have hB : (0 : ℝ) ≤ 3 * (Real.exp ((K : ℝ) * (T - t₀)) ^ 4
        * gronwallBound 0 (K : ℝ) 1 (T - t₀)
        * (2 * (M₂ : ℝ) * C' + 4 * (L : ℝ) * C' ^ 2 * gronwallBound 0 (K : ℝ) 1 (T - t₀))) :=
      mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg he4 hg0)
        (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM₂) hC'0)
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) (sq_nonneg C')) hg0)))
    have hC : (0 : ℝ) ≤ Real.exp ((K : ℝ) * (T - t₀)) ^ 4
        * (3 * C'' * (L : ℝ) * gronwallBound 0 (K : ℝ) 1 (T - t₀) + (M₃ : ℝ)) :=
      mul_nonneg he4 (add_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC''0) hL) hg0) hM₃)
    linarith
  refine lipschitzWith_uncurry3_of_apply_sub_le (mul_nonneg hCbig0 hgt0) (fun z x₀ k => ?_)
  rw [dist_eq_norm]
  exact norm_thirdFundamentalSolution_apply_baseCurve_sub_le hv hΦ h0 hDvlip hD2vlip hD3vlip
    z x₀ (hAfun z) (hAfun x₀) (hAcontfun z) (hAcontfun x₀) (hD2contfun z) (hD2contfun x₀)
    (hD3contfun z) (hD3contfun x₀) hC'0 (hC'fun z) (hC'fun x₀) hC''0 (hC''fun z) (hC''fun x₀)
    (hΨ z) (h0Ψ z) (hΨ x₀) (h0Ψ x₀)
    (hVfamfam0 z) (hVfamfamd z) (hVfamfamc z) (hD₃famchar z)
    (hVfamfam0 x₀) (hVfamfamd x₀) (hVfamfamc x₀) (hD₃famchar x₀) ht k

/-- **Continuity of the third iterated derivative from multilinear derivative data.**  If the second
iterated derivative `iteratedFDeriv ℝ 2 f` is everywhere Fréchet differentiable with derivative
`D3ml x : E →L ContinuousMultilinearMap ℝ (Fin 2) E` (the *multilinear* representation of the third
derivative — a value in a **properly normed** space, sidestepping the un-normed triple
continuous-linear-map tower), and `D3ml` is continuous, then the third iterated derivative
`iteratedFDeriv ℝ 3 f` is continuous.

This is the obstruction-free continuity of the third derivative in the exact form the
`contDiff`/`iteratedFDeriv` chain consumes.  Proof: `curryLeft_iteratedFDeriv_three_eq_of_hasFDerivAt`
identifies `D3ml x` with `(iteratedFDeriv ℝ 3 f x).curryLeft`, so
`iteratedFDeriv ℝ 3 f x = (continuousMultilinearCurryLeftEquiv …).symm (D3ml x)`; the curry isometry's
inverse is continuous, so the composite is continuous.  Crucially, the hypothesis carries the third
derivative as `D3ml : E → (E →L ContinuousMultilinearMap ℝ (Fin 2) E)` — a normed codomain — rather
than as an `E → (E →L E →L E →L E)` whose triple operator norm does not synthesize in Mathlib
v4.29.1. -/
theorem continuous_iteratedFDeriv_three_of_hasFDerivAt_continuous
    {f : E → E}
    {D3ml : E → (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)}
    (hD3 : ∀ x, HasFDerivAt (iteratedFDeriv ℝ 2 f) (D3ml x) x)
    (hcont : Continuous D3ml) :
    Continuous (iteratedFDeriv ℝ 3 f) := by
  have key : iteratedFDeriv ℝ 3 f
      = fun x => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => E) E).symm (D3ml x) := by
    funext x
    have h := curryLeft_iteratedFDeriv_three_eq_of_hasFDerivAt (hD3 x)
    apply (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => E) E).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact h.symm
  rw [key]
  exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => E) E).symm.continuous.comp hcont

/-- **Differentiability of the second iterated derivative from multilinear derivative data.**  If the
second iterated derivative `iteratedFDeriv ℝ 2 f` is everywhere Fréchet differentiable with derivative
`D3ml x` (multilinear-valued), then it is differentiable.  The trivial `HasFDerivAt.differentiableAt`
half of the `ContDiff ℝ 3` upgrade, kept multilinear so it never touches the un-normed triple
continuous-linear-map tower. -/
theorem differentiable_iteratedFDeriv_two_of_hasFDerivAt
    {f : E → E}
    {D3ml : E → (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)}
    (hD3 : ∀ x, HasFDerivAt (iteratedFDeriv ℝ 2 f) (D3ml x) x) :
    Differentiable ℝ (iteratedFDeriv ℝ 2 f) :=
  fun x => (hD3 x).differentiableAt

/-- **`ContDiff ℝ 3` from `ContDiff ℝ 2` plus multilinear third-derivative data.**  The obstruction-free
capstone bridge to `C³` smoothness.  Given that `f` is already `C²`, that its second iterated
derivative `iteratedFDeriv ℝ 2 f` is everywhere Fréchet differentiable with a *continuous*,
*multilinear-valued* derivative `D3ml`, then `f` is `C³`.

This packages the `contDiff_nat_iff_continuous_differentiable` criterion at `n = 3`: the missing
ingredients beyond `C²` are continuity of the third iterated derivative
(`continuous_iteratedFDeriv_three_of_hasFDerivAt_continuous`) and differentiability of the second
(`differentiable_iteratedFDeriv_two_of_hasFDerivAt`), both supplied here from the multilinear
derivative datum `D3ml` — which lives in the well-normed
`E →L ContinuousMultilinearMap ℝ (Fin 2) E`, never in the un-normed `E →L E →L E →L E`.  This is the
abstract interface a flow-specific caller feeds with the fundamental-solution third-derivative data to
reach `ContDiff ℝ 3` dependence on initial conditions. -/
theorem contDiff_three_of_contDiff_two_of_hasFDerivAt_continuous
    {f : E → E}
    {D3ml : E → (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)}
    (hf2 : ContDiff ℝ 2 f)
    (hD3 : ∀ x, HasFDerivAt (iteratedFDeriv ℝ 2 f) (D3ml x) x)
    (hcont : Continuous D3ml) :
    ContDiff ℝ 3 f := by
  rw [show (3 : WithTop ℕ∞) = ((3 : ℕ) : WithTop ℕ∞) from by norm_cast,
    contDiff_nat_iff_continuous_differentiable]
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · interval_cases m
    · exact hf2.continuous_iteratedFDeriv (by norm_num)
    · exact hf2.continuous_iteratedFDeriv (by norm_num)
    · exact hf2.continuous_iteratedFDeriv (by norm_num)
    · exact continuous_iteratedFDeriv_three_of_hasFDerivAt_continuous hD3 hcont
  · interval_cases m
    · exact hf2.differentiable_iteratedFDeriv (by norm_num)
    · exact hf2.differentiable_iteratedFDeriv (by norm_num)
    · exact differentiable_iteratedFDeriv_two_of_hasFDerivAt hD3

/-- **`uncurry2CLM` is norm-nonexpansive** — `‖uncurry2CLM T‖ ≤ ‖T‖` — proved *without ever forming*
`‖uncurry2CLM‖`.  Taking the operator norm of `uncurry2CLM` itself requires
`Norm ((E →L E →L E) →L ML(Fin 2))`, which fails to synthesize in Mathlib v4.29.1 (the domain
`E →L E →L E` sits behind an expensive instance diamond).  Instead the bound is read off slot-by-slot
via `ContinuousMultilinearMap.opNorm_le_bound` and two `ContinuousLinearMap.le_opNorm` steps on the
*double* CLM space (the module's established pattern, cf. `lipschitzWith_uncurry3_of_apply_sub_le`),
so only norms that *do* synthesize are used.  This is the size datum that lets `uncurry2CLM`
post-compose a little-o (`isLittleO_uncurry2CLM_comp`). -/
theorem norm_uncurry2CLM_le (T : E →L[ℝ] (E →L[ℝ] E)) : ‖uncurry2CLM T‖ ≤ ‖T‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (ContinuousLinearMap.opNorm_nonneg T) (fun m => ?_)
  rw [uncurry2CLM_apply]
  calc ‖T (m 0) (m 1)‖
      ≤ ‖T (m 0)‖ * ‖m 1‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖T‖ * ‖m 0‖) * ‖m 1‖ := by gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖T‖ * (‖m 0‖ * ‖m 1‖) := by ring
    _ = ‖T‖ * ∏ i, ‖m i‖ := by rw [Fin.prod_univ_two]

/-- **Post-composition of a little-o with the nonexpansive `uncurry2CLM`.**  If `u =o[l] w` (with `u`
valued in the double space `E →L E →L E`) then `y ↦ uncurry2CLM (u y) =o[l] w`.  Proof: unfold both
little-o's to the `∀ c > 0, eventually ‖·‖ ≤ c ‖w‖` form (`Asymptotics.isLittleO_iff`) and transport
the bound pointwise through `norm_uncurry2CLM_le`.  Routing through `isLittleO_iff` +
`filter_upwards` + `Trans.trans` (rather than `ContinuousLinearMap.isBigO_comp` /
`IsBigO.trans_isLittleO`) is deliberate: the latter drag in `uncurry2CLM`'s domain as a *seminormed*
space, forcing a whnf reconciliation of the double-space `Norm` diamond
(`ContinuousLinearMap.hasOpNorm` vs `SeminormedAddCommGroup.toNorm`) that blows up; the
`isLittleO_iff` route only ever manipulates the already-formed norms and is defeq-robust. -/
theorem isLittleO_uncurry2CLM_comp {α : Type*} {l : Filter α}
    {u : α → (E →L[ℝ] (E →L[ℝ] E))} {G : Type*} [SeminormedAddGroup G] {w : α → G}
    (h : u =o[l] w) : (fun y => uncurry2CLM (u y)) =o[l] w := by
  rw [Asymptotics.isLittleO_iff] at h ⊢
  intro c hc
  filter_upwards [h hc] with y hy
  exact (norm_uncurry2CLM_le (u y)).trans hy

/-- **The nested→multilinear `HasFDerivAt` bridge for the second iterated derivative.**  This is the
single wall that blocked applying the `ContDiff ℝ 3` capstone to the flow.  Given that `f` is `C²`
with first derivative `Df` and second (composition-form) derivative `D2`, and that `D2` is Fréchet
differentiable at `x` with derivative the *nested triple* operator `D3 : E →L E →L E →L E`, the
(multilinear) second iterated derivative `iteratedFDeriv ℝ 2 f` is Fréchet differentiable at `x` with
derivative the *multilinear-valued* operator `uncurry2CLM.comp D3 : E →L ML(Fin 2)`.

The naive route — rewrite `iteratedFDeriv ℝ 2 f = uncurry2CLM ∘ D2` and apply the chain rule
`uncurry2CLM.hasFDerivAt.comp x hD3` — **whnf-diverges / fails to unify**: it forces Lean to
reconcile the plain topological-module structure carried by `uncurry2CLM`'s domain `E →L E →L E`
with the seminormed structure the chain rule demands, an expensive defeq on the nested space.

The proof here sidesteps that entirely.  It extracts the defining little-o of `hD3` (with the
implicit arguments supplied *explicitly* — `HasFDerivAt.isLittleO` on a double-space codomain
otherwise fails to assign its metavariables), post-composes it through the nonexpansive `uncurry2CLM`
(`isLittleO_uncurry2CLM_comp`), and rewrites the resulting little-o into the Fréchet-difference shape
of the goal using the pointwise identity `iteratedFDeriv ℝ 2 f y = uncurry2CLM (D2 y)`
(`iteratedFDeriv_two_eq_uncurry2CLM_of_hasFDerivAt`) and the linearity of `uncurry2CLM`.  Only norms
that synthesize are ever touched. -/
theorem hasFDerivAt_iteratedFDeriv_two_uncurry2CLM
    {f : E → E} {Df : E → (E →L[ℝ] E)} {D2 : E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3 : E →L[ℝ] (E →L[ℝ] (E →L[ℝ] E))} {x : E}
    (hDf : ∀ y, HasFDerivAt f (Df y) y) (hD2 : ∀ y, HasFDerivAt Df (D2 y) y)
    (hD3 : HasFDerivAt D2 D3 x) :
    HasFDerivAt (iteratedFDeriv ℝ 2 f) (uncurry2CLM.comp D3) x := by
  have hlo := HasFDerivAt.isLittleO (𝕜 := ℝ) (f := D2) (f' := D3) (x := x) hD3
  refine HasFDerivAt.of_isLittleO ((isLittleO_uncurry2CLM_comp hlo).congr_left (fun y => ?_))
  rw [iteratedFDeriv_two_eq_uncurry2CLM_of_hasFDerivAt hDf (hD2 y),
      iteratedFDeriv_two_eq_uncurry2CLM_of_hasFDerivAt hDf (hD2 x),
      ContinuousLinearMap.comp_apply, map_sub, map_sub]

/-- **Obstruction-free `ContDiff ℝ 3` from nested second-fundamental-solution data.**  The clean
interface that a flow-specific caller feeds to reach `C³` dependence on initial conditions.  Given
that `f` is already `C²` with first/second (composition-form) derivatives `Df`, `D2`, that `D2` is
everywhere Fréchet differentiable with the *nested triple* third-fundamental operator `D3fam y`
(`HasFDerivAt D2 (D3fam y) y` — exactly the datum `exists_hasFDerivAt_secondFundamentalSolution`
delivers), and that the *multilinear packaging* `z ↦ uncurry3 (D3fam z)` is continuous (the
obstruction-free continuity `lipschitzWith_thirdFundamentalSolution_multilinear` supplies), then `f`
is `C³`.

This packages the existing capstone `contDiff_three_of_contDiff_two_of_hasFDerivAt_continuous` with
the multilinear third-derivative datum `D3ml x = (uncurry3 (D3fam x)).curryLeft`:
`hasFDerivAt_iteratedFDeriv_two_uncurry2CLM` (+ `uncurry3_curryLeft`) supplies the pointwise
`HasFDerivAt (iteratedFDeriv ℝ 2 f) (D3ml x) x`, and the continuity of `D3ml` is the continuity of
`z ↦ uncurry3 (D3fam z)` transported through the isometry `continuousMultilinearCurryLeftEquiv`
(whose forward map *is* `curryLeft`).  Crucially the third derivative is carried throughout as a
value in the well-normed `ML(Fin 3)` / `E →L ML(Fin 2)` spaces — never in the un-normed
`E →L E →L E →L E`. -/
theorem contDiff_three_of_hasFDerivAt_nested_of_continuous
    {f : E → E} {Df : E → (E →L[ℝ] E)} {D2 : E → (E →L[ℝ] (E →L[ℝ] E))}
    {D3fam : E → (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] E)))}
    (hf2 : ContDiff ℝ 2 f)
    (hDf : ∀ y, HasFDerivAt f (Df y) y)
    (hD2 : ∀ y, HasFDerivAt Df (D2 y) y)
    (hD3 : ∀ y, HasFDerivAt D2 (D3fam y) y)
    (hcont : Continuous (fun z => uncurry3 (D3fam z))) :
    ContDiff ℝ 3 f := by
  refine contDiff_three_of_contDiff_two_of_hasFDerivAt_continuous
    (D3ml := fun x => (uncurry3 (D3fam x)).curryLeft) hf2 (fun x => ?_) ?_
  · show HasFDerivAt (iteratedFDeriv ℝ 2 f) ((uncurry3 (D3fam x)).curryLeft) x
    rw [uncurry3_curryLeft]
    exact hasFDerivAt_iteratedFDeriv_two_uncurry2CLM hDf hD2 (hD3 x)
  · exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 3 => E) E).continuous.comp hcont

/-- **The nested second-fundamental-solution `HasFDerivAt` chain *bundled with* its multilinear
continuity** — the exact triple of data `contDiff_three_of_hasFDerivAt_nested_of_continuous` consumes
on the third-derivative side.  This packages `exists_hasFDerivAt_secondFundamentalSolution` (the
everywhere `fderiv D₂ = D₃fam` half of the resolvent's spatial `C³`) together with the multilinear
continuity `z ↦ uncurry3 (D₃fam z)` of the third fundamental solution
(`lipschitzWith_thirdFundamentalSolution_multilinear`), for the **same** packaged operators — the
identification the two halves could not share when quoted as separate theorems (the third fundamental
solution `D₃fam` and its linearised-first-variation family `Vfamfam` are the existentially bound
witnesses, so their characterisation is only in scope inside a single proof).

Building both from *one* `exists_thirdVariationOperator_of_field` invocation (whose seventh conjunct
is the third-variation-ODE characterisation `hD₃bilinear` fed to *both* the `HasFDerivAt` slot
`thirdVariationOperator_hD₃_slot_of_bilinear` and the multilinear Lipschitz base gap
`norm_thirdFundamentalSolution_apply_baseCurve_sub_le`) is exactly what lets the continuity be stated
for the `D₃fam` that the chain differentiates to.  The lone extra hypothesis beyond
`exists_hasFDerivAt_secondFundamentalSolution` is `hD3vlip` (spatial Lipschitzness of the `Fin 3`
third derivative `D3v`), which drives the continuity but is inert for the pointwise chain.  This is
the "sole remaining ingredient" the resolvent-`C³` docstring flagged: with it,
`contDiff_three_of_hasFDerivAt_nested_of_continuous` closes `ContDiff ℝ 3` dependence on initial
data. -/
theorem exists_hasFDerivAt_secondFundamentalSolution_multilinearContinuous [CompleteSpace E]
    {Dv : ℝ → E → (E →L[ℝ] E)}
    {D2vc : ℝ → E → (E →L[ℝ] (E →L[ℝ] E))}
    {D2vm : ℝ → E → (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E)}
    {D3vm : ℝ → E → (E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) E))}
    {D3v : ℝ → E → ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E}
    {L M₂ M₃ : ℝ≥0} {C' C'' N : ℝ}
    (hv : ∀ τ, LipschitzWith K (v τ)) (hΦ : ∀ x, IsIntegralCurve (Φ x) v) (h0 : ∀ x, Φ x t₀ = x)
    (hDv : ∀ s ξ, HasFDerivAt (v s) (Dv s ξ) ξ) (hDvlip : ∀ s, LipschitzWith L (Dv s))
    (hD2vc : ∀ s ξ, HasFDerivAt (Dv s) (D2vc s ξ) ξ) (hD2vclip : ∀ s, LipschitzWith M₂ (D2vc s))
    (hD3vm : ∀ s ξ, HasFDerivAt (D2vm s) (D3vm s ξ) ξ) (hD3vmlip : ∀ s, LipschitzWith M₃ (D3vm s))
    (hD3vlip : ∀ s, LipschitzWith M₃ (D3v s))
    (hcompat : ∀ s ξ, D2vc s ξ = curry2 (D2vm s ξ))
    (hAfun : ∀ z, ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K)
    (hAcontfun : ∀ z, Continuous (fun s => Dv s (Φ z s)))
    (hD2contfun : ∀ z, Continuous (fun s => D2vc s (Φ z s)))
    (hD3mcont : ∀ z, Continuous (fun s => D3vm s (Φ z s)))
    (hD3vcont : ∀ z, Continuous (fun s => D3v s (Φ z s)))
    (hC'0 : 0 ≤ C') (hC'fun : ∀ z, ∀ s, ‖D2vc s (Φ z s)‖ ≤ C')
    (hN0 : 0 ≤ N) (hN : ∀ z, ∀ s, ‖D3vm s (Φ z s)‖ ≤ N)
    (hC''0 : 0 ≤ C'') (hC'' : ∀ z, ∀ s, ‖D3v s (Φ z s)‖ ≤ C'')
    (hcurry : ∀ z, ∀ s, D3vm s (Φ z s) = (D3v s (Φ z s)).curryLeft)
    {Ψ : E → E → ℝ → E}
    (hΨ : ∀ z, ∀ x, IsIntegralCurve (Ψ z x) (variationalFieldVec (fun s => Dv s (Φ z s))))
    (h0Ψ : ∀ z, ∀ x, Ψ z x t₀ = x)
    {T : ℝ} (ht : t ∈ Set.Icc t₀ T) :
    ∃ (D₂ : E → (E →L[ℝ] (E →L[ℝ] E)))
        (D₃fam : E → (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] E)))),
      (∀ (z h : E) (Vlin : ℝ → (E →L[ℝ] E)), Vlin t₀ = 0 →
        (∀ s, HasDerivAt Vlin
          ((Dv s (Φ z s)).comp (Vlin s)
            + ((D2vc s (Φ z s)).comp (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s) h).comp
                (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) s)) s) →
        D₂ z h = Vlin t) ∧
      (∀ y, HasFDerivAt D₂ (D₃fam y) y) ∧
      Continuous (fun z => uncurry3 (D₃fam z)) := by
  choose D₂ hD₂char using fun z => exists_continuousLinearMap_linearisedVariation
    z (hAfun z) (hAcontfun z) (hD2contfun z) (hΨ z) (h0Ψ z) hC'0 (hC'fun z) ht
  choose Vfamfam D₃fam hprops using fun z => exists_thirdVariationOperator_of_field
    z (hAfun z) (hAcontfun z) (hD2contfun z) (hD3vcont z) (hΨ z) (h0Ψ z) hC'0 hC''0
      (hC'fun z) (hC'' z) ht
  refine ⟨D₂, D₃fam, hD₂char, fun y => ?_, ?_⟩
  · obtain ⟨hVfam0, hVfamd, _, _, _, _, hD₃bilinear⟩ := hprops y
    apply hasFDerivAt_of_eventually_norm_sub_sub_le_sq (f := D₂) (f' := D₃fam y) (x₀ := y)
    filter_upwards [Metric.ball_mem_nhds y one_pos] with z hz
    have hk : ‖z - y‖ ≤ 1 := by
      have hmem := Metric.mem_ball.mp hz
      rw [dist_eq_norm] at hmem
      exact hmem.le
    have hW : Continuous (fun s => fundamentalSolution (hAfun y) (hΨ y) (h0Ψ y) s) :=
      continuous_fundamentalSolution_time (hAfun y) (hΨ y) (h0Ψ y)
    obtain ⟨W₂, hW₂0, hW₂⟩ := exists_hasDerivAt_firstVariation_linearised
      y (hAfun y) (hAcontfun y) (hD2contfun y) (hΨ y) (h0Ψ y) z
    obtain ⟨Wdiff, hWdiff0, hWdiff⟩ := exists_hasDerivAt_inhomogVariation_of_continuous
      (hAfun y) (hAcontfun y) (((hAcontfun z).sub (hAcontfun y)).clm_comp hW) t₀
    have hslot := thirdVariationOperator_hD₃_slot_of_bilinear y z (hAfun y) (hΨ y) (h0Ψ y)
      hVfam0 hVfamd (hcurry y) hD₃bilinear hW₂ hW₂0
    exact norm_secondFundamentalSolution_op_sub_thirdVariation_le_sq_uniformC
      hv hΦ h0 hDv hDvlip hD2vc hD2vclip hD3vm hD3vmlip hcompat z y
      (hAfun z) (hAfun y) (hAcontfun y) (hAcontfun z) (hD2contfun z) (hD2contfun y) (hD3mcont y)
      hC'0 (hC'fun z) (hC'fun y) hN0 (hN y) (hΨ y) (h0Ψ y) (hΨ z) (h0Ψ z)
      hW₂ hW₂0 hWdiff hWdiff0 (hD₂char z) (hD₂char y) hslot hk ht
  · exact (lipschitzWith_thirdFundamentalSolution_multilinear hv hΦ h0 hDvlip hD2vclip hD3vlip
      hAfun hAcontfun hD2contfun hD3vcont hC'0 hC'fun hC''0 hC'' hΨ h0Ψ
      (fun z => (hprops z).1) (fun z => (hprops z).2.1) (fun z => (hprops z).2.2.1)
      (fun z => (hprops z).2.2.2.2.2.2) ht).continuous

/-- **`C³` dependence of the flow on initial data — the Item 1/2 unblock.**  For a `C^{3,1}` vector
field `v` on a real Banach space (uniformly `K`-Lipschitz, time-continuous, with first/second/third
spatial derivatives `Dv`, `D2vc`/`D2vm`, `D3vm`/`D3v` — jointly continuous and spatially Lipschitz,
in the compatible composition/multilinear representations), the time-`t` flow map `z ↦ Φ z t` is
`ContDiff ℝ 3` (three times continuously Fréchet differentiable in the initial value).

This is the theorem the compact-manifold gauge flow of Item 2 and the tensor time-derivative chain
rule of Item 1 ultimately consume: Mathlib v4.29.1 supplies smooth ODE-flow dependence only at the
Banach/first-order level, and this closes the `C³` initial-data regularity built up through the whole
`SmoothDependenceCk` tower.

The proof assembles three now-available pieces for a **single shared** flow family `Φ`:
(1) `exists_flow_contDiff_two_of_lipschitz_secondDeriv` supplies `Φ` together with the honest
`ContDiff ℝ 2 (z ↦ Φ z t)`; (2) `exists_hasFDerivAt_secondFundamentalSolution_multilinearContinuous`
supplies the nested third-fundamental chain `∀ y, HasFDerivAt D₂ (D₃fam y) y` *and* the multilinear
continuity `Continuous (z ↦ uncurry3 (D₃fam z))`; (3) the `C¹`/`C²` bootstraps
(`hasFDerivAt_flow_of_lipschitz_deriv`, the base-point `C²` remainder
`norm_fundamentalSolution_sub_sub_linearVariation_le_sq`) identify the flow's first derivative with
the resolvent and the resolvent's derivative with the packaged `D₂`.  Feeding all of these to the
obstruction-free `contDiff_three_of_hasFDerivAt_nested_of_continuous` — which routes the third
derivative through the well-normed `ML(Fin 3)` / `E →L ML(Fin 2)` spaces, never the un-normed
`E →L E →L E →L E` — yields `ContDiff ℝ 3`.  The along-flow bounds are read off the derivative
Lipschitz constants (`C' = L`, `‖D3vm‖ ≤ N = ‖D2vm‖`-Lipschitz, `‖D3v‖ = ‖D3v.curryLeft‖ = ‖D3vm‖`
by the `curryLeft` isometry). -/
theorem exists_flow_contDiff_three_of_lipschitz_thirdDeriv [CompleteSpace E]
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
    (ht0 : t₀ ≤ t) :
    ∃ Φ : E → ℝ → E, (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) ∧
        ContDiff ℝ 3 (fun z => Φ z t) := by
  obtain ⟨Φ, h0, hΦ, hf2⟩ := exists_flow_contDiff_two_of_lipschitz_secondDeriv
    hv hvc hDv hDvc hDvlip hD2vc hD2vcc hD2vclip ht0
  have hAfun : ∀ z, ∀ s, ‖Dv s (Φ z s)‖₊ ≤ K := fun z s => by
    have h : ‖Dv s (Φ z s)‖ ≤ (K : ℝ) := (hDv s (Φ z s)).le_of_lipschitz (hv s)
    exact_mod_cast h
  have hAcontfun : ∀ z, Continuous (fun s => Dv s (Φ z s)) := fun z =>
    hDvc.comp (continuous_id.prodMk (hΦ z).continuous)
  have hD2contfun : ∀ z, Continuous (fun s => D2vc s (Φ z s)) := fun z =>
    hD2vcc.comp (continuous_id.prodMk (hΦ z).continuous)
  have hD3mcont : ∀ z, Continuous (fun s => D3vm s (Φ z s)) := fun z =>
    hD3vmc.comp (continuous_id.prodMk (hΦ z).continuous)
  have hD3vcont : ∀ z, Continuous (fun s => D3v s (Φ z s)) := fun z =>
    hD3vc.comp (continuous_id.prodMk (hΦ z).continuous)
  have hCz : ∀ z, ∀ s, ‖D2vc s (Φ z s)‖ ≤ (L : ℝ) := fun z s =>
    (hD2vc s (Φ z s)).le_of_lipschitz (hDvlip s)
  have hNfun : ∀ z, ∀ s, ‖D3vm s (Φ z s)‖ ≤ (N : ℝ) := fun z s =>
    (hD3vm s (Φ z s)).le_of_lipschitz (hD2vmlip s)
  have hC''fun : ∀ z, ∀ s, ‖D3v s (Φ z s)‖ ≤ (N : ℝ) := fun z s => by
    have hcn : ‖(D3v s (Φ z s)).curryLeft‖ = ‖D3v s (Φ z s)‖ :=
      ContinuousMultilinearMap.curryLeft_norm _
    have hbnd := hNfun z s
    rw [hcurry s (Φ z s), hcn] at hbnd
    exact hbnd
  have htmem : t ∈ Set.Icc t₀ t := ⟨ht0, le_refl t⟩
  choose Ψ h0Ψ hΨ using fun z => exists_variationalFlowFamily (hAfun z) (hAcontfun z)
  obtain ⟨D₂, D₃fam, hD₂char, hD3chain, hcont⟩ :=
    exists_hasFDerivAt_secondFundamentalSolution_multilinearContinuous
      hv hΦ h0 hDv hDvlip hD2vc hD2vclip hD3vm hD3vmlip hD3vlip hcompat hAfun hAcontfun
      hD2contfun hD3mcont hD3vcont L.coe_nonneg hCz N.coe_nonneg hNfun N.coe_nonneg hC''fun
      (fun z s => hcurry s (Φ z s)) hΨ h0Ψ htmem
  have hDf : ∀ z, HasFDerivAt (fun w => Φ w t)
      (fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) t) z := fun z =>
    hasFDerivAt_flow_of_lipschitz_deriv hv (hAfun z) (hΨ z) (h0Ψ z) hΦ h0 z ht0
      (Dv := Dv) (fun _ s _ ξ _ => (hDv s ξ).hasFDerivWithinAt) L.coe_nonneg
      (fun _ s _ ξ _ => by
        have hlip := (hDvlip s).dist_le_mul ξ (Φ z s)
        rw [dist_eq_norm, dist_eq_norm] at hlip
        exact hlip)
  have hD2 : ∀ z, HasFDerivAt
      (fun z' => fundamentalSolution (hAfun z') (hΨ z') (h0Ψ z') t) (D₂ z) z := by
    intro z
    refine hasFDerivAt_of_eventually_norm_sub_sub_le_sq (C :=
        (L : ℝ) ^ 2 * Real.exp ((K : ℝ) * (t - t₀)) ^ 3
            * gronwallBound 0 (K : ℝ) 1 (t - t₀) ^ 2
          + ((M₂ : ℝ) * Real.exp (2 * (K : ℝ) * (t - t₀))
              + (L : ℝ) * ((L : ℝ) * Real.exp (2 * (K : ℝ) * (t - t₀))
                  * gronwallBound 0 (K : ℝ) 1 (t - t₀)))
            * Real.exp ((K : ℝ) * (t - t₀)) * gronwallBound 0 (K : ℝ) 1 (t - t₀))
      (Filter.Eventually.of_forall (fun z' => ?_))
    obtain ⟨Vz, hVz0, hVz⟩ := exists_hasDerivAt_firstVariation_true
      z (hAfun z) (hAcontfun z) (hΨ z) (h0Ψ z) z' (hAcontfun z')
    obtain ⟨Vlin, hVlin0, hVlin⟩ := exists_hasDerivAt_firstVariation_linearised
      z (hAfun z) (hAcontfun z) (hD2contfun z) (hΨ z) (h0Ψ z) z'
    have hrem := norm_fundamentalSolution_sub_sub_linearVariation_le_sq
      hv hΦ h0 hDv hDvlip hD2vc hD2vclip z (hAfun z) (hAcontfun z) L.coe_nonneg (hCz z)
      (hΨ z) (h0Ψ z) z' (hAfun z') (hAcontfun z') (hΨ z') (h0Ψ z') hVz hVz0 hVlin hVlin0 htmem
    have hval : D₂ z (z' - z) = Vlin t := hD₂char z (z' - z) Vlin hVlin0 hVlin
    rw [hval]; exact hrem
  exact ⟨Φ, h0, hΦ,
    contDiff_three_of_hasFDerivAt_nested_of_continuous hf2 hDf hD2 hD3chain hcont⟩

end SmoothDependenceCk
end AnalyticPDE
end RicciFlow
