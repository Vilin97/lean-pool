/-
Copyright (c) 2026 Joseph K. Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph K. Miller
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-! # Wasserstein-1 distance via Kantorovich–Rubinstein duality (cost-generic)

The optimal-transport core, all generic over the underlying (pseudo)metric space
— no Vlasov / phase-space dependency.  Contents: the cost-parameterized functional
`wassersteinCost`, the W₁ distance `wasserstein1` (the `c = dist` case), the
truncated-metric variant `wassersteinBar` (Wbar), and their property lemmas
(symmetry, triangle, non-expansion under 1-Lipschitz pushforward, KR-dual lower
bound, finiteness under finite first moments). -/

open MeasureTheory

namespace Vlasov

/- Wasserstein-1 distance between two measures on a (pseudo)metric space,
defined via the Kantorovich–Rubinstein dual formula

  W₁(μ, ν) = sup { ∫ f dμ − ∫ f dν | f : 1-Lipschitz, f : α → ℝ }.

Returns `ℝ≥0∞` so that unbounded suprema (e.g. when a measure has no finite
first moment) are represented honestly as `⊤` rather than collapsing to the
conditional-sup junk value `0` that `⨆` produces on `ℝ`.  Negative
arguments to `ENNReal.ofReal` round up to `0`; that is consistent with the
dual formula because the family of 1-Lipschitz `f` is closed under `f ↦ -f`,
so the positive parts already realise the absolute value of the signed
difference. -/
/-- **Cost-parameterized Wasserstein-1 functional.**  KR-dual sup over functions
whose oscillation is controlled by a cost `c`.  Using the explicit oscillation
bound `|f x − f y| ≤ c x y` (rather than `LipschitzWith 1 f` w.r.t. an ambient
metric) decouples the definition from the `PseudoMetricSpace` instance, so a
cost like `min (dist x y) 1` (the truncated-metric "Wbar" cost) instantiates with
no new instance.  `wasserstein1` is the `c = dist` case. -/
noncomputable def wassersteinCost {α : Type*} [MeasurableSpace α]
    (c : α → α → ℝ) (μ ν : Measure α) : ENNReal :=
  ⨆ (f : α → ℝ) (_ : ∀ x y, |f x - f y| ≤ c x y),
    ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν)

/-- The oscillation test class `∀ x y, |f x − f y| ≤ dist x y` coincides with
`LipschitzWith 1 f` for real-valued `f` on a pseudometric space.  Bridge between
`wassersteinCost dist` (the cost-parameterized form) and the `LipschitzWith`-
phrased property lemmas. -/
lemma lipschitzWith_one_iff_oscillation {α : Type*} [PseudoMetricSpace α]
    (f : α → ℝ) : LipschitzWith 1 f ↔ ∀ x y, |f x - f y| ≤ dist x y := by
  constructor
  · intro hf x y
    have := hf.dist_le_mul x y
    rwa [Real.dist_eq, NNReal.coe_one, one_mul] at this
  · intro h
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, NNReal.coe_one, one_mul]
    exact h x y

/-- The Kantorovich–Rubinstein dual Wasserstein-1 distance: the `c = dist` case
of `wassersteinCost`. -/
noncomputable def wasserstein1 {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ ν : Measure α) : ENNReal :=
  wassersteinCost (fun x y => dist x y) μ ν

/-- `wasserstein1` equals the `LipschitzWith 1`-phrased sup.  The property lemmas
below `rw` through this; consumers reference `wasserstein1` only through these
property lemmas. -/
lemma wasserstein1_eq_iSup_lipschitz {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ ν : Measure α) :
    wasserstein1 μ ν = ⨆ (f : α → ℝ) (_ : LipschitzWith 1 f),
      ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) := by
  unfold wasserstein1 wassersteinCost
  simp only [lipschitzWith_one_iff_oscillation]

/-- For probability measures μ, ν on a normed space `E` with finite first moments
(i.e. `Integrable (fun y => ‖y‖) μ` and same for ν), the Wasserstein-1 distance
is finite: `wasserstein1 μ ν < ⊤`.

Proof sketch:  For any 1-Lipschitz `φ : E → ℝ`, set `ψ y := φ y - φ 0`.  Then
|ψ(y)| ≤ ‖y‖ by 1-Lipschitz-ness, and ∫φdμ − ∫φdν = ∫ψdμ − ∫ψdν (the
constants φ(0)·μ(univ) = φ(0)·ν(univ) cancel since both are probability
measures).
So ∫φdμ − ∫φdν ≤ ∫|ψ|dμ + ∫|ψ|dν ≤ ∫‖y‖dμ + ∫‖y‖dν =: M, finite.
Taking sup over 1-Lip φ: `wasserstein1 μ ν ≤ ENNReal.ofReal M < ⊤`. -/
lemma wasserstein1_lt_top_of_finite_moment
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun y => ‖y‖) μ) (hν : Integrable (fun y => ‖y‖) ν) :
    wasserstein1 μ ν < ⊤ := by
  -- Bound: sup over 1-Lip φ of ∫φd(μ-ν) ≤ ∫‖y‖dμ + ∫‖y‖dν =: M, which is
  -- finite.
  set M : ℝ := ∫ y, ‖y‖ ∂μ + ∫ y, ‖y‖ ∂ν with hM_def
  suffices h : wasserstein1 μ ν ≤ ENNReal.ofReal M from
    h.trans_lt ENNReal.ofReal_lt_top
  rw [wasserstein1_eq_iSup_lipschitz]
  refine iSup_le fun φ => iSup_le fun hφ => ?_
  apply ENNReal.ofReal_le_ofReal
  -- Pointwise: |φ y - φ 0| ≤ ‖y‖ (1-Lipschitz)
  have hψ_bound : ∀ y, |φ y - φ 0| ≤ ‖y‖ := fun y => by
    have h_lip := hφ.dist_le_mul y 0
    rw [Real.dist_eq, dist_zero_right, NNReal.coe_one, one_mul] at h_lip
    exact h_lip
  -- φ is integrable on both μ and ν (bounded a.e. by integrable |φ 0| + ‖y‖)
  have hφ_cont : Continuous φ := hφ.continuous
  have hφ_meas_μ : AEStronglyMeasurable φ μ := hφ_cont.aestronglyMeasurable
  have hφ_meas_ν : AEStronglyMeasurable φ ν := hφ_cont.aestronglyMeasurable
  have h_bound_abs : ∀ y, |φ y| ≤ |φ 0| + ‖y‖ := fun y => by
    calc |φ y| = |(φ y - φ 0) + φ 0| := by ring_nf
      _ ≤ |φ y - φ 0| + |φ 0| := abs_add_le _ _
      _ ≤ ‖y‖ + |φ 0| := by linarith [hψ_bound y]
      _ = |φ 0| + ‖y‖ := by ring
  have h_dom_μ : Integrable (fun y => |φ 0| + ‖y‖) μ :=
    (integrable_const _).add hμ
  have h_dom_ν : Integrable (fun y => |φ 0| + ‖y‖) ν :=
    (integrable_const _).add hν
  have hφ_int_μ : Integrable φ μ :=
    h_dom_μ.mono hφ_meas_μ (Filter.Eventually.of_forall fun y => by
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (norm_nonneg _))]
      exact h_bound_abs y)
  have hφ_int_ν : Integrable φ ν :=
    h_dom_ν.mono hφ_meas_ν (Filter.Eventually.of_forall fun y => by
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (norm_nonneg _))]
      exact h_bound_abs y)
  -- ∫(φ y - φ 0) dμ = ∫φ dμ - φ 0  (since μ is a probability measure)
  have h_int_μ_const : ∫ _ : E, φ 0 ∂μ = φ 0 := by
    simp [integral_const]
  have h_int_ν_const : ∫ _ : E, φ 0 ∂ν = φ 0 := by
    simp [integral_const]
  have h_int_μ_sub : ∫ y, (φ y - φ 0) ∂μ = ∫ y, φ y ∂μ - φ 0 := by
    rw [integral_sub hφ_int_μ (integrable_const _), h_int_μ_const]
  have h_int_ν_sub : ∫ y, (φ y - φ 0) ∂ν = ∫ y, φ y ∂ν - φ 0 := by
    rw [integral_sub hφ_int_ν (integrable_const _), h_int_ν_const]
  -- ∫φ dμ - ∫φ dν = ∫(φ - φ 0)dμ - ∫(φ - φ 0)dν  (constants cancel)
  have h_diff_eq : ∫ y, φ y ∂μ - ∫ y, φ y ∂ν =
      ∫ y, (φ y - φ 0) ∂μ - ∫ y, (φ y - φ 0) ∂ν := by
    rw [h_int_μ_sub, h_int_ν_sub]; ring
  rw [h_diff_eq]
  -- Bound each side: ∫(φ-φ 0)dμ ≤ ∫‖y‖dμ and -∫(φ-φ 0)dν ≤ ∫‖y‖dν
  have hψ_int_μ : Integrable (fun y => φ y - φ 0) μ :=
    hφ_int_μ.sub (integrable_const _)
  have hψ_int_ν : Integrable (fun y => φ y - φ 0) ν :=
    hφ_int_ν.sub (integrable_const _)
  have h_bound_μ : ∫ y, (φ y - φ 0) ∂μ ≤ ∫ y, ‖y‖ ∂μ := by
    calc ∫ y, (φ y - φ 0) ∂μ
        ≤ ∫ y, |φ y - φ 0| ∂μ :=
          integral_mono_ae hψ_int_μ hψ_int_μ.abs
            (Filter.Eventually.of_forall fun _ => le_abs_self _)
      _ ≤ ∫ y, ‖y‖ ∂μ :=
          integral_mono_ae hψ_int_μ.abs hμ (Filter.Eventually.of_forall hψ_bound)
  have h_bound_ν : -∫ y, (φ y - φ 0) ∂ν ≤ ∫ y, ‖y‖ ∂ν := by
    rw [← integral_neg]
    calc ∫ y, -(φ y - φ 0) ∂ν
        ≤ ∫ y, |φ y - φ 0| ∂ν :=
          integral_mono_ae hψ_int_ν.neg hψ_int_ν.abs
            (Filter.Eventually.of_forall fun y => neg_le_abs _)
      _ ≤ ∫ y, ‖y‖ ∂ν :=
          integral_mono_ae hψ_int_ν.abs hν (Filter.Eventually.of_forall hψ_bound)
  linarith

/-- Convenience corollary: under the same hypotheses, `wasserstein1 μ ν ≠ ⊤`. -/
lemma wasserstein1_ne_top_of_finite_moment
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun y => ‖y‖) μ) (hν : Integrable (fun y => ‖y‖) ν) :
    wasserstein1 μ ν ≠ ⊤ :=
  (wasserstein1_lt_top_of_finite_moment μ ν hμ hν).ne

/-! ### Basic algebra of `wasserstein1`

The KR-dual sup-formula makes `wasserstein1` a pseudometric on `Measure α` (we
only get a *pseudo*-metric, not a metric, because `wasserstein1 μ ν = 0` does
not characterise `μ = ν` in this generality).  The three lemmas below are
self-distance / symmetry / triangle, all derived directly from the sup-formula.
Together they make `wasserstein1` usable as the codomain of a sup-W₁ pseudo-
distance on time-indexed measure curves (see `supW1On` in
`LeanPool/Vlasov/OT/CharacteristicFlow.lean`). -/

/-- `wassersteinCost c μ μ = 0` (cost-generic; no hypothesis on `c`).  Self-distance
is zero; `wasserstein1_self` is the `c = dist` corollary. -/
lemma wassersteinCost_self {α : Type*} [MeasurableSpace α]
    (c : α → α → ℝ) (μ : Measure α) : wassersteinCost c μ μ = 0 := by
  unfold wassersteinCost
  apply le_antisymm _ (zero_le)
  refine iSup_le fun _ => iSup_le fun _ => ?_
  simp

lemma wasserstein1_self {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ : Measure α) : wasserstein1 μ μ = 0 :=
  wassersteinCost_self (fun x y => dist x y) μ

/-- Symmetry: `wassersteinCost c μ ν = wassersteinCost c ν μ`.  The oscillation
test class `|f x − f y| ≤ c x y` is closed under `f ↦ −f`, so **no symmetry
assumption on `c`** is needed. -/
lemma wassersteinCost_comm {α : Type*} [MeasurableSpace α]
    (c : α → α → ℝ) (μ ν : Measure α) :
    wassersteinCost c μ ν = wassersteinCost c ν μ := by
  unfold wassersteinCost
  have hneg : ∀ (f : α → ℝ), (∀ x y, |f x - f y| ≤ c x y) →
      ∀ x y, |(-f) x - (-f) y| ≤ c x y := by
    intro f hf x y
    simp only [Pi.neg_apply]
    rw [show -f x - -f y = -(f x - f y) by ring, abs_neg]
    exact hf x y
  apply le_antisymm
  · refine iSup_le fun f => iSup_le fun hf => ?_
    refine le_iSup_of_le (-f) (le_iSup_of_le (hneg f hf) (le_of_eq ?_))
    simp only [Pi.neg_apply, integral_neg]
    congr 1; ring
  · refine iSup_le fun f => iSup_le fun hf => ?_
    refine le_iSup_of_le (-f) (le_iSup_of_le (hneg f hf) (le_of_eq ?_))
    simp only [Pi.neg_apply, integral_neg]
    congr 1; ring

lemma wasserstein1_comm {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ ν : Measure α) : wasserstein1 μ ν = wasserstein1 ν μ :=
  wassersteinCost_comm (fun x y => dist x y) μ ν

/-- Triangle inequality: `wassersteinCost c μ τ ≤ wassersteinCost c μ ν +
wassersteinCost c ν τ`.  **No triangle assumption on `c`** — the inequality is
the test-function integral decomposition (the same `f` is valid for all three
costs `wassersteinCost c · ·`). -/
lemma wassersteinCost_triangle {α : Type*} [MeasurableSpace α]
    (c : α → α → ℝ) (μ ν τ : Measure α) :
    wassersteinCost c μ τ ≤ wassersteinCost c μ ν + wassersteinCost c ν τ := by
  unfold wassersteinCost
  refine iSup_le fun f => iSup_le fun hf => ?_
  have hsplit : ∫ x, f x ∂μ - ∫ x, f x ∂τ =
      (∫ x, f x ∂μ - ∫ x, f x ∂ν) + (∫ x, f x ∂ν - ∫ x, f x ∂τ) := by ring
  rw [hsplit]
  calc ENNReal.ofReal _
      ≤ ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν)
          + ENNReal.ofReal (∫ x, f x ∂ν - ∫ x, f x ∂τ) :=
        ENNReal.ofReal_add_le
    _ ≤ (⨆ (g : α → ℝ) (_ : ∀ x y, |g x - g y| ≤ c x y),
            ENNReal.ofReal (∫ x, g x ∂μ - ∫ x, g x ∂ν))
        + (⨆ (g : α → ℝ) (_ : ∀ x y, |g x - g y| ≤ c x y),
            ENNReal.ofReal (∫ x, g x ∂ν - ∫ x, g x ∂τ)) := by
        gcongr
        · exact le_iSup_of_le f (le_iSup_of_le hf le_rfl)
        · exact le_iSup_of_le f (le_iSup_of_le hf le_rfl)

lemma wasserstein1_triangle {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ ν τ : Measure α) :
    wasserstein1 μ τ ≤ wasserstein1 μ ν + wasserstein1 ν τ :=
  wassersteinCost_triangle (fun x y => dist x y) μ ν τ

/-- Quantitative finite-moment bound for `wasserstein1`: the W₁ distance is
bounded by the sum of the two measures' first moments.

This refines `wasserstein1_lt_top_of_finite_moment` (which only states ≠⊤)
by providing the explicit upper bound `∫‖y‖dμ + ∫‖y‖dν`.  Used by the sup-W₁
pseudodistance on `VlasovMeasureCurve`s to derive finiteness from the
uniform first-moment bound. -/
lemma wasserstein1_le_moments_sum
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun y => ‖y‖) μ) (hν : Integrable (fun y => ‖y‖) ν) :
    wasserstein1 μ ν ≤ ENNReal.ofReal (∫ y, ‖y‖ ∂μ + ∫ y, ‖y‖ ∂ν) := by
  -- Same shape of proof as `wasserstein1_lt_top_of_finite_moment`, but
  -- producing the bound `ofReal M` itself instead of the consequent `< ⊤`.
  rw [wasserstein1_eq_iSup_lipschitz]
  refine iSup_le fun φ => iSup_le fun hφ => ?_
  apply ENNReal.ofReal_le_ofReal
  have hψ_bound : ∀ y, |φ y - φ 0| ≤ ‖y‖ := fun y => by
    have h_lip := hφ.dist_le_mul y 0
    rw [Real.dist_eq, dist_zero_right, NNReal.coe_one, one_mul] at h_lip
    exact h_lip
  have hφ_cont : Continuous φ := hφ.continuous
  have hφ_meas_μ : AEStronglyMeasurable φ μ := hφ_cont.aestronglyMeasurable
  have hφ_meas_ν : AEStronglyMeasurable φ ν := hφ_cont.aestronglyMeasurable
  have h_bound_abs : ∀ y, |φ y| ≤ |φ 0| + ‖y‖ := fun y => by
    calc |φ y| = |(φ y - φ 0) + φ 0| := by ring_nf
      _ ≤ |φ y - φ 0| + |φ 0| := abs_add_le _ _
      _ ≤ ‖y‖ + |φ 0| := by linarith [hψ_bound y]
      _ = |φ 0| + ‖y‖ := by ring
  have h_dom_μ : Integrable (fun y => |φ 0| + ‖y‖) μ :=
    (integrable_const _).add hμ
  have h_dom_ν : Integrable (fun y => |φ 0| + ‖y‖) ν :=
    (integrable_const _).add hν
  have hφ_int_μ : Integrable φ μ :=
    h_dom_μ.mono hφ_meas_μ (Filter.Eventually.of_forall fun y => by
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (norm_nonneg _))]
      exact h_bound_abs y)
  have hφ_int_ν : Integrable φ ν :=
    h_dom_ν.mono hφ_meas_ν (Filter.Eventually.of_forall fun y => by
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (norm_nonneg _))]
      exact h_bound_abs y)
  have h_int_μ_const : ∫ _ : E, φ 0 ∂μ = φ 0 := by
    simp [integral_const]
  have h_int_ν_const : ∫ _ : E, φ 0 ∂ν = φ 0 := by
    simp [integral_const]
  have h_int_μ_sub : ∫ y, (φ y - φ 0) ∂μ = ∫ y, φ y ∂μ - φ 0 := by
    rw [integral_sub hφ_int_μ (integrable_const _), h_int_μ_const]
  have h_int_ν_sub : ∫ y, (φ y - φ 0) ∂ν = ∫ y, φ y ∂ν - φ 0 := by
    rw [integral_sub hφ_int_ν (integrable_const _), h_int_ν_const]
  have h_diff_eq : ∫ y, φ y ∂μ - ∫ y, φ y ∂ν =
      ∫ y, (φ y - φ 0) ∂μ - ∫ y, (φ y - φ 0) ∂ν := by
    rw [h_int_μ_sub, h_int_ν_sub]; ring
  rw [h_diff_eq]
  have hψ_int_μ : Integrable (fun y => φ y - φ 0) μ :=
    hφ_int_μ.sub (integrable_const _)
  have hψ_int_ν : Integrable (fun y => φ y - φ 0) ν :=
    hφ_int_ν.sub (integrable_const _)
  have h_bound_μ : ∫ y, (φ y - φ 0) ∂μ ≤ ∫ y, ‖y‖ ∂μ := by
    calc ∫ y, (φ y - φ 0) ∂μ
        ≤ ∫ y, |φ y - φ 0| ∂μ :=
          integral_mono_ae hψ_int_μ hψ_int_μ.abs
            (Filter.Eventually.of_forall fun _ => le_abs_self _)
      _ ≤ ∫ y, ‖y‖ ∂μ :=
          integral_mono_ae hψ_int_μ.abs hμ (Filter.Eventually.of_forall hψ_bound)
  have h_bound_ν : -∫ y, (φ y - φ 0) ∂ν ≤ ∫ y, ‖y‖ ∂ν := by
    rw [← integral_neg]
    calc ∫ y, -(φ y - φ 0) ∂ν
        ≤ ∫ y, |φ y - φ 0| ∂ν :=
          integral_mono_ae hψ_int_ν.neg hψ_int_ν.abs
            (Filter.Eventually.of_forall fun y => neg_le_abs _)
      _ ≤ ∫ y, ‖y‖ ∂ν :=
          integral_mono_ae hψ_int_ν.abs hν (Filter.Eventually.of_forall hψ_bound)
  linarith

/-- **Cost-generic non-expansion under Lipschitz pushforward.**

If `T : α → β` is `L`-Lipschitz **with respect to the costs**
(`c_β (T x) (T y) ≤ L · c_α x y`) and `c_β` is dominated by the metric on `β`
(`c_β x y ≤ dist x y`, which makes every `c_β`-oscillation test function
1-Lipschitz, hence continuous and measurable — what `integral_map` needs), then
pushforward by `T` is `L`-non-expansive in `wassersteinCost`:
`wassersteinCost c_β (T_# μ) (T_# ν) ≤ L · wassersteinCost c_α μ ν`.

`wasserstein1_le_of_lipschitz_map` (`c = dist`, below) and the Wbar analog
(`c = fun x y => min (dist x y) 1`) are instances. -/
lemma wassersteinCost_le_of_lipschitz_map
    {α β : Type*}
    [MeasurableSpace α]
    [MeasurableSpace β] [PseudoMetricSpace β] [OpensMeasurableSpace β]
    (c_α : α → α → ℝ) (c_β : β → β → ℝ)
    (hc_β_le : ∀ x y, c_β x y ≤ dist x y)
    (T : α → β) (L : NNReal)
    (hT_cost : ∀ x y, c_β (T x) (T y) ≤ (L : ℝ) * c_α x y)
    (hT_meas : Measurable T)
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    wassersteinCost c_β (Measure.map T μ) (Measure.map T ν) ≤
      (L : ENNReal) * wassersteinCost c_α μ ν := by
  unfold wassersteinCost
  refine iSup_le fun g => iSup_le fun hg => ?_
  -- `c_β`-oscillation + `c_β ≤ dist` ⇒ `g` is 1-Lipschitz ⇒ continuous ⇒ measurable.
  have hg_lip : LipschitzWith 1 g := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, NNReal.coe_one, one_mul]
    exact le_trans (hg x y) (hc_β_le x y)
  have hg_meas : Measurable g := hg_lip.continuous.measurable
  rw [integral_map hT_meas.aemeasurable hg_meas.aestronglyMeasurable,
      integral_map hT_meas.aemeasurable hg_meas.aestronglyMeasurable]
  -- `|g(Tx) - g(Ty)| ≤ c_β(Tx,Ty) ≤ L·c_α x y`.
  have h_gT_osc : ∀ x y : α, |g (T x) - g (T y)| ≤ (L : ℝ) * c_α x y :=
    fun x y => le_trans (hg (T x) (T y)) (hT_cost x y)
  by_cases hL : L = 0
  · -- L = 0: `g ∘ T` is constant (oscillation ≤ 0), so the integral difference is 0.
    have hα_nonempty : Nonempty α := by
      by_contra h
      rw [not_nonempty_iff] at h
      have : μ Set.univ = 0 := by
        rw [Set.eq_empty_of_isEmpty (Set.univ : Set α)]; exact measure_empty
      rw [measure_univ] at this; exact one_ne_zero this
    obtain ⟨x₀⟩ := hα_nonempty
    have h_gT_const : ∀ x : α, g (T x) = g (T x₀) := by
      intro x
      have h0 : |g (T x) - g (T x₀)| ≤ 0 := by
        have := h_gT_osc x x₀; rw [hL, NNReal.coe_zero, zero_mul] at this; exact this
      have : g (T x) - g (T x₀) = 0 := abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _))
      linarith
    rw [funext h_gT_const]
    simp [integral_const, measureReal_def, measure_univ, sub_self, ENNReal.ofReal_zero]
  · -- L > 0: `h := (g ∘ T)/L` has `c_α`-oscillation; rescale.
    have hL_pos : (0 : ℝ) < (L : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hL)
    have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt hL_pos
    set h : α → ℝ := fun x => g (T x) / (L : ℝ) with h_def
    have h_osc : ∀ x y, |h x - h y| ≤ c_α x y := by
      intro x y
      have h_eq : |h x - h y| = |g (T x) - g (T y)| / (L : ℝ) := by
        simp only [h_def, ← sub_div, abs_div, abs_of_pos hL_pos]
      rw [h_eq, div_le_iff₀ hL_pos]
      calc |g (T x) - g (T y)| ≤ (L : ℝ) * c_α x y := h_gT_osc x y
        _ = c_α x y * (L : ℝ) := mul_comm _ _
    have h_int_factor :
        ∀ (κ : Measure α), ∫ x, g (T x) ∂κ = (L : ℝ) * ∫ x, h x ∂κ := by
      intro κ; simp_rw [h_def]; rw [integral_div, mul_div_cancel₀ _ hL_ne]
    have h_diff_factor : ∫ x, g (T x) ∂μ - ∫ x, g (T x) ∂ν =
        (L : ℝ) * (∫ x, h x ∂μ - ∫ x, h x ∂ν) := by
      rw [h_int_factor μ, h_int_factor ν]; ring
    rw [h_diff_factor, ENNReal.ofReal_mul (NNReal.coe_nonneg L), ENNReal.ofReal_coe_nnreal]
    refine mul_le_mul_of_nonneg_left ?_ (zero_le)
    exact le_iSup_of_le h (le_iSup_of_le h_osc le_rfl)

/-- **W₁ non-expansion under Lipschitz pushforward** — the `c = dist` instance of
`wassersteinCost_le_of_lipschitz_map`. -/
lemma wasserstein1_le_of_lipschitz_map
    {α β : Type*}
    [MeasurableSpace α] [PseudoMetricSpace α]
    [MeasurableSpace β] [PseudoMetricSpace β] [OpensMeasurableSpace β]
    (T : α → β) (L : NNReal) (hT : LipschitzWith L T) (hT_meas : Measurable T)
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    wasserstein1 (Measure.map T μ) (Measure.map T ν) ≤
      (L : ENNReal) * wasserstein1 μ ν :=
  wassersteinCost_le_of_lipschitz_map (fun x y => dist x y) (fun x y => dist x y)
    (fun _ _ => le_refl _) T L (fun x y => hT.dist_le_mul x y) hT_meas μ ν

/-- **Wbar-additivity sanity check.**  The truncated cost
`min(dist, 1)` satisfies both hypotheses of `wassersteinCost_le_of_lipschitz_map`
(`min(dist,1) ≤ dist`; and for 1-Lipschitz `T`,
`min(dist(Tx,Ty),1) ≤ min(dist x y, 1)`), so the property lemma drops in at
`c := fun x y => min (dist x y) 1`. -/
example {α β : Type*}
    [MeasurableSpace α] [PseudoMetricSpace α]
    [MeasurableSpace β] [PseudoMetricSpace β] [OpensMeasurableSpace β]
    (T : α → β) (hT : LipschitzWith 1 T) (hT_meas : Measurable T)
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    wassersteinCost (fun x y => min (dist x y) 1) (Measure.map T μ) (Measure.map T ν) ≤
      (1 : ENNReal) * wassersteinCost (fun x y => min (dist x y) 1) μ ν :=
  wassersteinCost_le_of_lipschitz_map _ _ (fun x y => min_le_left _ _) T 1
    (fun x y => by
      rw [NNReal.coe_one, one_mul]
      refine min_le_min ?_ (le_refl 1)
      have := hT.dist_le_mul x y; rwa [NNReal.coe_one, one_mul] at this)
    hT_meas μ ν

/-- **KR-dual lower bound for `wasserstein1`.**

For any 1-Lipschitz `f : α → ℝ` and any measures μ, ν on a pseudo-metric
measurable space, the (positive part of the) integral difference is a
lower bound on `W₁(μ, ν)`:
  `ENNReal.ofReal (∫ f dμ - ∫ f dν) ≤ wasserstein1 μ ν`.

This is the "easy direction" of the Kantorovich-Rubinstein dual
characterization — it is built into the definition `wasserstein1 :=
⨆ f hf, ENNReal.ofReal (∫ f dμ - ∫ f dν)` and follows by `le_iSup`.

Chained with `f → -f` 1-Lipschitz, it gives the
"W₁=0 → ∫f dμ = ∫f dν for 1-Lipschitz f" reduction used by the
separation lemma `wasserstein1_eq_zero_iff_measure_eq`.

**Cost-generic**: stated below for `wassersteinCost c` with `f`
of `c`-oscillation, no hypothesis on `c`; `wasserstein1_dual_lower_bound` is the
`c = dist` corollary. -/
lemma wassersteinCost_dual_lower_bound
    {α : Type*} [MeasurableSpace α]
    (c : α → α → ℝ) (μ ν : Measure α) (f : α → ℝ)
    (hf : ∀ x y, |f x - f y| ≤ c x y) :
    ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) ≤ wassersteinCost c μ ν := by
  unfold wassersteinCost
  exact le_iSup_of_le f (le_iSup_of_le hf le_rfl)

lemma wasserstein1_dual_lower_bound
    {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ ν : Measure α) (f : α → ℝ) (hf : LipschitzWith 1 f) :
    ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) ≤ wasserstein1 μ ν :=
  wassersteinCost_dual_lower_bound (fun x y => dist x y) μ ν f
    ((lipschitzWith_one_iff_oscillation f).mp hf)

/-- **Wbar-additivity across the property layer.**  The cost-generic
`_self`/`_comm`/`_triangle`/`_dual_lower_bound` carry no hypothesis on `c`, so
each instantiates at the truncated cost `min(dist, 1)` unconditionally — in
particular `_triangle` needs **no** triangle inequality on `c` (the inequality
is the test-function decomposition). -/
example {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ ν τ : Measure α) (f : α → ℝ) (hf : ∀ x y, |f x - f y| ≤ min (dist x y) 1) :
    wassersteinCost (fun x y => min (dist x y) 1) μ μ = 0 ∧
    wassersteinCost (fun x y => min (dist x y) 1) μ ν =
      wassersteinCost (fun x y => min (dist x y) 1) ν μ ∧
    wassersteinCost (fun x y => min (dist x y) 1) μ τ ≤
      wassersteinCost (fun x y => min (dist x y) 1) μ ν +
        wassersteinCost (fun x y => min (dist x y) 1) ν τ ∧
    ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) ≤
      wassersteinCost (fun x y => min (dist x y) 1) μ ν :=
  ⟨wassersteinCost_self _ μ, wassersteinCost_comm _ μ ν,
   wassersteinCost_triangle _ μ ν τ, wassersteinCost_dual_lower_bound _ μ ν f hf⟩

/-! ### `wassersteinBar` — the truncated (cutoff) Wasserstein-1 distance Wbar

`Wbar := wassersteinCost (min(dist, 1))` (Dobrushin 1979 §5).  The bounded cost
makes the dual test class *bounded* 1-Lipschitz, so Wbar metrizes narrow
convergence directly and is always finite (no moment hypotheses).  The property
layer instantiates verbatim from the cost-generic lemmas: `min(dist, 1)` is a
continuous pseudometric dominated by `dist`, so every hypothesis is met. -/

/-- The **truncated Wasserstein-1 distance** `Wbar` (Dobrushin 1979 §5): the
`c = min(dist, 1)` instance of `wassersteinCost`. -/
noncomputable def wassersteinBar {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ ν : Measure α) : ENNReal :=
  wassersteinCost (fun x y => min (dist x y) 1) μ ν

lemma wassersteinBar_self {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ : Measure α) : wassersteinBar μ μ = 0 :=
  wassersteinCost_self _ μ

lemma wassersteinBar_comm {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ ν : Measure α) : wassersteinBar μ ν = wassersteinBar ν μ :=
  wassersteinCost_comm _ μ ν

lemma wassersteinBar_triangle {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ ν τ : Measure α) :
    wassersteinBar μ τ ≤ wassersteinBar μ ν + wassersteinBar ν τ :=
  wassersteinCost_triangle _ μ ν τ

lemma wassersteinBar_dual_lower_bound {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α]
    (μ ν : Measure α) (f : α → ℝ) (hf : ∀ x y, |f x - f y| ≤ min (dist x y) 1) :
    ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) ≤ wassersteinBar μ ν :=
  wassersteinCost_dual_lower_bound _ μ ν f hf

/-- Wbar non-expansion under 1-Lipschitz pushforward: `Wbar(T_# μ, T_# ν) ≤ Wbar(μ, ν)`.
The cost-Lipschitz hypothesis is `min(dist(Tx,Ty),1) ≤ min(dist x y, 1)` (from
`dist(Tx,Ty) ≤ dist x y`). -/
lemma wassersteinBar_le_of_lipschitz_map {α β : Type*}
    [MeasurableSpace α] [PseudoMetricSpace α]
    [MeasurableSpace β] [PseudoMetricSpace β] [OpensMeasurableSpace β]
    (T : α → β) (hT : LipschitzWith 1 T) (hT_meas : Measurable T)
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    wassersteinBar (Measure.map T μ) (Measure.map T ν) ≤ wassersteinBar μ ν := by
  unfold wassersteinBar
  have h := wassersteinCost_le_of_lipschitz_map
    (fun x y => min (dist x y) 1) (fun x y => min (dist x y) 1)
    (fun x y => min_le_left _ _) T 1
    (fun x y => by
      rw [NNReal.coe_one, one_mul]
      refine min_le_min ?_ (le_refl 1)
      have := hT.dist_le_mul x y; rwa [NNReal.coe_one, one_mul] at this)
    hT_meas μ ν
  rwa [ENNReal.coe_one, one_mul] at h

/-- **Bounded-continuous integral equality from 1-Lipschitz integral equality.**

For probability measures μ, ν on a normed `AddCommGroup` `α` with the Borel
σ-algebra, both having finite first moments, if `∫ f dμ = ∫ f dν` for every
1-Lipschitz function `f : α → ℝ` (with appropriate integrability), then the same
equality holds for every bounded continuous function `f : α →ᵇ ℝ`.

**Proof.**
* Step A: upgrade the 1-Lipschitz hypothesis to arbitrary `K`-Lipschitz
  integrable functions by scaling into the 1-Lipschitz class (`c⁻¹ • g` with
  `c = K + 1`).
* Step B: closed sets `F` receive equal measure.  Thickened indicators
  `thickenedIndicator δ F` are bounded Lipschitz, so their integrals against μ
  and ν agree (Step A); letting `δ → 0` and using
  `tendsto_lintegral_thickenedIndicator_of_isClosed` gives `μ F = ν F`.
* Closed sets form a π-system generating the Borel σ-algebra, so `μ = ν` by
  `ext_of_generate_finite`; equality of all BC integrals is then immediate. -/
theorem integral_boundedContinuous_eq_of_integral_lipschitz_eq
    {α : Type*}
    [MeasurableSpace α] [NormedAddCommGroup α] [BorelSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (_h_1lip : ∀ (f : α → ℝ), LipschitzWith 1 f →
               Integrable f μ → Integrable f ν →
               ∫ x, f x ∂μ = ∫ x, f x ∂ν) :
    ∀ (f : BoundedContinuousFunction α ℝ), ∫ x, f x ∂μ = ∫ x, f x ∂ν := by
  -- It suffices to prove `μ = ν`; then equality of all BC integrals is immediate.
  suffices hμν : μ = ν by intro f; rw [hμν]
  -- Step A: upgrade the 1-Lipschitz hypothesis to arbitrary `K`-Lipschitz integrable
  -- functions, by scaling into the 1-Lipschitz class (`c⁻¹ • g` with `c = K + 1`).
  have h_lip_eq : ∀ (g : α → ℝ) (K : NNReal), LipschitzWith K g →
      Integrable g μ → Integrable g ν → ∫ x, g x ∂μ = ∫ x, g x ∂ν := by
    intro g K hg hgμ hgν
    set c : ℝ := (K : ℝ) + 1 with hc
    have hc_pos : (0 : ℝ) < c := by rw [hc]; positivity
    have hcK : (K : ℝ) ≤ c := by rw [hc]; linarith
    have hcK1 : c⁻¹ * (K : ℝ) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hcK (le_of_lt (inv_pos.mpr hc_pos))
      rwa [inv_mul_cancel₀ hc_pos.ne'] at h
    have h1 : LipschitzWith 1 (fun x => c⁻¹ * g x) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [NNReal.coe_one, one_mul]
      have key : dist (c⁻¹ * g x) (c⁻¹ * g y) = c⁻¹ * dist (g x) (g y) := by
        rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hc_pos)]
      calc dist (c⁻¹ * g x) (c⁻¹ * g y)
          = c⁻¹ * dist (g x) (g y) := key
        _ ≤ c⁻¹ * ((K : ℝ) * dist x y) :=
            mul_le_mul_of_nonneg_left (hg.dist_le_mul x y) (le_of_lt (inv_pos.mpr hc_pos))
        _ = (c⁻¹ * (K : ℝ)) * dist x y := by ring
        _ ≤ 1 * dist x y := mul_le_mul_of_nonneg_right hcK1 dist_nonneg
        _ = dist x y := one_mul _
    have h_scaled : ∫ x, c⁻¹ * g x ∂μ = ∫ x, c⁻¹ * g x ∂ν :=
      _h_1lip (fun x => c⁻¹ * g x) h1 (hgμ.const_mul c⁻¹) (hgν.const_mul c⁻¹)
    rw [integral_const_mul, integral_const_mul] at h_scaled
    exact mul_left_cancel₀ (inv_ne_zero hc_pos.ne') h_scaled
  -- Step B: closed sets receive equal measure, via thickened-indicator integrals.
  have key : ∀ F : Set α, IsClosed F → μ F = ν F := by
    intro F hF
    have δs_pos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
    have δs_lim : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hμ_lim := tendsto_lintegral_thickenedIndicator_of_isClosed μ hF δs_pos δs_lim
    have hν_lim := tendsto_lintegral_thickenedIndicator_of_isClosed ν hF δs_pos δs_lim
    have hlint_eq : ∀ n : ℕ,
        (∫⁻ ω, (thickenedIndicator (δs_pos n) F ω : ENNReal) ∂μ)
          = ∫⁻ ω, (thickenedIndicator (δs_pos n) F ω : ENNReal) ∂ν := by
      intro n
      rw [lintegral_coe_eq_integral (fun ω => thickenedIndicator (δs_pos n) F ω)
            (integrable_thickenedIndicator (μ := μ) F (δs_pos n)),
          lintegral_coe_eq_integral (fun ω => thickenedIndicator (δs_pos n) F ω)
            (integrable_thickenedIndicator (μ := ν) F (δs_pos n))]
      congr 1
      exact h_lip_eq _ _
        ((NNReal.isometry_coe.lipschitz).comp (lipschitzWith_thickenedIndicator (δs_pos n) F))
        (integrable_thickenedIndicator (μ := μ) F (δs_pos n))
        (integrable_thickenedIndicator (μ := ν) F (δs_pos n))
    simp_rw [hlint_eq] at hμ_lim
    exact tendsto_nhds_unique hμ_lim hν_lim
  -- Closed sets form a π-system generating the Borel σ-algebra.
  apply ext_of_generate_finite _ ?_ isPiSystem_isClosed
  · exact fun F hF => key F hF
  · exact key Set.univ isClosed_univ
  · rw [BorelSpace.measurable_eq (α := α), borel_eq_generateFrom_isClosed]


/-! ## Further `wasserstein1` properties
    (separation, narrow-liminf LSC, ofReal-exp monotonicity). -/

/-- **Separation lemma for `wasserstein1`.**

For probability measures μ, ν on a Polish normed space with finite
first moments, `W₁(μ, ν) = 0` iff `μ = ν`.

`wasserstein1` enters the proof body only through its property lemmas:
* `wasserstein1_self` (backward direction).
* `wasserstein1_dual_lower_bound` (W₁=0 → 1-Lipschitz integral equality).

The substantive middle (1-Lipschitz equality → BC equality) is
`integral_boundedContinuous_eq_of_integral_lipschitz_eq` (above); the final
step (BC equality → μ = ν) routes through Mathlib's
`ext_of_forall_integral_eq_of_IsFiniteMeasure`. -/
lemma wasserstein1_eq_zero_iff_measure_eq
    {α : Type*}
    [MeasurableSpace α] [NormedAddCommGroup α] [BorelSpace α]
    [HasOuterApproxClosed α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    wasserstein1 μ ν = 0 ↔ μ = ν := by
  constructor
  · -- Forward (substantive): W₁=0 → μ=ν.
    intro h_w1_zero
    -- Step 1 (property-only via `wasserstein1_dual_lower_bound`):
    -- W₁=0 → ∫f dμ = ∫f dν for every integrable 1-Lipschitz f.
    have h_1lip_eq : ∀ (f : α → ℝ), LipschitzWith 1 f →
                     Integrable f μ → Integrable f ν →
                     ∫ x, f x ∂μ = ∫ x, f x ∂ν := by
      intro f hf _hf_int_μ _hf_int_ν
      -- Apply the property at f and -f; combine.
      have h_pos : ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) ≤ wasserstein1 μ ν :=
        wasserstein1_dual_lower_bound μ ν f hf
      have hf_neg : LipschitzWith 1 (-f) := by
        simpa using hf.neg
      have h_neg :
          ENNReal.ofReal (∫ x, (-f) x ∂μ - ∫ x, (-f) x ∂ν) ≤ wasserstein1 μ ν :=
        wasserstein1_dual_lower_bound μ ν (-f) hf_neg
      rw [h_w1_zero] at h_pos h_neg
      -- ENNReal.ofReal ≤ 0 (in ENNReal) iff = 0 iff the real argument is ≤ 0.
      have h_pos_eq : ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν) = 0 :=
        le_antisymm h_pos (zero_le)
      have h_neg_eq : ENNReal.ofReal (∫ x, (-f) x ∂μ - ∫ x, (-f) x ∂ν) = 0 :=
        le_antisymm h_neg (zero_le)
      have h_diff_pos : ∫ x, f x ∂μ - ∫ x, f x ∂ν ≤ 0 :=
        (ENNReal.ofReal_eq_zero).mp h_pos_eq
      have h_diff_neg : ∫ x, (-f) x ∂μ - ∫ x, (-f) x ∂ν ≤ 0 :=
        (ENNReal.ofReal_eq_zero).mp h_neg_eq
      -- ∫(-f) dμ - ∫(-f) dν = -(∫f dμ - ∫f dν).
      have h_neg_int : ∫ x, (-f) x ∂μ - ∫ x, (-f) x ∂ν =
          -(∫ x, f x ∂μ - ∫ x, f x ∂ν) := by
        simp only [Pi.neg_apply, integral_neg]; ring
      rw [h_neg_int] at h_diff_neg
      linarith
    -- Step 2: 1-Lipschitz integral equality → BC integral equality.
    -- See `integral_boundedContinuous_eq_of_integral_lipschitz_eq` above.
    have h_bc_eq :
        ∀ (f : BoundedContinuousFunction α ℝ), ∫ x, f x ∂μ = ∫ x, f x ∂ν :=
      integral_boundedContinuous_eq_of_integral_lipschitz_eq μ ν h_1lip_eq
    -- Step 3 (Mathlib `ext_of_forall_integral_eq_of_IsFiniteMeasure`): BC equality → μ=ν.
    exact ext_of_forall_integral_eq_of_IsFiniteMeasure h_bc_eq
  · -- Backward (trivial): μ=ν → W₁=0, via the property `wasserstein1_self`.
    intro h_eq
    subst h_eq
    exact wasserstein1_self μ

/-- **Static narrow lower-semicontinuity of `wasserstein1`** (Villani, Thm 6.9,
in KR-dual form).  If `νs n → ν` narrowly (tested against bounded continuous
functions) and `μ, ν` have finite first moments, then
`W₁(μ, ν) ≤ liminf_n W₁(μ, νs n)`.

This is the *static* optimal-transport fact — pure lower semicontinuity of the
metric under weak convergence, with no flow/superposition.  Prokhorov supplies
the narrow limit; this upgrades a W₁-Cauchy sequence to W₁-convergence.
Distinct from the *dynamic* narrow continuity along a Vlasov flow, which
genuinely needs DiPerna–Lions superposition; the static LSC does not.

**Proof.**  For each 1-Lipschitz `φ` truncate to `φ_k = clamp(φ, -k, k)` (bounded
and 1-Lipschitz).  Narrow convergence gives `∫ φ_k d(νs n) → ∫ φ_k dν`, and the
dual lower bound gives `ofReal(∫φ_k dμ − ∫φ_k d(νs n)) ≤ W₁(μ, νs n)`; passing to
the liminf in `n` yields `ofReal(∫φ_k dμ − ∫φ_k dν) ≤ liminf_n W₁(μ, νs n)`.  Then
`k → ∞` by dominated convergence (`|φ_k| ≤ |φ 0| + ‖·‖`, integrable since μ, ν
have finite first moment) recovers `ofReal(∫φ dμ − ∫φ dν) ≤ liminf_n W₁`.  Taking
the `⨆` over `φ` closes it.  The narrow hypothesis is taken in
bounded-continuous-test form (what `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`
exposes), so the `exists_wasserstein1_limit_of_cauchy` caller feeds it directly
from Prokhorov. -/
lemma wasserstein1_le_liminf_of_narrow
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (hμ_int : Integrable (fun y => ‖y‖) μ)
    (νs : ℕ → Measure E)
    (ν : Measure E) [IsProbabilityMeasure ν] (hν_int : Integrable (fun y => ‖y‖) ν)
    (h_narrow : ∀ g : BoundedContinuousFunction E ℝ,
      Filter.Tendsto (fun n => ∫ x, g x ∂(νs n)) Filter.atTop (nhds (∫ x, g x ∂ν))) :
    wasserstein1 μ ν ≤ Filter.liminf (fun n => wasserstein1 μ (νs n)) Filter.atTop := by
  rw [wasserstein1_eq_iSup_lipschitz]
  refine iSup_le fun f => iSup_le fun hf => ?_
  -- `f` is integrable wrt μ and ν via the dominator `|f x| ≤ |f 0| + ‖x‖`.
  have hf_dom : ∀ x : E, |f x| ≤ |f 0| + ‖x‖ := by
    intro x
    have hd : |f x - f 0| ≤ ‖x‖ := by
      have := hf.dist_le_mul x 0
      rwa [Real.dist_eq, NNReal.coe_one, one_mul, dist_zero_right] at this
    have h2 := abs_sub_le (f x) (f 0) 0
    simp only [sub_zero] at h2
    linarith
  have hf_cont : Continuous f := hf.continuous
  have hf_int_μ : Integrable f μ :=
    ((integrable_const |f 0|).add hμ_int).mono' hf_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hf_dom x)
  have hf_int_ν : Integrable f ν :=
    ((integrable_const |f 0|).add hν_int).mono' hf_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hf_dom x)
  -- Truncations `f_k = clamp(f, -k, k)`.
  set fR : ℕ → E → ℝ := fun k x => max (-(k : ℝ)) (min (f x) (k : ℝ)) with hfR_def
  have hfR_lip : ∀ k : ℕ, LipschitzWith 1 (fR k) := by
    intro k
    have hmin : LipschitzWith 1 (fun x => min (f x) (k : ℝ)) := by
      have h := hf.min (LipschitzWith.const (k : ℝ))
      rwa [max_eq_left (zero_le)] at h
    have h := (LipschitzWith.const (-(k : ℝ))).max hmin
    rwa [max_eq_right (zero_le)] at h
  have hfR_cont : ∀ k, Continuous (fR k) := fun k => (hfR_lip k).continuous
  have hfR_bdd : ∀ (k : ℕ) (x : E), |fR k x| ≤ (k : ℝ) := by
    intro k x
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  -- Clamp is a contraction toward `[-k, k]`: `|f_k x| ≤ |f x|`.
  have habs_clamp : ∀ (a kk : ℝ), 0 ≤ kk → |max (-kk) (min a kk)| ≤ |a| := by
    intro a kk hkk
    rw [abs_le]
    refine ⟨le_trans (le_min (neg_abs_le a) (by linarith [abs_nonneg a])) (le_max_right _ _),
      max_le (by linarith [abs_nonneg a]) ((min_le_left a kk).trans (le_abs_self a))⟩
  have h_dom : ∀ (k : ℕ) (x : E), ‖fR k x‖ ≤ |f 0| + ‖x‖ := by
    intro k x
    rw [Real.norm_eq_abs]
    exact (habs_clamp (f x) (k : ℝ) (Nat.cast_nonneg k)).trans (hf_dom x)
  -- Each truncation as a bounded continuous function (for the narrow hypothesis).
  set gR : ℕ → BoundedContinuousFunction E ℝ := fun k =>
    BoundedContinuousFunction.mkOfBound ⟨fR k, hfR_cont k⟩ (2 * (k : ℝ))
      (fun x y => by
        have hx := hfR_bdd k x; have hy := hfR_bdd k y
        rw [abs_le] at hx hy
        simp only [ContinuousMap.coe_mk, Real.dist_eq]
        rw [abs_le]; constructor <;> linarith) with hgR_def
  -- Per-truncation bound: `ofReal(∫f_k dμ − ∫f_k dν) ≤ liminf_n W₁(μ, νs n)`.
  have h_per_k : ∀ k : ℕ,
      ENNReal.ofReal (∫ x, fR k x ∂μ - ∫ x, fR k x ∂ν) ≤
        Filter.liminf (fun n => wasserstein1 μ (νs n)) Filter.atTop := by
    intro k
    have h_tend : Filter.Tendsto (fun n => ∫ x, fR k x ∂(νs n)) Filter.atTop
        (nhds (∫ x, fR k x ∂ν)) := by
      have h := h_narrow (gR k)
      simp only [hgR_def, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk] at h
      exact h
    have h_tend2 : Filter.Tendsto
        (fun n => ENNReal.ofReal (∫ x, fR k x ∂μ - ∫ x, fR k x ∂(νs n)))
        Filter.atTop (nhds (ENNReal.ofReal (∫ x, fR k x ∂μ - ∫ x, fR k x ∂ν))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.sub h_tend)
    have h_le : ∀ n, ENNReal.ofReal (∫ x, fR k x ∂μ - ∫ x, fR k x ∂(νs n)) ≤
        wasserstein1 μ (νs n) := fun n =>
      wasserstein1_dual_lower_bound μ (νs n) (fR k) (hfR_lip k)
    calc ENNReal.ofReal (∫ x, fR k x ∂μ - ∫ x, fR k x ∂ν)
        = Filter.liminf
            (fun n => ENNReal.ofReal (∫ x, fR k x ∂μ - ∫ x, fR k x ∂(νs n)))
            Filter.atTop :=
          h_tend2.liminf_eq.symm
      _ ≤ Filter.liminf (fun n => wasserstein1 μ (νs n)) Filter.atTop :=
          Filter.liminf_le_liminf (Filter.Eventually.of_forall h_le)
  -- `k → ∞`: dominated convergence on μ and ν.
  have h_ptwise : ∀ x : E, Filter.Tendsto (fun k => fR k x) Filter.atTop (nhds (f x)) := by
    intro x
    have h_ev : ∀ᶠ k in Filter.atTop, fR k x = f x := by
      filter_upwards [Filter.eventually_ge_atTop ⌈|f x|⌉₊] with k hk
      have hk' : |f x| ≤ (k : ℝ) := (Nat.le_ceil |f x|).trans (by exact_mod_cast hk)
      simp only [hfR_def]
      rw [min_eq_left ((le_abs_self (f x)).trans hk'),
          max_eq_right (le_trans (neg_le_neg hk') (neg_abs_le (f x)))]
    exact tendsto_const_nhds.congr' (h_ev.mono fun k hk => hk.symm)
  have h_dct_μ :
      Filter.Tendsto (fun k => ∫ x, fR k x ∂μ) Filter.atTop (nhds (∫ x, f x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => |f 0| + ‖x‖)
      (fun k => (hfR_cont k).aestronglyMeasurable) ((integrable_const |f 0|).add hμ_int)
      (fun k => Filter.Eventually.of_forall fun x => h_dom k x)
      (Filter.Eventually.of_forall h_ptwise)
  have h_dct_ν :
      Filter.Tendsto (fun k => ∫ x, fR k x ∂ν) Filter.atTop (nhds (∫ x, f x ∂ν)) :=
    tendsto_integral_of_dominated_convergence (fun x => |f 0| + ‖x‖)
      (fun k => (hfR_cont k).aestronglyMeasurable) ((integrable_const |f 0|).add hν_int)
      (fun k => Filter.Eventually.of_forall fun x => h_dom k x)
      (Filter.Eventually.of_forall h_ptwise)
  have h_dct : Filter.Tendsto
      (fun k => ENNReal.ofReal (∫ x, fR k x ∂μ - ∫ x, fR k x ∂ν))
      Filter.atTop (nhds (ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, f x ∂ν))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (h_dct_μ.sub h_dct_ν)
  exact le_of_tendsto' h_dct h_per_k

/-- For C > 0 and 0 ≤ s ≤ t, we have
ENNReal.ofReal (Real.exp (C * s)) ≤ ENNReal.ofReal (Real.exp (C * t)).
This is the monotonicity of the exponential bound in time. -/
lemma wasserstein1_ofReal_exp_monotone
    (C : ℝ) (hC : 0 < C) (s t : ℝ) (hst : s ≤ t) :
    ENNReal.ofReal (Real.exp (C * s)) ≤ ENNReal.ofReal (Real.exp (C * t)) := by
  apply ENNReal.ofReal_le_ofReal
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hst hC.le)

-- `dobrushin_package_exists` and `dobrushin`
-- (the .tex thm:dobrushin marquee) live in
-- `LeanPool/Vlasov/OT/WellPosedness.lean` §10, alongside the theorem ladder
-- their proofs compose against (items 5/6 + W1ContOn + Gronwall lift + ennreal
-- bound).  `meanFieldLimit` consumes the Dobrushin estimate as a hypothesis
-- (`hDobrushin : ∀ N, DobrushinStabilityEstimate ...`) rather than calling
-- `dobrushin` directly.

/-! ## Equation (Dobrushin stability estimate) (`tex: eq:dobrushin`) -/

end Vlasov
