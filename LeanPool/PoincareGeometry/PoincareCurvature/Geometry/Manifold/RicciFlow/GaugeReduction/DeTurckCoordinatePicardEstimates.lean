/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeReduction

/-! # De Turck Coordinate Picard Estimates -/

@[expose] public noncomputable section

open Metric Set
open scoped Manifold ContDiff Topology NNReal

namespace RicciFlow

/-!
# Coordinate Picard–Lindelöf estimates for the DeTurck gauge field

This module proves the seven component estimates required by
`ModelGaugeFlowODE.isPicardLindelof_variationalVectorField_of_component_closedBall_continuity`
for the coordinate expression of the intrinsic DeTurck gauge field:

* `hf_lip`, `hDf_lip` : spatial Lipschitz bounds on a closed coordinate ball,
* `hf_bound`, `hD_bound` : uniform norm bounds on that ball,
* `hA_bound` : operator-norm bound on the initial variational ball,
* `hf_cont`, `hDf_cont` : continuity in time at fixed space points,
* `hmul` : the Picard interval-size inequality, for an explicit choice of
  `tmin`, `tmax`, `r`.

## Definitions

For a metric family `g`, a background connection family `background`, and a base
point `p₀`, `deTurckGaugeCoordinateField g background p₀ : ℝ → E → E` is the
chart representative of the gauge field in `extChartAt I p₀`, and
`deTurckGaugeCoordinateDerivative` is its spatial derivative `fderiv ℝ`.

CONVENTION: `intrinsicDeTurckGaugeField` is the *negated* DeTurck vector field;
the definitions below preserve this negation (the chart differential is linear).

## Proved vs. assumed

The main theorem `deTurckGaugeCoordinatePicardEstimates` proves all seven
estimates (plus `hmul`) from an explicit regularity package:

* `hreg` : the coordinate field is `C²` in space, uniformly for `t` in a
  reference time interval;
* `hjoint` : joint time–space continuity of the field and its derivative;
* `hjoint2` : joint time–space continuity of the second derivative.

The passage from this package to the seven estimates is proved here with no
`sorry`, using standard Mathlib lemmas (mean value theorem on convex sets,
compactness bounds).  The regularity package itself is **not** proved in the
repository — see "Missing regularity" below — and is therefore taken as an
explicit hypothesis, stated precisely.

## Missing regularity (exact statement)

The following is NOT established anywhere in the repository.  Let
`f := deTurckGaugeCoordinateField (I := I) (M := M) g background p₀`,
`y₀ := extChartAt I p₀ p₀`.  The missing input is:

> For every `t₀ : ℝ` and `a : ℝ≥0` with `0 < (a : ℝ)`:
> 1. `∀ t ∈ Icc (t₀ - 1) (t₀ + 1), ContDiffOn ℝ 2 (f t) (ball y₀ ((a : ℝ) + 1))`;
> 2. `ContinuousOn (fun p : ℝ × E => (f p.1 p.2, fderiv ℝ (f p.1) p.2))
>      (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ (a : ℝ))`;
> 3. `ContinuousOn (fun p : ℝ × E => fderiv ℝ (fderiv ℝ (f p.1)) p.2)
>      (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ (a : ℝ))`.

What the repository *does* contain: at fixed time `t`, the (raised, unnegated)
DeTurck vector field section is `C¹` on a patch —
`intrinsicDeTurckVectorField_contMDiffOn_of_contMDiffOn_intrinsicDeTurckOneForm`
gives `ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1` — and negation preserves this for the
gauge field.  What is missing: (a) the upgrade from `C¹` to `C²` (needed for the
Lipschitz bound on the derivative, `hDf_lip`), even in fixed-time form; and
(b) *any* time regularity — `MetricFamily` and `ConnectionFamily` carry no
time-continuity assumptions, so joint time–space continuity of the coordinate
field (needed for `hf_cont`, `hDf_cont`, and the uniform-in-time bounds
`hf_bound`, `hD_bound`) is entirely absent.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

/-- Coordinate expression of the DeTurck gauge field in the extended chart
`extChartAt I p₀`: the chart representative
`y ↦ D(extChartAt I p₀) x (V t x)`, identified with `E` via
`NormedSpace.fromTangentSpace`, where `x = (extChartAt I p₀).symm y` and
`V = intrinsicDeTurckGaugeField g background`.

CONVENTION: `intrinsicDeTurckGaugeField` is the *negated* DeTurck vector field;
this definition preserves the negation. -/
noncomputable def deTurckGaugeCoordinateField
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (p₀ : M) : ℝ → E → E :=
  fun t y =>
    let φ := extChartAt I p₀
    let x := φ.symm y
    NormedSpace.fromTangentSpace (φ x)
      (mfderiv I 𝓘(ℝ, E) φ x
        (intrinsicDeTurckGaugeField (I := I) (M := M) g background t x))

/-- Spatial derivative of the DeTurck gauge coordinate field. -/
noncomputable def deTurckGaugeCoordinateDerivative
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (p₀ : M) : ℝ → E → E →L[ℝ] E :=
  fun t y => fderiv ℝ (deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ t) y

/-- Abstract Picard-estimate assembly.

From `C²`-in-space regularity (uniform in time) plus joint time–space continuity
of the field, its derivative, and its second derivative, all seven
Picard–Lindelöf component estimates follow on a suitably small time interval
around `t₀`.  The proof is pure analysis: the mean value theorem on the convex
compact ball `closedBall y₀ a`, plus uniform bounds from compactness of the
reference space-time product. -/
theorem picardEstimates_of_contDiffOn_two_and_jointContinuity
    {f : ℝ → E → E} {y₀ : E} {t₀ : ℝ} {a : ℝ≥0} (ha : 0 < (a : ℝ))
    (A₀ : E →L[ℝ] E)
    (hreg : ∀ t ∈ Icc (t₀ - 1) (t₀ + 1),
      ContDiffOn ℝ 2 (f t) (ball y₀ ((a : ℝ) + 1)))
    (hjoint : ContinuousOn (fun p : ℝ × E => (f p.1 p.2, fderiv ℝ (f p.1) p.2))
      (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ (a : ℝ)))
    (hjoint2 : ContinuousOn (fun p : ℝ × E => fderiv ℝ (fderiv ℝ (f p.1)) p.2)
      (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ (a : ℝ))) :
    ∃ (tmin tmax : ℝ) (r Kf KD Lf BA BD : ℝ≥0),
      (∀ t ∈ Icc tmin tmax, LipschitzOnWith Kf (f t) (closedBall y₀ ↑a)) ∧
      (∀ t ∈ Icc tmin tmax, LipschitzOnWith KD (fderiv ℝ (f t)) (closedBall y₀ ↑a)) ∧
      (∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall y₀ ↑a, ‖f t y‖ ≤ ↑Lf) ∧
      (∀ A ∈ closedBall A₀ ↑a, ‖A‖₊ ≤ BA) ∧
      (∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall y₀ ↑a, ‖fderiv ℝ (f t) y‖₊ ≤ BD) ∧
      (∀ y ∈ closedBall y₀ ↑a, ContinuousOn (fun t : ℝ => f t y) (Icc tmin tmax)) ∧
      (∀ y ∈ closedBall y₀ ↑a,
        ContinuousOn (fun t : ℝ => fderiv ℝ (f t) y) (Icc tmin tmax)) ∧
      (↑(max Lf (BD * BA)) * max (tmax - t₀) (t₀ - tmin) ≤ ↑a - ↑r) := by
  -- The reference space-time product is compact.
  have hprod : IsCompact (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ (a : ℝ)) :=
    isCompact_Icc.prod (isCompact_closedBall y₀ _)
  -- Split the joint continuity into components.
  have hjoint_fst : ContinuousOn (fun p : ℝ × E => f p.1 p.2)
      (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ (a : ℝ)) := hjoint.fst
  have hjoint_snd : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2)
      (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ (a : ℝ)) := hjoint.snd
  -- Uniform real bounds on the compact reference product.
  obtain ⟨Cf, hCf⟩ := IsCompact.exists_bound_of_continuousOn hprod hjoint_fst
  obtain ⟨CD, hCD⟩ := IsCompact.exists_bound_of_continuousOn hprod hjoint_snd
  obtain ⟨CD2, hCD2⟩ := IsCompact.exists_bound_of_continuousOn hprod hjoint2
  -- Nonnegative (nnnorm) versions of the bounds.
  have hCf_nn : ∀ t ∈ Icc (t₀ - 1) (t₀ + 1), ∀ y ∈ closedBall y₀ (↑a),
      ‖f t y‖₊ ≤ ‖Cf‖₊ := by
    intro t ht y hy
    have h : ‖f t y‖ ≤ |Cf| := le_trans (hCf (t, y) ⟨ht, hy⟩) (le_abs_self Cf)
    rw [← NNReal.coe_le_coe]
    simp only [coe_nnnorm]
    calc ‖f t y‖ ≤ |Cf| := h
      _ = ‖Cf‖ := (Real.norm_eq_abs Cf).symm
  have hCD_nn : ∀ t ∈ Icc (t₀ - 1) (t₀ + 1), ∀ y ∈ closedBall y₀ (↑a),
      ‖fderiv ℝ (f t) y‖₊ ≤ ‖CD‖₊ := by
    intro t ht y hy
    have h : ‖fderiv ℝ (f t) y‖ ≤ |CD| :=
      le_trans (hCD (t, y) ⟨ht, hy⟩) (le_abs_self CD)
    rw [← NNReal.coe_le_coe]
    simp only [coe_nnnorm]
    calc ‖fderiv ℝ (f t) y‖ ≤ |CD| := h
      _ = ‖CD‖ := (Real.norm_eq_abs CD).symm
  have hCD2_nn : ∀ t ∈ Icc (t₀ - 1) (t₀ + 1), ∀ y ∈ closedBall y₀ (↑a),
      ‖fderiv ℝ (fderiv ℝ (f t)) y‖₊ ≤ ‖CD2‖₊ := by
    intro t ht y hy
    have h : ‖fderiv ℝ (fderiv ℝ (f t)) y‖ ≤ |CD2| :=
      le_trans (hCD2 (t, y) ⟨ht, hy⟩) (le_abs_self CD2)
    rw [← NNReal.coe_le_coe]
    simp only [coe_nnnorm]
    calc ‖fderiv ℝ (fderiv ℝ (f t)) y‖ ≤ |CD2| := h
      _ = ‖CD2‖ := (Real.norm_eq_abs CD2).symm
  -- Per-time differentiability from the C² hypothesis.
  have hdiff1 : ∀ t ∈ Icc (t₀ - 1) (t₀ + 1),
      DifferentiableOn ℝ (f t) (ball y₀ ((a : ℝ) + 1)) := by
    intro t ht
    exact (hreg t ht).differentiableOn (by simp)
  have hdiff2 : ∀ t ∈ Icc (t₀ - 1) (t₀ + 1),
      DifferentiableOn ℝ (fderiv ℝ (f t)) (ball y₀ ((a : ℝ) + 1)) := by
    intro t ht
    have h2 : ContDiffOn ℝ (1 + 1) (f t) (ball y₀ ((a : ℝ) + 1)) := hreg t ht
    obtain ⟨-, -, hDf1⟩ :=
      (contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball).mp h2
    exact hDf1.differentiableOn (by simp)
  -- The closed ball sits inside the open ball where C² holds.
  have hball_sub : closedBall y₀ (↑a) ⊆ ball y₀ (↑a + 1) := by
    intro y hy
    rw [mem_closedBall] at hy
    rw [mem_ball]
    calc dist y y₀ ≤ (a : ℝ) := hy
      _ < (a : ℝ) + 1 := by linarith
  -- Combined factor P and remaining radius X.
  set P : ℝ≥0 := max ‖Cf‖₊ (‖CD‖₊ * (‖A₀‖₊ + a)) with hP_def
  have hP_nn : (0 : ℝ) ≤ ((P : ℝ≥0) : ℝ) := by positivity
  set X : ℝ := (a : ℝ) - ((a / 2 : ℝ≥0) : ℝ) with hX_def
  have hX_nn : 0 ≤ X := by
    have hr : ((a / 2 : ℝ≥0) : ℝ) = (a : ℝ) / 2 := by
      rw [NNReal.coe_div]
      norm_num
    have h1 : (0 : ℝ) ≤ (a : ℝ) := by positivity
    rw [hX_def, hr]
    linarith
  -- Time radius δ, small enough for the Picard inequality.
  set δ : ℝ := min 1 (X / (↑P + 1)) with hδ_def
  have hδ_nn : 0 ≤ δ := by
    rw [hδ_def]
    exact le_min zero_le_one (div_nonneg hX_nn (by positivity))
  have hδ_le1 : δ ≤ 1 := by rw [hδ_def]; exact min_le_left _ _
  have hδ_le : δ ≤ X / (↑P + 1) := by rw [hδ_def]; exact min_le_right _ _
  -- The small time interval sits inside the reference interval.
  have hIcc_sub : Icc (t₀ - δ) (t₀ + δ) ⊆ Icc (t₀ - 1) (t₀ + 1) := by
    intro t ht
    simp only [mem_Icc] at ht ⊢
    constructor <;> linarith
  refine ⟨t₀ - δ, t₀ + δ, a / 2, ‖CD‖₊, ‖CD2‖₊, ‖Cf‖₊, ‖A₀‖₊ + a, ‖CD‖₊,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- hf_lip: C¹ with bounded derivative on the convex ball gives Lipschitz.
    intro t ht
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) _ _ (convex_closedBall y₀ ↑a)
    · intro y hy
      exact (hdiff1 t (hIcc_sub ht)).differentiableAt
        (isOpen_ball.mem_nhds (hball_sub hy))
    · intro y hy
      exact hCD_nn t (hIcc_sub ht) y hy
  · -- hDf_lip: the derivative is C¹ with bounded second derivative.
    intro t ht
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) _ _ (convex_closedBall y₀ ↑a)
    · intro y hy
      exact (hdiff2 t (hIcc_sub ht)).differentiableAt
        (isOpen_ball.mem_nhds (hball_sub hy))
    · intro y hy
      exact hCD2_nn t (hIcc_sub ht) y hy
  · -- hf_bound: uniform bound from joint continuity on the compact product.
    intro t ht y hy
    have h := hCf_nn t (hIcc_sub ht) y hy
    -- goal: ‖f t y‖ ≤ ↑(‖Cf‖₊)
    calc ‖f t y‖ = ((‖f t y‖₊ : ℝ≥0) : ℝ) := (coe_nnnorm _).symm
      _ ≤ ((‖Cf‖₊ : ℝ≥0) : ℝ) := by exact_mod_cast h
  · -- hA_bound: pure operator-norm estimate, no regularity needed.
    intro A hA
    have h1 : dist A A₀ ≤ (a : ℝ) := mem_closedBall.mp hA
    have h2 : ‖A - A₀‖ ≤ (a : ℝ) := by rwa [dist_eq_norm] at h1
    have h3 : ‖A‖ ≤ ‖A₀‖ + (a : ℝ) := by
      have e : A₀ + (A - A₀) = A := add_sub_cancel _ _
      calc ‖A‖ = ‖A₀ + (A - A₀)‖ := by rw [e]
        _ ≤ ‖A₀‖ + ‖A - A₀‖ := norm_add_le _ _
        _ ≤ ‖A₀‖ + (a : ℝ) := by linarith [h2]
    exact_mod_cast h3
  · -- hD_bound: uniform derivative bound from joint continuity.
    intro t ht y hy
    exact hCD_nn t (hIcc_sub ht) y hy
  · -- hf_cont: separate time continuity from joint continuity.
    intro y hy
    have h1 : ContinuousOn (fun t : ℝ => (t, y)) (Icc (t₀ - δ) (t₀ + δ)) :=
      continuousOn_id.prodMk continuousOn_const
    have hmaps : MapsTo (fun t : ℝ => (t, y)) (Icc (t₀ - δ) (t₀ + δ))
        (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ ↑a) := by
      intro t ht
      exact ⟨hIcc_sub ht, hy⟩
    have hcomp := hjoint_fst.comp h1 hmaps
    simpa [Function.comp_def] using hcomp
  · -- hDf_cont: separate time continuity of the derivative.
    intro y hy
    have h1 : ContinuousOn (fun t : ℝ => (t, y)) (Icc (t₀ - δ) (t₀ + δ)) :=
      continuousOn_id.prodMk continuousOn_const
    have hmaps : MapsTo (fun t : ℝ => (t, y)) (Icc (t₀ - δ) (t₀ + δ))
        (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall y₀ ↑a) := by
      intro t ht
      exact ⟨hIcc_sub ht, hy⟩
    have hcomp := hjoint_snd.comp h1 hmaps
    simpa [Function.comp_def] using hcomp
  · -- hmul: the interval-size inequality, by choice of δ.
    have e1 : (t₀ + δ) - t₀ = δ := by ring
    have e2 : t₀ - (t₀ - δ) = δ := by ring
    rw [e1, e2, max_self, ← hP_def, ← hX_def]
    -- Goal: ↑P * δ ≤ X
    have hpos : (0 : ℝ) < (↑P + 1) := by positivity
    calc ((P : ℝ≥0) : ℝ) * δ
        ≤ ((P : ℝ≥0) : ℝ) * (X / (↑P + 1)) :=
          mul_le_mul_of_nonneg_left hδ_le hP_nn
      _ = ((P : ℝ≥0) : ℝ) * X / (↑P + 1) := by rw [mul_div_assoc']
      _ ≤ X := by
          rw [div_le_iff₀ hpos]
          have e : X * (↑P + 1) = ((P : ℝ≥0) : ℝ) * X + X := by ring
          rw [e]
          linarith [hX_nn]

/-- The seven Picard–Lindelöf estimates for the DeTurck gauge field's coordinate
expression, from the explicit regularity package (`hreg`, `hjoint`, `hjoint2`).

This is the direct instantiation of
`picardEstimates_of_contDiffOn_two_and_jointContinuity` at the genuine
coordinate field `deTurckGaugeCoordinateField` (the negated DeTurck field in
`extChartAt I p₀`) with spatial derivative `deTurckGaugeCoordinateDerivative`.
Its conclusions are exactly the hypotheses of
`ModelGaugeFlowODE.isPicardLindelof_variationalVectorField_of_component_closedBall_continuity`. -/
theorem deTurckGaugeCoordinatePicardEstimates
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (p₀ : M) (t₀ : ℝ) (a : ℝ≥0) (ha : 0 < (a : ℝ))
    (A₀ : E →L[ℝ] E)
    (hreg : ∀ t ∈ Icc (t₀ - 1) (t₀ + 1),
      ContDiffOn ℝ 2
        (deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ t)
        (ball (extChartAt I p₀ p₀) ((a : ℝ) + 1)))
    (hjoint : ContinuousOn
      (fun p : ℝ × E =>
        (deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ p.1 p.2,
          fderiv ℝ (deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ p.1) p.2))
      (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall (extChartAt I p₀ p₀) (a : ℝ)))
    (hjoint2 : ContinuousOn
      (fun p : ℝ × E =>
        fderiv ℝ
          (fderiv ℝ (deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ p.1)) p.2)
      (Icc (t₀ - 1) (t₀ + 1) ×ˢ closedBall (extChartAt I p₀ p₀) (a : ℝ))) :
    ∃ (tmin tmax : ℝ) (r Kf KD Lf BA BD : ℝ≥0),
      (∀ t ∈ Icc tmin tmax,
        LipschitzOnWith Kf
          (deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ t)
          (closedBall (extChartAt I p₀ p₀) ↑a)) ∧
      (∀ t ∈ Icc tmin tmax,
        LipschitzOnWith KD
          (deTurckGaugeCoordinateDerivative (I := I) (M := M) g background p₀ t)
          (closedBall (extChartAt I p₀ p₀) ↑a)) ∧
      (∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall (extChartAt I p₀ p₀) ↑a,
        ‖deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ t y‖ ≤ ↑Lf) ∧
      (∀ A ∈ closedBall A₀ ↑a, ‖A‖₊ ≤ BA) ∧
      (∀ t ∈ Icc tmin tmax, ∀ y ∈ closedBall (extChartAt I p₀ p₀) ↑a,
        ‖deTurckGaugeCoordinateDerivative (I := I) (M := M) g background p₀ t y‖₊ ≤ BD) ∧
      (∀ y ∈ closedBall (extChartAt I p₀ p₀) ↑a,
        ContinuousOn
          (fun t : ℝ => deTurckGaugeCoordinateField (I := I) (M := M) g background p₀ t y)
          (Icc tmin tmax)) ∧
      (∀ y ∈ closedBall (extChartAt I p₀ p₀) ↑a,
        ContinuousOn
          (fun t : ℝ => deTurckGaugeCoordinateDerivative (I := I) (M := M) g background p₀ t y)
          (Icc tmin tmax)) ∧
      (↑(max Lf (BD * BA)) * max (tmax - t₀) (t₀ - tmin) ≤ ↑a - ↑r) :=
  picardEstimates_of_contDiffOn_two_and_jointContinuity
    (f := deTurckGaugeCoordinateField (I := I) (M := M) g background p₀)
    (y₀ := extChartAt I p₀ p₀) ha A₀ hreg hjoint hjoint2

end RicciFlow
