/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.InterpolationLemma
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.UniformSmallness
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.ContinuousOn

/-! # Joint Regularity Upgrade -/

@[expose] public noncomputable section

open Metric Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-!
# Joint Regularity Upgrade via Interpolation

This module proves the key reduction: uniform C² bounds + joint C⁰
implies joint C¹, via the interpolation lemma.

Given `F : ℝ → E → F'` with:
- Each `F t` is C² on `ball x₀ R` with `‖D²(F t)‖ ≤ M₂` (uniform in `t`)
- `(t,x) ↦ F t x` is jointly continuous

Then `(t,x) ↦ D(F t)(x)` is jointly continuous.

## Proof Strategy

Fix `(t₀,x₁)`. For `(t,x)` near `(t₀,x₁)`:
1. Set `H(y) = F t y - F t₀ y`. Then `‖H‖ ≤ M₀(t)` where `M₀(t) → 0`
   as `t → t₀` by joint C⁰ (uniform on compact balls via `UniformSmallness`).
2. `‖D²H(y)‖ ≤ 2M₂` by triangle inequality.
3. Interpolation applied to `H` at `x`:
   `‖D(F t)(x) - D(F t₀)(x)‖ = ‖DH(x)‖ ≤ 2M₀(t)/h + h(2M₂)`.
4. Choose `h = √M₀(t)`: bound `= 2√M₀(t)·(1+M₂) → 0`.
5. Combine with spatial continuity of `D(F t₀)` at `x₁` (from C² regularity).
-/

/-- Each time-slice is differentiable at every point of the ball. -/
theorem differentiableAt_slice_of_contDiffOn {F : ℝ → E → F'} {x₀ : E} {R : ℝ}
    {t : ℝ} {y : E}
    (hreg : ∀ s : ℝ, ContDiffOn ℝ 2 (F s) (ball x₀ R))
    (hy : y ∈ ball x₀ R) :
    DifferentiableAt ℝ (F t) y :=
  ((hreg t).differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds hy)

/-- The difference `H = F t - F t₀` of time-slices is C² on the ball. -/
theorem contDiffOn_slice_diff {F : ℝ → E → F'} {x₀ : E} {R : ℝ} {t t₀ : ℝ}
    (hreg : ∀ s : ℝ, ContDiffOn ℝ 2 (F s) (ball x₀ R)) :
    ContDiffOn ℝ 2 (fun y => F t y - F t₀ y) (ball x₀ R) :=
  (hreg t).sub (hreg t₀)

/-- Second derivative of the slice difference equals the difference of
second derivatives. Uses that the two agree on a neighborhood of `y`. -/
theorem fderiv_fderiv_slice_diff {F : ℝ → E → F'} {x₀ : E} {R : ℝ}
    {t t₀ : ℝ} {y : E}
    (hreg : ∀ s : ℝ, ContDiffOn ℝ 2 (F s) (ball x₀ R))
    (hy : y ∈ ball x₀ R) :
    fderiv ℝ (fun z => fderiv ℝ (fun w => F t w - F t₀ w) z) y
      = fderiv ℝ (fun z => fderiv ℝ (F t) z) y
        - fderiv ℝ (fun z => fderiv ℝ (F t₀) z) y := by
  have hCt : ContDiffAt ℝ 2 (F t) y := (hreg t).contDiffAt (isOpen_ball.mem_nhds hy)
  have hCt₀ : ContDiffAt ℝ 2 (F t₀) y := (hreg t₀).contDiffAt (isOpen_ball.mem_nhds hy)
  have hD1 : DifferentiableAt ℝ (fderiv ℝ (F t)) y :=
    (contDiffAt_two_hasFDerivAt_fderiv hCt).differentiableAt
  have hD2 : DifferentiableAt ℝ (fderiv ℝ (F t₀)) y :=
    (contDiffAt_two_hasFDerivAt_fderiv hCt₀).differentiableAt
  -- The two functions agree on the ball (a neighborhood of y)
  have heq : (fun z => fderiv ℝ (fun w => F t w - F t₀ w) z)
      =ᶠ[𝓝 y] (fun z => fderiv ℝ (F t) z - fderiv ℝ (F t₀) z) := by
    filter_upwards [isOpen_ball.mem_nhds hy] with z hz
    exact fderiv_fun_sub (differentiableAt_slice_of_contDiffOn hreg hz)
      (differentiableAt_slice_of_contDiffOn (t := t₀) hreg hz)
  have hsub : HasFDerivAt (fun z => fderiv ℝ (F t) z - fderiv ℝ (F t₀) z)
      (fderiv ℝ (fun z => fderiv ℝ (F t) z) y
        - fderiv ℝ (fun z => fderiv ℝ (F t₀) z) y) y := by
    have h := (hD1.sub hD2).hasFDerivAt
    rwa [fderiv_sub hD1 hD2] at h
  have hF := hsub.congr_of_eventuallyEq heq
  exact hF.fderiv

/-- Triangle bound: `‖D²(F t - F t₀)(y)‖ ≤ 2M₂`. -/
theorem norm_fderiv_fderiv_slice_diff_le {F : ℝ → E → F'} {x₀ : E} {R : ℝ}
    {t t₀ : ℝ} {y : E} {M₂ : ℝ}
    (hreg : ∀ s : ℝ, ContDiffOn ℝ 2 (F s) (ball x₀ R))
    (hD2 : ∀ s : ℝ, ∀ z ∈ ball x₀ R,
      ‖fderiv ℝ (fun w => fderiv ℝ (F s) w) z‖ ≤ M₂)
    (hy : y ∈ ball x₀ R) :
    ‖fderiv ℝ (fun z => fderiv ℝ (fun w => F t w - F t₀ w) z) y‖ ≤ 2 * M₂ := by
  rw [fderiv_fderiv_slice_diff hreg hy]
  calc ‖fderiv ℝ (fun z => fderiv ℝ (F t) z) y
          - fderiv ℝ (fun z => fderiv ℝ (F t₀) z) y‖
      ≤ ‖fderiv ℝ (fun z => fderiv ℝ (F t) z) y‖
        + ‖fderiv ℝ (fun z => fderiv ℝ (F t₀) z) y‖ :=
        norm_sub_le (fderiv ℝ (fun z => fderiv ℝ (F t) z) y)
          (fderiv ℝ (fun z => fderiv ℝ (F t₀) z) y)
    _ ≤ M₂ + M₂ := add_le_add (hD2 t y hy) (hD2 t₀ y hy)
    _ = 2 * M₂ := by ring

/-- Interpolation applied to the difference of time-slices.

For `x ∈ closedBall x₀ r` and `0 < h ≤ r/2`, if `‖F t - F t₀‖ ≤ M₀`
on `closedBall x₀ (2r)`, then
`‖D(F t)(x) - D(F t₀)(x)‖ ≤ 2M₀/h + h(2M₂)`.
-/
theorem interpolation_slice_diff_bound
    {F : ℝ → E → F'} {x₀ : E} {R r : ℝ} (hr : 0 < r) (hR : 2 * r < R)
    {M₂ : ℝ}
    (hreg : ∀ s : ℝ, ContDiffOn ℝ 2 (F s) (ball x₀ R))
    (hD2 : ∀ s : ℝ, ∀ y ∈ ball x₀ R,
      ‖fderiv ℝ (fun z => fderiv ℝ (F s) z) y‖ ≤ M₂)
    {t t₀ : ℝ} {M₀ : ℝ}
    (hH : ∀ y ∈ closedBall x₀ (2 * r), ‖F t y - F t₀ y‖ ≤ M₀)
    {x : E} (hx : x ∈ closedBall x₀ r)
    {h : ℝ} (hh : 0 < h) (hhr : h ≤ r / 2) :
    ‖fderiv ℝ (F t) x - fderiv ℝ (F t₀) x‖ ≤ 2 * M₀ / h + h * (2 * M₂) := by
  have hx_norm : ‖x - x₀‖ ≤ r := by
    have := mem_closedBall.mp hx; rwa [dist_eq_norm] at this
  -- The small ball sits inside the big ball
  have hball_sub : ball x r ⊆ ball x₀ R := by
    intro y hy
    rw [mem_ball, dist_eq_norm] at hy ⊢
    calc ‖y - x₀‖ = ‖(y - x) + (x - x₀)‖ := by abel
      _ ≤ ‖y - x‖ + ‖x - x₀‖ := norm_add_le _ _
      _ < r + r := by linarith [hy, hx_norm]
      _ = 2 * r := by ring
      _ < R := hR
  have hball2_sub : ball x r ⊆ closedBall x₀ (2 * r) := by
    intro y hy
    rw [mem_ball, dist_eq_norm] at hy
    rw [mem_closedBall, dist_eq_norm]
    calc ‖y - x₀‖ = ‖(y - x) + (x - x₀)‖ := by abel
      _ ≤ ‖y - x‖ + ‖x - x₀‖ := norm_add_le _ _
      _ ≤ r + r := by linarith [hy.le, hx_norm]
      _ = 2 * r := by ring
  have hclosed_sub : closedBall x (r / 2) ⊆ ball x r := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    rw [mem_ball, dist_eq_norm]
    linarith [hy, hr]
  -- Apply the interpolation lemma to H = F t - F t₀, centered at x with radius r
  have key := norm_fderiv_le_of_C2_bound
    (f := fun y => F t y - F t₀ y) (x₀ := x) (R := r) (x := x)
    ((contDiffOn_slice_diff hreg).mono hball_sub)
    (M₀ := M₀) (M₂ := 2 * M₂)
    (fun y hy => hH y (hball2_sub hy))
    (fun y hy => norm_fderiv_fderiv_slice_diff_le hreg hD2 (hball_sub hy))
    (δ := r / 2) (h := h) (by linarith) hh hhr hclosed_sub
  -- Rewrite fderiv of the difference as a difference of fderivs
  have hxR : x ∈ ball x₀ R := by
    apply hball_sub
    rw [mem_ball, dist_self]
    exact hr
  have hdiff : DifferentiableAt ℝ (F t) x ∧ DifferentiableAt ℝ (F t₀) x :=
    ⟨differentiableAt_slice_of_contDiffOn hreg hxR,
     differentiableAt_slice_of_contDiffOn (t := t₀) hreg hxR⟩
  rw [fderiv_fun_sub hdiff.1 hdiff.2] at key
  exact key

/-- Joint C⁰ + uniform C² bounds ⟹ joint continuity of the derivative.

This is the core reduction for discharging `DeTurckCoordinateFieldJointRegularity`.
The uniform `M₂` bound comes from the PDE estimate (uniform C³ metric bounds
imply uniform C² field bounds via jet calculus).

The proof fixes `(t₀,x₁)` and shows continuity there. For `(t,x)` nearby,
the triangle inequality splits into a time term (controlled by interpolation
applied to `H = F t - F t₀` with `h = √M₀(t)`, where `M₀(t) → 0` by uniform
smallness on the compact ball) and a spatial term (controlled by C² regularity
of the fixed slice `F t₀`). -/
theorem joint_deriv_continuous_of_uniform_C2
    {F : ℝ → E → F'} {x₀ : E} {R r : ℝ} (hr : 0 < r) (hR : 2 * r < R)
    {M₂ : ℝ} (hM₂ : 0 ≤ M₂)
    (hreg : ∀ s : ℝ, ContDiffOn ℝ 2 (F s) (ball x₀ R))
    (hD2 : ∀ s : ℝ, ∀ y ∈ ball x₀ R,
      ‖fderiv ℝ (fun z => fderiv ℝ (F s) z) y‖ ≤ M₂)
    (hjoint : ContinuousOn (fun p : ℝ × E => F p.1 p.2)
      (univ ×ˢ closedBall x₀ (2 * r))) :
    ContinuousOn (fun p : ℝ × E => fderiv ℝ (F p.1) p.2)
      (univ ×ˢ closedBall x₀ r) := by
  intro p hp
  obtain ⟨t₀, x₁⟩ := p
  simp only [mem_prod, mem_univ, true_and] at hp
  -- hp : x₁ ∈ closedBall x₀ r
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  -- Spatial continuity of D(F t₀) at x₁, from C² regularity
  have hx₁_norm : ‖x₁ - x₀‖ ≤ r := by
    have := mem_closedBall.mp hp; rwa [dist_eq_norm] at this
  have hx₁R : x₁ ∈ ball x₀ R := by
    rw [mem_ball, dist_eq_norm]; linarith [hx₁_norm, hr, hR]
  have hcont_spatial : ContinuousAt (fun x => fderiv ℝ (F t₀) x) x₁ :=
    ((hreg t₀).continuousOn_fderiv_of_isOpen isOpen_ball (by norm_num)).continuousAt
      (isOpen_ball.mem_nhds hx₁R)
  rw [Metric.continuousAt_iff] at hcont_spatial
  obtain ⟨δs, hδs, hsp⟩ := hcont_spatial (ε / 2) (by linarith)
  -- hsp : ∀ x, dist x x₁ < δs → dist (D(F t₀) x) (D(F t₀) x₁) < ε/2
  -- Choose the smallness threshold ε₁ for the time term
  set c := 2 * (1 + M₂) with hc
  have hcpos : 0 < c := by rw [hc]; linarith [hM₂]
  have h1 : (0:ℝ) < r ^ 2 / 4 := by positivity
  have h2 : (0:ℝ) < (ε / (2 * c)) ^ 2 := by
    have hpos : (0:ℝ) < ε / (2 * c) := div_pos hε (by linarith [hcpos])
    exact pow_pos hpos 2
  obtain ⟨ε₁, hε₁pos, hε₁ub1, hε₁ub2⟩ :
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ r ^ 2 / 4 ∧ ε₁ < (ε / (2 * c)) ^ 2 := by
    set a := r ^ 2 / 4 with ha
    set b := (ε / (2 * c)) ^ 2 with hb
    refine ⟨(min a b) / 2, by linarith [lt_min h1 h2], ?_, ?_⟩
    · have hmin : min a b ≤ a := min_le_left a b
      linarith
    · have hmin : min a b ≤ b := min_le_right a b
      have hbpos : 0 < b := h2
      linarith
  obtain ⟨η, hηpos, hη⟩ :=
    uniform_smallness_of_joint_continuous hjoint (t₀ := t₀) ε₁ hε₁pos
  -- hη : ∀ t, dist t t₀ < η → ∀ y ∈ closedBall x₀ (2*r), ‖F t y - F t₀ y‖ < ε₁
  refine ⟨min δs η, lt_min hδs hηpos, fun q hqmem hqdist => ?_⟩
  obtain ⟨t, x⟩ := q
  simp only [mem_prod, mem_univ, true_and] at hqmem
  -- hqmem : x ∈ closedBall x₀ r
  -- goal: dist (D(F t) x) (D(F t₀) x₁) < ε
  rw [dist_eq_norm]
  show ‖fderiv ℝ (F t) x - fderiv ℝ (F t₀) x₁‖ < ε
  rw [Prod.dist_eq] at hqdist
  have ht_close : dist t t₀ < η :=
    lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hqdist (min_le_right _ _))
  have hx_close : dist x x₁ < δs :=
    lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hqdist (min_le_left _ _))
  -- Time term: interpolation with h = √ε₁
  have hM₀ : ∀ y ∈ closedBall x₀ (2 * r), ‖F t y - F t₀ y‖ ≤ ε₁ :=
    fun y hy => (hη t ht_close y hy).le
  have hsqrt_pos : 0 < Real.sqrt ε₁ := Real.sqrt_pos.mpr hε₁pos
  have hsqrt_le : Real.sqrt ε₁ ≤ r / 2 := by
    have h1 : Real.sqrt ε₁ ≤ Real.sqrt (r ^ 2 / 4) :=
      (Real.sqrt_le_sqrt_iff (by positivity)).mpr hε₁ub1
    have h2 : Real.sqrt (r ^ 2 / 4) = r / 2 := by
      have hr2 : (r / 2) ^ 2 = r ^ 2 / 4 := by ring
      rw [← hr2, Real.sqrt_sq (by linarith)]
    linarith
  have hinterp := interpolation_slice_diff_bound hr hR hreg hD2 hM₀ hqmem
    hsqrt_pos hsqrt_le
  -- hinterp : ‖D(F t) x - D(F t₀) x‖ ≤ 2*ε₁/√ε₁ + √ε₁*(2*M₂)
  have hsqrt_eq : 2 * ε₁ / Real.sqrt ε₁ = 2 * Real.sqrt ε₁ := by
    have h1 : ε₁ / Real.sqrt ε₁ = Real.sqrt ε₁ := by
      rw [div_eq_iff (ne_of_gt hsqrt_pos)]
      exact (Real.mul_self_sqrt hε₁pos.le).symm
    calc 2 * ε₁ / Real.sqrt ε₁ = 2 * (ε₁ / Real.sqrt ε₁) := by ring
      _ = 2 * Real.sqrt ε₁ := by rw [h1]
  rw [hsqrt_eq] at hinterp
  have hsqrt_lt : Real.sqrt ε₁ < ε / (2 * c) := by
    have h1 : Real.sqrt ε₁ < Real.sqrt ((ε / (2 * c)) ^ 2) :=
      (Real.sqrt_lt_sqrt_iff hε₁pos.le).mpr hε₁ub2
    have h2 : (0:ℝ) ≤ ε / (2 * c) := by positivity
    rwa [Real.sqrt_sq h2] at h1
  have htime : ‖fderiv ℝ (F t) x - fderiv ℝ (F t₀) x‖ < ε / 2 := by
    calc ‖fderiv ℝ (F t) x - fderiv ℝ (F t₀) x‖
        ≤ 2 * Real.sqrt ε₁ + Real.sqrt ε₁ * (2 * M₂) := hinterp
      _ = c * Real.sqrt ε₁ := by rw [hc]; ring
      _ < c * (ε / (2 * c)) := mul_lt_mul_of_pos_left hsqrt_lt hcpos
      _ = ε / 2 := by field_simp
  -- Spatial term: continuity of D(F t₀) at x₁
  have hspatial : ‖fderiv ℝ (F t₀) x - fderiv ℝ (F t₀) x₁‖ < ε / 2 := by
    have h := hsp hx_close
    simpa [dist_eq_norm] using h
  -- Triangle inequality combines them
  have htri : ‖fderiv ℝ (F t) x - fderiv ℝ (F t₀) x₁‖
      ≤ ‖fderiv ℝ (F t) x - fderiv ℝ (F t₀) x‖
        + ‖fderiv ℝ (F t₀) x - fderiv ℝ (F t₀) x₁‖ := by
    have heq : fderiv ℝ (F t) x - fderiv ℝ (F t₀) x₁
        = (fderiv ℝ (F t) x - fderiv ℝ (F t₀) x)
          + (fderiv ℝ (F t₀) x - fderiv ℝ (F t₀) x₁) := by abel
    rw [heq]
    exact norm_add_le (fderiv ℝ (F t) x - fderiv ℝ (F t₀) x)
      (fderiv ℝ (F t₀) x - fderiv ℝ (F t₀) x₁)
  calc ‖fderiv ℝ (F t) x - fderiv ℝ (F t₀) x₁‖
      ≤ ‖fderiv ℝ (F t) x - fderiv ℝ (F t₀) x‖
        + ‖fderiv ℝ (F t₀) x - fderiv ℝ (F t₀) x₁‖ := htri
    _ < ε / 2 + ε / 2 := add_lt_add htime hspatial
    _ = ε := by ring

/-- Second-derivative version: the upgrade iterates.

If the derivative family `G t = D(F t)` itself satisfies the hypotheses
(uniform C² bounds on `D(F t)`, i.e. uniform C³ bounds on `F t`, plus joint
continuity of `D(F t)`), then `D²(F t)` is jointly continuous.

In the DeTurck application, joint continuity of `D(F t)` is the *output* of
`joint_deriv_continuous_of_uniform_C2`, and uniform C³ bounds on the metric
give uniform C² bounds on the derivative field via jet calculus. This replaces
the earlier tautological axiom (whose hypothesis *was* its conclusion) with a
genuine statement proved by applying the main theorem to the derivative family.
-/
theorem joint_second_deriv_continuous_of_uniform_C3
    {F : ℝ → E → E} {x₀ : E} {R r : ℝ} (hr : 0 < r) (hR : 2 * r < R)
    {M₃ : ℝ} (hM₃ : 0 ≤ M₃)
    (hregD : ∀ s : ℝ, ContDiffOn ℝ 2 (fun z => fderiv ℝ (F s) z) (ball x₀ R))
    (hD3 : ∀ s : ℝ, ∀ y ∈ ball x₀ R,
      ‖fderiv ℝ (fun z => fderiv ℝ (fun w => fderiv ℝ (F s) w) z) y‖ ≤ M₃)
    (hjointD : ContinuousOn (fun p : ℝ × E => fderiv ℝ (F p.1) p.2)
      (univ ×ˢ closedBall x₀ (2 * r))) :
    ContinuousOn
      (fun p : ℝ × E => fderiv ℝ (fun z => fderiv ℝ (F p.1) z) p.2)
      (univ ×ˢ closedBall x₀ r) :=
  joint_deriv_continuous_of_uniform_C2 hr hR hM₃ hregD hD3 hjointD

end
